"""Public JSON-to-C boundary tests, with freshly extracted library declarations.

Run after building the theories, under the pinned opam environment. Each class
extracts the tracked production client into a temporary build/c directory; no
probe paths or preexisting generated JSON are used. Small AST clients below
exercise reusable rules using those actual, identity-checked declarations.
"""

import copy
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "extract_c.py"
SPEC = importlib.util.spec_from_file_location("extract_c", SCRIPT)
backend = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = backend
SPEC.loader.exec_module(backend)


def rel(name):
    return {"what": "expr:rel", "name": name}


def lam(names, body):
    return {"what": "expr:lambda", "argnames": names, "body": body}


def constructor(name, *args):
    return {"what": "expr:constructor", "name": name, "args": list(args)}


def natural(value):
    result = constructor("O")
    for _ in range(value):
        result = constructor("S", result)
    return result


def apply(function, *args):
    if isinstance(function, str):
        function = {"what": "expr:global", "name": function}
    return {"what": "expr:apply", "func": function, "args": list(args)}


def returned(value):
    return constructor("Go", constructor("RetF", value))


def bind(computation, name, next_computation):
    return apply("bind", computation, lam([name], next_computation))


def let(name, value, body):
    return {"what": "expr:let", "name": name, "nameval": value, "body": body}


def case(value, *alternatives):
    return {"what": "expr:case", "expr": value, "cases": [
        {"what": "case", "pat": {"what": "pat:constructor", "name": name,
                                "argnames": arguments}, "body": body}
        for name, arguments, body in alternatives
    ]}


def nat_case(value, zero, successor, predecessor="rest"):
    return case(value, ("O", [], zero), ("S", [predecessor], successor))


def pair(first, second):
    return constructor("Pair", first, second)


def walk(root):
    # Fixture traversal stays independent of the backend's private validator.
    pending = [root]
    while pending:
        value = pending.pop()
        if isinstance(value, dict):
            yield value
            pending.extend(value.values())
        elif isinstance(value, list):
            pending.extend(value)


def declaration(document, name):
    for item in document["declarations"]:
        if item.get("name") == name:
            return item
        for fix in item.get("fixlist", []):
            if fix["name"] == name:
                return fix
    raise RuntimeError("test requires extracted declaration " + name)


class GeneratorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        rocq = shlex.split(os.environ.get("ROCQ", "rocq"))
        if not rocq:
            raise RuntimeError("ROCQ must not be empty")
        if shutil.which(rocq[0]) is None:
            if "ROCQ" in os.environ:
                raise RuntimeError("ROCQ executable not found: " + rocq[0])
            raise unittest.SkipTest("Rocq is unavailable; run under opam exec")
        temporary = tempfile.TemporaryDirectory(prefix="c-extraction-tests-")
        cls.addClassCleanup(temporary.cleanup)
        cls.root = Path(temporary.name)
        cls.output = cls.root / "build" / "c"
        cls.output.mkdir(parents=True)
        result = subprocess.run(
            rocq + ["repl", "-batch", "-quiet", "-Q", str(ROOT / "theories"),
                    "RefineToITree", "-l", str(ROOT / "extraction" / "ExtractC.v")],
            cwd=cls.root, capture_output=True, text=True, timeout=120,
        )
        if result.returncode:
            raise RuntimeError("Fresh target extraction failed; build the theories first:\n"
                               + result.stdout + result.stderr)
        cls.document = json.loads((cls.output / "targets.json").read_text(encoding="utf-8"))
        # Get actual erased dictionary syntax rather than recreating it in tests.
        cls.dictionaries = {}
        for node in walk(declaration(cls.document, "fib_L3")["value"]):
            if node.get("what") == "expr:apply" and node["func"].get("what") == "expr:global":
                name = node["func"]["name"]
                if name in {"array_alloc", "cost_iter"}:
                    cls.dictionaries[name] = copy.deepcopy(node["args"][0])

    def program(self, body, time_only=False, recursive=False):
        document = copy.deepcopy(self.document)
        client = copy.deepcopy(declaration(document, "fib_L3"))
        client["name"] = "client"
        client["value"] = lam(["input"], body)
        if time_only:
            # Select the actual TimeE coordinate from the tracked client's sum.
            client["type"]["right"]["args"][0] = copy.deepcopy(
                client["type"]["right"]["args"][0]["args"][1])
        if recursive:
            client["what"] = "fixgroup:item"
            document["declarations"].append({"what": "decl:fixgroup", "fixlist": [client]})
        else:
            document["declarations"].append(client)
        return document

    def generate_body(self, body, time_only=False, recursive=False):
        return backend.generate(self.program(body, time_only, recursive), ["client"])

    def memory(self, name, *args):
        return apply(name, copy.deepcopy(self.dictionaries["array_alloc"]), *args)

    def charged(self, name, *args):
        return apply(name, copy.deepcopy(self.dictionaries["cost_iter"]), *args)

    def time_charged(self, name, *args):
        # The direct identity is the existing sum dictionary's final argument.
        identity = self.dictionaries["cost_iter"]["args"][-1]
        return apply(name, copy.deepcopy(identity), *args)

    def iteration(self, state, body, initial):
        return self.charged("cost_iter", lam([state], body), initial)

    def rejects(self, body, diagnostic, time_only=False, recursive=False):
        with self.assertRaisesRegex(backend.Unsupported, diagnostic):
            self.generate_body(body, time_only, recursive)

    def execute(self, body, inputs, expected, sanitize=False):
        self.execute_generated(self.generate_body(body), [("client", value) for value in inputs],
                               expected, sanitize)

    def execute_generated(self, generated, calls, expected, sanitize=False):
        cc = shlex.split(os.environ.get("CLANG", "clang"))
        if not cc or shutil.which(cc[0]) is None:
            self.fail("C boundary tests require Clang (or CLANG)")
        source, header, _metadata = generated
        with tempfile.TemporaryDirectory(dir=self.output, prefix="native-") as directory:
            directory = Path(directory)
            (directory / "generated.c").write_text(source, encoding="utf-8")
            (directory / "generated.h").write_text(header, encoding="utf-8")
            statements = "".join('  printf("%" PRIu64 "\\n", ' + name + '(UINT64_C('
                                 + str(value) + ')));\n' for name, value in calls)
            (directory / "driver.c").write_text(
                '#include "generated.h"\n#include <inttypes.h>\n#include <stdio.h>\n'
                "int main(void)\n{\n" + statements + "  return 0;\n}\n", encoding="utf-8")
            command = cc + ["-std=c11", "-O2", "-Wall", "-Wextra", "-Wpedantic", "-Werror",
                            "-Wconversion", "-Wshadow", "-Wstrict-prototypes",
                            "-Wmissing-prototypes", "-Wformat=2", "-Wundef", "-Wvla"]
            if sanitize:
                command += ["-g", "-fno-omit-frame-pointer",
                            "-fsanitize=address,undefined,unsigned-integer-overflow",
                            "-fno-sanitize-recover=all"]
            command += [str(directory / "generated.c"), str(directory / "driver.c"),
                        "-o", str(directory / "run")]
            result = subprocess.run(command, capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr + "\n" + source)
            result = subprocess.run([str(directory / "run")], capture_output=True,
                                    text=True, timeout=20)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual([int(line) for line in result.stdout.splitlines()], expected)

    def test_actual_targets_and_metadata(self):
        source, header, metadata = backend.generate(
            self.document, ["fib_L3", "fib_L4"], {"fib_L3": "fib_l3", "fib_L4": "fib_l4"})
        for extracted, c_name in (("fib_L3", "fib_l3"), ("fib_L4", "fib_l4")):
            self.assertIn("uint64_t " + c_name + "(uint64_t input);", header)
            self.assertEqual(metadata[extracted]["array_cells"], 2)
            self.assertEqual(metadata[extracted]["loops"], 2)
            self.assertEqual(metadata[extracted]["recursive_calls"], 0)
        self.assertIn('#include "generated.h"', source)
        self.assertNotRegex(source, r"\b(?:itree|trigger|malloc|calloc|realloc|cost_iter|bind)\b")
        self.assertEqual(backend.generate(self.document, ["fib_L3"]),
                         backend.generate(copy.deepcopy(self.document), ["fib_L3"]))

    def test_actual_l1_l2_native_results_and_recursion_metadata(self):
        targets = ["fib_L3", "fib_L4", "fib_L1", "fib_L2"]
        names = {name: name.lower() for name in targets}
        generated = backend.generate(self.document, targets, names)
        source, header, metadata = generated
        self.assertEqual(metadata["fib_L1"]["recursive_calls"], 2)
        self.assertEqual(metadata["fib_L1"]["array_cells"], 0)
        self.assertEqual(metadata["fib_L1"]["loops"], 0)
        self.assertEqual(metadata["fib_L2"]["recursive_calls"], 0)
        self.assertEqual(metadata["fib_L2"]["array_cells"], 2)
        self.assertEqual(metadata["fib_L2"]["loops"], 1)
        self.assertEqual(len(re.findall(
            r"const uint64_t v[0-9]+ = fib_l1\(v[0-9]+\);", source)), 2)
        for name in names.values():
            self.assertIn("uint64_t " + name + "(uint64_t input);", header)
        for item in metadata.values():
            self.assertIs(type(item["recursive_calls"]), int)
        # Exact-integer values, computed independently of the extracted AST.
        reference, first, second = [], 0, 1
        for _ in range(92):
            reference.append(first)
            first, second = second, first + second
        calls = [(name, n) for name in names.values()
                 for n in range(21 if name == "fib_l1" else 92)]
        self.execute_generated(generated, calls, [reference[n] for _name, n in calls], sanitize=True)

    def test_time_only_return_and_identity_function_entry(self):
        for body, expected in ((returned(rel("input")), [0, 7, 91]), (self.time_charged(
                "function_entry", lam(["n"], self.time_charged("cost_add", rel("n"), natural(3))),
                rel("input")), [3, 10, 94])):
            with self.subTest(body=body):
                generated = backend.generate(self.program(body, time_only=True), ["client"])
                source, header, metadata = generated
                self.assertIn("uint64_t client(uint64_t input);", header)
                self.assertEqual(metadata["client"]["array_cells"], 0)
                self.assertEqual(metadata["client"]["recursive_calls"], 0)
                self.assertNotIn("cells[", source)
                self.execute_generated(generated, [("client", n) for n in (0, 7, 91)], expected)

    def test_recursive_countdown_uses_mapped_native_self_calls(self):
        body = self.time_charged("function_entry", lam(["n"], nat_case(
            rel("n"), returned(natural(3)), bind(apply("client", rel("rest")), "value",
                self.time_charged("cost_add", rel("value"), natural(2))))), rel("input"))
        generated = backend.generate(self.program(body, time_only=True, recursive=True),
                                     ["client"], {"client": "walk_down"})
        source, header, metadata = generated
        self.assertEqual(metadata["client"]["recursive_calls"], 1)
        self.assertEqual(metadata["client"]["c_name"], "walk_down")
        self.assertEqual(metadata["client"]["array_cells"], 0)
        self.assertEqual(metadata["client"]["loops"], 0)
        self.assertIn("uint64_t walk_down(uint64_t input);", header)
        self.assertRegex(source, r"const uint64_t v[0-9]+ = walk_down\(v[0-9]+\);")
        self.assertNotIn("client(", source)
        self.execute_generated(generated, [("walk_down", n) for n in (0, 1, 2, 5, 20)],
                               [3, 5, 7, 13, 43], sanitize=True)

    def test_time_only_cost_iter_and_local_identity_wrappers(self):
        step = case(rel("state"), ("Pair", ["n", "total"], nat_case(
            rel("n"), returned(constructor("Inr", rel("total"))),
            bind(self.time_charged("cost_add", rel("total"), natural(3)), "next",
                 returned(constructor("Inl", pair(rel("rest"), rel("next"))))))))
        body = let("identity", lam(["x"], rel("x")), self.time_charged(
            "function_entry", lam(["start"], self.time_charged(
                "cost_iter", lam(["state"], step), pair(rel("start"), natural(0)))),
            apply(rel("identity"), rel("input"))))
        generated = self.generate_body(body, time_only=True)
        self.assertEqual(generated[2]["client"]["recursive_calls"], 0)
        self.assertEqual(generated[2]["client"]["loops"], 1)
        self.execute_generated(generated, [("client", n) for n in (0, 1, 7, 20)],
                               [0, 3, 21, 60], sanitize=True)

    def test_time_only_dictionary_shapes_and_effect_modes_are_checked(self):
        body = self.time_charged("cost_add", rel("input"), natural(1))
        mutations = [
            lambda d: d["func"].update(name="reSum_inr"),
            lambda d: d["args"].pop(),
            lambda d: d["args"][0].update(argnames=["x"]),
            lambda d: d["args"][0].update(body=lam(["x"], rel("x"))),
            lambda d: d["args"].__setitem__(1, natural(0)),
            lambda d: d["args"].__setitem__(1, {"what": "expr:coerce", "value": {"what": "expr:dummy"}}),
        ]
        for mutation in mutations:
            broken = copy.deepcopy(body)
            mutation(broken["args"][0])
            with self.subTest(mutation=mutation):
                self.rejects(broken, "dictionary", time_only=True)
                self.rejects(let("unused", lam(["x"], broken), returned(rel("input"))),
                             "dictionary", time_only=True)
        self.rejects(self.charged("cost_add", rel("input"), natural(1)),
                     "dictionary", time_only=True)
        self.rejects(body, "dictionary")
        self.rejects(self.memory("array_alloc", natural(1)), "array.*TimeE", time_only=True)

    def test_recursive_arguments_require_matched_input_descent(self):
        arguments = [rel("input"), constructor("S", rel("rest")), natural(0),
                     apply("add", rel("rest"), natural(0)),
                     apply("sub", rel("input"), natural(1)),
                     apply("div2", rel("input"))]
        for argument in arguments:
            with self.subTest(argument=argument):
                body = nat_case(rel("input"), returned(natural(0)), apply("client", argument))
                self.rejects(body, "strictly smaller matched predecessor",
                             time_only=True, recursive=True)
        computed_scrutinee = nat_case(apply("add", rel("input"), natural(1)),
                                     returned(natural(0)), apply("client", rel("rest")))
        self.rejects(computed_scrutinee, "matched predecessor", time_only=True, recursive=True)

    def test_recursive_self_arity_and_value_mode_are_checked(self):
        for invalid, message in (
                (apply("client"), "self-call arity"),
                (apply("client", rel("rest"), rel("rest")), "self-call arity"),
                ({"what": "expr:global", "name": "client"}, "fully applied"),
                (returned(apply("client", rel("rest"))), "must be a computation"),
                (self.time_charged("cost_add", apply("client", rel("rest")), natural(1)),
                 "must be a computation")):
            with self.subTest(invalid=invalid):
                body = nat_case(rel("input"), returned(natural(0)), invalid)
                self.rejects(body, message, time_only=True, recursive=True)
        document = self.program(returned(natural(0)), time_only=True, recursive=True)
        declaration(document, "client")["value"]["argnames"].append("extra")
        with self.assertRaisesRegex(backend.Unsupported, "unary input lambda"):
            backend.generate(document, ["client"])

    def test_recursive_descent_survives_immutable_aliases_and_local_calls(self):
        body = nat_case(rel("input"), returned(natural(5)), let("saved", rel("rest"),
            bind(returned(rel("saved")), "argument", apply(
                lam(["n"], apply("client", rel("n"))), rel("argument")))))
        generated = self.generate_body(body, time_only=True, recursive=True)
        self.execute_generated(generated, [("client", n) for n in (0, 1, 7, 20)], [5, 5, 5, 5])
        captured = nat_case(rel("input"), returned(natural(5)), let("saved", rel("rest"),
            let("recur", lam(["_"], apply("client", rel("saved"))),
                let("saved", rel("input"), apply(rel("recur"), constructor("Tt"))))))
        self.execute_generated(self.generate_body(captured, time_only=True, recursive=True),
                               [("client", n) for n in (0, 1, 7)], [5, 5, 5])
        # Unused pure closures can shadow an outer recursive closure's name.
        shadowed = nat_case(rel("input"), returned(natural(5)),
            let("recur", lam(["n"], apply("client", rel("n"))),
                let("unused_argument", lam(["recur"], rel("recur")),
                    let("unused_local", lam(["_"], let("recur", lam(["x"], rel("x")),
                        apply(rel("recur"), rel("input")))), apply(rel("recur"), rel("rest"))))))
        self.execute_generated(self.generate_body(shadowed, time_only=True, recursive=True),
                               [("client", n) for n in (0, 1, 7)], [5, 5, 5])

    def test_recursive_descent_can_skip_multiple_matched_predecessors(self):
        body = nat_case(rel("input"), returned(natural(0)), nat_case(
            rel("rest"), returned(natural(1)),
            bind(apply("client", rel("earlier")), "answer",
                 self.time_charged("cost_add", rel("answer"), natural(3))), "earlier"))
        generated = self.generate_body(body, time_only=True, recursive=True)
        self.assertEqual(generated[2]["client"]["recursive_calls"], 1)
        self.execute_generated(generated, [("client", n) for n in (0, 1, 2, 3, 4, 5, 20)],
                               [0, 1, 3, 4, 6, 7, 30], sanitize=True)

    def test_recursive_immutable_predecessor_survives_unrelated_branch_and_loop(self):
        loop = self.time_charged("cost_iter", lam(["n"], nat_case(
            rel("n"), returned(constructor("Inr", constructor("Tt"))),
            returned(constructor("Inl", rel("loop_rest"))), "loop_rest")), rel("input"))
        branch = case(apply("leb", rel("input"), natural(3)),
                      ("True", [], returned(constructor("Tt"))),
                      ("False", [], returned(constructor("Tt"))))
        body = nat_case(rel("input"), returned(natural(4)), let("saved", rel("rest"),
            bind(loop, "_", bind(branch, "_", apply("client", rel("saved"))))))
        generated = self.generate_body(body, time_only=True, recursive=True)
        self.assertEqual(generated[2]["client"]["loops"], 1)
        self.execute_generated(generated, [("client", n) for n in (0, 1, 5, 20)], [4, 4, 4, 4])

    def test_recursive_descent_does_not_leak_across_shadowing_results_or_joins(self):
        choices = case(apply("leb", rel("input"), natural(3)),
                       ("True", [], returned(rel("rest"))),
                       ("False", [], returned(rel("input"))))
        same_predecessor = copy.deepcopy(choices)
        same_predecessor["cases"][1]["body"] = returned(rel("rest"))
        successors = [
            let("rest", rel("input"), apply("client", rel("rest"))),
            apply(lam(["rest"], apply("client", rel("rest"))), rel("input")),
            let("recur", lam(["n"], apply("client", rel("n"))),
                bind(apply(rel("recur"), rel("rest")), "_",
                     apply(rel("recur"), rel("input")))),
            bind(apply("client", rel("rest")), "answer", apply("client", rel("answer"))),
            bind(choices, "selected", apply("client", rel("selected"))),
            # Joins deliberately forget even identical predecessor results.
            bind(same_predecessor, "selected", apply("client", rel("selected"))),
        ]
        for successor in successors:
            with self.subTest(successor=successor):
                body = nat_case(rel("input"), returned(natural(0)), successor)
                self.rejects(body, "matched predecessor", time_only=True, recursive=True)

    def test_recursive_descent_does_not_leak_through_mutable_loop_state_or_results(self):
        # After a loop update, the S-bound value could equal the original input.
        state_loop = self.time_charged("cost_iter", lam(["n"], nat_case(
            rel("n"), returned(constructor("Inl", constructor("S", rel("input")))),
            bind(apply("client", rel("loop_rest")), "answer",
                 returned(constructor("Inr", rel("answer")))), "loop_rest")), rel("rest"))
        result_loop = self.time_charged("cost_iter", lam(["_"],
            returned(constructor("Inr", rel("rest")))), constructor("Tt"))
        for successor in (state_loop, bind(result_loop, "next", apply("client", rel("next")))):
            with self.subTest(successor=successor):
                body = nat_case(rel("input"), returned(natural(0)), successor)
                self.rejects(body, "matched predecessor", time_only=True, recursive=True)

    def test_recursive_calls_inside_unused_closures_are_rejected(self):
        for body in (
                let("unused", lam(["x"], apply("client", rel("input"))), returned(natural(0))),
                nat_case(rel("input"), returned(natural(0)), let("unused",
                    lam(["x"], apply("client", rel("rest"))), returned(natural(1)))),
                let("unused", lam(["x"], lam(["y"], apply("client", rel("y")))),
                    returned(natural(0))),
                nat_case(rel("input"), returned(natural(0)),
                    let("recur", lam(["n"], apply("client", rel("n"))),
                        let("unused", lam(["_"], apply(rel("recur"), rel("input"))),
                            apply(rel("recur"), rel("rest"))))),
                nat_case(rel("input"), returned(natural(0)),
                    let("recur", lam(["n"], apply("client", rel("n"))),
                        let("relay", lam(["n"], apply(rel("recur"), rel("n"))),
                            let("unused", lam(["_"], apply(rel("relay"), rel("input"))),
                                apply(rel("relay"), rel("rest")))))),
                nat_case(rel("input"), returned(natural(0)),
                    let("recur", lam(["n"], apply("client", rel("n"))),
                        let("functions", pair(rel("recur"), constructor("Tt")),
                            let("unused", lam(["_"], case(rel("functions"),
                                ("Pair", ["call", "_"], apply(rel("call"), rel("input"))))),
                                apply(rel("recur"), rel("rest")))))),
                apply(lam(["_"], returned(natural(0))),
                      lam(["x"], apply("client", rel("input"))))):
            with self.subTest(body=body):
                self.rejects(body, "unused/unexpanded", time_only=True, recursive=True)

    def test_mutual_recursion_recursive_arrays_and_helper_crosscalls_are_rejected(self):
        body = nat_case(rel("input"), returned(natural(0)), apply("client", rel("rest")))
        document = self.program(body, time_only=True, recursive=True)
        helper = copy.deepcopy(declaration(document, "client"))
        helper["name"] = "other"
        document["declarations"][-1]["fixlist"].append(helper)
        with self.assertRaisesRegex(backend.Unsupported, "mutual recursion"):
            backend.generate(document, ["client", "other"])
        self.rejects(body, "recursive arrays", recursive=True)
        self.rejects(bind(self.memory("array_alloc", natural(1)), "_", body),
                     "array.*TimeE", time_only=True, recursive=True)

        for name in ("other", "pure_helper", "fib_L1", "fib_L2"):
            crosscall = nat_case(rel("input"), returned(natural(0)), apply(name, rel("rest")))
            document = self.program(crosscall, time_only=True, recursive=True)
            targets = ["client"]
            if name in {"other", "pure_helper"}:
                helper = copy.deepcopy(declaration(document, "client"))
                helper["name"] = name
                helper["value"] = lam(["input"], returned(rel("input")))
                if name == "pure_helper":
                    helper["type"]["right"] = copy.deepcopy(helper["type"]["left"])
                    helper["value"] = lam(["input"], nat_case(
                        rel("input"), natural(0), apply(name, rel("rest"))))
                document["declarations"].append({"what": "decl:fixgroup", "fixlist": [helper]})
                if name == "other":
                    targets.append(name)
                else:
                    with self.assertRaisesRegex(backend.Unsupported, "only nat -> itree"):
                        backend.generate(document, [name])
            else:
                targets.append(name)
            with self.subTest(name=name):
                with self.assertRaisesRegex(backend.Unsupported, "unregistered/unsupported global"):
                    backend.generate(document, targets)

    def test_direct_return_constant_and_ignored_locals_compile_strictly(self):
        self.execute(returned(natural(7)), [0, 91], [7, 7])
        self.execute(let("unused", apply("add", rel("input"), natural(1)),
                         returned(natural(3))), [0, 9], [3, 3])
        self.execute(bind(self.memory("array_alloc", natural(1)), "_", returned(natural(2))),
                     [0], [2])

    def test_native_arithmetic_and_unsigned_subtraction(self):
        self.execute(returned(apply("sub", natural(0), rel("input"))),
                     [0, 1, 2], [0, 2 ** 64 - 1, 2 ** 64 - 2])
        self.execute(self.charged("cost_sub", natural(0), rel("input")),
                     [1], [2 ** 64 - 1])
        body = self.charged("function_entry", lam(["n"],
            returned(apply("div2", apply("mul", apply("add", rel("n"), natural(6)), natural(3))))),
            rel("input"))
        self.execute(body, [0, 1, 9], [9, 10, 22], sanitize=True)

    def test_parallel_loop_state_updates_and_nested_pairs(self):
        body = case(rel("state"), ("Pair", ["remaining", "coordinates"],
            case(rel("coordinates"), ("Pair", ["a", "b"],
                nat_case(rel("remaining"), returned(constructor("Inr", rel("a"))),
                         returned(constructor("Inl", pair(rel("rest"), pair(rel("b"), rel("a"))))))))))
        self.execute(self.iteration("state", body, pair(rel("input"), pair(natural(1), natural(2)))),
                     list(range(8)), [1, 2, 1, 2, 1, 2, 1, 2], sanitize=True)

    def test_scalar_and_unit_loop_state(self):
        body = nat_case(rel("n"), returned(constructor("Inr", natural(8))),
                        returned(constructor("Inl", rel("rest"))))
        self.execute(self.iteration("n", body, rel("input")), [0, 1, 5], [8, 8, 8])
        self.execute(self.iteration("unit", returned(constructor("Inr", rel("input"))),
                                    constructor("Tt")), [2, 4], [2, 4])
        boolean_loop = case(rel("flag"),
            ("True", [], returned(constructor("Inl", constructor("False")))),
            ("False", [], returned(constructor("Inr", rel("input")))))
        self.execute(self.iteration("flag", boolean_loop, constructor("True")), [0, 6], [0, 6])

    def test_loop_binding_is_frozen_before_a_later_iteration(self):
        inner = self.iteration("n", nat_case(rel("n"), returned(constructor("Inr", natural(0))),
                                             returned(constructor("Inl", rel("rest")))), rel("n"))
        outer = nat_case(rel("n"), returned(constructor("Inr", natural(0))),
            bind(self.charged("cost_add", rel("n"), natural(10)), "saved",
                bind(inner, "_", returned(constructor("Inr", rel("saved"))))))
        self.execute(self.iteration("n", outer, rel("input")), [0, 1, 5], [0, 11, 15])

    def test_array_read_and_bound_expression_precede_write(self):
        body = bind(self.memory("array_alloc", natural(1)), "_",
            bind(self.memory("array_set", natural(0), rel("input")), "_",
                bind(bind(self.memory("array_read", natural(0)), "old",
                          returned(apply("add", rel("old"), natural(7)))), "saved",
                    bind(self.memory("array_set", natural(0), natural(9)), "_",
                        returned(rel("saved"))))))
        self.execute(body, [0, 1, 15], [7, 8, 22], sanitize=True)

    def test_case_scrutinee_and_predecessor_remain_stable(self):
        # The successor binding is consumed only after another loop and write.
        body = bind(self.memory("array_alloc", natural(1)), "_",
            bind(self.memory("array_set", natural(0), rel("input")), "_",
                bind(self.memory("array_read", natural(0)), "saved",
                    nat_case(rel("saved"), returned(natural(20)),
                        bind(self.memory("array_set", natural(0), natural(0)), "_",
                            bind(self.iteration("n", returned(constructor("Inr", natural(0))),
                                                rel("input")), "_", returned(rel("rest"))))))))
        self.execute(body, [0, 1, 7], [20, 0, 6])

    def test_both_branches_initialize_but_one_branch_does_not(self):
        branches = case(apply("leb", rel("input"), natural(3)),
                        ("True", [], self.memory("array_set", natural(0), natural(4))),
                        ("False", [], self.memory("array_set", natural(0), natural(8))))
        body = bind(self.memory("array_alloc", natural(1)), "_",
                    bind(branches, "_", self.memory("array_read", natural(0))))
        self.execute(body, [0, 3, 4, 9], [4, 4, 8, 8], sanitize=True)
        broken = copy.deepcopy(branches)
        broken["cases"][1]["body"] = returned(constructor("Tt"))
        self.rejects(bind(self.memory("array_alloc", natural(1)), "_",
                          bind(broken, "_", self.memory("array_read", natural(0)))), "initialized")

    def test_loop_initialization_is_not_assumed_after_exit(self):
        loop = self.iteration("n", nat_case(rel("n"), returned(constructor("Inr", constructor("Tt"))),
            bind(self.memory("array_set", natural(0), natural(4)), "_",
                 returned(constructor("Inl", rel("rest"))))), rel("input"))
        self.rejects(bind(self.memory("array_alloc", natural(1)), "_",
                          bind(loop, "_", self.memory("array_read", natural(0)))), "initialized")

    def test_static_memory_rejections(self):
        for name, args, diagnostic in (
            ("array_alloc", [natural(0)], "positive"),
            ("array_alloc", [rel("input")], "static"),
            ("array_read", [natural(0)], "bounds"),
            ("array_set", [natural(0), natural(1)], "bounds"),
        ):
            with self.subTest(name=name, args=args):
                self.rejects(self.memory(name, *args), diagnostic)
        for action, diagnostic in (
            (self.memory("array_read", natural(0)), "initialized"),
            (self.memory("array_read", natural(1)), "bounds"),
            (self.memory("array_set", natural(1), natural(7)), "bounds"),
            (self.memory("array_read", rel("input")), "static"),
            (self.memory("array_set", rel("input"), natural(1)), "static"),
            (self.memory("array_alloc", natural(1)), "one positive"),
            (self.memory("array_read", apply("add", natural(0), natural(0))), "static"),
        ):
            with self.subTest(action=action):
                self.rejects(bind(self.memory("array_alloc", natural(1)), "_", action), diagnostic)

    def test_allocation_in_branch_or_loop_is_rejected(self):
        allocation = bind(self.memory("array_alloc", natural(1)), "_", returned(natural(0)))
        self.rejects(nat_case(rel("input"), allocation, returned(natural(0))), "outside branches/loops")
        self.rejects(self.iteration("n", bind(self.memory("array_alloc", natural(1)), "_",
                     returned(constructor("Inr", natural(0)))), rel("input")), "outside branches/loops")

    def test_declared_allocation_base_can_be_a_literal_index(self):
        body = bind(self.memory("array_alloc", natural(1)), "base",
                    bind(self.memory("array_set", rel("base"), rel("input")), "_",
                         self.memory("array_read", rel("base"))))
        self.execute(body, [0, 9], [0, 9])

    def test_registered_bodies_types_and_inductives_are_not_name_only(self):
        for name, field, replacement in (
            ("add", "value", lam(["n", "m"], rel("n"))),
            ("bind", "value", lam(["u", "k"], rel("u"))),
            ("cost_add", "type", {"what": "type:unknown"}),
            ("function_entry", "value", lam(["h", "program", "input"], returned(natural(0)))),
            ("id_IFun", "value", lam(["e"], natural(0))),
            ("array_read", "value", lam(["h", "index"], returned(natural(0)))),
        ):
            document = self.program(returned(rel("input")))
            declaration(document, name)[field] = replacement
            with self.subTest(name=name):
                with self.assertRaisesRegex(backend.Unsupported, "identity/shape mismatch"):
                    backend.generate(document, ["client"])
        for name in ("nat", "prod", "sum", "itree", "arrayE", "timeE"):
            document = self.program(returned(rel("input")))
            declaration(document, name)["constructors"][0]["argtypes"].append({"what": "type:unknown"})
            with self.subTest(inductive=name):
                with self.assertRaisesRegex(backend.Unsupported, "identity/shape mismatch"):
                    backend.generate(document, ["client"])

    def test_registered_transitive_dependencies_cannot_be_missing_or_replaced(self):
        for name in ("add", "subst", "trigger", "reSum_id", "inr_sum1", "nat"):
            document = copy.deepcopy(self.document)
            document["declarations"] = [item for item in document["declarations"]
                                        if item.get("name") != name
                                        and all(fix["name"] != name for fix in item.get("fixlist", []))]
            with self.subTest(name=name):
                with self.assertRaisesRegex(backend.Unsupported, "missing registered|unregistered"):
                    backend.generate(document, ["fib_L3"])

    def test_collisions_include_fixgroup_items_and_constructors(self):
        additions = [
            copy.deepcopy(declaration(self.document, "bind")),
            {"what": "decl:fixgroup", "fixlist": [copy.deepcopy(declaration(self.document, "add"))]},
            {"what": "decl:ind", "name": "intruder", "argnames": [],
             "constructors": [{"name": "O", "argtypes": []}]},
            {"what": "decl:ind", "name": "intruder", "argnames": [],
             "constructors": [{"name": "bind", "argtypes": []}]},
        ]
        for addition in additions:
            document = self.program(returned(natural(0)))
            document["declarations"].append(addition)
            with self.subTest(addition=addition):
                with self.assertRaisesRegex(backend.Unsupported, "colliding"):
                    backend.generate(document, ["client"])

    def test_dictionary_handler_and_composition_must_be_exact(self):
        body = self.charged("cost_add", rel("input"), natural(1))
        changes = [
            lambda d: d["func"].update(name="reSum_inl"),
            lambda d: d["args"][1]["body"]["args"].reverse(),
            lambda d: d["args"][2].update(body={"what": "expr:global", "name": "inl_sum1"}),
            lambda d: d["args"][6]["args"][0].update(body=lam(["e"], rel("e"))),
            lambda d: d["args"].__setitem__(0, {"what": "expr:dummy"}),
        ]
        for change in changes:
            broken = copy.deepcopy(body)
            change(broken["args"][0])
            with self.subTest(change=change):
                self.rejects(broken, "dictionary")

    def test_unknown_helpers_raw_trees_and_effects_are_rejected(self):
        for body, message in (
            (returned(apply("mystery", rel("input"))), "unregistered"),
            (returned(apply("client", rel("input"))), "recursive|unregistered"),
            (constructor("Go", constructor("TauF", returned(rel("input")))), "constructor|effect|Return"),
            (apply("trigger", constructor("Tick")), "unsupported global|effect"),
            (returned({"what": "expr:coerce", "value": rel("input")}), "executable node"),
            (returned({"what": "expr:dummy"}), "executable node"),
            (returned({"what": "expr:fix", "body": rel("input")}), "expression"),
        ):
            with self.subTest(body=body):
                self.rejects(body, message)

    def test_unsupported_shapes_in_unused_closures_are_rejected(self):
        for invalid in (
            {"what": "expr:coerce", "value": rel("x")},
            {"what": "expr:global", "name": "add"},
            apply("cost_add", rel("x")),
            rel("unbound"),
            constructor("RetF", rel("x")),
        ):
            with self.subTest(invalid=invalid):
                with self.assertRaises(backend.Unsupported):
                    self.generate_body(let("unused", lam(["x"], invalid), returned(rel("input"))))

    def test_pure_values_and_computations_are_not_interchangeable(self):
        for body in (
            returned(self.charged("cost_add", rel("input"), natural(1))),
            bind(natural(1), "n", returned(rel("n"))),
            self.charged("cost_add", constructor("True"), natural(1)),
            bind(returned(natural(1)), "n", rel("n")),
        ):
            with self.subTest(body=body):
                self.rejects(body, "operation|Return|scalar|computation")

    def test_loop_shape_mismatch_and_no_exit_are_rejected(self):
        self.rejects(self.iteration("n", returned(rel("n")), rel("input")), "inl/inr")
        self.rejects(self.iteration("n", returned(constructor("Inl", rel("n"))), rel("input")),
                     "no syntactic exit")
        body = nat_case(rel("n"), returned(constructor("Inr", natural(0))),
                        returned(constructor("Inl", pair(rel("rest"), natural(0)))))
        self.rejects(self.iteration("n", body, rel("input")), "state scalar type mismatch")

    def test_malformed_nodes_report_unsupported(self):
        bodies = [None, [], {}, {"what": []}, {"what": "expr:apply"},
                  returned({"what": "expr:rel", "name": []}),
                  returned({"what": "expr:constructor", "name": "O", "args": {}}),
                  returned({"what": "expr:constructor", "name": "S", "args": []}),
                  bind(returned(natural(0)), "n", returned(rel("missing"))),
                  apply("bind", returned(natural(0))),
                  apply(lam(["same", "same"], returned(natural(0))), natural(1), natural(2)),
                  nat_case(rel("input"), returned(natural(0)), returned(natural(1)))]
        bodies[-1]["cases"][1]["pat"]["argnames"] = []
        for body in bodies:
            with self.subTest(body=body):
                with self.assertRaises(backend.Unsupported):
                    self.generate_body(body)

    def test_malformed_module_declarations_and_type_shapes(self):
        mutations = [
            lambda d: d.pop("declarations"),
            lambda d: d.update(used_modules=["External"]),
            lambda d: d.update(need_magic=True),
            lambda d: d.update(need_dummy=0),
            lambda d: d.update(declarations=[None]),
            lambda d: d.update(declarations=[{"what": []}]),
            lambda d: d["declarations"].append({"what": "decl:fixgroup", "fixlist": [None]}),
            lambda d: d["declarations"].append({"what": "decl:axiom", "name": "untrusted"}),
            lambda d: declaration(d, "client").update(type={"what": "type:unknown"}),
            lambda d: declaration(d, "client")["type"].update(left={"what": "type:glob", "name": [], "args": []}),
        ]
        for mutation in mutations:
            document = self.program(returned(natural(0)))
            mutation(document)
            with self.subTest(mutation=mutation):
                with self.assertRaises(backend.Unsupported):
                    backend.generate(document, ["client"])
        for malformed in (None, [], {}, {"what": "module"}):
            with self.subTest(document=malformed):
                with self.assertRaises(backend.Unsupported):
                    backend.generate(malformed, ["client"])

    def test_target_mapping_and_c_identifiers(self):
        for targets, names in (
            ([], None), ("fib_L3", None), (["missing"], None),
            (["fib_L3", "fib_L3"], None), (["add"], None),
            (["fib_L3"], {"missing": "extra"}),
            (["fib_L3", "fib_L4"], {"fib_L3": "same", "fib_L4": "same"}),
            (["fib_L3"], {"fib_L3": None}),
        ):
            with self.subTest(targets=targets, names=names):
                with self.assertRaises(backend.Unsupported):
                    backend.generate(self.document, targets, names)
        for name in ("for", "uint64_t", "UINT64_C", "main", "_reserved", "bad-name", "", "f();",
                     "malloc", "printf", "memcpy", "sqrt", "size_t"):
            with self.subTest(c_name=name):
                with self.assertRaises(backend.Unsupported):
                    backend.generate(self.document, ["fib_L3"], {"fib_L3": name})

    def test_cli_emits_all_three_files_and_clean_diagnostics(self):
        output = self.output / "cli output with spaces"
        targets = ["fib_L1", "fib_L2", "fib_L3", "fib_L4"]
        command = [sys.executable, str(SCRIPT), str(self.output / "targets.json"),
                   *[name + "=" + name.lower() for name in targets], "--output-dir", str(output)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual({item.name for item in output.iterdir()},
                         {"generated.c", "generated.h", "lowering-metadata.json"})
        expected = backend.generate(self.document, targets, {name: name.lower() for name in targets})
        self.assertEqual((output / "generated.c").read_text(encoding="utf-8"), expected[0])
        self.assertEqual(json.loads((output / "lowering-metadata.json").read_text(encoding="utf-8")),
                         expected[2])
        for contents in ("not JSON", '{"what": "module", "what": "module"}',
                         json.dumps(self.program(returned({"what": "expr:rel"})))):
            malformed = self.output / "malformed.json"
            malformed.write_text(contents, encoding="utf-8")
            rejected = self.output / "rejected"
            result = subprocess.run([sys.executable, str(SCRIPT), str(malformed), "client",
                                     "--output-dir", str(rejected)],
                                    capture_output=True, text=True, timeout=30)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("extract-c:", result.stderr)
            self.assertNotIn("Traceback", result.stderr)
            self.assertFalse(rejected.exists())


if __name__ == "__main__":
    unittest.main()
