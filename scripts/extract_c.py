#!/usr/bin/env python3
"""Lower the registered Rocq 9.2 JSON fragment to standalone C11.

Public boundary: generate(document, targets, entrypoint_names=None) returns
(source, header, metadata), or raises Unsupported. JSON is extraction's MiniML
AST, not a kernel certificate. The adjacent registry pins audited library
declarations (including their dependency closure), never client implementations.
Changing a pin requires inspecting the new extraction and its source identity.

Numbers use native uint64_t arithmetic, including wrapping subtraction. This is
not mathematical-natural arithmetic or a verified compiler. Closures, products,
and loop-control sums exist only during generation. Memory analysis deliberately
intersects branches and forgets initialization gained inside loops.

Recursive clients are limited to singleton, unary TimeE fixgroups. Direct
self-calls must consume an immutable descendant of the original input obtained
by successful nat S patterns (one or more predecessor steps). Aliases and local
lambda applications preserve that information; arithmetic, recursive results,
branch-result joins, and mutable loop state/results do not. Unexpanded local
closures containing self-calls or references to recursive local closures are
rejected, including otherwise valid descent.
This conservative syntactic check is not a kernel provenance or
translation-correctness proof.
"""

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Optional


class Unsupported(Exception):
    """The document is malformed or outside the registered source fragment."""


def require(condition, message):
    if not condition:
        raise Unsupported(message)


_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")
_C_NAME = re.compile(r"[A-Za-z][A-Za-z_0-9]*")
# Reserve C/header identifiers and names used by generated locals and guards.
# Reject these before output so chosen entrypoints compile as declared.
_C_RESERVED = set("""
auto break case char const continue default do double else enum extern float
for goto if inline int long register restrict return short signed sizeof static
struct switch typedef union unsigned void volatile while _Alignas _Alignof
_Atomic _Bool _Complex _Generic _Imaginary _Noreturn _Static_assert _Thread_local
main input cells REFINETOITREE_GENERATED_H
""".split())
# C11 reserves standard-library external identifiers even when their headers
# are not included. Clang also diagnoses incompatible builtin declarations.
_C_RESERVED.update("""
abort abs aligned_alloc atexit at_quick_exit atof atoi atol atoll bsearch calloc
div exit free getenv labs ldiv llabs lldiv malloc mblen mbstowcs mbtowc qsort
quick_exit rand realloc srand strtod strtof strtol strtold strtoll strtoul
strtoull system wcstombs wctomb asctime clock ctime difftime gmtime localtime
mktime strftime time clearerr fclose feof ferror fflush fgetc fgetpos fgets
fopen fprintf fputc fputs fread freopen fscanf fseek fsetpos ftell fwrite
getc getchar gets perror printf putc putchar puts remove rename rewind scanf
setbuf setvbuf snprintf sprintf sscanf tmpfile tmpnam ungetc vfprintf vfscanf
vprintf vscanf vsnprintf vsprintf vsscanf memchr memcmp memcpy memmove memset
strcat strchr strcmp strcoll strcpy strcspn strerror strlen strncat strncmp
strncpy strpbrk strrchr strspn strstr strtok strxfrm assert errno isalnum
isalpha isblank iscntrl isdigit isgraph islower isprint ispunct isspace isupper
isxdigit tolower toupper setlocale localeconv signal raise setjmp longjmp
fenv_t fexcept_t feclearexcept fegetenv fegetexceptflag fegetround feholdexcept
feraiseexcept fesetenv fesetexceptflag fesetround fetestexcept feupdateenv
va_list va_start va_arg va_copy va_end size_t ptrdiff_t wchar_t max_align_t
sig_atomic_t clock_t time_t FILE fpos_t wint_t wctype_t wctrans_t mbstate_t
btowc fgetwc fgetws fputwc fputws fwide fwprintf fwscanf getwc getwchar mbrlen
mbrtowc mbsinit mbsrtowcs putwc putwchar swprintf swscanf ungetwc vfwprintf
vfwscanf vswprintf vswscanf vwprintf vwscanf wcrtomb wcscat wcschr wcscmp wcscoll
wcscpy wcscspn wcsftime wcslen wcsncat wcsncmp wcsncpy wcspbrk wcsrchr wcsrtombs
wcsspn wcsstr wcstod wcstof wcstok wcstol wcstold wcstoll wcstoul wcstoull
wcsxfrm wctob wmemchr wmemcmp wmemcpy wmemmove wmemset wprintf wscanf iswalnum
iswalpha iswblank iswcntrl iswctype iswdigit iswgraph iswlower iswprint iswpunct
iswspace iswupper iswxdigit towctrans towlower towupper wctrans wctype
bool true false complex imaginary I NULL EOF
""".split())
for _math_name in """
acos acosh asin asinh atan atan2 atanh cbrt ceil copysign cos cosh erf erfc exp
exp2 expm1 fabs fdim floor fma fmax fmin fmod frexp hypot ilogb ldexp lgamma
llrint llround log log10 log1p log2 logb lrint lround modf nan nearbyint
nextafter nexttoward pow remainder remquo rint round scalbln scalbn sin sinh
sqrt tan tanh tgamma trunc cabs cacos cacosh carg casin casinh catan catanh
ccos ccosh cexp cimag clog conj cpow cproj creal csin csinh csqrt ctan ctanh
""".split():
    _C_RESERVED.update(_math_name + suffix for suffix in ("", "f", "l"))
_PURE_ARITIES = {"add": 2, "mul": 2, "sub": 2, "leb": 2, "div2": 1}
_COMPUTATION_ARITIES = {
    "bind": 2, "function_entry": 3, "cost_iter": 3,
    "cost_add": 3, "cost_mul": 3, "cost_sub": 3,
    "array_alloc": 2, "array_read": 2, "array_set": 3,
}
_DICTIONARY_GLOBALS = {
    "reSum_inl", "reSum_inr", "reSum_id", "cat_IFun", "id_IFun",
    "inl_sum1", "inr_sum1",
}
_CONSTRUCTORS = {
    "O": 0, "S": 1, "True": 0, "False": 0, "Tt": 0,
    "Pair": 2, "Inl": 1, "Inr": 1, "Go": 1, "RetF": 1,
}


def _record(value, fields, context):
    require(isinstance(value, dict) and set(value) == set(fields),
            context + ": unexpected object fields/shape")


def _name(value, context):
    require(isinstance(value, str) and _NAME.fullmatch(value) is not None,
            context + ": expected an extraction identifier")


def _names(value, context):
    require(isinstance(value, list), context + ": expected argument-name list")
    seen = set()
    for name in value:
        _name(name, context)
        require(name == "_" or name not in seen, context + ": duplicate binder " + name)
        seen.add(name)


def _nodes(value, context):
    require(isinstance(value, list), context + ": expected node list")
    return value


def _validate_tree(root, category):
    """Check exact JSON schemas before any lowering or dependency traversal."""
    pending = [(root, category)]
    while pending:
        node, category = pending.pop()
        require(isinstance(node, dict) and isinstance(node.get("what"), str),
                category + ": expected tagged JSON object")
        tag = node["what"]
        if category == "type":
            if tag in {"type:unknown", "type:dummy"}:
                _record(node, ("what",), tag)
            elif tag in {"type:var", "type:varidx"}:
                _record(node, ("what", "name"), tag)
                if tag == "type:varidx":
                    require(type(node["name"]) is int and node["name"] > 0,
                            "type:varidx: expected positive integer")
                else:
                    _name(node["name"], tag)
            elif tag == "type:glob":
                _record(node, ("what", "name", "args"), tag)
                _name(node["name"], tag)
                pending.extend((arg, "type") for arg in _nodes(node["args"], tag))
            elif tag == "type:arrow":
                _record(node, ("what", "left", "right"), tag)
                pending.extend((node[key], "type") for key in ("left", "right"))
            else:
                raise Unsupported("unsupported extraction type: " + tag)
        elif category == "expr":
            if tag in {"expr:rel", "expr:global"}:
                _record(node, ("what", "name"), tag)
                _name(node["name"], tag)
            elif tag == "expr:dummy":
                _record(node, ("what",), tag)
            elif tag == "expr:coerce":
                _record(node, ("what", "value"), tag)
                pending.append((node["value"], "expr"))
            elif tag == "expr:lambda":
                _record(node, ("what", "argnames", "body"), tag)
                _names(node["argnames"], tag)
                pending.append((node["body"], "expr"))
            elif tag == "expr:let":
                _record(node, ("what", "name", "nameval", "body"), tag)
                _name(node["name"], tag)
                pending.extend((node[key], "expr") for key in ("nameval", "body"))
            elif tag in {"expr:apply", "expr:constructor"}:
                key = "func" if tag == "expr:apply" else "name"
                _record(node, ("what", key, "args"), tag)
                if key == "name":
                    _name(node[key], tag)
                else:
                    pending.append((node[key], "expr"))
                pending.extend((arg, "expr") for arg in _nodes(node["args"], tag))
            elif tag == "expr:case":
                _record(node, ("what", "expr", "cases"), tag)
                pending.append((node["expr"], "expr"))
                cases = _nodes(node["cases"], tag)
                require(cases, "case expression must have alternatives")
                seen = set()
                for case in cases:
                    _record(case, ("what", "pat", "body"), "case")
                    require(case["what"] == "case", "unexpected case tag")
                    pattern = case["pat"]
                    _record(pattern, ("what", "name", "argnames"), "pattern")
                    require(pattern["what"] == "pat:constructor",
                            "only constructor patterns supported")
                    _name(pattern["name"], "pattern")
                    _names(pattern["argnames"], "pattern")
                    require(pattern["name"] not in seen, "duplicate case alternative")
                    seen.add(pattern["name"])
                    pending.append((case["body"], "expr"))
            else:
                raise Unsupported("unsupported extraction expression: " + tag)


def _walk(root):
    pending = [root]
    while pending:
        node = pending.pop()
        if isinstance(node, dict):
            yield node
            pending.extend(node.values())
        elif isinstance(node, list):
            pending.extend(node)


def _digest(declaration):
    canonical = json.dumps(declaration, sort_keys=True, separators=(",", ":"),
                           ensure_ascii=True).encode("ascii")
    return hashlib.sha256(canonical).hexdigest()


class _Document:
    def __init__(self, document):
        _record(document, ("what", "name", "need_magic", "need_dummy",
                           "used_modules", "declarations"), "module")
        require(document["what"] == "module", "expected extraction module")
        _name(document["name"], "module")
        require(document["need_magic"] is False, "extraction requiring magic is unsupported")
        require(type(document["need_dummy"]) is bool, "unexpected need_dummy flag")
        require(document["used_modules"] == [], "external extraction modules are unsupported")
        self.symbols = {}
        self.terms = {}
        declarations = _nodes(document["declarations"], "declarations")
        for declaration in declarations:
            require(isinstance(declaration, dict), "expected declaration object")
            kind = declaration.get("what")
            require(isinstance(kind, str), "expected declaration tag string")
            if kind == "decl:fixgroup":
                _record(declaration, ("what", "fixlist"), "fixgroup")
                items = _nodes(declaration["fixlist"], "fixgroup")
                require(items, "empty fixgroup")
                for item in items:
                    _record(item, ("what", "name", "type", "value"), "fixgroup:item")
                    require(item["what"] == "fixgroup:item", "unexpected fixgroup item")
                    self._add(item["name"], declaration)
                    self.terms[item["name"]] = item
                    _validate_tree(item["type"], "type")
                    _validate_tree(item["value"], "expr")
            elif kind == "decl:ind":
                _record(declaration, ("what", "name", "argnames", "constructors"), kind)
                self._add(declaration["name"], declaration)
                _names(declaration["argnames"], kind)
                constructors = _nodes(declaration["constructors"], kind)
                require(constructors, "empty inductive declaration")
                for constructor in constructors:
                    _record(constructor, ("name", "argtypes"), "constructor declaration")
                    self._add(constructor["name"], declaration)
                    for arg in _nodes(constructor["argtypes"], "constructor types"):
                        _validate_tree(arg, "type")
            elif kind in {"decl:type", "decl:term"}:
                fields = (("what", "name", "argnames", "value") if kind == "decl:type"
                          else ("what", "name", "type", "value"))
                _record(declaration, fields, kind)
                self._add(declaration["name"], declaration)
                if kind == "decl:type":
                    _names(declaration["argnames"], kind)
                    _validate_tree(declaration["value"], "type")
                else:
                    self.terms[declaration["name"]] = declaration
                    _validate_tree(declaration["type"], "type")
                    _validate_tree(declaration["value"], "expr")
            else:
                raise Unsupported("unsupported extraction declaration: " + str(kind))

        try:
            registry = json.loads(Path(__file__).with_name("c_extraction_registry.json")
                                  .read_text(encoding="utf-8"))["declarations"]
        except (OSError, ValueError, KeyError) as error:
            raise Unsupported("cannot load audited C extraction registry: " + str(error)) from error
        self.registered = set()
        # Check every present registered symbol, even if a selected client does
        # not use it. A constructor cannot impersonate a registered function.
        for name, pin in registry.items():
            declaration = self.symbols.get(name)
            if declaration is not None:
                require(_digest(declaration) == pin["sha256"],
                        "registered declaration identity/shape mismatch: " + name)
                self.registered.update(symbol for symbol, owner in self.symbols.items()
                                       if owner is declaration)
        # A pinned wrapper is meaningful only with its original dependencies.
        for name in sorted(self.registered):
            for node in _walk(self.symbols[name]):
                if node.get("what") in {"type:glob", "expr:global", "expr:constructor",
                                        "pat:constructor"}:
                    require(node["name"] in self.registered,
                            "missing registered dependency: " + node["name"] + " (from " + name + ")")

    def _add(self, name, declaration):
        _name(name, "declaration")
        require(name not in self.symbols, "duplicate/colliding extraction symbol: " + name)
        self.symbols[name] = declaration

    def client(self, target):
        require(target in self.terms and target not in self.registered,
                "entrypoint must be an unregistered client term/fixgroup item: " + target)
        declaration = self.terms[target]
        owner = self.symbols[target]
        recursive = owner["what"] == "decl:fixgroup"
        if recursive:
            require(len(owner["fixlist"]) == 1, "mutual recursion is unsupported: " + target)
        time_only = declaration["type"] == _expected_type(time_only=True)
        require(time_only or declaration["type"] == _expected_type(),
                "only nat -> itree TimeE nat or nat -> itree (ArrayE nat +' TimeE) nat "
                "entrypoints supported: " + target)
        if recursive:
            require(time_only, "recursive entrypoints require TimeE only; recursive arrays unsupported")
            require(declaration["value"]["what"] == "expr:lambda"
                    and len(declaration["value"]["argnames"]) == 1,
                    "recursive entrypoint requires a unary input lambda")
        dictionary_nodes, application_heads, return_payloads = set(), set(), set()
        arities = dict(_PURE_ARITIES, **_COMPUTATION_ARITIES)
        for node in _walk(declaration["value"]):
            if node.get("what") == "expr:apply" and node["func"]["what"] == "expr:global":
                name, arguments = node["func"]["name"], node["args"]
                if recursive and name == target:
                    require(len(arguments) == 1, "recursive self-call arity: " + target)
                    application_heads.add(id(node["func"]))
                elif name in arities:
                    require(len(arguments) == arities[name], "operation arity: " + name)
                    application_heads.add(id(node["func"]))
                    if name in _COMPUTATION_ARITIES and name != "bind":
                        array = name.startswith("array_")
                        require(not (time_only and array), "array operation in a TimeE client: " + name)
                        side = "inl" if array else ("id" if time_only else "inr")
                        _dictionary(arguments[0], side)
                        dictionary_nodes.update(id(child) for child in _walk(arguments[0]))
            elif node.get("what") == "expr:constructor" and node["name"] == "Go":
                require(len(node["args"]) == 1, "constructor/pattern arity: Go")
                child = node["args"][0]
                require(child["what"] == "expr:constructor" and child["name"] == "RetF",
                        "only direct Return trees supported")
                return_payloads.add(id(child))
        for node in _walk(declaration):
            tag = node.get("what")
            if tag == "type:glob":
                require(node["name"] in self.registered,
                        "missing registered type: " + node["name"])
            elif tag == "expr:global":
                name = node["name"]
                require((recursive and name == target) or
                        (name in self.registered and name in
                         (set(_PURE_ARITIES) | set(_COMPUTATION_ARITIES) | _DICTIONARY_GLOBALS)),
                        "unregistered/unsupported global (including recursive helpers): " + name)
                require(id(node) in application_heads or id(node) in dictionary_nodes,
                        "only fully applied registered operations/direct dictionaries supported: " + name)
            elif tag in {"expr:dummy", "expr:coerce"}:
                require(id(node) in dictionary_nodes,
                        "unsupported executable node/erasure outside an effect dictionary: " + tag)
            elif tag in {"expr:constructor", "pat:constructor"}:
                name = node["name"]
                require(name in self.registered and name in _CONSTRUCTORS,
                        "unsupported constructor/effect: " + name)
                args = node["args"] if tag == "expr:constructor" else node["argnames"]
                require(len(args) == _CONSTRUCTORS[name], "constructor/pattern arity: " + name)
                if tag == "pat:constructor":
                    require(name in {"O", "S", "True", "False", "Pair"},
                            "only nat/bool/product case patterns supported: " + name)
                elif name == "RetF":
                    require(id(node) in return_payloads, "RetF must occur in a direct Return tree")
        _validate_scope(declaration["value"])
        return declaration, time_only, recursive


def _scoped_nodes(root):
    """Visit every expression with its lexical binders, including unused bodies."""
    pending = [(root, frozenset())]
    while pending:
        node, scope = pending.pop()
        tag = node["what"]
        yield node, scope
        if tag == "expr:lambda":
            pending.append((node["body"], scope | (set(node["argnames"]) - {"_"})))
        elif tag == "expr:let":
            pending.append((node["nameval"], scope))
            pending.append((node["body"], scope | ({node["name"]} - {"_"})))
        elif tag == "expr:case":
            pending.append((node["expr"], scope))
            for alternative in node["cases"]:
                names = set(alternative["pat"]["argnames"]) - {"_"}
                pending.append((alternative["body"], scope | names))
        elif tag in {"expr:apply", "expr:constructor"}:
            pending.extend((arg, scope) for arg in node["args"])
            if tag == "expr:apply":
                pending.append((node["func"], scope))
        elif tag == "expr:coerce":
            pending.append((node["value"], scope))


def _validate_scope(root):
    """Check binders even in build-time closures that happen not to be called."""
    for node, scope in _scoped_nodes(root):
        if node["what"] == "expr:rel":
            require(node["name"] in scope, "unbound local: " + node["name"])


def _expected_type(time_only=False):
    def glob(name, *args):
        return {"what": "type:glob", "name": name, "args": list(args)}
    unknown = {"what": "type:unknown"}
    nat = glob("nat")
    effects = glob("timeE", unknown)
    if not time_only:
        effects = glob("sum1", glob("arrayE", nat, unknown), effects, unknown)
    return {"what": "type:arrow", "left": nat, "right": glob("itree", effects, nat)}


def _application(node, name, arity):
    return (node.get("what") == "expr:apply"
            and node["func"] == {"what": "expr:global", "name": name}
            and len(node["args"]) == arity)


def _dictionary(node, side):
    """Accept only direct sum injections or the exact TimeE identity dictionary."""
    if side == "id":
        _identity_dictionary(node)
        return
    dummy = {"what": "expr:dummy"}
    require(_application(node, "reSum_" + side, 7), "unsupported effect dictionary")
    erased, composition, injection, a, b, c, identity = node["args"]
    require(erased == {"what": "expr:coerce", "value": dummy} and a == b == c == dummy,
            "unexpected effect dictionary erasure")
    require(composition.get("what") == "expr:lambda"
            and len(composition["argnames"]) == 6,
            "unsupported effect dictionary composition lambda")
    names = composition["argnames"]
    require(names[3] != "_" and names[4] != "_"
            and _application(composition["body"], "cat_IFun", 2)
            and composition["body"]["args"] == [
                {"what": "expr:rel", "name": name} for name in names[3:5]],
            "unsupported effect dictionary composition operands")
    require(injection.get("what") == "expr:lambda" and len(injection["argnames"]) == 3
            and injection["body"] == {"what": "expr:global", "name": side + "_sum1"},
            "unexpected effect dictionary injection")
    _identity_dictionary(identity)


def _identity_dictionary(node):
    require(_application(node, "reSum_id", 2), "unexpected effect dictionary identity")
    function, argument = node["args"]
    dummy = {"what": "expr:dummy"}
    require(argument == dummy and function.get("what") == "expr:lambda"
            and len(function["argnames"]) == 2
            and function["body"] == {"what": "expr:global", "name": "id_IFun"},
            "unexpected effect dictionary identity lambda")


@dataclass(frozen=True)
class _Scalar:
    kind: str
    code: str
    literal: Optional[int] = None
    # None: no known ancestry; 0: original input; >0: successive nat S matches.
    # Only immutable aliases/snapshots and successful S patterns propagate it.
    input_distance: Optional[int] = None


@dataclass(frozen=True)
class _Closure:
    names: list
    body: dict
    env: dict


@dataclass(frozen=True)
class _Step:
    tag: str
    value: object


@dataclass(frozen=True)
class _Result:
    value: object


def _number(value):
    require(0 <= value < 2 ** 64, "natural literal outside uint64_t")
    return _Scalar("nat", "UINT64_C(" + str(value) + ")", value)


class _Lower:
    def __init__(self, time_only=False, recursive_target=None, c_name=None):
        self.lines = []
        self.counter = 0
        self.depth = 0
        self.capacity = 0
        self.initialized = set()
        self.loops = 0
        self.operations = {}
        self.time_only = time_only
        self.recursive_calls = 0
        self.recursive_target = recursive_target
        self.c_name = c_name
        # Retain closures as well as IDs: an unexpanded closure with a self-call
        # must be rejected, even if that call never reaches the lowering path.
        self.recursive_closures = {}
        self.expanded_closures = set()

    def fresh(self):
        self.counter += 1
        return "v" + str(self.counter)

    @staticmethod
    def nat(value):
        require(isinstance(value, _Scalar) and value.kind == "nat", "expected nat scalar")
        return value

    def scalar(self, kind, expression, input_distance=None):
        name = self.fresh()
        self.lines.extend(["const uint64_t " + name + " = " + expression + ";",
                           "(void)" + name + ";"])
        return _Scalar(kind, name, input_distance=input_distance)

    def slots(self, value, declarations):
        if isinstance(value, _Scalar):
            name = self.fresh()
            # Taking the address marks even write-only coordinates as used,
            # without reading an uninitialized scalar or relaxing C warnings.
            declarations.extend(["uint64_t " + name + ";", "(void)&" + name + ";"])
            # Mutable branch/loop destinations deliberately forget descent.
            return _Scalar(value.kind, name)
        if isinstance(value, tuple):
            return tuple(self.slots(item, declarations) for item in value)
        require(value is None, "only scalar/product/unit results can cross control-flow joins")
        return None

    def assign(self, target, value):
        if isinstance(target, _Scalar):
            require(isinstance(value, _Scalar) and target.kind == value.kind,
                    "branch/loop state scalar type mismatch")
            self.lines.append(target.code + " = " + value.code + ";")
        elif isinstance(target, tuple):
            require(isinstance(value, tuple) and len(value) == len(target),
                    "branch/loop state product shape mismatch")
            for left, right in zip(target, value):
                self.assign(left, right)
        else:
            require(target is None and value is None, "branch/loop state unit shape mismatch")

    def freeze(self, value):
        """Snapshot all loop coordinates before exposing them to a callback."""
        if isinstance(value, _Scalar):
            return self.scalar(value.kind, value.code, value.input_distance)
        if isinstance(value, tuple):
            return tuple(self.freeze(item) for item in value)
        require(value is None, "loop state must contain only scalars/products/unit")
        return None

    def capture(self, node, env, mode):
        outer = self.lines
        self.lines = []
        self.emit(node, env, mode, lambda value: self.lines.append(_Result(value)))
        body = self.lines
        self.lines = outer
        results = [line for line in body if isinstance(line, _Result)]
        require(results, "expression has no result")
        if len(results) == 1 and body[-1] is results[0]:
            self.lines.extend(body[:-1])
            return results[0].value
        declarations = []
        result = self.slots(results[0].value, declarations)
        self.lines.extend(declarations)
        for line in body:
            if isinstance(line, _Result):
                self.assign(result, line.value)
            else:
                self.lines.append(line)
        # A join's mutable destination is not exposed to subsequent loops.
        return self.freeze(result)

    def value(self, node, env):
        return self.capture(node, env, "pure")

    def recursive_value(self, value):
        if isinstance(value, _Closure):
            return id(value) in self.recursive_closures
        if isinstance(value, tuple):
            return any(self.recursive_value(item) for item in value)
        if isinstance(value, _Step):
            return self.recursive_value(value.value)
        return False

    def uses_recursion(self, node, env):
        # Free references can capture an already-recursive local wrapper, even
        # if the new closure contains no global self-call of its own. Bound
        # names must not be mistaken for similarly named captured closures.
        return any((child["what"] == "expr:global" and child["name"] == self.recursive_target)
                   or (child["what"] == "expr:rel" and child["name"] not in scope
                       and self.recursive_value(env.get(child["name"])))
                   for child, scope in _scoped_nodes(node))

    def call(self, closure, arguments, mode, finish):
        require(isinstance(closure, _Closure) and len(closure.names) == len(arguments),
                "only fully applied local lambdas are supported")
        if id(closure) in self.recursive_closures:
            self.expanded_closures.add(id(closure))
        local = dict(closure.env)
        local.update((name, value) for name, value in zip(closure.names, arguments) if name != "_")
        self.emit(closure.body, local, mode, finish)

    def primitive(self, name, arguments):
        require(name in _PURE_ARITIES and len(arguments) == _PURE_ARITIES[name],
                "arithmetic primitive arity: " + name)
        values = [self.nat(arg).code for arg in arguments]
        if name == "div2":
            expression = "(" + values[0] + " / UINT64_C(2))"
        else:
            operator = {"add": "+", "mul": "*", "sub": "-", "leb": "<="}[name]
            expression = "(" + values[0] + " " + operator + " " + values[1] + ")"
        return self.scalar("bool" if name == "leb" else "nat", expression)

    def iteration(self, closure, initial, finish):
        self.loops += 1
        declarations = []
        state = self.slots(initial, declarations)
        self.lines.extend(declarations)
        self.assign(state, initial)
        outer = self.lines
        self.lines = []
        result_declarations, results = [], []
        before = set(self.initialized)
        self.depth += 1
        snapshot = self.freeze(state)

        def step(value):
            require(isinstance(value, _Step), "iteration body must return inl/inr")
            if value.tag == "Inl":
                # Even a simple coordinate swap must be a parallel assignment.
                next_state = self.freeze(value.value)
                self.assign(state, next_state)
                self.lines.append("continue;")
            else:
                if not results:
                    results.append(self.slots(value.value, result_declarations))
                self.assign(results[0], value.value)
                self.lines.append("break;")

        self.call(closure, [snapshot], "comp", step)
        require(results, "iteration has no syntactic exit")
        self.depth -= 1
        self.initialized = before
        body = self.lines
        self.lines = outer
        self.lines.extend(result_declarations)
        self.lines.append("for (;;) {")
        self.lines.extend(body)
        self.lines.append("}")
        finish(self.freeze(results[0]))

    def case(self, node, env, mode, finish):
        value = self.value(node["expr"], env)
        patterns = {case["pat"]["name"]: case for case in node["cases"]}
        if isinstance(value, tuple):
            require(set(patterns) == {"Pair"} and len(value) == 2, "product case shape")
            case = patterns["Pair"]
            names = case["pat"]["argnames"]
            local = dict(env)
            local.update((name, item) for name, item in zip(names, value) if name != "_")
            self.emit(case["body"], local, mode, finish)
            return
        require(isinstance(value, _Scalar), "only scalar/product cases are supported")
        is_nat = value.kind == "nat"
        names = ("O", "S") if is_nat else ("True", "False")
        require(set(patterns) == set(names), "only exhaustive nat/bool cases supported")
        # Every source value is immutable here, including array reads and the
        # loop-state snapshot. Branch bodies cannot change the scrutinee.
        condition = (value.code + " == UINT64_C(0)") if is_nat else value.code
        before = set(self.initialized)
        after = []
        self.depth += 1
        for index, name in enumerate(names):
            self.initialized = set(before)
            self.lines.append("if (" + condition + ") {" if index == 0 else "} else {")
            case = patterns[name]
            local = dict(env)
            params = case["pat"]["argnames"]
            if name == "S" and params[0] != "_":
                distance = value.input_distance
                local[params[0]] = self.scalar("nat", "(" + value.code + " - UINT64_C(1))",
                                              None if distance is None else distance + 1)
            self.emit(case["body"], local, mode, finish)
            after.append(set(self.initialized))
        self.lines.append("}")
        self.depth -= 1
        self.initialized = set.intersection(*after)

    def emit(self, node, env, mode, finish):
        kind = node["what"]
        if kind == "expr:let":
            value = self.value(node["nameval"], env)
            local = dict(env)
            if node["name"] != "_":
                local[node["name"]] = value
            self.emit(node["body"], local, mode, finish)
        elif kind == "expr:case":
            self.case(node, env, mode, finish)
        elif kind == "expr:rel":
            require(mode == "pure", "a computation cannot be a scalar/local value")
            require(node["name"] != "_" and node["name"] in env,
                    "unbound local: " + node["name"])
            finish(env[node["name"]])
        elif kind == "expr:lambda":
            require(mode == "pure", "expected computation, found lambda")
            closure = _Closure(node["argnames"], node["body"], dict(env))
            if self.recursive_target is not None and self.uses_recursion(node, env):
                self.recursive_closures[id(closure)] = closure
            finish(closure)
        elif kind == "expr:constructor":
            name, args = node["name"], node["args"]
            if mode == "comp":
                require(name == "Go" and args[0].get("what") == "expr:constructor"
                        and args[0]["name"] == "RetF", "only direct Return trees supported")
                self.emit(args[0]["args"][0], env, "pure", finish)
            else:
                require(name not in {"Go", "RetF"}, "tree/computation used as a pure value")
                values = [self.value(arg, env) for arg in args]
                if name == "O":
                    finish(_number(0))
                elif name == "S":
                    predecessor = self.nat(values[0])
                    finish(_number(predecessor.literal + 1) if predecessor.literal is not None
                           else self.primitive("add", [predecessor, _number(1)]))
                elif name in {"True", "False"}:
                    finish(_Scalar("bool", "UINT64_C(" + str(int(name == "True")) + ")"))
                elif name == "Tt":
                    finish(None)
                elif name == "Pair":
                    finish(tuple(values))
                elif name in {"Inl", "Inr"}:
                    finish(_Step(name, values[0]))
                else:
                    raise Unsupported("unsupported value constructor: " + name)
        elif kind == "expr:apply":
            head, args = node["func"], node["args"]
            if head["what"] != "expr:global":
                closure = self.value(head, env)
                arguments = [self.value(arg, env) for arg in args]
                self.call(closure, arguments, mode, finish)
                return
            name = head["name"]
            if name == self.recursive_target:
                require(mode == "comp", "recursive self-call must be a computation")
                require(len(args) == 1, "recursive self-call arity: " + name)
                argument = self.nat(self.value(args[0], env))
                require(argument.input_distance is not None and argument.input_distance > 0,
                        "recursive argument must be a strictly smaller matched predecessor "
                        "of the original input")
                self.recursive_calls += 1
                finish(self.scalar("nat", self.c_name + "(" + argument.code + ")"))
                return
            arities = _PURE_ARITIES if mode == "pure" else _COMPUTATION_ARITIES
            require(name in arities, "unsupported " + mode + " operation: " + name)
            require(len(args) == arities[name], "operation arity: " + name)
            self.operations[name] = self.operations.get(name, 0) + 1
            if name in _PURE_ARITIES:
                finish(self.primitive(name, [self.value(arg, env) for arg in args]))
            elif name == "bind":
                continuation = self.value(args[1], env)
                require(isinstance(continuation, _Closure) and len(continuation.names) == 1,
                        "bind requires a unary local continuation")
                if continuation.names == ["_"]:
                    self.emit(args[0], env, "comp", lambda _value: None)
                    value = None
                else:
                    value = self.capture(args[0], env, "comp")
                self.call(continuation, [value], "comp", finish)
            elif name in {"function_entry", "cost_iter"}:
                _dictionary(args[0], "id" if self.time_only else "inr")
                closure = self.value(args[1], env)
                initial = self.value(args[2], env)
                if name == "cost_iter":
                    self.iteration(closure, initial, finish)
                else:
                    self.call(closure, [initial], "comp", finish)
            elif name.startswith("cost_"):
                _dictionary(args[0], "id" if self.time_only else "inr")
                finish(self.primitive(name[5:], [self.value(arg, env) for arg in args[1:]]))
            else:
                _dictionary(args[0], "inl")
                index = self.nat(self.value(args[1], env)).literal
                require(index is not None, "only static literal allocation sizes/indices supported")
                if name == "array_alloc":
                    require(self.depth == 0 and self.capacity == 0 and index > 0,
                            "only one positive fixed allocation outside branches/loops supported")
                    self.capacity = index
                    self.lines.extend(["uint64_t cells[" + str(index) + "];", "(void)cells;"])
                    finish(_number(0))
                else:
                    require(index < self.capacity, "array index statically out of bounds or no allocation")
                    if name == "array_read":
                        require(index in self.initialized, "array read not definitely initialized")
                        finish(self.scalar("nat", "cells[" + str(index) + "]"))
                    else:
                        value = self.nat(self.value(args[2], env))
                        self.lines.append("cells[" + str(index) + "] = " + value.code + ";")
                        self.initialized.add(index)
                        finish(None)
        else:
            raise Unsupported("unsupported executable node: " + kind)


def _formatted(lines):
    output = []
    depth = 1
    for line in lines:
        if line.startswith("}"):
            depth -= 1
        require(depth >= 1, "internal C block imbalance")
        output.append("  " * depth + line)
        if line.endswith("{"):
            depth += 1
    require(depth == 1, "internal C block imbalance")
    return "\n".join(output)


def _c_name(name):
    require(isinstance(name, str) and _C_NAME.fullmatch(name) is not None,
            "unsupported C entrypoint identifier: " + repr(name))
    require(name not in _C_RESERVED and not re.fullmatch(r"v[0-9]+", name)
            and not re.match(r"(?:u?int(?:_least|_fast)?[0-9]+_t|u?intptr_t|u?intmax_t)$", name)
            and not name.startswith(("INT", "UINT", "SIZE_", "PTRDIFF_", "SIG_ATOMIC_",
                                     "WCHAR_", "WINT_")),
            "reserved C entrypoint identifier: " + name)


def generate(document, targets, entrypoint_names=None):
    """Translate selected extracted names; mapping values choose C entrypoints.

    All failures caused by unsupported/malformed source raise Unsupported. The
    caller owns output paths. No output is written by this function.
    """
    try:
        require(isinstance(targets, (list, tuple)) and targets, "expected a nonempty target list")
        for target in targets:
            _name(target, "target")
        require(len(set(targets)) == len(targets), "duplicate target")
        if entrypoint_names is None:
            entrypoint_names = {}
        require(isinstance(entrypoint_names, dict), "expected entrypoint-name mapping")
        require(set(entrypoint_names) <= set(targets), "entrypoint mapping has an unselected target")
        names = [entrypoint_names.get(target, target) for target in targets]
        for name in names:
            _c_name(name)
        require(len(set(names)) == len(names), "duplicate C entrypoint name")
        parsed = _Document(document)
        prototypes, functions, metadata = [], [], {}
        for target, c_name in zip(targets, names):
            declaration, time_only, recursive = parsed.client(target)
            compiler = _Lower(time_only, target if recursive else None, c_name)
            closure = compiler.value(declaration["value"], {})
            compiler.lines.append("(void)input;")

            def returned(value):
                compiler.lines.append("return " + compiler.nat(value).code + ";")

            compiler.call(closure, [_Scalar("nat", "input", input_distance=0)], "comp", returned)
            require(set(compiler.recursive_closures) <= compiler.expanded_closures,
                    "recursive self-call in an unused/unexpanded local closure is unsupported")
            prototype = "uint64_t " + c_name + "(uint64_t input)"
            prototypes.append(prototype + ";")
            functions.append(prototype + "\n{\n" + _formatted(compiler.lines) + "\n}")
            metadata[target] = {
                "c_name": c_name, "array_cells": compiler.capacity,
                "loops": compiler.loops, "lowered_calls": compiler.operations,
                "recursive_calls": compiler.recursive_calls,
            }
        header = ("/* Generated from Rocq extraction JSON; do not edit. */\n"
                  "#ifndef REFINETOITREE_GENERATED_H\n#define REFINETOITREE_GENERATED_H\n"
                  "#include <stdint.h>\n\n" + "\n".join(prototypes) + "\n\n#endif\n")
        source = ("/* Generated C11; native unsigned arithmetic, including subtraction. */\n"
                  '#include "generated.h"\n\n' + "\n\n".join(functions) + "\n")
        return source, header, metadata
    except RecursionError as error:
        raise Unsupported("extraction document or local expansion is too deeply nested") from error


def _unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON object key: " + key)
        result[key] = value
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("input", type=Path, metavar="INPUT_JSON")
    parser.add_argument("targets", nargs="+", metavar="NAME[=C_NAME]")
    parser.add_argument("--output-dir", type=Path, required=True, metavar="DIR")
    args = parser.parse_args(argv)
    try:
        targets, names = [], {}
        for spec in args.targets:
            target, separator, c_name = spec.partition("=")
            require(target not in targets, "duplicate target: " + target)
            targets.append(target)
            if separator:
                names[target] = c_name
        document = json.loads(args.input.read_text(encoding="utf-8"),
                              object_pairs_hook=_unique_pairs)
        source, header, metadata = generate(document, targets, names)
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for filename, text in (("generated.c", source), ("generated.h", header),
                               ("lowering-metadata.json", json.dumps(metadata, indent=2) + "\n")):
            (args.output_dir / filename).write_text(text, encoding="utf-8")
    except (Unsupported, OSError, UnicodeError, ValueError, RecursionError) as error:
        print("extract-c: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
