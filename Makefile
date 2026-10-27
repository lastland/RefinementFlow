ROCQ ?= rocq
PYTHON ?= python3
CLANG ?= clang

.DEFAULT_GOAL := all
.PHONY: all build clean examples assumptions guard-tests extract-c check-c benchmark-c check install-hooks install

all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

build: all

Makefile.coq: _CoqProject
	$(ROCQ) makefile -f _CoqProject -o $@

# Replay executable observations even when compilation is up to date.
examples: all
	$(ROCQ) repl -batch -quiet -Q theories RefineToITree -l theories/Examples.v

# Each manifest entry must produce exactly one closed assumptions report.
assumptions: all
	$(PYTHON) scripts/check_assumptions.py --rocq "$(ROCQ)"

guard-tests: all
	ROCQ="$(ROCQ)" CLANG="$(CLANG)" $(PYTHON) -m unittest discover -s tests -v

# Always regenerate from the actual derived implementations. Share the all
# prerequisite with the proof gates, including under parallel make check.
extract-c: all
	mkdir -p build/c
	$(ROCQ) repl -q -batch -quiet -Q theories RefineToITree -l extraction/ExtractC.v
	$(PYTHON) scripts/extract_c.py build/c/targets.json fib_L3=fib_l3 fib_L4=fib_l4 fib_L1=fib_l1 fib_L2=fib_l2 --output-dir build/c

check-c: extract-c
	$(PYTHON) scripts/check_c.py --rocq "$(ROCQ)" --clang "$(CLANG)" --build-dir build/c --reuse-extraction

# Optional wall-clock experiment; timing variation is not a correctness gate.
benchmark-c: extract-c
	$(PYTHON) scripts/benchmark_c.py --clang "$(CLANG)"

check: examples assumptions guard-tests check-c

install-hooks:
	$(PYTHON) scripts/git_hooks.py install

install: all
	+$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	$(RM) Makefile.coq Makefile.coq.conf
	$(RM) -r build/c
