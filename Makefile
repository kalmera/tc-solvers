DUNE ?= dune
ROCQ ?= rocq
ROCQ_JOBS ?= 4
RANK_WORKLIST ?= bitmap
export RANK_WORKLIST
.DEFAULT_GOAL := all
.PHONY: all proofs rocq extract regenerate goblint-solvers goblint-adapters ocaml test narrowing-fixed-point clean check-generated library
all: regenerate
	$(MAKE) test
RocqMakefile: _RocqProject
	$(ROCQ) makefile -f _RocqProject -o $@
proofs rocq: RocqMakefile
	$(MAKE) -j$(ROCQ_JOBS) -f RocqMakefile all
narrowing-fixed-point: RocqMakefile
	$(MAKE) -j$(ROCQ_JOBS) -f RocqMakefile rocq/solvers/slr/narrowing_fixed_point/tests/Instances.vo rocq/solvers/slr/narrowing_fixed_point/tests/LeastInstances.vo
# Recompile extraction roots even when their .vo files are current.
extract: proofs
	$(ROCQ) compile -Q rocq TcSolvers rocq/extraction/ExtractSimple.v
	$(ROCQ) compile -Q rocq TcSolvers rocq/extraction/ExtractRestarting.v
	$(ROCQ) compile -Q rocq TcSolvers rocq/extraction/ExtractNarrowingFixedPoint.v
	$(ROCQ) compile -Q rocq TcSolvers rocq/extraction/GoblintControl.v
	python3 tools/mark_generated.py
regenerate goblint-solvers: extract
	$(MAKE) goblint-adapters
	$(MAKE) library
library:
	python3 ocaml/library/generate.py
goblint-adapters:
	sh ocaml/adapters/goblint/generate_goblint_slrtc_solvers.sh
	python3 ocaml/adapters/goblint/narrowing_fixed_point/generate.py
	cp ocaml/adapters/goblint/goblint_slrtc_register.ml ocaml/adapters/goblint/generated/slrtc_register.ml
	python3 tools/mark_generated.py
ocaml:
	$(DUNE) build @install
	$(DUNE) runtest examples
test: ocaml
	$(DUNE) runtest tests
	python3 -m unittest discover -s tests/install -p 'test_*.py'
check-generated: regenerate
	python3 tools/check_generated.py
clean:
	if test -f RocqMakefile; then $(MAKE) -f RocqMakefile clean; fi
	$(DUNE) clean
