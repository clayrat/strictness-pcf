# Regenerate the extracted OCaml from Rocq, then build and run the examples.
#   make        - extract, build, and run
#   make extract- (re)generate checker.ml / checker.mli from Extract.v
#   make clean  - remove generated OCaml, the dune _build, and Rocq artifacts

.PHONY: all extract run clean

all: run

checker.ml checker.mli: Extract.v ../theories/Checker.vo ../theories/Strictness.vo ../theories/Examples.vo
	coqc -Q ../theories PCF Extract.v
	@if grep -q 'Obj.magic' checker.ml; then \
		echo 'error: extraction introduced Obj.magic'; exit 1; \
	fi

extract: checker.ml

run: checker.ml
	dune exec ./main.exe

clean:
	rm -f checker.ml checker.mli *.vo *.vok *.vos *.glob .*.aux
	rm -rf _build
