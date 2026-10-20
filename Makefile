# Development tasks.  `make -j4 test` runs the tests in parallel.
PYTHON ?= python3
HARNESS := tools/harness
E := examples/multiplier
# the tests that run programs through the harness (inputs2: the verifier of a key with two public inputs)
HARNESS_TESTS := fp curve pairing g2_check binding groth16 inputs2
# and the plain-Python ones: poly, inputs (keys with 3 to 5 public inputs), and bn254_ref, which checks the
# reference against py_ecc
TESTS := $(HARNESS_TESTS) poly inputs

.PHONY: help harness test $(addprefix test-,$(TESTS)) test-bn254_ref bench example lint fmt

help:
	@echo 'make harness    build tools/harness (hand, deploy, costs, sizes)'
	@echo 'make test       the tests (make -j4 test runs them in parallel)'
	@echo 'make test-NAME  one test: $(TESTS), or bn254_ref (needs py_ecc)'
	@echo 'make bench      the cost of each F_p operation'
	@echo 'make example    check that the files in examples/ regenerate byte for byte'
	@echo 'make lint       ruff, mypy, cargo fmt and clippy, as CI runs them'
	@echo 'make fmt        format the Python and the Rust code'

harness:
	cd $(HARNESS) && cargo build --release --locked

test: $(addprefix test-,$(TESTS))

$(addprefix test-,$(filter-out inputs2,$(HARNESS_TESTS))): test-%: harness
	$(PYTHON) tests/test_$*.py

test-inputs2: harness
	INPUTS=2 $(PYTHON) tests/test_groth16.py

test-poly test-inputs test-bn254_ref: test-%:
	$(PYTHON) tests/test_$*.py

bench: harness
	$(PYTHON) tests/test_fp.py bench

example:
	$(PYTHON) tools/groth16_snarkjs.py program $(E)/verification_key.json --values 1 --out build/check
	$(PYTHON) tools/groth16_snarkjs.py witness $(E)/verification_key.json $(E)/proof.json $(E)/public.json \
		--leaves $(E)/leaves.json --out build/check
	gunzip -c $(E)/verifier.simpl.gz | cmp - build/check.simpl
	gunzip -c $(E)/verifier.w0.json.gz | cmp - build/check.w0.json
	$(PYTHON) examples/fp_mul.py | cmp - examples/fp_mul.simpl
	@echo 'the examples regenerate byte for byte'

lint:
	ruff check .
	ruff format --check .
	mypy
	cd $(HARNESS) && cargo fmt --check && cargo clippy --release --locked --all-targets -- -D warnings

fmt:
	ruff check --fix .
	ruff format .
	cd $(HARNESS) && cargo fmt
