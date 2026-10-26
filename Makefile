# Development tasks.  `make -j4 test` runs the tests in parallel.
PYTHON ?= python3
HARNESS := tools/harness
E := examples/multiplier
# the tests that run programs through the harness (inputs2: the verifier of a key with two public inputs;
# inputs: keys with 3 to 5, in the numeric model and, for the window factors, in the harness;
# fflonk_keccak, fflonk_sha256: the fflonk verifier in each transcript mode; noir: the Groth16 verifier of
# a Noir circuit, bound by its first public input)
HARNESS_TESTS := fp curve pairing g2_check binding groth16 inputs2 inputs keccak msm fflonk_keccak fflonk_sha256 noir
# and the plain-Python ones: poly, invariants (what the generator refuses), tools (what the command-line
# tools refuse), and bn254_ref, which checks the reference against py_ecc
TESTS := $(HARNESS_TESTS) poly invariants tools

.PHONY: help harness test $(addprefix test-,$(TESTS)) test-bn254_ref bench example example-uprog fflonk-demo noir-demo lint fmt

help:
	@echo 'make harness    build tools/harness (hand, deploy, costs, sizes)'
	@echo 'make test       the tests (make -j4 test runs them in parallel)'
	@echo 'make test-NAME  one test: $(TESTS), or bn254_ref (needs py_ecc)'
	@echo 'make bench      the cost of each F_p operation'
	@echo 'make example    check that the files in examples/ regenerate byte for byte'
	@echo 'make example-uprog  and that deploy compile gives the committed .uprog and .wnames (minutes)'
	@echo 'make fflonk-demo  the fflonk toy circuit in both transcript modes, setup and prove (circom, Node.js)'
	@echo 'make noir-demo  the Noir toy circuit for Groth16, setup and prove (nargo, noir-cli, Node.js)'
	@echo 'make lint       ruff, mypy, cargo fmt and clippy, as CI runs them'
	@echo 'make fmt        format the Python and the Rust code'

harness:
	cd $(HARNESS) && cargo build --release --locked

test: $(addprefix test-,$(TESTS))

$(addprefix test-,$(filter-out inputs2 fflonk_%,$(HARNESS_TESTS))): test-%: harness
	$(PYTHON) tests/test_$*.py

test-inputs2: harness
	INPUTS=2 $(PYTHON) tests/test_groth16.py

test-fflonk_keccak test-fflonk_sha256: test-fflonk_%: harness
	$(PYTHON) tests/test_fflonk.py $*

test-poly test-invariants test-tools test-bn254_ref: test-%:
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

# the committed consensus encoding and witness names, from which the address is derived (deploy address)
example-uprog: example harness
	$(HARNESS)/target/release/deploy compile build/check.simpl build/check
	cmp build/check.uprog $(E)/verifier.uprog
	cmp build/check.wnames $(E)/verifier.wnames
	@echo 'deploy compile gives the committed verifier.uprog and verifier.wnames'

# the fflonk toy circuit, setup and prove in each transcript mode, for the harness's dummy sighash (no
# Elements node; after deploy compile, tools/regtest.sh build/fflonk_<t> proves and spends on one)
fflonk-demo: harness
	for t in keccak sha256; do \
		$(PYTHON) tools/demo.py setup --protocol fflonk --transcript $$t --out build/fflonk_$$t && \
		$(PYTHON) tools/demo.py prove --out build/fflonk_$$t \
			--sighash 9ef140b9bd336a9c5f00476986ac6a42cbadba9edd3de4b7fe36b5490fd0754a || exit 1; \
	done

# the Noir toy circuit for Groth16, setup and prove for the harness's dummy sighash (no Elements node;
# after deploy compile, tools/regtest.sh build/noir proves and spends on one)
noir-demo: harness
	$(PYTHON) tools/demo.py setup --frontend noir --out build/noir
	$(PYTHON) tools/demo.py prove --out build/noir \
		--sighash 9ef140b9bd336a9c5f00476986ac6a42cbadba9edd3de4b7fe36b5490fd0754a

lint:
	ruff check .
	ruff format --check .
	mypy
	cd $(HARNESS) && cargo fmt --check && cargo clippy --release --locked --all-targets -- -D warnings

fmt:
	ruff check --fix .
	ruff format .
	cd $(HARNESS) && cargo fmt
