.PHONY: usage

BLASTER_TIMEOUT ?= 30
CVC5_FLOOR_VERSION ?= 1.2.1

usage:
	@echo " - build_blaster: Build Blaster."
	@echo " - clean_blaster: Clean compiled lean files for Blaster."
	@echo " - check_blaster: Same as build_blaster but also checks that each lean file"
	@echo " - build_tests: Build the pure and default Z3 test tiers."
	@echo " - clean_tests: Clean compiled Lean files."
	@echo " - check_tests: Run the pure and default Z3 test tiers from clean states."
	@echo " - test-pure: Run solver-independent tests (no solver required)."
	@echo " - test-z3: Run backend tests with Z3 only."
	@echo " - test-cvc5: Run strict backend tests with cvc5 only."
	@echo " - test-cvc5-floor: Run cvc5 1.2.1 discovery and smoke checks."
	@echo " - test-all-solvers: Run cross-backend tests (both solvers required)."
	@echo " - build_all: Blaster, and Tests."
	@echo " - clean_all: Blaster, and Tests."
	@echo " - check_all: Blaster, and Tests."

.PHONY: build_blaster
build_blaster:
	lake build Blaster

.PHONY: clean_blaster
clean_blaster:
	lake clean Blaster

.PHONY: check_blaster
check_blaster: clean_blaster
	./scripts/check_lean_project_compilation.sh Blaster

.PHONY: test-pure
test-pure:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	env -u BLASTER_SOLVER -u BLASTER_TIMEOUT -u BLASTER_STRICT_CVC5_RESULTS LEAN_NUM_THREADS=5 lake build Tests.Pure

.PHONY: test-z3
test-z3:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	BLASTER_SOLVER=z3 BLASTER_TIMEOUT=$(BLASTER_TIMEOUT) BLASTER_STRICT_CVC5_RESULTS=0 LEAN_NUM_THREADS=5 lake build Tests.Z3

.PHONY: test-cvc5
test-cvc5:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	BLASTER_SOLVER=cvc5 BLASTER_TIMEOUT=$(BLASTER_TIMEOUT) BLASTER_STRICT_CVC5_RESULTS=1 LEAN_NUM_THREADS=5 lake build Tests.Cvc5

.PHONY: test-cvc5-floor
test-cvc5-floor:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	cvc5 --version | head -1 | grep -F "version $(CVC5_FLOOR_VERSION) ["
	env -u BLASTER_TIMEOUT BLASTER_SOLVER=cvc5 BLASTER_STRICT_CVC5_RESULTS=1 lake exe solvercheck cvc5
	env -u BLASTER_TIMEOUT BLASTER_SOLVER=cvc5 BLASTER_STRICT_CVC5_RESULTS=1 LEAN_NUM_THREADS=5 lake build Tests.Smt.Cvc5Floor

.PHONY: test-all-solvers
test-all-solvers:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	env -u BLASTER_SOLVER -u BLASTER_TIMEOUT BLASTER_STRICT_CVC5_RESULTS=1 LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests Tests.AllSolvers

.PHONY: build_tests
build_tests:
	$(MAKE) test-pure
	$(MAKE) test-z3

.PHONY: clean_tests
clean_tests:
	lake clean

.PHONY: check_tests
check_tests:
	$(MAKE) test-pure
	$(MAKE) test-z3

# Aggregate commands
# To maintain when you add new components
.PHONY: build_all
build_all:
	$(MAKE) build_blaster
	$(MAKE) build_tests

.PHONY: clean_all
clean_all:
	$(MAKE) clean_blaster
	$(MAKE) clean_tests

.PHONY: check_all
check_all:
	$(MAKE) check_blaster
	$(MAKE) check_tests
