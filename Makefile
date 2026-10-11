.PHONY: usage

usage:
	@echo " - build_blaster: Build Blaster."
	@echo " - clean_blaster: Clean compiled lean files for Blaster."
	@echo " - check_blaster: Same as build_blaster but also checks that each lean file"
	@echo " - build_tests: Build Tests."
	@echo " - clean_tests: Clean compiled lean files for Tests."
	@echo " - check_tests: Same as build_tests but also checks that each lean file"
	@echo " - test-solver: Run solver-infrastructure tests (TestsSolver; needs z3)."
	@echo " - test-cvc5: Run the opt-in cvc5 tests (TestsCvc5; needs cvc5 and z3)."
	@echo " - solvercheck: Check installed solvers (version and required capabilities)."
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

.PHONY: build_tests
build_tests:
	LEAN_NUM_THREADS=5 lake test

.PHONY: clean_tests
clean_tests:
	lake clean

.PHONY: check_tests
check_tests: clean_tests
	LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests

# Solver-infrastructure tests (pure, plus z3-only) and opt-in cvc5 tests.
# Each file is checked with `lake env lean`; any error fails the target.
LEAN_FILE_CHECK = LEAN_NUM_THREADS=5 xargs -n1 -P4 sh -c 'lake env lean "$$0" || { echo "FAILED: $$0"; exit 255; }'

.PHONY: test-solver
test-solver: build_blaster
	find TestsSolver -name '*.lean' | sort | $(LEAN_FILE_CHECK)

.PHONY: test-cvc5
test-cvc5: build_blaster
	find TestsCvc5 -name '*.lean' ! -name 'CounterexampleSpike.lean' | sort | $(LEAN_FILE_CHECK)

.PHONY: solvercheck
solvercheck: build_blaster
	lake env lean --run SolverCheck.lean

# Aggregate commands
# To maintain when you add new components
.PHONY: build_all
build_all: build_blaster build_tests

.PHONY: clean_all
clean_all: clean_blaster clean_tests

.PHONY: check_all
check_all: check_blaster check_tests
