.PHONY: usage

usage:
	@echo " - build_blaster: Build Blaster."
	@echo " - clean_blaster: Clean compiled lean files for Blaster."
	@echo " - check_blaster: Same as build_blaster but also checks that each lean file"
	@echo " - build_tests: Build Tests."
	@echo " - clean_tests: Clean compiled lean files for Tests."
	@echo " - check_tests: Same as build_tests but also checks that each lean file"
	@echo " - test-cvc5: Run the opt-in cvc5 tests (TestsCvc5; needs cvc5 and Z3)."
	@echo " - test-cvc5-backend: Run the backend test tiers with cvc5 selected."
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

.PHONY: test-cvc5
test-cvc5:
	LEAN_NUM_THREADS=5 LEAN_PROJECT_EXCLUDE_MODULES=TestsCvc5.CounterexampleSpike ./scripts/check_lean_project_compilation.sh TestsCvc5

.PHONY: test-cvc5-backend
test-cvc5-backend:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	BLASTER_SOLVER=cvc5 BLASTER_STRICT_CVC5_RESULTS=1 LEAN_NUM_THREADS=5 lake build Tests.Backend

# Aggregate commands
# To maintain when you add new components
.PHONY: build_all
build_all: build_blaster build_tests

.PHONY: clean_all
clean_all: clean_blaster clean_tests

.PHONY: check_all
check_all: check_blaster check_tests
