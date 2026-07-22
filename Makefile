.PHONY: usage

usage:
	@echo " - build_blaster: Build Blaster."
	@echo " - clean_blaster: Clean compiled lean files for Blaster."
	@echo " - check_blaster: Same as build_blaster but also checks that each lean file"
	@echo " - build_tests: Build Tests with the default Z3 backend."
	@echo " - clean_tests: Clean compiled Lean files."
	@echo " - check_tests: Run the default Z3 test tier from a clean state."
	@echo " - test-z3: Run backend tests with Z3 only."
	@echo " - test-cvc5: Run strict backend tests with cvc5 only."
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

.PHONY: test-z3
test-z3:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	env -u BLASTER_SOLVER -u BLASTER_STRICT_CVC5_RESULTS LEAN_NUM_THREADS=5 lake build Tests.Z3

.PHONY: test-cvc5
test-cvc5:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	BLASTER_SOLVER=cvc5 BLASTER_STRICT_CVC5_RESULTS=1 LEAN_NUM_THREADS=5 lake build Tests.Cvc5

.PHONY: test-all-solvers
test-all-solvers:
	rm -rf .lake/build/lib/lean/Tests .lake/build/ir/Tests
	env -u BLASTER_SOLVER BLASTER_STRICT_CVC5_RESULTS=1 LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests Tests.AllSolvers

.PHONY: build_tests
build_tests:
	$(MAKE) test-z3

.PHONY: clean_tests
clean_tests:
	lake clean

.PHONY: check_tests
check_tests:
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
