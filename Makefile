.PHONY: usage

usage:
	@echo " - build_solver: Build Solver."
	@echo " - clean_solver: Clean compiled lean files for Solver."
	@echo " - check_solver: Same as build_solver but also checks that each lean file"
	@echo " - build_tests: Build Tests."
	@echo " - clean_tests: Clean compiled lean files for Tests."
	@echo " - check_tests: Same as build_tests but also checks that each lean file"
	@echo " - build_all: Solver, and Tests."
	@echo " - clean_all: Solver, and Tests."
	@echo " - check_all: Solver, and Tests."

.PHONY: build_solver
build_solver:
	lake build Solver

.PHONY: clean_solver
clean_solver:
	lake clean

.PHONY: check_solver
check_solver: clean_solver
	./scripts/check_lean_project_compilation.sh Solver Solver

TESTS_FOLDER := Tests
.PHONY: build_tests
build_tests:
	lake build Tests

.PHONY: clean_tests
clean_tests:
	lake clean Tests

.PHONY: check_tests
check_tests: clean_tests
	./scripts/check_lean_project_compilation.sh Tests Tests
# Aggregate commands
# To maintain when you add new components
.PHONY: build_all
build_all: build_solver build_tests
.PHONY: clean_all
clean_all: clean_solver clean_tests

.PHONY: check_all
check_all: check_solver check_tests