# Contributing to Blaster

Thank you for your interest in contributing to Blaster! We welcome contributions of all kinds, including bug fixes, new features, performance improvements, documentation, and benchmarks.

## Table of Contents

- [Code of Conduct](#code-of-conduct)
- [Getting Started](#getting-started)
- [Development Workflow](#development-workflow)
- [Branching Strategy](#branching-strategy)
- [Coding Standards](#coding-standards)
- [Testing Requirements](#testing-requirements)
- [Pull Request Process](#pull-request-process)
- [Communication](#communication)
- [Issue Labels](#issue-labels)
- [Project Governance](#project-governance)

## Code of Conduct

We are committed to providing a welcoming and inclusive environment for all contributors. Please be respectful and professional in all interactions.

## Getting Started

1. **Fork the repository** and clone it locally
2. **Set up your development environment** following the [installation instructions](README.md#-installation)
3. **Check existing issues** to see if your contribution is already being discussed
4. **Create an issue** if you're planning a significant change or new feature

## Development Workflow

### Before You Start

- **For new features or significant changes**: Open a GitHub Discussion or Issue first to discuss your approach. This helps avoid wasted effort if the change conflicts with core principles or project direction.
- **For bug fixes**: Check if an issue already exists, or create one describing the bug.
- **For documentation improvements**: Feel free to submit a PR directly.

### Local Development

1. Create a feature branch from `staging` (see [Branching Strategy](#branching-strategy))
2. Make your changes following our [Coding Standards](#coding-standards)
3. Add or update tests as required (see [Testing Requirements](#testing-requirements))
4. Test your changes locally. We recommend using the `make check_all` command to run the build and tests.
5. Commit your changes using [Conventional Commits](#commit-message-format)
6. Push to your fork and create a Pull Request targeting `staging`

## Branching Strategy

We use a three-tier branching model:

- **`main`**: Stable, production-ready code. All releases are tagged from this branch.
- **`staging`**: Integration branch for features that have been merged.
- **`feature/*`**: Individual feature branches for development and PRs.

### Branch Naming Convention

- Features: `feature/description-of-feature`
- Bug fixes: `fix/description-of-bug`
- Documentation: `docs/description-of-change`
- Performance: `perf/description-of-improvement`

### Workflow

```
main (stable)
  ↑
staging (integration)
  ↑
feature/your-feature (development)
```

1. Create your feature branch from `main`: `git checkout -b feature/my-feature main`
2. Make your changes and commit them
3. Push your branch to your fork
4. Open a PR targeting `staging` 
5. After review and approval, maintainers will merge to `staging`
6. When ready for release, changes in `staging` are merged to `main`

## Coding Standards

### Lean4 Style Guide

We follow the standard Lean4 style conventions supported by the VSCode extension:

- **Indentation**: 2 spaces (no tabs)
- **Line length**: Aim for 100 characters, hard limit at 120
- **Naming conventions**:
  - Types and typeclasses: `UpperCamelCase`
  - Functions and theorems: `lowerCamelCase`
  - Constants: `lowerCamelCase`
  - Namespaces: `LowerCase` or `Lower.Case`

### Code Organization

- Keep functions focused and single-purpose
- Group related definitions together
- Use meaningful variable names

### Documentation

- Add doc comments (`/--` ... `-/`) for all public functions
- Include examples in doc comments where helpful
- Update README.md if adding user-facing features

## Testing Requirements

All contributions must include appropriate tests. Our CI automatically runs the test suite on all PRs.

### For New Features

- Add new test cases covering the feature's functionality
- Include both positive and negative test cases
- Add tests to the appropriate test file or create a new one
- Document expected behavior in test comments using either `guard_msg` or the different tactic's options

### For Bug Fixes

1. **Add a test that reproduces the bug** as an Issue in the `Tests/Issues/` folder, documenting the expected behavior
2. **Implement your fix**
3. **Verify the test now passes**
4. **Add the original failing example** to the `Tests/Issues/` folder with a the next available number and reference to the issue ticketnumber

Example structure:
```
Tests/Issues/
  Issue<number>.lean
```

### Running Tests

To run all tests:
```bash
# Run all tests
make test_all
```

### Running the Build

To build blaster:
```bash
make build_blaster
```

### Running the full check

To run the full check:
```bash
make check_all
```

This wil run the build, tests, and ensure that all files were considered by the build system.

## Pull Request Process

### Before Submitting

- [ ] Tests pass locally
- [ ] Code follows our style guidelines
- [ ] Commits follow Conventional Commits format
- [ ] Documentation is updated (if applicable)
- [ ] Issue number is referenced in PR description

### Commit Message Format

We try to use [Conventional Commits](https://www.conventionalcommits.org/) for clear and structured commit history.

```
<type>(<scope>): <description>

[optional body]

[optional footer]
```

**Types:**
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `style`: Code style changes (formatting, no functional changes)
- `refactor`: Code refactoring
- `perf`: Performance improvements
- `test`: Adding or updating tests
- `chore`: Maintenance tasks, dependency updates

**Examples:**
```
feat(smt): add support for bitvector operations

fix(optimizer): resolve timeout in recursive function handling

Fixes #123

docs(readme): update installation instructions for Z3
```

### PR Template

When creating a PR, please include:

```markdown
## Description
Brief description of the changes

## Type of Change
- [ ] Bug fix (non-breaking change fixing an issue)
- [ ] New feature (non-breaking change adding functionality)
- [ ] Breaking change (fix or feature causing existing functionality to change)
- [ ] Documentation update

## Related Issue
Fixes #(issue number)

## Testing
Description of testing performed

## Checklist
- [ ] My code follows the project's style guidelines
- [ ] I have added tests that prove my fix/feature works
- [ ] New and existing tests pass locally
- [ ] I have added necessary documentation
- [ ] For bug fixes: I have added the failing example to Issues/
```

### Review Process

1. **Automated checks**: CI will run tests and check that all files were considered by the build system.
2. **Maintainer review**: A maintainer will review your PR
3. **Feedback**: Address any requested changes
4. **Approval**: Once approved, a maintainer will merge your PR

**Expected timeline**: We aim to provide initial feedback within one week and triage issues every two weeks.

## Communication

### Where to Communicate

- **GitHub Discussions**: Best for feature proposals, architectural discussions, and general questions
- **GitHub Issues**: For bug reports and specific feature requests. All issues are tracked in the public GitHub Project board.
- **Pull Requests**: For code review discussions

### Creating Effective Issues

When creating an issue, please:

1. **Search existing issues** to avoid duplicates
2. **Use appropriate labels** (see [Issue Labels](#issue-labels))
3. **Provide context**:
   - For bugs: Steps to reproduce, expected vs. actual behavior, environment details
   - For features: Use case, proposed solution, alternatives considered
4. **Include code samples** using Lean4 syntax highlighting:

```lean
-- Your code example here
```

## Issue Labels

We use labels to categorize. We use a GitHub Project to provide additional context and track the progress of issues. Please apply appropriate labels when creating issues:

### Type Labels
- `bug`: Something isn't working correctly
- `enhancement`: New feature or improvement request
- `documentation`: Documentation improvements or additions
- `performance`: Performance-related issues or improvements
- `question`: General questions about usage or behavior

### Difficulty Labels
- `good first issue`: Good for newcomers to the project
- `help wanted`: We'd especially appreciate community contributions

### Area Labels
- `area: smt`: SMT backend and solver integration
- `area: optimizer`: Expression optimization
- `area: tests`: Testing infrastructure
- `area: ci`: Continuous integration
- `area: build`: Build system and dependencies

## Project Governance

### Maintainers

Blaster is owned by **Input Output Global** and maintained by:

- [Romain Soulat](https://github.com/RSoulatIOHK)
- [Jean-Frédéric Etienne](https://github.com/etiennejf)

### Project Tracking

We use a GitHub Project board to track progress on issues and pull requests:

- **Backlog**: Issues being considered for future work
- **To Do**: Issues prioritized for upcoming work
- **In Progress**: Currently being worked on
- **In Review**: Pull requests under review
- **Done**: Completed work
- **Won't Do**: Issues that will not be worked on

**Note**: We're developing a bot to automatically notify issue authors when their ticket moves from Backlog to To Do and when it's assigned to a delivery cycle. Stay tuned!

### Response Time Commitment

- **Initial response to issues**: Within 1 week
- **PR reviews**: Within 1 week of submission
- **Triage cycle**: Every 2 weeks

We appreciate your patience and understanding. If you haven't received a response within these timeframes, feel free to ping the issue or PR.

## Recognition

We value all contributions to Blaster! Contributors will be:
- Listed in the project's contributor graph
- Mentioned in release notes for significant contributions
- Acknowledged in the project README (for substantial contributions)

## Questions?

If you have questions that aren't covered in this guide:

1. Check the [README](README.md)
2. Search [existing discussions](../../discussions)
3. Create a new [discussion](../../discussions/new) or [issue](../../issues/new)

Thank you for contributing to Blaster! 🚀