name: Bug Report
description: Report a bug or unexpected behavior in Blaster
title: "[Bug]: "
labels: ["bug", "status: needs-reproduction"]
body:
  - type: markdown
    attributes:
      value: |
        Thanks for taking the time to report a bug! Please fill out the information below to help us resolve the issue.

  - type: textarea
    id: description
    attributes:
      label: Description
      description: A clear and concise description of what the bug is.
      placeholder: Tell us what happened
    validations:
      required: true

  - type: textarea
    id: reproduction
    attributes:
      label: Steps to Reproduce
      description: Provide a minimal example that reproduces the issue
      placeholder: All the necessary information to reproduce your bug
      value: |
        ```lean
        -- Your minimal reproducible example here
        ```
    validations:
      required: true

  - type: textarea
    id: expected
    attributes:
      label: Expected Behavior
      description: What did you expect to happen?
      placeholder: Describe the expected outcome
    validations:
      required: true

  - type: textarea
    id: actual
    attributes:
      label: Actual Behavior
      description: What actually happened? Include any error messages.
      placeholder: Describe what actually happened
    validations:
      required: true

  - type: input
    id: lean-version
    attributes:
      label: Lean Version
      description: What version of Lean4 are you using?
      placeholder: e.g., v4.24.0
    validations:
      required: true

  - type: input
    id: z3-version
    attributes:
      label: Z3 Version
      description: What version of Z3 are you using?
      placeholder: e.g., v4.15.2
    validations:
      required: true

  - type: textarea
    id: additional-context
    attributes:
      label: Additional Context
      description: Add any other context about the problem here
      placeholder: Any other relevant information