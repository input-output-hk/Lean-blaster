name: Feature Request
description: Suggest a new feature or enhancement for Blaster
title: "[Feature]: "
labels: ["enhancement", "status: needs-discussion"]
body:
  - type: markdown
    attributes:
      value: |
        Thanks for suggesting a feature! Please provide details below to help us understand your proposal.

  - type: textarea
    id: problem
    attributes:
      label: Problem Statement
      description: What problem does this feature solve? Is your feature request related to a problem?
      placeholder: I'm frustrated when... / It would be helpful if...
    validations:
      required: true

  - type: textarea
    id: alternatives
    attributes:
      label: Alternatives Considered
      description: Have you considered any alternative solutions or workarounds?
      placeholder: Describe alternatives you've considered

  - type: textarea
    id: use-case
    attributes:
      label: Use Case
      description: Provide a concrete example of how this feature would be used
      placeholder: |
        ```lean
        -- Example showing how the feature would be used
        ```
    validations:
      required: true

  - type: dropdown
    id: priority
    attributes:
      label: Priority
      description: How important is this feature to you?
      options:
        - Low - Nice to have
        - Medium - Would be beneficial
        - High - Important for my use case
        - Critical - Blocking my work
    validations:
      required: true

  - type: textarea
    id: additional-context
    attributes:
      label: Additional Context
      description: Add any other context, mockups, or examples about the feature request
      placeholder: Any other relevant information