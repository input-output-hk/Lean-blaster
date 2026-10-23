# Working on Lean-blaster

For issue-driven bug fixes, use the `fix-issue` skill in
`.agents/skills/fix-issue/SKILL.md`. Follow the setup and validation commands in
`.github/agent-fix/config.json`; the CI setup script is for disposable Linux
runners, while local work may use an equivalent installed toolchain.

- Start with an existing problem issue and a minimal reproducer. Identify the
  intended behavior and root cause before choosing a patch.
- Fix the mechanism for a family of inputs. Do not recognize a particular issue,
  theorem name, or example and hardcode its result.
- Preserve the original reproducer in `Tests/FixedIssues/Issue<N>.lean`, reference
  the issue, and import it from `Tests/FixedIssues.lean`. Add variants and cases
  where the rule must not apply. For bot runs, mark the standalone original block
  as specified in the profile, so it can be rerun independently on the base.
- Preserve specifications on changed functions. Document non-obvious inputs,
  results, rewrite forms, preconditions, and side conditions when needed.
- Preserve Lean semantics, expression-sharing invariants, local-context scope,
  and explicit-stack traversal. Do not introduce axioms, admissions, or disabled
  diagnostics to make a test pass. Keep Valid, Falsified, and Undetermined distinct.
- Run focused checks and `make check_all`. Report actual diagnostics and failures;
  compare suspected preexisting failures on an untouched base. Never weaken an
  expected result simply to obtain a green build.
- Keep fixes focused. New encodings, backends, significant public APIs,
  dependencies, or toolchain changes need prior design discussion.
- Open draft PRs with the linked issue, root cause, correctness argument, generic
  coverage, validation, and limitations. Never merge automatically.
