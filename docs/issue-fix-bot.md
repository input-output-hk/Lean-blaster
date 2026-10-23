# Small-issue fix bot

A maintainer adds `agent:fix` to an open issue containing a fenced minimal
reproducer. The bot reproduces the failure, looks for a general fix, preserves the
original regression, documents relevant specifications, and opens a draft PR.
It never merges. An Actions **Run workflow** entry point also accepts an issue
number, from the default branch only.

The report's **Target Branch** field selects both the implementation to test and
the PR destination. If blank, an unambiguous legacy branch statement such as
`Branch: release/foo` is recognized; otherwise the repository default is used.
Code fences and hidden HTML comments do not select branches. Conflicting or
unknown branches produce an issue diagnostic before model usage. The manual
entry point has a maintainer override for the target branch.

At the start, the runner resolves the selected same-repository branch to an
immutable commit. Baseline reproduction, the patch, and validation all use that
commit; the PR targets that branch. Trusted commands and publishing rules come
from a **separate** pinned default-branch policy checkout. A bug branch cannot
replace those rules or its setup script. The trusted Lean installer reads the
selected branch's versioned official Lean toolchain as data. Custom/nightly
toolchains require setup discussion rather than an implicit fallback.
The runner reserves `.agent-fix/` for transient data and rejects branches that
track that path or supply linked or special artifact files.

## Enable the pilot

1. Merge the workflow, helper package, skill, and repository profile together.
2. Add an OpenAI project API key as the repository Actions secret
   `OPENAI_API_KEY`, or make an organization secret available to this repository.
   Do not put the key in an issue, prompt, commit, or workflow file. Configure the
   project's API spending controls separately; job timeouts are runtime limits,
   not spending limits. API usage is billed separately from a ChatGPT
   subscription; desktop sign-in does not supply CI API authentication. See
   [OpenAI billing](https://help.openai.com/en/articles/9039756-managing-billing-settings-on-chatgpt-web-and-platform).
3. Allow GitHub Actions to create PRs in the repository's Actions settings, subject
   to organization policy. The workflow uses the scoped `GITHUB_TOKEN` and does
   not need a personal access token. Do not enable automatic approval or merging.
4. Create a label named `agent:fix`. Only users with current repository write,
   maintain, or admin permission can start a run; triage permission alone is not
   sufficient. Reruns check the original actor and the rerunning actor.
5. Optionally set repository/organization variable `AGENT_FIX_MODEL` to an
   approved model. Empty uses the Codex default. The action and CLI versions are
   pinned in the reusable workflow and should be updated deliberately.
6. Select a small, reproducible issue without an existing bot PR, and apply the
   label. Inspect the Actions run, original baseline failure, draft diff, and CI.

The required bug-report form asks for a complete example, command, optional target
branch, expected and actual outcomes, and Lean/Z3 versions. Older issues with equivalent information
remain usable. The model must return `needs-information` if the report cannot be
meaningfully reproduced; a nonempty code block alone is not sufficient evidence.

The original regression and all new variants must pass. Full checks are run on
both the untouched base and the patched version. A failing full suite is clearly
flagged in the draft; equal nonzero exit codes do not prove that the failures are
the same. Maintainers must compare the diagnostics and fix new failures before
accepting the change. Infrastructure failures stop publication. A successful
baseline regression also stops publication because it does not demonstrate a fix.

Current GitHub token behavior can leave PR-triggered CI runs awaiting a maintainer's
**Approve workflows to run** action. Review the patch before approving those runs.
There is no live model/API test during installation or ordinary script unit tests.

## Original reproducer convention

For issue 413, the profile requires `Tests/FixedIssues/Issue413.lean`, an issue
reference, and `import Tests.FixedIssues.Issue413` in `Tests/FixedIssues.lean`.
The standalone original block is separated from broader tests:

```lean
import Tests.Utils

-- https://github.com/input-output-hk/Lean-blaster/issues/413
-- BEGIN ORIGINAL REPRODUCER
universe u v
#testOptimize [ "Issue413Original" ]
  (PUnit.unit.{max u v + 1} ≠ PUnit.unit.{max v u + 1}) ===> False
-- END ORIGINAL REPRODUCER

-- Broader cases belong below, including negative and inconclusive comparisons.
```

The runner prefixes the block with `original_prelude` from the trusted profile,
then runs it alone on base and patched code. Include its universe, namespace,
instance, and type declarations inside the block when needed. Do not refer to
helpers introduced by the fix or to declarations elsewhere in the test file.
For a false theorem such as #413, assert the correct falsification or tactic
rejection; do not commit an admitted false proof or the contradiction it enabled.

The input or claim from the issue must remain intact. A regression assertion can
adapt the harness to expect correct behavior. Review the baseline diagnostic:
an unrelated compilation error is not proof of the reported failure. A matching
compiler crash is valid evidence when the reported bug itself is a crash.

## Reuse in other repositories

The portable skill, runner, report schema, and reusable workflow initially live
in Lean-blaster. Each adopting repository needs:

- `.github/workflows/agent-fix.yml`: its small label/manual trigger calling the
  shared workflow.
- `.github/agent-fix/config.json`: its trusted setup/test commands, editable and
  production paths, source extensions, regression naming and import convention,
  standalone original markers/prelude/command, and small-fix limits.
- A setup script if its toolchain needs provisioning. Existing setup commands
  can be used instead. Lean/Z3 commands are specific to this repository.
- The API secret and PR-creation setting described above, plus an `agent:fix`
  label. Add a short `AGENTS.md` pointer if local developers should use the same
  process; a personal global instruction does not install a CI workflow.

Use the same reviewed **full commit SHA** for the workflow reference and the
`automation-ref` input. The reusable workflow explicitly checks out its own
helpers because `actions/checkout` otherwise retrieves the caller repository.
For example, replace the `uses` and `with` portion of the local caller job with:

```yaml
uses: input-output-hk/Lean-blaster/.github/workflows/agent-fix-run.yml@<reviewed-commit-sha>
with:
  issue-number: ${{ github.event.issue.number && format('{0}', github.event.issue.number) || inputs.issue-number }}
  automation-ref: <reviewed-commit-sha>
  target-branch: ${{ inputs.target-branch || '' }}
  model: ${{ vars.AGENT_FIX_MODEL || '' }}
secrets:
  OPENAI_API_KEY: ${{ secrets.OPENAI_API_KEY }}
```

Retain the caller's event filter and declared permissions. Do not simply copy a
Lean profile into Python, Rust, or other repositories: use the native regression
path, test runner, comment syntax, and setup. The regression command runs the
committed issue-specific file; the original command runs only its extracted
standalone block. Set both `umbrella_path` and `umbrella_import` to `null` for
runners that automatically discover tests; keep both configured for an import
graph or native test manifest. Test the profile before use.

One shared version can serve many repositories. Updating it is an explicit pin
update, not a silent change to every consumer. A dedicated automation repository
can host the same package later; update the explicit helper repository in the
shared workflow at that point. Organization `.github` defaults do not install
Actions workflows automatically into other repositories.

## Boundaries and recovery

The preflight job checks maintainer permissions and can post a missing-reproducer
or branch-selection diagnostic; it never executes target-branch code. The agent job has no repository write credentials. It uses the Codex action's
protected API proxy, `drop-sudo`, and workspace permission profile; Codex is its
last step. The final bounded JSON report contains the complete unified patch.
The validation job starts from the selected branch's clean pinned base and reruns the configured
commands without write credentials. The publisher starts from another clean base,
rechecks the issue fingerprint and label, applies the constrained patch as data,
and creates a draft without executing generated code or reported test commands.
These are validation checks for review, not a proof of generality or an adversarially
tamper-proof test sandbox. Human review and normal CI remain acceptance gates.

The initial Lean profile permits at most 12 regular `.lean` source files and 600
added/deleted lines. It rejects source deletions, executable/symlink/binary files,
hidden files, automation/configuration changes, missing regressions/imports, and
test-only fixes. New dependencies, toolchains, architecture, or broad refactors
need separate discussion. The final report is capped at 96 KiB, its patch at
64 KiB, and the issue snapshot at 32 KiB, measured as UTF-8 bytes.

Runs serialize per issue. Existing bot PRs are not overwritten, even if closed;
continue the existing work or deliberately remove the old branch/PR association
after review before starting a replacement. Pushes are never forced. If PR
creation fails after a branch push, a rerun can recover the same run's identical
tree; a different result stops instead of overwriting the branch. If an issue's
title/body changes or its triggering label is withdrawn before publication, the
run stops. Relabel after inspecting the new input. Cancel an ongoing run in Actions
to stop sooner.

Use a disposable GitHub-hosted runner. Do not put production secrets or a broad
write token in the agent or validation jobs. Failed setup, schema, patch, or
regression gates stay in Actions logs and produce no PR; successful non-fixed
model outcomes produce a diagnostic on the issue.

## Local validation of the bot

```sh
python3 -B -m unittest discover -s scripts -p 'test_agent_fix.py'
bash -n .github/agent-fix/setup.sh
actionlint .github/workflows/agent-fix.yml .github/workflows/agent-fix-run.yml .github/workflows/agent-fix-check.yml
git diff --check
```

These test the deterministic runner and workflow syntax. An end-to-end trial still
requires a configured API project, GitHub permissions, a merged workflow, and a
maintainer-selected issue. It consumes API and Actions usage.

References: [Codex GitHub Action](https://learn.chatgpt.com/docs/github-action),
[reusable GitHub workflows](https://docs.github.com/en/actions/how-tos/reuse-automations/reuse-workflows),
[GitHub token behavior](https://docs.github.com/en/actions/concepts/security/github_token).
