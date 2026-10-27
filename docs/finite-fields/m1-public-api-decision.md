# FFM-06: Public residue namespace and exports

## Decision and approval boundary

Select **`Blaster.FiniteField.Residue (p : Nat)`** as the public nominal carrier
and **`Blaster.FiniteField.PrimeModulus p`** as the public primality-evidence
name. Select **re-export through `import Blaster`**, with
`import Blaster.FiniteField` available as the algebra-only umbrella and narrower
imports below. This is a concrete API selection, not an explicit-import-only
policy or a choice left to the implementation ticket.

The plan requests maintainer confirmation of the public name. **That confirmation
is outstanding; this job does not claim it.** The selected namespace and export
policy are recorded together for that confirmation. A different name or an
explicit-import-only policy requires an explicit revision of this record, not a
silent change during implementation. Final approval and merging remain with the
maintainer under the [M1 execution contract](m1-execution-decision.md).

This decision changes documentation only. None of the proposed modules, aliases,
prime evidence or field operations is implemented by this ticket. The nominal
representation, one-carrier architecture and ring/prime-field split are retained,
not reopened.

## Inspected baseline and rationale

- The local `Blaster.lean` imports `Blaster.Command`, `Blaster.Logging`,
  `Blaster.Optimize`, `Blaster.Smt` and `Blaster.StateMachine`. It currently has
  no finite-field import. The public
  [base entry point](https://github.com/input-output-hk/lean-blaster/blob/a69c5c266864a90064884519a5d208f5321cf379/Blaster.lean)
  identifies the pinned reference; the import observation is from the local file.
- The local `Makefile` and `scripts/check_lean_project_compilation.sh` require
  every source module under `Blaster/` to appear in a clean root-library build.
  Re-exporting the algebra umbrella from the root fits that existing convention
  without a new build target, coverage exclusion or protected-file edit.
- The pinned public
  [FF-04 nominal source](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/Blaster/FF04/Nominal.lean)
  defines `Blaster.FF04.Residue p` as a structure with `rep : Fin p`, deriving
  `DecidableEq` and `Repr`. Under `[NeZero p]` it supplies modular operations,
  `Lean.Grind.CommRing` and `Lean.Grind.IsCharP`, but no inverse or division.
- The pinned
  [FF-04 reconstruction record](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/docs/finite-fields/ff-04-reconstruction.md)
  retains a nominal ring and separately checked primality for field reasoning.
  Its experiment and timings are historical evidence, not results rerun here.
  `Blaster/FF04/` is absent from this checkout; those public files were read over
  HTTPS, not imported, merged or compiled.

The tradeoff is that the main import gains the algebra declarations and their
conditional instances. Users needing only modular-ring algebra can avoid the
command/solver import graph through the narrower imports. Importing algebra must
not execute a solver, select native FF mode, load a prime registry, or register
the FF-04 replay experiment. No new external package is selected.

## Intended public modules and export policy

Paths and names below are the intended implementation contract, not existing
files. A Lean import makes declarations and instances available; it does not
open their namespace or create shortened aliases.

| Module / intended source path | Public surface and import contract |
| --- | --- |
| `Blaster.FiniteField.Residue` / `Blaster/FiniteField/Residue.lean` | Defines the sole nominal `Blaster.FiniteField.Residue p`, its representation interface and lawful modular-ring instances. No dependency on the prime or field layer. FFM-11 owns implementation. |
| `Blaster.FiniteField.PrimeModulus` / `Blaster/FiniteField/PrimeModulus.lean` | Defines the proposition-valued evidence class `Blaster.FiniteField.PrimeModulus p` and proved consequences, including `NeZero p`. No inverse/division or dependency on the field layer. FFM-12 owns the precise predicate, proof interface and admission. |
| `Blaster.FiniteField.Field` / `Blaster/FiniteField/Field.lean` | Imports the residue and prime-evidence modules; supplies inverse, division and the lawful `Lean.Grind.Field` instance on the same `Residue p`, conditional on `[PrimeModulus p]`. FFM-17 owns implementation and proofs. No second carrier named `Field`. |
| `Blaster.FiniteField` / `Blaster/FiniteField.lean` | Algebra umbrella importing `Residue` and `PrimeModulus`, and `Field` when FFM-17 implements it. Does not import solver adapters, certificate corpora or experimental replay commands. |
| `Blaster` / `Blaster.lean` | Adds an import of `Blaster.FiniteField` when the public modules are implemented, retaining all existing imports. Re-exports the umbrella's declarations and conditional instances transitively. |

Do not create empty placeholder modules to satisfy this table before their owning
tickets. The umbrella grows only when the corresponding implementation lands.
The chosen export policy already covers the later field layer: adding it does
not authorize unconditional field instances.

Public declarations stay under `Blaster.FiniteField`, with residue-specific
operations and lemmas under `Blaster.FiniteField.Residue`. Do not add global
`Residue`, `Blaster.Residue` or global `PrimeModulus` aliases. Users may write
fully qualified names, or explicitly `open Blaster.FiniteField` in their own
module. Importing `Blaster` does not implicitly open that namespace.

### Access to PrimeModulus evidence

After FFM-12, `import Blaster`, `import Blaster.FiniteField`, or the narrow
`import Blaster.FiniteField.PrimeModulus` makes the evidence interface available.
Importing only `Blaster.FiniteField.Residue` deliberately does not supply it.
Generic prime-field clients bind `[Blaster.FiniteField.PrimeModulus p]`. A client
with a checked proof `h : Blaster.FiniteField.PrimeModulus p` can install it
locally using `letI : Blaster.FiniteField.PrimeModulus p := h`; it need not import
or enable a solver to use that evidence.

The class must certify mathematical primality of the exact modulus, not merely
nonzeroness, a Boolean answer or an assumed field-law dictionary. Its constructor
and proof fields remain FFM-12 work, consistent with the
[large-prime proof-source decision](m1-large-prime-decision.md). That decision's
Curve25519 proof must be transported into this evidence interface by checked
Lean proofs. This record does not invent an already available fixture theorem
name, automatic prime search, or a populated global instance registry.

## One carrier and the ring/field boundary

- Define the nominal structure once, in the public residue module, retaining
  `rep : Fin p`. `Residue p` is not an abbreviation for `Fin p` or a new type
  selected by whether a primality instance is in scope. Its type parameter is
  only `p`; evidence is required by operations and laws, not part of its identity.
- Preserve numerals, natural/integer casts, addition, multiplication, negation,
  subtraction, natural powers and the lawful ring/characteristic instances under
  `[NeZero p]`. Composite nonzero moduli remain valid rings. Modulus one is the
  zero ring, not a prime field; modulus zero has no `NeZero` ring API. Equality
  and representation facts that need no nonzero assumption stay independent.
- Only proved `[PrimeModulus p]` enables `Inv`, `Div` and `Lean.Grind.Field` on
  `Residue p`. Prove the implication to `NeZero p` once in the evidence layer;
  reuse the ring instances rather than defining competing prime-only ring
  operations. Field division must never be inherited from truncating `Fin.div`.
- Importing the field module alone supplies conditional declarations, not a
  proof that any particular modulus is prime. Neither a numeric modulus cache,
  an SMT finite-field sort declaration nor native solving supplies that proof.
  A composite modulus must not acquire field instances through any import route.
- General ring algebra with symbolic `p` does not promise symbolic-modulus SMT
  admission. Opaque recognition and prime admission remain separate FFM-11 and
  FFM-12 work. No reconstruction guarantee, trusted-mode axiom or widening of
  `blasterProven` is authorized by the public exports.

## FF-04 compatibility and migration

Retain the compatibility module **`Blaster.FF04.Nominal`** at
`Blaster/FF04/Nominal.lean` when the experiment is brought forward. It imports
`Blaster.FiniteField.Residue` and exposes **`Blaster.FF04.Residue` as a reducible
alias of `Blaster.FiniteField.Residue`**, not another structure, wrapper or
coercion bridge. The original experimental structure declaration and duplicated
ring instances must be replaced, not kept alongside the public declaration.

Keep the experiment's representation-facing spellings
`Blaster.FF04.Residue.mk`, `Blaster.FF04.Residue.rep`,
`Blaster.FF04.Residue.ext` and `Blaster.FF04.Residue.mk.injEq` as forwarding
aliases/theorems to the corresponding public declarations if used by retained
experiment sources. Do not assume a type abbreviation automatically creates
all of Lean's old qualified constructor/projection/theorem names. Do not
re-register ring instances or copy their proofs under the old namespace.
Generated instance names are not a supported compatibility API; migrate such
references to inference or the public declarations.

Migrate retained FF-04 implementation callers to the canonical public carrier
and its declarations. In particular, audit nominal-type recognition in replay
and reification: it must recognize the canonical declaration after reducing the
compatibility alias, not retain a second nominal-type key. The compatibility
module preserves old experiment imports and source-level carrier use; compiled
artifacts must be rebuilt. It does not promise binary compatibility or complete
support for every generated name.

Keep experimental replay explicitly imported, not part of the algebra umbrella.
If compatibility sources are restored under `Blaster/`, make the compatibility
module reachable from the library root for existing source coverage, without
introducing a dependency from the public residue module back to FF-04. Bringing
forward the rest of the experiment and its build registration is separate work;
this record does not copy it or change the coverage runner. The compatibility
alias is the ticket's explicit exception to clean-cutover removal of old names;
there is no second carrier and no removal date selected here.

## Implementation acceptance handoff

FFM-11 must exercise both public import routes and the narrow ring import;
check lawful operations for a composite modulus; and, when compatibility is
brought forward, check that old/new carrier values interoperate by definitional
equality without casts. Check old qualified representation names used by the
experiment and run the migrated replay/normalizer, not just an alias smoke test.
FFM-12 must check exact-subject primality evidence and its `NeZero` consequence.
FFM-17 must check field inference with that evidence and failure of inverse,
division and field inference with only `NeZero`, including a composite example.
These are future implementation checks, not claims of execution in this job.

## FFM-06 ticket report and job summary

Change: add this decision record only. It selects the public namespace,
main-import re-export policy, narrow imports, primality-evidence access and
same-carrier FF-04 compatibility contract. No production implementation,
protected files, test outcomes, build declarations, dependency pins or solver
configuration are changed. This section is the ticket report and job summary
retained in the stack's commit; publication and maintainer signoff are not claimed.

### Validation

Executed on 2026-10-27 from the repository root, with the two PROJECT checks
run serially. Wall times below include the complete shell command.

| Exact command | Observed outcome |
| --- | --- |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_blaster` | Pass, exit 0; `/opt/z3-4.15.2-arm64-glibc-2.34/bin/z3`, Z3 4.15.2; clean compilation and source coverage, 171 jobs; 90.35 seconds. |
| `PATH="$(dirname "$(readlink -f /usr/local/bin/z3-4.15.2)"):/home/agent/.elan/bin:/usr/bin:/bin"; command -v z3 && z3 --version && make check_tests` | Pass, exit 0; same Z3 4.15.2; pure tier 200 jobs, Z3 tier 611 jobs; 172.64 seconds. Lifecycle tests emitted model-response diagnostic warnings; both tiers completed successfully. |
| `test -s docs/finite-fields/m1-public-api-decision.md` | Pass, exit 0; decision artifact is nonempty. |
| `git diff --check` | Pass, exit 0; no whitespace errors in tracked changes. |
| `git diff --no-index --check /dev/null docs/finite-fields/m1-public-api-decision.md` | Exit 1 with no whitespace diagnostics: the new document differs from `/dev/null`. This additionally inspects the file before staging; it is not a failing PROJECT gate. |

The requested name/layering search was performed with the repository search
tool instead of shell `rg`, using exactly these arguments:

```json
{"pattern":"Blaster\\.FiniteField|Residue|PrimeModulus","path":"docs/finite-fields/m1-public-api-decision.md","case":true,"gitignore":true}
```

Outcome: matches in the selected names, module table, evidence-access contract,
ring/field boundary and compatibility strategy. This is the content-search
equivalent of the ticket's `rg -n` check; no shell `rg` run is claimed. Manual
inspection of the cited prototype and current entry point informed the decision.
There is no changed runtime surface to smoke-test in this documentation-only job.

### Remaining work and limitations

- Maintainer confirmation of `Blaster.FiniteField.Residue` and the selected
  main-import export policy remains outstanding. No approval is inferred from
  the assignment or from successful PROJECT checks.
- FFM-11, FFM-12 and FFM-17 own the implementation and behavioral checks above.
  No proposed public import, compatibility alias, primality proof or field
  instance was compiled by this decision ticket.
- The FF-04 sources were inspected at the pinned public revision only; no
  experiment replay or historical timing was rerun. PROJECT checks validate the
  unchanged current library and pure/Z3 tiers, not future FF behavior or cvc5
  native solving. No default-environment `lake test` is used.
- `git diff --cached --check` also passed after staging the new document.
  The optional local command
  `git commit -m "Record finite-field public API decision" -- docs/finite-fields/m1-public-api-decision.md`
  exited 128 because Git author identity is not configured. No identity was
  invented or configured. The validated artifact is supplied for the stack's
  owner-attributed commit; no local commit or remote publication is claimed.
