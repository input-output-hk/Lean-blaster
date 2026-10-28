# FFM-19: deferred-M2 finite-field rule-audit bookmark

## Status and unchanged boundary

This is a source-linked handoff, **not a full rule audit or proof qualification**.
FFM-19 adds no M1 proof-production probes, CPC probes, proof traces, proof
binaries or Lean-checked FF-rule examples. Its algebraic normalization and
semantic corpus fixtures are not FF-rule examples. No external repository was
cloned or built for this bookmark.

[FFM-03](m1-solver-distribution-decision.md) selects upstream cvc5 1.3.4
GPL/CoCoA for M1 solving only and defers proof production to M2. Retain the
[FF-04 architecture](ff-04-reconstruction.md): local nominal modular arithmetic,
a selective core-only checked normalizer port, ordinary `decide`, and an
untrusted textual CPC reader whose accepted conclusions require kernel-checked
Lean proofs. This bookmark does not select Mathlib, Qq, lean-cvc5 FFI, Logos,
a native evaluator or a new field representation as a core dependency.
`blasterProven` and the settled trust boundary remain unchanged.

The existing FF-04 replay is **preserved historical evidence**, not a new
FFM-19 rule example: its fixed cvc5 1.4.1 text has explicit conclusions, and its
reader reproves those conclusions with isolated referenced premises and grind.
Printed rule names and trust labels carry no proof authority. That replay is
neither a general rule checker nor an implementation of the normalizer-first
production dispatcher. The [FFM-08 report](ffm-08-ticket-report.md) retains its
historical validation and timings; required PROJECT checks may recompile the
preserved tests, but FFM-19 does not regenerate the trace or add rule examples.

## Deferred fork identity, inherited from FFM-03

These are bookmarks, not newly acquired or requalified artifacts:

- Repository/release: [psaccomani15/cvc5, `clean-wip`](https://github.com/psaccomani15/cvc5/releases/tag/clean-wip).
- Executable version: `1.3.3.dev+clean_WIP@b1f8abb`.
- Reported source: `b1f8abb80021d687df7547fedc41882c4416d981`.
- Linux x86_64 archive: <https://github.com/psaccomani15/cvc5/releases/download/clean-wip/cvc5-Linux-x86_64-static.zip>.
- Archive SHA-256: `918361fcee2e1d3c64be5d20eb62156aaee73943df3ae7aa62d58f199b6785dc`.
- Executable member: `cvc5-Linux-x86_64-static/bin/cvc5`.
- Executable SHA-256: `514ccdaea9e4a5a0eb7d3be2e89b9d6fc893e3560d0f536cbe5e122ef6376a61`.

FFM-03 records the mutable release tag at
`f011843845a37ddeb555d04a8b07c68641810c52`, different from the executable's
reported source. The mismatch remains a provenance question for M2, not a
resolved source-to-binary mapping. Do not stage this fork, add a proof manifest,
or require it in M1 workers. Distribution approval, platform qualification and
proof-format qualification remain separate M2 decisions.

## Pinned source inventory

All links below identify source snapshots, not observed executable behavior:

- **Historical FF-04 report**, lean-blaster `724e32c377b5c6bfdecaf200984203b21c75355b`:
  [ff-04-reconstruction.md](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/docs/finite-fields/ff-04-reconstruction.md).
- **Selective normalizer port**, the same lean-blaster snapshot:
  [Blaster/FF04/Polynorm.lean](https://github.com/input-output-hk/lean-blaster/blob/724e32c377b5c6bfdecaf200984203b21c75355b/Blaster/FF04/Polynorm.lean).
- **Fork checker**, `b1f8abb80021d687df7547fedc41882c4416d981`:
  [src/theory/ff/proof_checker.cpp](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/src/theory/ff/proof_checker.cpp).
- **Fork printer**, the same fork snapshot:
  [src/proof/alf/alf_printer.cpp](https://github.com/psaccomani15/cvc5/blob/b1f8abb80021d687df7547fedc41882c4416d981/src/proof/alf/alf_printer.cpp).
- **lean-smt reconstruction**, `9b314968f6405395ecbc030c4d3f9b35e4974aa1`:
  [Smt/Reconstruct/ZMod.lean](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/Smt/Reconstruct/ZMod.lean).
- **lean-smt dependency identity**, the same lean-smt snapshot:
  [lake-manifest.json](https://github.com/ufmg-smite/lean-smt/blob/9b314968f6405395ecbc030c4d3f9b35e4974aa1/lake-manifest.json).
  This pins Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` (input tag
  `v4.32.0`) and lean-cvc5 `4733baf0722c870a5a449f132afa690947e00e2a`;
  it does not make them local dependencies.
- **Upstream cvc5 1.4.2**, `282d5e0c84baf49c780704c532f87ba66d8b513d`:
  [src/theory/ff/theory_ff.cpp](https://github.com/cvc5/cvc5/blob/282d5e0c84baf49c780704c532f87ba66d8b513d/src/theory/ff/theory_ff.cpp).

At the pinned fork, FF checks are **partially structural**, not a complete
semantic certificate checker: several branches construct conclusions from
arguments and shape checks. The printer's handled-rule list establishes printing
support, not soundness or Lean coverage. In the pinned upstream 1.4.2 source,
`TheoryFiniteFields::getProofChecker()` returns `nullptr`: there is no FF theory
proof checker there. Neither fact licenses trusting solver results or transferring
fork capabilities to the approved M1 solving binaries.

## Exact local normalization boundary

In namespace `Blaster.FF04.Polynorm`, `Context R := Nat → R` and `Expr R`
contains `val`, `var`, `neg`, `add`, `sub`, `mul` and natural-exponent `pow`.
The [local implementation](../../Blaster/FF04/Polynorm.lean) supplies these
interfaces, with `{R : Type u}`, `[Lean.Grind.CommRing R]`, `[DecidableEq R]`
and `ctx : Context R`:

```lean
Expr.eval_toPolynomial {e : Expr R} :
  Expr.eval ctx e = (Expr.toPolynomial e).denote ctx

Expr.denote_eq_from_toPolynomial_eq {e₁ e₂ : Expr R}
    (h : e₁.toPolynomial = e₂.toPolynomial) :
  e₁.eval ctx = e₂.eval ctx
```

Ordinary `decide` can discharge the normal-form equality premise for closed
reflected expressions; the second theorem then transports that equality to
expression evaluation. It does not prove the premise by itself, certify a
solver rule or infer field semantics. The current `Blaster.FiniteField.Residue p`
supplies the nominal coefficient ring under `[NeZero p]` (the historical
`Blaster.FF04.Residue` spelling forwards to it); ring identities do not require
primality. Equality of normal forms is sufficient, not a completeness result:
the preserved composite-ring zero-coefficient limitation is documented in FF-04.

There is no automatic local reifier connecting arbitrary Lean expressions or
solver terms to this grammar. Explicit reflected expressions and their contexts
are supplied by the corpus. Checked variable/context correspondence, coefficient
and modulus interpretation, reconstruction of premises, and transport through
optimizer rewrites to the original goal remain integration gaps. The narrow
historical CPC reader does not fill these gaps for a general dispatcher.

The pinned lean-smt entrypoint is a reference, not an imported implementation.
Its Qq/Mathlib reifiers and ideal/variety machinery require separate adaptation;
its optional native paths include `Meta.nativeEqTrue`. **All
`nativeEqTrue`-dependent paths, including native normalization and native root
completeness decisions, are excluded** from the retained local ordinary-decide
architecture. No new axiom, admission or native-decision trust is authorized.

## Unresolved M2 handoff questions

These are questions to carry forward, not conclusions of an audit or analyses
completed by FFM-19:

| Area | Obligation to resolve in M2 |
| --- | --- |
| `FF_POLY_NORM_EQ` | How are both scaling coefficients proved nonzero, with checked field/primality assumptions and exact premise/conclusion correspondence, before cancellation justifies equivalence of equations? |
| `FF_DISEQ` | What is the witness/Skolem semantics for `(l - r) * w = 1`, and how is the chosen witness connected to the disequality? An arbitrary free witness is not the same contract as the lean-smt choice-based reconstruction. |
| `FF_ROOT_BRANCH` | How are univariate scope, polynomial ideal membership and completeness of the supplied root list certified, rather than merely checking listed roots or accepting a printed branch list? What ordinary checked procedure and resource bound are appropriate? |
| Ideal membership and contradiction | What checked certificate connects generators, polynomial combinations and their coefficients to membership, field polynomials, variety preservation and `1`-membership contradiction? How are all referenced premises and reified variables tied to the original problem? |
| Finite-field exhaustion | How are the finite domain, complete enumeration, branch coverage, field assumptions and empty/nonempty variety semantics justified? What scalable alternative or explicit supported limit applies when full-domain enumeration is impractical? |

Finite-domain completeness, ideal/variety reconstruction and exhaustion costs
remain unresolved handoff items. Normalization measurements do not answer them.
No rule-coverage matrix, successful probe, Lean-checked FF-rule example or full
rule audit is claimed by this bookmark.
