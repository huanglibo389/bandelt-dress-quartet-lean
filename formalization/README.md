# Lean 4 formalization of the v0.60 bridge-ledger proof

This project gives a kernel-checked Lean 4 formalization of the theorem chain
used in the v0.60 manuscript:

1. the finite split and adjacent-correction functional `f₁`;
2. the Appendix A principal-chart, bridge-reversal, source-settlement, and
   four-family decomposition;
3. the exact formula (A.30) and the proof that all four families are
   nonnegative;
4. the ordered-quadruple kernel identity, the exact finite counting identity,
   and the explicit repeated-tuple error;
5. the normalized `2/3 + o(1)` upper bound and the matching sharp asymptotic
   value;
6. the logically independent Appendix B distance-covariance identity.

The final theorem chain does **not** invoke the alternative permuton proof.
It reuses finite-tree, quartet-split, graph, random-relabeling, and
maximum-statistic infrastructure from
`rvazdev-ex/quartet_distance_bandelt_dress`.  The exact ten-module transitive
subset used by this proof is vendored under `QuartetDistance/`, so the project
no longer depends on a sibling checkout.  Its provenance and MIT license are
recorded in `VENDORED_MODULES.md` and `THIRD_PARTY_NOTICES.md`.

## Authoritative manuscript snapshot

- TeX:
  `../paper/quartet_submission_v0_60_explicit_appendix_a.tex`
- TeX SHA-256:
  `17310279b78db47b52c94041b187586e37811bc2ff962d7b085402ea652ec980`
- PDF:
  `../paper/quartet_submission_v0_60_explicit_appendix_a.pdf`
- PDF SHA-256:
  `f4db706d13e383a53e62b4207c4375088e87cba5189c8aeec22912fddbf79856`
- reference infrastructure commit:
  `e0bcc79c179a571c9b3f6485eb666a790c73c228`

## Versions

- Lean: `4.32.0`
- mathlib: `v4.32.0`
- pinned mathlib commit:
  `81a5d257c8e410db227a6665ed08f64fea08e997`

## Main checked declarations

```text
QuartetV060.ConcreteFourFamilies.auxiliaryFunctional_real_eq_scaledLedger
QuartetV060.ConcreteFourFamilies.auxiliaryFunctional_nonnegative
QuartetV060.DistinctTupleCounting.auxiliaryFunctional_counting_identity
QuartetV060.MainTheorem.normalized_bounds
QuartetV060.Sharpness.normalizedMaximum_tendsto_two_thirds
QuartetV060.DistanceCovariance.splitSystemDistanceCovariance_eq_detSquare
QuartetV060.DistanceCovariance.splitSystemDistanceCovariance_nonnegative
```

The first declaration is the concrete Lean counterpart of (A.30): `f₁`
equals the sum of the four square families with coefficients
`1/4, 1/2, 1/2, 1`.  The second proves `f₁ ≥ 0`.  The next three connect this
Appendix A result to the finite quartet count and the sharp asymptotic
theorem.  The final two formalize Appendix B.

## Build and audit

From this directory:

```bash
lake build
lake env lean QuartetV060/AxiomAudit.lean
```

The only external package dependency is the pinned mathlib release.  The
former `../quartet_lean_reference` path is not required.

The audit file prints the axioms of the final Appendix A theorem, normalized
main theorem, sharp asymptotic theorem, and Appendix B theorem.  At the
recorded snapshot, each depends only on Lean's standard logical axioms:

```text
propext
Classical.choice
Quot.sound
```

There are no occurrences of `sorry`, `admit`, custom `axiom` declarations,
`opaque`, `unsafe`, or `native_decide` in `QuartetV060/` or
`QuartetV060.lean`.  The finite 24-permutation Gram calculation is proved by
an explicit six-pair fiber count in `QuartetTopologyCounting.lean`; it is not
delegated to native code execution.

## Scope

The theorem required for the Bandelt--Dress conjecture is formalized for
binary leaf-labelled phylogenetic trees, exactly the setting of the
manuscript's main result.  Several early algebra modules are more abstract,
but the final Appendix A instantiation uses that binary tree model.

Appendix C is a reproducible numerical illustration, not a logical input to
the theorem.  Its general identities are covered by the proved definitions
and theorems above; the manuscript's particular 25-leaf Newick data and
printed rational totals have not been promoted to separate Lean theorems.
That distinction is recorded in `FORMALIZATION_MAP.md`.
