# Bandelt--Dress quartet project (v0.60)

This is a private research repository for the manuscript

> **A Split-Decomposition Approach to the Bandelt--Dress Quartet Distance Bound**
>
> Libo Huang and Stefan Grünewald

and its Lean 4/mathlib formalization companion.

## Repository layout

- `paper/` contains the authoritative v0.60 TeX source, compiled PDF,
  Appendix C source, and the two vector figures required for compilation.
- `formalization/` contains the self-contained Lean 4 project, including the
  exact vendored subset of the reference infrastructure used by the proof.
- `formalization/FORMALIZATION_MAP.md` maps the manuscript statements to Lean
  declarations.
- `formalization/QuartetV060/AxiomAudit.lean` records the final axiom audit.

The generated Lean build directory `.lake/` is intentionally excluded. It is
large, machine-specific, and recreated by `lake build`.

## Build the manuscript

```bash
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  quartet_submission_v0_60_explicit_appendix_a.tex
```

The repository already includes the compiled PDF:

```text
paper/quartet_submission_v0_60_explicit_appendix_a.pdf
```

## Build and audit the Lean project

Lean and mathlib versions are pinned by `formalization/lean-toolchain` and
`formalization/lake-manifest.json`.

```bash
cd formalization
lake build
lake env lean QuartetV060/AxiomAudit.lean
```

The first build downloads the pinned mathlib dependency and may require
substantial disk space. Build artifacts remain untracked under
`formalization/.lake/`.

## Scope and status

The manuscript and formalization should be read together with
`formalization/FORMALIZATION_MAP.md`. Appendix C is a reproducible numerical
illustration; its particular 25-leaf data and printed rational totals are not
separate Lean theorems.

This repository is private and contains an active research manuscript. No
permission for public redistribution is granted by its private availability.
The vendored third-party Lean modules retain their original MIT license; see
`formalization/THIRD_PARTY_NOTICES.md`.

## AI-assistance disclosure

The manuscript contains the full disclosure near its end. In brief, Section 5
and Lemmas A.4 and A.5 were developed with the assistance of GPT-5.6 Sol, and
Appendix C was produced entirely by GPT-5.6 Sol. The remaining content,
including equations (25)--(28) and the final expression in equation (A.30),
was developed jointly by Stefan Grünewald and Libo Huang and is also
documented in Huang's doctoral dissertation, made available through CNKI in
2018.
