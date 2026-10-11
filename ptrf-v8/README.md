# A Sum-of-Squares Decomposition for Quartet Covariance

**Full title:** *A Sum-of-Squares Decomposition for Quartet Covariance: Bivariate Independence and Quartet Distance*  
**Authors:** Stefan Grünewald and Libo Huang

This directory preserves the PTRF-targeted v8 manuscript and its matched Lean 4 supplementary material. The source snapshot includes the zero-mass-cell copyedit dated 5 September 2026. It is distinct from the older v0.60 manuscript in `../paper/` and formalization in `../formalization/`, which remain unchanged.

Publication here does not assert journal acceptance or verify the current status of any journal submission.

## Read and download

| File | Contents |
|---|---|
| [Grunewald_Huang_PTRF_v8.pdf](Grunewald_Huang_PTRF_v8.pdf) | The 27-page manuscript |
| [Grunewald_Huang_PTRF_v8.tex](Grunewald_Huang_PTRF_v8.tex) | Manuscript LaTeX source |
| [Grunewald_Huang_PTRF_v8_References.bib](Grunewald_Huang_PTRF_v8_References.bib) | Bibliography |
| [Grunewald_Huang_PTRF_v8_Source.zip](Grunewald_Huang_PTRF_v8_Source.zip) | Complete manuscript source package, including class and bibliography-style inputs |
| [ESM_1.zip](ESM_1.zip) | Matched source-only Lean supplement: 142 Lean files, pinned dependencies, correspondence tables, audit records, and licence notices |
| [PTRF_v8_ALIGNMENT_DELIVERY_MANIFEST.txt](PTRF_v8_ALIGNMENT_DELIVERY_MANIFEST.txt) | Preserved version and historical verification record |
| [SHA256SUMS](SHA256SUMS) | Checksums of the files in this directory, except this checksum list itself |

The original six files were copied without changing their bytes. Before this upload, their recorded hashes, the manuscript hashes in the Lean package's `MANUSCRIPT_LOCK.md`, and all 156 entries in the supplement's internal `SHA256SUMS` were checked. This upload does **not** claim a fresh Lean build or a new mathematical review; historical build and audit records remain inside the supplement.

## Reproduce the Lean checks

Unpack `ESM_1.zip` and enter `Grunewald_Huang_PTRF_v8_Lean4_Supplement`. Follow its `README.md`, including the pinned Lean/mathlib versions:

```sh
lake exe cache get
lake build
lake env lean BernoulliSupplementAudit.lean
```

See `THEOREM_CORRESPONDENCE.md` for the manuscript-to-Lean map and `MANUSCRIPT_LOCK.md` for the exact manuscript snapshot. Generated `.lake` caches are not included.

## Rights and scope

The manuscript retains its authors' copyright; uploading it here does not apply the Lean code's MIT licence to the paper. The author-written Lean files use the MIT licence included in `ESM_1.zip`, with separate notices for vendored third-party files. The manuscript source package retains the publisher-supplied template's own notices.

The manuscript's author names, affiliations, and author-contact details are retained as part of the unchanged scholarly manuscript. Submission cover letters, private correspondence, earlier backups, and machine-specific build caches are not included.
