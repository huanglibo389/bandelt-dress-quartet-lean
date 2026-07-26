# Manuscript files

The authoritative v0.60 manuscript is:

- `quartet_submission_v0_60_explicit_appendix_a.tex`
- `quartet_submission_v0_60_explicit_appendix_a.pdf`

The main TeX source additionally requires:

- `appendix_c_general_binary_v060.tex`
- `local_four_sector_vector.pdf`
- `bridge_three_block_symmetry_vector.pdf`

Compile from this directory with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  quartet_submission_v0_60_explicit_appendix_a.tex
```

Integrity values for the uploaded snapshot:

```text
TeX  SHA-256  17310279b78db47b52c94041b187586e37811bc2ff962d7b085402ea652ec980
PDF  SHA-256  f4db706d13e383a53e62b4207c4375088e87cba5189c8aeec22912fddbf79856
```

