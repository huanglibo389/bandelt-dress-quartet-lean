# Vendored dependency boundary

The project is self-contained apart from Lean 4 and mathlib.  It no longer
requires a sibling `quartet_lean_reference` directory.

## Why these ten modules are included

The local proof directly imports:

```text
QuartetDistance.GraphQuartet
QuartetDistance.TiedSampleCount
QuartetDistance.Upper
QuartetDistance.Lower
QuartetDistance.Maximum
```

Their internal imports add:

```text
QuartetDistance.Arithmetic
QuartetDistance.Circular
QuartetDistance.Counting
QuartetDistance.Tree
QuartetDistance.TreeAdequacy
```

The union is the minimal transitive module closure.  In graph form:

```text
GraphQuartet -> TreeAdequacy -> Tree -> Circular -> Mathlib
TiedSampleCount ---------------------> Circular -> Mathlib
Lower -> Upper -> Arithmetic --------------------> Mathlib
               -> Circular ----------------------> Mathlib
               -> Counting ----------------------> Mathlib
               -> Tree -> Circular --------------> Mathlib
Maximum -----------------------------------------> Mathlib
```

## Independence check

The package declaration in `lakefile.toml` now requires only mathlib:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.32.0"
```

There is no `path = "../quartet_lean_reference"` entry.  Therefore moving or
deleting the former sibling reference checkout cannot affect compilation.

## Provenance

The copied files come from upstream commit
`e0bcc79c179a571c9b3f6485eb666a790c73c228`.  See
`THIRD_PARTY_NOTICES.md` and
`third_party/quartet_distance_bandelt_dress/LICENSE`.
