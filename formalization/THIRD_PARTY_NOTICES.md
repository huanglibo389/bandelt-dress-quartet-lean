# Third-party notices

## `quartet_distance_bandelt_dress`

This project vendors the following Lean modules from
[`rvazdev-ex/quartet_distance_bandelt_dress`](https://github.com/rvazdev-ex/quartet_distance_bandelt_dress):

- `QuartetDistance/Arithmetic.lean`
- `QuartetDistance/Circular.lean`
- `QuartetDistance/Counting.lean`
- `QuartetDistance/Tree.lean`
- `QuartetDistance/TreeAdequacy.lean`
- `QuartetDistance/GraphQuartet.lean`
- `QuartetDistance/TiedSampleCount.lean`
- `QuartetDistance/Upper.lean`
- `QuartetDistance/Lower.lean`
- `QuartetDistance/Maximum.lean`

They are the complete transitive closure of the reference modules imported by
the v0.60 formalization.  No other source file from that repository is needed
to build this project.

- Upstream commit:
  `e0bcc79c179a571c9b3f6485eb666a790c73c228`
- Upstream copyright:
  Copyright (c) 2026 Ricardo Valencia Albornoz
- License: MIT
- Full license text:
  `third_party/quartet_distance_bandelt_dress/LICENSE`

The vendored source files are preserved byte-for-byte from the recorded
upstream commit.  The local root file `QuartetDistance.lean` is only an import
index for this selected module set.
