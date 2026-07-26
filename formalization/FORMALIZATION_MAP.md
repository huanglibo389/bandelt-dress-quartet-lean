# v0.60 paper-to-Lean coverage map

## Status vocabulary

- **proved**: a compiled Lean theorem proves the indicated claim.
- **proved in the theorem specialization**: the claim is proved for binary
  leaf-labelled phylogenetic trees, which is the domain of the main theorem;
  the manuscript's broader expository `X`-tree formulation is not separately
  encoded as a graph structure.
- **computational illustration**: not used in the proof; the general identity
  is proved, but the particular printed data set is not a separate Lean
  theorem.

Passing `lake build` certifies only the Lean declarations.  The separate
axiom audit and placeholder scan are also required.

## Main body and finite counting

| Paper component | Lean module and principal declaration | Status |
|---|---|---|
| Normalized finite masses and complement partitions | `Basic.normalizedCard_inter_add_inter_compl`, `Basic.normalizedCard_add_compl` | proved |
| Normalized `2 × 2` split table and determinant square | `Determinant.Table2`, `Table2.centeredCovariance_eq_det` | proved |
| Row/column reversal and transpose invariance | `Table2.detSquare_reverseRows`, `detSquare_reverseCols`, `detSquare_transpose` | proved |
| Adjacent side-pair contrast | `SidePairData.rawContrast_sq_eq_neighboringContrast_sq` | proved |
| Binary leaf-labelled tree and displayed quartet infrastructure | vendored `QuartetDistance.Tree`, `GraphQuartet`, `Upper` plus local `PhyloOccurrences` | proved |
| Relevant edges and ordered adjacent corrections | `PhyloOccurrences.RelevantEdge`, `AdjacentCorrection`, `correctionSystem` | proved in the theorem specialization |
| Four ordinary/corrected levels defining `f₁` | `Auxiliary.auxiliaryFunctional` | proved |
| Full-domain adjacent-correction indicator | `PositionalIndicator.adjacent_indicator`, `adjacent_indicator_complements`, and `PhyloOccurrences.corrected_indicator_eq_product` | proved |
| Kernel expansion of `f₁` | `CorrectionKernel.auxiliaryFunctional_kernel_identity` and `DistinctTupleCounting.auxiliaryFunctional_eq_allKernelSum` | proved |
| Kernel-to-path identity | `TreeKernel.kernel_eq_pathWeight_sub_pathWeight` | proved |
| Path-weight range, including repeated labels | `ActivePathGeometry.pathWeight_eq_zero_or_one`, `RepeatedPathGeometry.pathWeight_eq_zero_or_one_full` | proved |
| Quartet-topology local Gram table | `QuartetTopologyCounting.localKernel_product_sum`, `localKernel_same_sum`, `localKernel_diff_sum` | proved |
| Exact distinct/repeated tuple split | `DistinctTupleCounting.allKernelSum_eq_distinct_add_repeated` | proved |
| Explicit collision polynomial and remainder bound | `collision_count_polynomial`, `abs_repeatedRemainder_le` | proved |
| Exact counting identity | `DistinctTupleCounting.auxiliaryFunctional_counting_identity` | proved |
| Finite same-quartet lower bound | `MainTheorem.sameCount_lower_bound` | proved |
| Finite quartet-distance upper bound | `MainTheorem.diffCount_upper_bound` | proved |
| Normalized main theorem | `MainTheorem.normalized_bounds` | proved |
| Random-relabeling lower bound and actual maximum | `Sharpness.maximumDistance_lower_bound`, `exists_maximizing_trees` | proved |
| Sharp asymptotic value `M_n / C(n,4) → 2/3` | `Sharpness.normalizedMaximum_tendsto_two_thirds` | proved |

## Appendix A: bridge-ledger closure

| Paper component | Lean module and principal declaration | Status |
|---|---|---|
| Four sectors `a,b,c,d`, relation classes, and finite partitions | `FourSector`, `ResidualPartition` | proved |
| Principal atoms and branch-to-atom correspondence | `PrincipalBranches`, `PrincipalAtoms` | proved in the theorem specialization |
| Principal charts and local joint masses | `PrincipalChart`, `ConcreteDeterminantLevels` | proved in the theorem specialization |
| Local `r,c,a,x` masses and centered identities | `LocalTable`, `LocalCoordinates` | proved |
| Symmetric coefficient expansion and domination inequality | `LocalTable.domination_expansion`, `domination_inequality` | proved |
| Weighted centered cancellation and two-sided determinant algebra | `WeightedCancellation`, `Determinant` | proved |
| One-coordinate residual partition identity | `ResidualPartition.residual_square_algebra`, `exact_residual_identity`, and supporting partition lemmas | proved |
| Retained and omitted square forms (A.15a/A.15b) | `ConcreteRetainedSquares.A15a`, `A15b` | proved |
| Retained square expansions (A.17/A.18) | `ConcreteRetainedSquares.A17`, `A18` | proved |
| Ordered three-block bridge chart and reversal `(K,H,L) ↦ (L,H,K)` | `BridgeReversal`, `PhyloBridgeReversal` | proved |
| Concrete endpoint coefficient transport under reversal | `ConcreteBridgeLedger.endpointData_reverse`, `package_second_eq_reversed_first`, `sum_package_second_eq_first` | proved |
| Bridge-orbit boundary cancellation | `ConcreteBridgeLedger.boundaryContribution_reverse`, `sum_boundaryContribution_eq_zero` | proved |
| Seven-source activation/regrouping | `SevenSource.fourLevel_eq_sevenSource`, `fourLevel_eq_two_occurrences` | proved |
| Occurrence crosswalk and multiplicity-one source sums | `ConcreteOccurrenceSettlement.sigmaCorrectionsEquiv`, `sum_corrections_by_source` | proved |
| Corrected/ordinary row-boundary cancellation | `sum_ordinary_boundary_eq_zero`, `sum_corrected_boundary_eq_zero` | proved |
| Concrete row settlement | `ConcreteRowSettlement.global_fourLevel_eq_directRow` | proved |
| Completed-square packages and face coefficients | `CompletedSquares`, `ConcretePackageSettlement` | proved |
| Global first/second-face reindexing and cancellation | `ConcreteGlobalPackage.global_endpoint_face_cancellation_I`, `global_endpoint_face_cancellation_D` | proved |
| Global package ledgers | `ConcreteGlobalPackage.global_package_ledger_I`, `global_package_ledger_D` | proved |
| Blockwise identity (A.30b) | `ConcreteBlockwisePsi.chart_two_block_settlement`, `global_row_I_ledger`, `global_row_D_ledger` | proved |
| Remaining coefficient `Ψ` and (A.32) | `ConcreteBlockwisePsi.endpoint_core_nonnegative`, `residual_core_nonnegative`, `psi_nonnegative` | proved |
| Four square families `S₁,S₂,S₃,S₄` | `ConcreteFourFamilies.S1` through `S4` | proved |
| Exact unscaled ledger (A.29h) | `ConcreteFourFamilies.four_mul_auxiliaryFunctional_real_eq_rawLedger` | proved |
| Exact four-family formula (A.30) | `ConcreteFourFamilies.auxiliaryFunctional_real_eq_scaledLedger` | proved |
| Nonnegativity of each family and of `f₁` | `S1_nonnegative` through `S4_nonnegative`, `auxiliaryFunctional_nonnegative` | proved |

The concrete Appendix A chain is a chart- and occurrence-indexed proof for
the binary leaf-labelled tree model used by the theorem.  The generic algebra
files isolate many identities over arbitrary finite types; there is no
separate Lean graph type representing every reduced vertex-labelled
`X`-tree from the manuscript's expository preliminaries.

## Appendix B

| Paper component | Lean declaration | Status |
|---|---|---|
| Empirical mean and centered split indicator | `DistanceCovariance.empiricalMean`, `centeredIndicator` | proved |
| Double-centered split pseudometric | `doubleCentered_splitPseudometric` | proved |
| Linearity for weighted split systems | `doubleCentered_weightedSplitPseudometric_eq` | proved |
| Normalized intersection table entries | `splitIntersectionTable_a_eq` through `splitIntersectionTable_d_eq` | proved |
| Centered covariance equals split determinant | `centeredIndicator_product_mean_eq_det` | proved |
| Full distance-covariance identity | `splitSystemDistanceCovariance_eq_detSquare` | proved |
| Nonnegativity for nonnegative edge lengths | `splitSystemDistanceCovariance_nonnegative` | proved |

## Appendix C

Appendix C is not used by any theorem.  Its three algorithms instantiate the
same finite definitions whose general equality is proved above:

- direct `f₁`: `Auxiliary.auxiliaryFunctional`;
- four-family reverse calculation: `ConcreteFourFamilies.scaledLedger`;
- ordered-quadruple kernel: `CorrectionKernel` and
  `DistinctTupleCounting.auxiliaryFunctional_eq_allKernelSum`.

The specific two 25-leaf Newick trees and the displayed value
`9273/390625` remain a **computational illustration**, not a separate Lean
declaration.  Therefore the formal proof of the conjecture is complete
without trusting those printed numerical values, while the example itself
must still be reproduced by its exact-arithmetic program if one wants to
audit the manuscript's concrete numbers.

## Audit

`QuartetV060/AxiomAudit.lean` prints the axioms of the final declarations.
The accepted audit condition is:

1. `lake build` succeeds;
2. the source contains no `sorry`, `admit`, custom `axiom`, `opaque`,
   `unsafe`, or `native_decide`;
3. the final declarations use only `propext`, `Classical.choice`, and
   `Quot.sound`.
