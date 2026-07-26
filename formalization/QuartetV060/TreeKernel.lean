import QuartetV060.PhyloOccurrences

/-!
# Concrete tree kernel and the path-weight bridge

This module expands the signed occurrence kernel of a binary phylogenetic
tree and identifies it, on the whole domain `X⁴`, with the difference of the
two positional path weights used in the manuscript.
-/

namespace QuartetV060

open scoped BigOperators

namespace TreeKernel

open QuartetDistance
open PhyloOccurrences

noncomputable section

variable
    {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

/-- The positional indicator of one relevant edge. -/
def edgeIndicator
    (T : Tree.PhyloTree X) (e : RelevantEdge T)
    (q₁ q₂ q₃ q₄ : X) : ℚ :=
  Positional.sidePairIndicator (ordinary T e).toSidePair q₁ q₂ q₃ q₄

/-- The positional indicator of one indexed ordered-adjacent correction. -/
def correctionIndicator
    {T : Tree.PhyloTree X} (a : AdjacentCorrection T)
    (q₁ q₂ q₃ q₄ : X) : ℚ :=
  Positional.sidePairIndicator (corrected a) q₁ q₂ q₃ q₄

/-- The signed edge-path weight, written first as the exact finite occurrence
sum.  Its cardinality form is proved below. -/
def pathWeight
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) : ℚ :=
  (∑ e : RelevantEdge T, edgeIndicator T e q₁ q₂ q₃ q₄) -
    (1 / 2 : ℚ) *
      ∑ a : AdjacentCorrection T,
        correctionIndicator a q₁ q₂ q₃ q₄

/-- The concrete kernel of a binary phylogenetic tree. -/
def kernel
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) : ℚ :=
  ((correctionSystem T).occurrenceFamily).kernel q₁ q₂ q₃ q₄

/-- Each correction indicator is the product of its two source-edge
indicators. -/
theorem correctionIndicator_eq_mul
    (T : Tree.PhyloTree X)
    (a : AdjacentCorrection T)
    (q₁ q₂ q₃ q₄ : X) :
    correctionIndicator a q₁ q₂ q₃ q₄ =
      edgeIndicator T (first a) q₁ q₂ q₃ q₄ *
        edgeIndicator T (second a) q₁ q₂ q₃ q₄ := by
  exact corrected_indicator_eq_product T a q₁ q₂ q₃ q₄

/-- Expansion of the disjoint signed occurrence type into its ordinary and
correction parts. -/
theorem kernel_eq_edge_sum_sub_correction_sum
    (T : Tree.PhyloTree X)
    (q₁ q₂ q₃ q₄ : X) :
    kernel T q₁ q₂ q₃ q₄ =
      (∑ e : RelevantEdge T,
        Kernel.phi (ordinary T e).toSidePair q₁ q₂ *
          Kernel.phi (ordinary T e).toSidePair q₃ q₄) -
      (1 / 2 : ℚ) *
        ∑ a : AdjacentCorrection T,
          Kernel.phi (corrected a) q₁ q₂ *
            Kernel.phi (corrected a) q₃ q₄ := by
  unfold kernel Kernel.OccurrenceFamily.kernel
    CorrectionSystem.occurrenceFamily correctionSystem
  simp only [Fintype.sum_sum_type]
  simp only [one_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring_nf

/-- Exact kernel-to-path identity.  The positional arguments
`(q₁,q₃;q₂,q₄)` and `(q₁,q₄;q₂,q₃)` are the manuscript's pairings
`13|24` and `14|23`. -/
theorem kernel_eq_pathWeight_sub_pathWeight
    (T : Tree.PhyloTree X)
    (q₁ q₂ q₃ q₄ : X) :
    kernel T q₁ q₂ q₃ q₄ =
      pathWeight T q₁ q₃ q₂ q₄ -
        pathWeight T q₁ q₄ q₂ q₃ := by
  rw [kernel_eq_edge_sum_sub_correction_sum]
  simp_rw [Positional.phi_product_eq_indicator_sub_indicator]
  simp only [pathWeight, edgeIndicator, correctionIndicator,
    Finset.sum_sub_distrib]
  ring

/-- The active relevant edges for one positional pairing. -/
noncomputable def activeEdges
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    Finset (RelevantEdge T) := by
  classical
  exact Finset.univ.filter fun e =>
    Positional.Separates (ordinary T e).toSidePair.left
      (ordinary T e).toSidePair.right q₁ q₂ q₃ q₄

/-- The active ordered-adjacent corrections for one positional pairing. -/
noncomputable def activeCorrections
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    Finset (AdjacentCorrection T) := by
  classical
  exact Finset.univ.filter fun a =>
    Positional.Separates (corrected a).left (corrected a).right
      q₁ q₂ q₃ q₄

private theorem sum_truth_indicator_eq_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P] :
    (∑ i : ι, if P i then (1 : ℚ) else 0) =
      ((Finset.univ.filter P).card : ℚ) := by
  classical
  calc
    (∑ i : ι, if P i then (1 : ℚ) else 0) =
        ∑ i ∈ Finset.univ.filter P, (1 : ℚ) := by
          simp
    _ = ((Finset.univ.filter P).card : ℚ) := by simp

/-- Cardinality version of the positional path weight from the paper. -/
theorem pathWeight_eq_card_sub_half_card
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    pathWeight T q₁ q₂ q₃ q₄ =
      ((activeEdges T q₁ q₂ q₃ q₄).card : ℚ) -
        (1 / 2 : ℚ) *
          ((activeCorrections T q₁ q₂ q₃ q₄).card : ℚ) := by
  classical
  simp only [pathWeight, edgeIndicator, correctionIndicator,
    Positional.sidePairIndicator, Positional.indicator,
    activeEdges, activeCorrections]
  rw [sum_truth_indicator_eq_card, sum_truth_indicator_eq_card]

end

end TreeKernel

end QuartetV060
