import QuartetV060.EdgeClusterInjective
import QuartetV060.BridgeReversal

/-!
# Concrete bridge reversal for binary phylogenetic trees

An ordered adjacent pair of relevant edges is reversed by swapping its two
source edges.  The concrete taxon blocks then satisfy
`(K,H,L) ↦ (L,H,K)`.  Thus the abstract bridge-orbit ledger is instantiated
by the actual ordered adjacent-edge range used by the manuscript.
-/

namespace QuartetV060

namespace PhyloBridgeReversal

open QuartetDistance
open PhyloOccurrences
open TreePathCounting
open EdgeClusterInjective

noncomputable section

variable
    {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

/-- Reverse an ordered adjacent correction by swapping its two source
edges. -/
noncomputable def reverseCorrection
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) : AdjacentCorrection T :=
  ⟨(second a, first a),
    (edgeAdjacent_comm (second a).1 (first a).1).2 a.2⟩

@[simp] theorem first_reverseCorrection
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    first (reverseCorrection a) = second a := rfl

@[simp] theorem second_reverseCorrection
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    second (reverseCorrection a) = first a := rfl

@[simp] theorem reverseCorrection_reverseCorrection
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    reverseCorrection (reverseCorrection a) = a := by
  apply Subtype.ext
  rfl

theorem reverseCorrection_ne
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    reverseCorrection a ≠ a := by
  intro h
  have hpair : (second a, first a) = (first a, second a) :=
    Subtype.mk.inj h
  have hfirst : second a = first a := congrArg Prod.fst hpair
  exact a.2.1 (congrArg Subtype.val hfirst.symm)

theorem first_cluster_ne_second_cluster
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (first a).1.cluster ≠ (second a).1.cluster := by
  intro h
  have hedge :
      (first a).1 = (second a).1 :=
    edgePosition_cluster_injective h
  exact a.2.1 hedge

@[simp] theorem correctionK_reverseCorrection
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    correctionK (reverseCorrection a) = correctionL a := by
  classical
  have hne :
      (first a).1.cluster ≠ (second a).1.cluster :=
    first_cluster_ne_second_cluster a
  by_cases hQP : (second a).1.cluster ⊆ (first a).1.cluster
  · have hnotPQ :
        ¬(first a).1.cluster ⊆ (second a).1.cluster := by
      intro hPQ
      exact hne (Finset.Subset.antisymm hPQ hQP)
    simp only [correctionK, correctionL, first_reverseCorrection,
      second_reverseCorrection, hQP, hnotPQ, if_true, if_false]
  · by_cases hPQ :
        (first a).1.cluster ⊆ (second a).1.cluster
    · simp only [correctionK, correctionL, first_reverseCorrection,
        second_reverseCorrection, hQP, hPQ, if_true, if_false]
    · simp only [correctionK, correctionL, first_reverseCorrection,
        second_reverseCorrection, hQP, hPQ, if_true, if_false]

@[simp] theorem correctionL_reverseCorrection
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    correctionL (reverseCorrection a) = correctionK a := by
  classical
  have hne :
      (first a).1.cluster ≠ (second a).1.cluster :=
    first_cluster_ne_second_cluster a
  by_cases hQP : (second a).1.cluster ⊆ (first a).1.cluster
  · have hnotPQ :
        ¬(first a).1.cluster ⊆ (second a).1.cluster := by
      intro hPQ
      exact hne (Finset.Subset.antisymm hPQ hQP)
    simp only [correctionK, correctionL, first_reverseCorrection,
      second_reverseCorrection, hQP, hnotPQ, if_true, if_false]
  · by_cases hPQ :
        (first a).1.cluster ⊆ (second a).1.cluster
    · simp only [correctionK, correctionL, first_reverseCorrection,
        second_reverseCorrection, hQP, hPQ, if_true, if_false]
    · simp only [correctionK, correctionL, first_reverseCorrection,
        second_reverseCorrection, hQP, hPQ, if_true, if_false]

/-- The concrete `(K,H,L)` decomposition belonging to one ordered adjacent
pair. -/
noncomputable def bridgeBlocks
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) : ThreeBlock X where
  K := correctionK a
  H := (correctionK a ∪ correctionL a)ᶜ
  L := correctionL a
  disjoint_KH := by
    rw [Finset.disjoint_left]
    intro x hxK hxH
    exact (Finset.mem_compl.mp hxH)
      (Finset.mem_union_left _ hxK)
  disjoint_KL := correctionK_disjoint_correctionL a
  disjoint_HL := by
    rw [Finset.disjoint_left]
    intro x hxH hxL
    exact (Finset.mem_compl.mp hxH)
      (Finset.mem_union_right _ hxL)
  cover := by
    ext x
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_univ,
      iff_true]
    tauto

@[simp] theorem bridgeBlocks_K
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (bridgeBlocks a).K = correctionK a := rfl

@[simp] theorem bridgeBlocks_H
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (bridgeBlocks a).H =
      (correctionK a ∪ correctionL a)ᶜ := rfl

@[simp] theorem bridgeBlocks_L
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (bridgeBlocks a).L = correctionL a := rfl

/-- The actual ordered adjacent edge `(g,e)` has exactly the reversed three
blocks of `(e,g)`. -/
theorem bridgeBlocks_reverseCorrection
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    bridgeBlocks (reverseCorrection a) =
      (bridgeBlocks a).reverse := by
  apply ThreeBlock.ext
  · exact correctionK_reverseCorrection a
  · simp only [bridgeBlocks_H, correctionK_reverseCorrection,
      correctionL_reverseCorrection, ThreeBlock.reverse_H]
    rw [Finset.union_comm]
  · exact correctionL_reverseCorrection a

/-- The manuscript's bridge-reversal system instantiated by all ordered
adjacent relevant-edge pairs of a concrete binary phylogenetic tree. -/
noncomputable def bridgeSystem
    (T : Tree.PhyloTree X) :
    BridgeSystem X (AdjacentCorrection T) where
  blocks := bridgeBlocks
  rho := reverseCorrection
  rho_involutive := reverseCorrection_reverseCorrection
  rho_ne := reverseCorrection_ne
  blocks_rho := bridgeBlocks_reverseCorrection

end

end PhyloBridgeReversal

end QuartetV060
