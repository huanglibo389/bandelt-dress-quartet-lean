import QuartetV060.TreeKernel
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Counting an active edge path

This module isolates the finite graph count used in the manuscript's
kernel-to-path argument.  The geometric statement that the active relevant
edges of a phylogenetic tree form an empty path or a nonempty path is proved
separately.  Here we prove, without suppressing multiplicities, that a
nonempty active path has `m` vertices and exactly `2(m - 1)` ordered adjacent
pairs.
-/

namespace QuartetV060

open scoped BigOperators

namespace TreePathCounting

open QuartetDistance
open PhyloOccurrences
open TreeKernel

noncomputable section

variable
    {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

theorem edgeAdjacent_comm
    {T : Tree.PhyloTree X}
    (p q : EdgePosition T) :
    EdgeAdjacent p q ↔ EdgeAdjacent q p := by
  unfold EdgeAdjacent
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inr h.symm))
  · rintro ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inr h.symm))

/-- A relevant edge together with evidence that it is active for the fixed
positional pairing. -/
def ActiveEdge
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :=
  {e : RelevantEdge T // e ∈ activeEdges T q₁ q₂ q₃ q₄}

noncomputable instance activeEdgeDecidableEq
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    DecidableEq (ActiveEdge T q₁ q₂ q₃ q₄) :=
  Classical.decEq _

noncomputable instance activeEdgeFintype
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    Fintype (ActiveEdge T q₁ q₂ q₃ q₄) :=
  Fintype.ofFinset (activeEdges T q₁ q₂ q₃ q₄) (by
    intro e
    rfl)

/-- The line graph induced by the active relevant edges. -/
def activeAdjGraph
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    SimpleGraph (ActiveEdge T q₁ q₂ q₃ q₄) where
  Adj e f := EdgeAdjacent e.1.1 f.1.1
  symm := ⟨by
    intro e f h
    exact (edgeAdjacent_comm e.1.1 f.1.1).mp h⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩

noncomputable instance activeAdjGraphDecidableRel
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    DecidableRel (activeAdjGraph T q₁ q₂ q₃ q₄).Adj :=
  Classical.decRel _

/-- Logical version of the full-domain adjacent-correction identity:
a correction occurrence is active exactly when both of its source-edge
occurrences are active. -/
theorem corrected_separates_iff_sources
    (T : Tree.PhyloTree X)
    (a : AdjacentCorrection T)
    (q₁ q₂ q₃ q₄ : X) :
    Positional.Separates (corrected a).left (corrected a).right
        q₁ q₂ q₃ q₄ ↔
      Positional.Separates
          (ordinary T (first a)).toSidePair.left
          (ordinary T (first a)).toSidePair.right
          q₁ q₂ q₃ q₄ ∧
        Positional.Separates
          (ordinary T (second a)).toSidePair.left
          (ordinary T (second a)).toSidePair.right
          q₁ q₂ q₃ q₄ := by
  have h :=
    corrected_indicator_eq_product T a q₁ q₂ q₃ q₄
  unfold Positional.sidePairIndicator Positional.indicator at h
  by_cases hc :
      Positional.Separates (corrected a).left (corrected a).right
        q₁ q₂ q₃ q₄ <;>
    by_cases hf :
      Positional.Separates
        (ordinary T (first a)).toSidePair.left
        (ordinary T (first a)).toSidePair.right
        q₁ q₂ q₃ q₄ <;>
    by_cases hs :
      Positional.Separates
        (ordinary T (second a)).toSidePair.left
        (ordinary T (second a)).toSidePair.right
        q₁ q₂ q₃ q₄ <;>
    simp_all

theorem mem_activeCorrections_iff
    (T : Tree.PhyloTree X)
    (a : AdjacentCorrection T)
    (q₁ q₂ q₃ q₄ : X) :
    a ∈ activeCorrections T q₁ q₂ q₃ q₄ ↔
      first a ∈ activeEdges T q₁ q₂ q₃ q₄ ∧
        second a ∈ activeEdges T q₁ q₂ q₃ q₄ := by
  classical
  simp only [activeCorrections, activeEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact corrected_separates_iff_sources T a q₁ q₂ q₃ q₄

/-- Active correction occurrences are exactly ordered adjacent pairs in the
active-edge graph.  The occurrence index is retained, so this equivalence
does not quotient the two orientations of an unordered adjacent pair. -/
noncomputable def activeCorrectionEquivOrderedAdjacency
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    {a : AdjacentCorrection T //
        a ∈ activeCorrections T q₁ q₂ q₃ q₄} ≃
      {ef :
          ActiveEdge T q₁ q₂ q₃ q₄ ×
            ActiveEdge T q₁ q₂ q₃ q₄ //
        (activeAdjGraph T q₁ q₂ q₃ q₄).Adj ef.1 ef.2} where
  toFun a := by
    have ha :=
      (mem_activeCorrections_iff T a.1 q₁ q₂ q₃ q₄).mp a.2
    refine
      ⟨(⟨first a.1, ha.1⟩, ⟨second a.1, ha.2⟩), ?_⟩
    simpa [activeAdjGraph, first, second] using a.1.2
  invFun ef := by
    let a : AdjacentCorrection T :=
      ⟨(ef.1.1.1, ef.1.2.1), by
        simpa [activeAdjGraph] using ef.2⟩
    refine ⟨a, ?_⟩
    exact
      (mem_activeCorrections_iff T a q₁ q₂ q₃ q₄).mpr
        ⟨ef.1.1.2, ef.1.2.2⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv ef := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl

@[simp] theorem card_activeEdge
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    Fintype.card (ActiveEdge T q₁ q₂ q₃ q₄) =
      (activeEdges T q₁ q₂ q₃ q₄).card := by
  classical
  simp [ActiveEdge]

/-- Exact handshake count: the active-correction cardinality is twice the
number of unordered adjacencies in the active-edge graph. -/
theorem two_mul_activeAdjGraph_edge_card
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    2 * (activeAdjGraph T q₁ q₂ q₃ q₄).edgeFinset.card =
      (activeCorrections T q₁ q₂ q₃ q₄).card := by
  classical
  calc
    2 * (activeAdjGraph T q₁ q₂ q₃ q₄).edgeFinset.card =
        (Finset.univ.filter fun ef :
        ActiveEdge T q₁ q₂ q₃ q₄ ×
          ActiveEdge T q₁ q₂ q₃ q₄ =>
          (activeAdjGraph T q₁ q₂ q₃ q₄).Adj ef.1 ef.2).card := by
            exact SimpleGraph.two_mul_card_edgeFinset
              (G := activeAdjGraph T q₁ q₂ q₃ q₄)
    _ =
        Fintype.card
          {ef :
              ActiveEdge T q₁ q₂ q₃ q₄ ×
                ActiveEdge T q₁ q₂ q₃ q₄ //
            (activeAdjGraph T q₁ q₂ q₃ q₄).Adj ef.1 ef.2} := by
              exact
                (Fintype.card_subtype fun ef :
                  ActiveEdge T q₁ q₂ q₃ q₄ ×
                    ActiveEdge T q₁ q₂ q₃ q₄ =>
                  (activeAdjGraph T q₁ q₂ q₃ q₄).Adj ef.1 ef.2).symm
    _ = Fintype.card
          {a : AdjacentCorrection T //
            a ∈ activeCorrections T q₁ q₂ q₃ q₄} := by
              exact Fintype.card_congr
                (activeCorrectionEquivOrderedAdjacency
                  T q₁ q₂ q₃ q₄).symm
    _ = (activeCorrections T q₁ q₂ q₃ q₄).card := by
          simp

theorem activeCorrections_eq_empty_of_activeEdges_eq_empty
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (h : activeEdges T q₁ q₂ q₃ q₄ = ∅) :
    activeCorrections T q₁ q₂ q₃ q₄ = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hsource :=
    (mem_activeCorrections_iff T a q₁ q₂ q₃ q₄).mp ha
  rw [h] at hsource
  simpa using hsource.1

/-- The empty active path has weight zero. -/
theorem pathWeight_eq_zero_of_activeEdges_eq_empty
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (h : activeEdges T q₁ q₂ q₃ q₄ = ∅) :
    pathWeight T q₁ q₂ q₃ q₄ = 0 := by
  rw [pathWeight_eq_card_sub_half_card,
    h, activeCorrections_eq_empty_of_activeEdges_eq_empty T q₁ q₂ q₃ q₄ h]
  norm_num

/-- If the active-edge adjacency graph is a tree, then its active path
weight is exactly one.  This theorem is the fully formal version of
`m - (1/2) 2(m-1) = 1`. -/
theorem pathWeight_eq_one_of_activeAdjGraph_isTree
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (htree : (activeAdjGraph T q₁ q₂ q₃ q₄).IsTree) :
    pathWeight T q₁ q₂ q₃ q₄ = 1 := by
  classical
  have hedge :=
    htree.card_edgeFinset
  have hadj :=
    two_mul_activeAdjGraph_edge_card T q₁ q₂ q₃ q₄
  have hvertices :
      Fintype.card (ActiveEdge T q₁ q₂ q₃ q₄) =
        (activeEdges T q₁ q₂ q₃ q₄).card :=
    card_activeEdge T q₁ q₂ q₃ q₄
  have hpositive :
      0 < Fintype.card (ActiveEdge T q₁ q₂ q₃ q₄) := by
    exact Fintype.card_pos_iff.mpr htree.connected.nonempty
  have hcount :
      (activeCorrections T q₁ q₂ q₃ q₄).card =
        2 * ((activeEdges T q₁ q₂ q₃ q₄).card - 1) := by
    omega
  rw [pathWeight_eq_card_sub_half_card, hcount]
  have hactive :
      1 ≤ (activeEdges T q₁ q₂ q₃ q₄).card := by
    omega
  push_cast
  rw [Nat.cast_sub hactive]
  ring

end

end TreePathCounting

end QuartetV060
