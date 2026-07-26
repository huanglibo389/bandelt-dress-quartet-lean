import QuartetV060.PositionalIndicator
import QuartetDistance.GraphQuartet

/-!
# Concrete edge and adjacent-correction occurrences of a binary tree

The reference project supplies a graph-theoretically adequate realization of
`Tree.PhyloTree`.  Here we enumerate every undirected edge exactly once by its
rooted edge position, retain precisely the quartet-relevant edges, and index
each ordered adjacent correction by its two source edge occurrences.
-/

namespace QuartetV060

open scoped BigOperators

namespace PhyloOccurrences

open QuartetDistance

noncomputable section

variable
    {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

abbrev ProperSubtree (t : Tree.FullTree X) :=
  GraphQuartet.FullTree.ProperSubtree t

abbrev EdgePosition (T : Tree.PhyloTree X) :=
  GraphQuartet.PhyloTree.EdgePosition T

/-- Exhaustive list of the parent-edge positions strictly inside a full
binary tree. -/
def allProperSubtrees :
    (t : Tree.FullTree X) → List (GraphQuartet.FullTree.ProperSubtree t)
  | .leaf _ => []
  | .fork l r =>
      GraphQuartet.FullTree.ProperSubtree.left l r ::
      GraphQuartet.FullTree.ProperSubtree.right l r ::
      ((allProperSubtrees l).map fun p =>
        GraphQuartet.FullTree.ProperSubtree.inLeft p) ++
      ((allProperSubtrees r).map fun p =>
        GraphQuartet.FullTree.ProperSubtree.inRight p)

omit [Fintype X] [Nonempty X] [DecidableEq X] in
theorem mem_allProperSubtrees
    {t : Tree.FullTree X}
    (p : GraphQuartet.FullTree.ProperSubtree t) :
    p ∈ allProperSubtrees t := by
  induction p with
  | left l r =>
      simp [allProperSubtrees]
  | right l r =>
      simp [allProperSubtrees]
  | inLeft p ih =>
      simp [allProperSubtrees, ih]
  | inRight p ih =>
      simp [allProperSubtrees, ih]

omit [Fintype X] [Nonempty X] [DecidableEq X] in
noncomputable instance properSubtreeDecidableEq
    (t : Tree.FullTree X) :
    DecidableEq (GraphQuartet.FullTree.ProperSubtree t) :=
  Classical.decEq _

omit [Fintype X] [Nonempty X] [DecidableEq X] in
noncomputable instance properSubtreeFintype
    (t : Tree.FullTree X) :
    Fintype (GraphQuartet.FullTree.ProperSubtree t) :=
  Fintype.ofList (allProperSubtrees t) mem_allProperSubtrees

/-- Exhaustive list of all unrooted edge positions: the root/crown edge,
followed by every edge internal to the crown. -/
def allEdgePositions (T : Tree.PhyloTree X) :
    List (GraphQuartet.PhyloTree.EdgePosition T) :=
  GraphQuartet.PhyloTree.EdgePosition.crown ::
    (allProperSubtrees T.crown).map
      GraphQuartet.PhyloTree.EdgePosition.inside

theorem mem_allEdgePositions
    (T : Tree.PhyloTree X)
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    p ∈ allEdgePositions T := by
  cases p with
  | crown =>
      simp [allEdgePositions]
  | inside p =>
      simp only [allEdgePositions, List.mem_cons, List.mem_map]
      right
      exact ⟨p, mem_allProperSubtrees p, rfl⟩

noncomputable instance edgePositionDecidableEq
    (T : Tree.PhyloTree X) :
    DecidableEq (GraphQuartet.PhyloTree.EdgePosition T) :=
  Classical.decEq _

noncomputable instance edgePositionFintype
    (T : Tree.PhyloTree X) :
    Fintype (GraphQuartet.PhyloTree.EdgePosition T) :=
  Fintype.ofList (allEdgePositions T) (mem_allEdgePositions T)

theorem cluster_nonempty
    (T : Tree.PhyloTree X)
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    p.cluster.Nonempty := by
  unfold GraphQuartet.PhyloTree.EdgePosition.cluster
  rw [Finset.image_nonempty]
  exact (List.toFinset_nonempty_iff p.tree.leaves).2 p.tree.leaves_ne_nil

theorem cluster_compl_nonempty
    (T : Tree.PhyloTree X)
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    p.clusterᶜ.Nonempty := by
  refine ⟨T.root, Finset.mem_compl.mpr ?_⟩
  intro hroot
  simp only [GraphQuartet.PhyloTree.EdgePosition.cluster,
    Finset.mem_image] at hroot
  obtain ⟨a, ha, hval⟩ := hroot
  exact a.property hval

/-- The quartet-relevant edge positions, i.e. the non-pendant edges in a
binary leaf-labelled phylogenetic tree. -/
def RelevantEdge (T : Tree.PhyloTree X) :=
  {p : GraphQuartet.PhyloTree.EdgePosition T //
    2 ≤ p.cluster.card ∧ 2 ≤ p.clusterᶜ.card}

noncomputable instance relevantEdgeDecidableEq
    (T : Tree.PhyloTree X) : DecidableEq (RelevantEdge T) :=
  Classical.decEq _

noncomputable instance relevantEdgeFintype
    (T : Tree.PhyloTree X) : Fintype (RelevantEdge T) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun p :
      GraphQuartet.PhyloTree.EdgePosition T =>
        2 ≤ p.cluster.card ∧ 2 ≤ p.clusterᶜ.card)
    (by simp [RelevantEdge])

/-- Two distinct rooted edge positions are adjacent when their underlying
graph edges share one endpoint. -/
def EdgeAdjacent
    {T : Tree.PhyloTree X}
    (p q : GraphQuartet.PhyloTree.EdgePosition T) : Prop :=
  p ≠ q ∧
    (p.parent = q.parent ∨ p.parent = q.child ∨
      p.child = q.parent ∨ p.child = q.child)

/-- Ordered adjacent pairs of quartet-relevant edges.  The order is part of
the index, exactly as in the manuscript. -/
def AdjacentCorrection (T : Tree.PhyloTree X) :=
  {pq : RelevantEdge T × RelevantEdge T //
    EdgeAdjacent pq.1.1 pq.2.1}

noncomputable instance adjacentCorrectionDecidableEq
    (T : Tree.PhyloTree X) : DecidableEq (AdjacentCorrection T) :=
  Classical.decEq _

noncomputable instance adjacentCorrectionFintype
    (T : Tree.PhyloTree X) : Fintype (AdjacentCorrection T) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun pq : RelevantEdge T × RelevantEdge T =>
      EdgeAdjacent pq.1.1 pq.2.1)
    (by simp [AdjacentCorrection])

def first
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) : RelevantEdge T :=
  a.1.1

def second
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) : RelevantEdge T :=
  a.1.2

/-- The outer block beyond the second edge of an ordered pair. -/
noncomputable def correctionK
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) : Finset X :=
  if (second a).1.cluster ⊆ (first a).1.cluster then
    (second a).1.cluster
  else if (first a).1.cluster ⊆ (second a).1.cluster then
    (second a).1.clusterᶜ
  else
    (second a).1.cluster

/-- The outer block beyond the first edge of an ordered pair. -/
noncomputable def correctionL
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) : Finset X :=
  if (second a).1.cluster ⊆ (first a).1.cluster then
    (first a).1.clusterᶜ
  else
    (first a).1.cluster

theorem correctionK_disjoint_correctionL
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    Disjoint (correctionK a) (correctionL a) := by
  classical
  by_cases hqp : (second a).1.cluster ⊆ (first a).1.cluster
  · simp only [correctionK, correctionL, hqp, if_true]
    exact Finset.disjoint_left.mpr (by
      intro x hxq hxp
      exact (Finset.mem_compl.mp hxp) (hqp hxq))
  · by_cases hpq : (first a).1.cluster ⊆ (second a).1.cluster
    · simp only [correctionK, correctionL, hqp, hpq, if_false, if_true]
      exact Finset.disjoint_left.mpr (by
        intro x hxq hxp
        exact (Finset.mem_compl.mp hxq) (hpq hxp))
    · simp only [correctionK, correctionL, hqp, hpq, if_false]
      rcases
          GraphQuartet.PhyloTree.EdgePosition.clusters_laminar
            (first a).1 (second a).1 with h | h | h
      · exact False.elim (hpq h)
      · exact False.elim (hqp h)
      · exact h.symm

private theorem nonempty_of_two_le_card
    {A : Finset X} (h : 2 ≤ A.card) : A.Nonempty := by
  exact Finset.card_pos.mp (by omega)

theorem correctionK_nonempty
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (correctionK a).Nonempty := by
  classical
  by_cases hqp : (second a).1.cluster ⊆ (first a).1.cluster
  · simp only [correctionK, hqp, if_true]
    exact nonempty_of_two_le_card (second a).2.1
  · by_cases hpq : (first a).1.cluster ⊆ (second a).1.cluster
    · simp only [correctionK, hqp, hpq, if_false, if_true]
      exact nonempty_of_two_le_card (second a).2.2
    · simp only [correctionK, hqp, hpq, if_false]
      exact nonempty_of_two_le_card (second a).2.1

theorem correctionL_nonempty
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (correctionL a).Nonempty := by
  classical
  by_cases hqp : (second a).1.cluster ⊆ (first a).1.cluster
  · simp only [correctionL, hqp, if_true]
    exact nonempty_of_two_le_card (first a).2.2
  · simp only [correctionL, hqp, if_false]
    exact nonempty_of_two_le_card (first a).2.1

/-- The ordinary oriented split represented by a relevant edge. -/
def ordinary
    (T : Tree.PhyloTree X)
    (e : RelevantEdge T) : OrientedSplit X where
  side := e.1.cluster
  side_nonempty := cluster_nonempty T e.1
  other_nonempty := cluster_compl_nonempty T e.1

/-- The concrete adjacent correction side-pair `(K,L)`. -/
noncomputable def corrected
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) : SidePair X where
  left := correctionK a
  right := correctionL a
  left_nonempty := correctionK_nonempty a
  right_nonempty := correctionL_nonempty a
  disjoint := correctionK_disjoint_correctionL a

/-- The concrete correction system extracted from a binary phylogenetic
tree. -/
noncomputable def correctionSystem
    (T : Tree.PhyloTree X) :
    CorrectionSystem X (RelevantEdge T) (AdjacentCorrection T) where
  ordinary := ordinary T
  source := first
  corrected := corrected

theorem first_cluster_eq_L_or_compl
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (first a).1.cluster = correctionL a ∨
      (first a).1.cluster = (correctionL a)ᶜ := by
  classical
  by_cases hqp : (second a).1.cluster ⊆ (first a).1.cluster
  · right
    simp [correctionL, hqp]
  · left
    simp [correctionL, hqp]

theorem second_cluster_eq_K_or_compl
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (second a).1.cluster = correctionK a ∨
      (second a).1.cluster = (correctionK a)ᶜ := by
  classical
  by_cases hqp : (second a).1.cluster ⊆ (first a).1.cluster
  · left
    simp [correctionK, hqp]
  · by_cases hpq : (first a).1.cluster ⊆ (second a).1.cluster
    · right
      simp [correctionK, hqp, hpq]
    · left
      simp [correctionK, hqp, hpq]

private theorem ordinary_indicator_eq
    (T : Tree.PhyloTree X)
    (e : RelevantEdge T) (A : Finset X)
    (h : e.1.cluster = A ∨ e.1.cluster = Aᶜ)
    (q₁ q₂ q₃ q₄ : X) :
    Positional.sidePairIndicator (ordinary T e).toSidePair
        q₁ q₂ q₃ q₄ =
      Positional.indicator A Aᶜ q₁ q₂ q₃ q₄ := by
  rcases h with h | h
  · simp [ordinary, Positional.sidePairIndicator,
      OrientedSplit.toSidePair, OrientedSplit.other, h]
  · have hrev :=
      Positional.indicator_reverse A Aᶜ q₁ q₂ q₃ q₄
    simpa [ordinary, Positional.sidePairIndicator,
      OrientedSplit.toSidePair, OrientedSplit.other, h] using hrev

/-- The manuscript's full-domain identity
`I_{C_(e,e')} = I_e I_e'`, now for the concrete tree correction system and
without any distinct-label hypothesis. -/
theorem corrected_indicator_eq_product
    (T : Tree.PhyloTree X)
    (a : AdjacentCorrection T)
    (q₁ q₂ q₃ q₄ : X) :
    Positional.sidePairIndicator (corrected a) q₁ q₂ q₃ q₄ =
      Positional.sidePairIndicator (ordinary T (first a)).toSidePair
          q₁ q₂ q₃ q₄ *
        Positional.sidePairIndicator (ordinary T (second a)).toSidePair
          q₁ q₂ q₃ q₄ := by
  have hbase :=
    Positional.adjacent_indicator_complements
      (correctionK a) (correctionL a)
      (correctionK_disjoint_correctionL a)
      q₁ q₂ q₃ q₄
  have hfirst :=
    ordinary_indicator_eq T (first a) (correctionL a)
      (first_cluster_eq_L_or_compl a) q₁ q₂ q₃ q₄
  have hsecond :=
    ordinary_indicator_eq T (second a) (correctionK a)
      (second_cluster_eq_K_or_compl a) q₁ q₂ q₃ q₄
  calc
    Positional.sidePairIndicator (corrected a) q₁ q₂ q₃ q₄ =
        Positional.indicator (correctionK a) (correctionL a)
          q₁ q₂ q₃ q₄ := rfl
    _ = Positional.indicator (correctionL a) (correctionL a)ᶜ
          q₁ q₂ q₃ q₄ *
        Positional.indicator (correctionK a) (correctionK a)ᶜ
          q₁ q₂ q₃ q₄ := hbase
    _ = Positional.sidePairIndicator
          (ordinary T (first a)).toSidePair q₁ q₂ q₃ q₄ *
        Positional.sidePairIndicator
          (ordinary T (second a)).toSidePair q₁ q₂ q₃ q₄ := by
            rw [hfirst, hsecond]

end

end PhyloOccurrences

end QuartetV060
