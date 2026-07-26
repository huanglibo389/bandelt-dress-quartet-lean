import QuartetV060.TreePathCounting
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Rooted edge positions and graph edges

This module identifies the manuscript's rooted edge occurrences with the
actual undirected edges in the finite graph realization of a phylogenetic
tree.  The orientation is only bookkeeping: every graph edge occurs exactly
once, with its parent endpoint on the distinguished-root side.
-/

namespace QuartetV060

namespace TreeEdgeGeometry

open QuartetDistance
open PhyloOccurrences
open TreeKernel
open TreePathCounting

noncomputable section

variable
    {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

omit [Fintype X] [Nonempty X] [DecidableEq X] in
private theorem properSubtree_eq_of_child_eq
    {t : Tree.FullTree X}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (hchild : p.child = q.child) :
    p = q := by
  induction t with
  | leaf x =>
      exact nomatch p
  | fork l r ihl ihr =>
      cases p with
      | left =>
          cases q with
          | left => rfl
          | right => simp [GraphQuartet.FullTree.ProperSubtree.child,
              GraphQuartet.FullTree.ProperSubtree.embed] at hchild
          | inLeft q =>
              exfalso
              apply q.root_not_below
              refine ⟨TreeAdequacy.FullTree.rootVertex q.tree, ?_⟩
              simpa [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] using hchild.symm
          | inRight q =>
              simp [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] at hchild
      | right =>
          cases q with
          | left => simp [GraphQuartet.FullTree.ProperSubtree.child,
              GraphQuartet.FullTree.ProperSubtree.embed] at hchild
          | right => rfl
          | inLeft q =>
              simp [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] at hchild
          | inRight q =>
              exfalso
              apply q.root_not_below
              refine ⟨TreeAdequacy.FullTree.rootVertex q.tree, ?_⟩
              simpa [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] using hchild.symm
      | inLeft p =>
          cases q with
          | left =>
              exfalso
              apply p.root_not_below
              refine ⟨TreeAdequacy.FullTree.rootVertex p.tree, ?_⟩
              simpa [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] using hchild
          | right =>
              simp [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] at hchild
          | inLeft q =>
              congr
              apply ihl p q
              simpa [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] using hchild
          | inRight q =>
              simp [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] at hchild
      | inRight p =>
          cases q with
          | left =>
              simp [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] at hchild
          | right =>
              exfalso
              apply p.root_not_below
              refine ⟨TreeAdequacy.FullTree.rootVertex p.tree, ?_⟩
              simpa [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] using hchild
          | inLeft q =>
              simp [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] at hchild
          | inRight q =>
              congr
              apply ihr p q
              simpa [GraphQuartet.FullTree.ProperSubtree.child,
                GraphQuartet.FullTree.ProperSubtree.embed] using hchild

theorem edgePosition_eq_of_child_eq
    {T : Tree.PhyloTree X}
    (p q : EdgePosition T)
    (hchild : p.child = q.child) :
    p = q := by
  cases p with
  | crown =>
      cases q with
      | crown => rfl
      | inside q =>
          exfalso
          apply q.root_not_below
          refine ⟨TreeAdequacy.FullTree.rootVertex q.tree, ?_⟩
          simpa [GraphQuartet.PhyloTree.EdgePosition.child,
            GraphQuartet.PhyloTree.EdgePosition.embed] using
              Sum.inr.inj hchild.symm
  | inside p =>
      cases q with
      | crown =>
          exfalso
          apply p.root_not_below
          refine ⟨TreeAdequacy.FullTree.rootVertex p.tree, ?_⟩
          simpa [GraphQuartet.PhyloTree.EdgePosition.child,
            GraphQuartet.PhyloTree.EdgePosition.embed] using
              Sum.inr.inj hchild
      | inside q =>
          exact congrArg GraphQuartet.PhyloTree.EdgePosition.inside
            (properSubtree_eq_of_child_eq p q (Sum.inr.inj hchild))

theorem edgePosition_root_not_below
    {T : Tree.PhyloTree X}
    (p : EdgePosition T) :
    ¬p.Below (.inl ()) := by
  cases p <;>
    simp [GraphQuartet.PhyloTree.EdgePosition.Below,
      GraphQuartet.PhyloTree.EdgePosition.embed]

/-- The actual undirected graph edge represented by a rooted edge position. -/
def positionEdge
    {T : Tree.PhyloTree X}
    (p : EdgePosition T) :
    (TreeAdequacy.PhyloTree.graph T).edgeSet :=
  ⟨s(p.parent, p.child), p.adj_parent_child⟩

theorem positionEdge_injective
    {T : Tree.PhyloTree X} :
    Function.Injective (positionEdge (T := T)) := by
  intro p q hpq
  have hedge :
      s(p.parent, p.child) = s(q.parent, q.child) :=
    Subtype.mk.inj hpq
  rw [Sym2.eq_iff] at hedge
  rcases hedge with hsame | hswap
  · exact edgePosition_eq_of_child_eq p q hsame.2
  · exfalso
    have hrootReach :
        ((TreeAdequacy.PhyloTree.graph T).deleteEdges
          {s(p.parent, p.child)}).Reachable p.parent (.inl ()) :=
      (p.parent_reachable_iff_not_below (.inl ())).2
        (edgePosition_root_not_below p)
    apply edgePosition_root_not_below q
    apply (q.reachable_iff_below (.inl ())).1
    simpa [hswap.1, hswap.2, Sym2.eq_swap] using hrootReach

theorem positionEdge_surjective
    {T : Tree.PhyloTree X} :
    Function.Surjective (positionEdge (T := T)) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy :
          (TreeAdequacy.PhyloTree.graph T).Adj x y := he
      obtain ⟨p, hp | hp⟩ :=
        GraphQuartet.PhyloTree.exists_edgePosition_of_adj T hxy
      · refine ⟨p, Subtype.ext ?_⟩
        simp [positionEdge, hp.1, hp.2]
      · refine ⟨p, Subtype.ext ?_⟩
        simp [positionEdge, hp.1, hp.2, Sym2.eq_swap]

/-- Rooted positions enumerate the graph edges exactly once. -/
noncomputable def edgePositionEquivEdgeSet
    (T : Tree.PhyloTree X) :
    EdgePosition T ≃ (TreeAdequacy.PhyloTree.graph T).edgeSet :=
  Equiv.ofBijective positionEdge
    ⟨positionEdge_injective, positionEdge_surjective⟩

theorem edgeAdjacent_iff_lineGraph_adj
    {T : Tree.PhyloTree X}
    (p q : EdgePosition T) :
    EdgeAdjacent p q ↔
      (TreeAdequacy.PhyloTree.graph T).lineGraph.Adj
        (positionEdge p) (positionEdge q) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  unfold EdgeAdjacent positionEdge
  simp only [ne_eq, Subtype.mk.injEq]
  constructor
  · rintro ⟨hpq, hshare⟩
    refine ⟨fun hedge => hpq (positionEdge_injective (Subtype.ext hedge)), ?_⟩
    rcases hshare with h | h | h | h
    · exact ⟨p.parent, by simp, by simp [h]⟩
    · exact ⟨p.parent, by simp, by simp [h]⟩
    · exact ⟨p.child, by simp, by simp [h]⟩
    · exact ⟨p.child, by simp, by simp [h]⟩
  · rintro ⟨hedge, v, hvp, hvq⟩
    refine ⟨fun hpq => hedge (Subtype.mk.inj (congrArg positionEdge hpq)), ?_⟩
    simp only [Sym2.mem_iff] at hvp hvq
    rcases hvp with hvp | hvp <;> rcases hvq with hvq | hvq
    · exact Or.inl (hvp.symm.trans hvq)
    · exact Or.inr (Or.inl (hvp.symm.trans hvq))
    · exact Or.inr (Or.inr (Or.inl (hvp.symm.trans hvq)))
    · exact Or.inr (Or.inr (Or.inr (hvp.symm.trans hvq)))

/-- A fixed graph vertex carrying a taxon label. -/
noncomputable def taxonVertex
    (T : Tree.PhyloTree X) (a : X) :
    TreeAdequacy.PhyloTree.Vertex T :=
  Classical.choose (TreeAdequacy.PhyloTree.exists_vertex_label T a)

@[simp] theorem taxonVertex_label
    (T : Tree.PhyloTree X) (a : X) :
    TreeAdequacy.PhyloTree.label? T (taxonVertex T a) = some a :=
  Classical.choose_spec (TreeAdequacy.PhyloTree.exists_vertex_label T a)

theorem taxonVertex_below_iff
    {T : Tree.PhyloTree X}
    (p : EdgePosition T) (a : X) :
    p.Below (taxonVertex T a) ↔ a ∈ p.cluster := by
  constructor
  · intro hbelow
    exact (p.exists_label_below_iff a).1
      ⟨taxonVertex T a, taxonVertex_label T a, hbelow⟩
  · intro ha
    obtain ⟨v, hvlabel, hvbelow⟩ :=
      (p.exists_label_below_iff a).2 ha
    have hv :
        taxonVertex T a = v :=
      GraphQuartet.PhyloTree.label_vertex_unique T
        (taxonVertex_label T a) hvlabel
    simpa [hv] using hvbelow

theorem not_reachable_of_below_not_below
    {T : Tree.PhyloTree X}
    (p : EdgePosition T)
    {x y : TreeAdequacy.PhyloTree.Vertex T}
    (hx : p.Below x) (hy : ¬p.Below y) :
    ¬((TreeAdequacy.PhyloTree.graph T).deleteEdges
      {s(p.parent, p.child)}).Reachable x y := by
  intro hxy
  have hchildX := p.reachable_of_below hx
  have hparentY := (p.parent_reachable_iff_not_below y).2 hy
  have hchildParent :=
    hchildX.trans (hxy.trans hparentY.symm)
  exact p.parent_not_below (p.below_of_reachable hchildParent)

/-- The unique simple path between two labelled vertices. -/
noncomputable def taxonPath
    (T : Tree.PhyloTree X) (a b : X) :
    (TreeAdequacy.PhyloTree.graph T).Walk
      (taxonVertex T a) (taxonVertex T b) :=
  Classical.choose
    ((TreeAdequacy.PhyloTree.graph_isTree T).existsUnique_path
      (taxonVertex T a) (taxonVertex T b))

theorem taxonPath_isPath
    (T : Tree.PhyloTree X) (a b : X) :
    (taxonPath T a b).IsPath :=
  (Classical.choose_spec
    ((TreeAdequacy.PhyloTree.graph_isTree T).existsUnique_path
      (taxonVertex T a) (taxonVertex T b))).1

/-- An edge occurring on the unique taxon path disconnects the two taxon
vertices when it is deleted.  This is the converse of
`Walk.mem_edges_of_not_reachable_deleteEdges`, specialized to a tree. -/
theorem not_reachable_delete_positionEdge_of_mem_taxonPath
    {T : Tree.PhyloTree X}
    (p : EdgePosition T) (a b : X)
    (hmem :
      (positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
        (taxonPath T a b).edges) :
    ¬((TreeAdequacy.PhyloTree.graph T).deleteEdges
      {(positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T))}).Reachable
        (taxonVertex T a) (taxonVertex T b) := by
  intro hreach
  rcases hreach with ⟨w⟩
  let wG : (TreeAdequacy.PhyloTree.graph T).Walk
      (taxonVertex T a) (taxonVertex T b) :=
    w.transfer (TreeAdequacy.PhyloTree.graph T) (fun e he =>
      SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _)
        (w.edges_subset_edgeSet he))
  have hpath :
      (wG.toPath :
          (TreeAdequacy.PhyloTree.graph T).Walk
            (taxonVertex T a) (taxonVertex T b)).IsPath :=
    wG.toPath.property
  have heq :
      taxonPath T a b =
        (wG.toPath :
          (TreeAdequacy.PhyloTree.graph T).Walk
            (taxonVertex T a) (taxonVertex T b)) :=
    (TreeAdequacy.PhyloTree.graph_isTree T).existsUnique_path
      (taxonVertex T a) (taxonVertex T b) |>.unique
        (taxonPath_isPath T a b) hpath
  have hmem' :
      (positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈ w.edges := by
    have hsub := wG.edges_toPath_subset_edges
    have hmemPath :
        (positionEdge p :
            Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
          (wG.toPath :
            (TreeAdequacy.PhyloTree.graph T).Walk
              (taxonVertex T a) (taxonVertex T b)).edges := by
      simpa [heq] using hmem
    have hmemWG :
        (positionEdge p :
            Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈ wG.edges :=
      hsub hmemPath
    simpa [wG, SimpleGraph.Walk.edges_transfer] using hmemWG
  have hedge := w.edges_subset_edgeSet hmem'
  simpa using hedge

/-- For a rooted edge of a tree, deleting that edge disconnects two vertices
exactly when one is below the edge and the other is not. -/
theorem not_reachable_delete_positionEdge_iff
    {T : Tree.PhyloTree X}
    (p : EdgePosition T)
    (x y : TreeAdequacy.PhyloTree.Vertex T) :
    ¬((TreeAdequacy.PhyloTree.graph T).deleteEdges
      {(positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T))}).Reachable x y ↔
      (p.Below x ↔ ¬p.Below y) := by
  change
    ¬((TreeAdequacy.PhyloTree.graph T).deleteEdges
      {s(p.parent, p.child)}).Reachable x y ↔
      (p.Below x ↔ ¬p.Below y)
  constructor
  · intro hnot
    constructor
    · intro hx hy
      exact hnot
        ((p.reachable_of_below hx).symm.trans
          (p.reachable_of_below hy))
    · intro hny
      by_contra hnx
      exact hnot
        (((p.parent_reachable_iff_not_below x).2 hnx).symm.trans
          ((p.parent_reachable_iff_not_below y).2 hny))
  · intro hopp hreach
    by_cases hx : p.Below x
    · have hy : ¬p.Below y := hopp.mp hx
      have hchildX := p.reachable_of_below hx
      have hparentY := (p.parent_reachable_iff_not_below y).2 hy
      have hchildParent :=
        hchildX.trans (hreach.trans hparentY.symm)
      exact p.parent_not_below (p.below_of_reachable hchildParent)
    · have hy : p.Below y := by
        by_contra hny
        exact hx (hopp.mpr hny)
      have hparentX := (p.parent_reachable_iff_not_below x).2 hx
      have hchildY := p.reachable_of_below hy
      have hparentChild :=
        hparentX.trans (hreach.trans hchildY.symm)
      exact p.parent_not_below
        (p.below_of_reachable hparentChild.symm)

/-- A rooted edge lies on the unique path between two taxa exactly when the
taxa lie on opposite sides of that edge. -/
theorem positionEdge_mem_taxonPath_iff
    {T : Tree.PhyloTree X}
    (p : EdgePosition T) (a b : X) :
    (positionEdge p :
        Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
        (taxonPath T a b).edges ↔
      (a ∈ p.cluster ↔ b ∉ p.cluster) := by
  constructor
  · intro hmem
    have hnot :=
      not_reachable_delete_positionEdge_of_mem_taxonPath p a b hmem
    have hopp :=
      (not_reachable_delete_positionEdge_iff p
        (taxonVertex T a) (taxonVertex T b)).mp hnot
    simpa only [taxonVertex_below_iff] using hopp
  · intro hopp
    have hnot :
        ¬((TreeAdequacy.PhyloTree.graph T).deleteEdges
          {(positionEdge p :
              Sym2 (TreeAdequacy.PhyloTree.Vertex T))}).Reachable
            (taxonVertex T a) (taxonVertex T b) := by
      apply (not_reachable_delete_positionEdge_iff p
        (taxonVertex T a) (taxonVertex T b)).2
      simpa only [taxonVertex_below_iff] using hopp
    exact (taxonPath T a b).mem_edges_of_not_reachable_deleteEdges hnot

/-- Every active edge lies on the unique path joining the first taxon of the
first positional pair to the first taxon of the opposite pair. -/
theorem positionEdge_mem_taxonPath_of_active
    (T : Tree.PhyloTree X)
    (q₁ q₂ q₃ q₄ : X)
    (e : ActiveEdge T q₁ q₂ q₃ q₄) :
    (positionEdge e.1.1 : Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
      (taxonPath T q₁ q₃).edges := by
  have hmem :
      Positional.Separates
        (ordinary T e.1).toSidePair.left
        (ordinary T e.1).toSidePair.right
        q₁ q₂ q₃ q₄ := by
    simpa only [activeEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using e.2
  have hsep :
      Positional.Separates e.1.1.cluster e.1.1.clusterᶜ
        q₁ q₂ q₃ q₄ := by
    simpa [activeEdges, ordinary, OrientedSplit.toSidePair,
      OrientedSplit.other] using hmem
  have hnot :
      ¬((TreeAdequacy.PhyloTree.graph T).deleteEdges
        {s(e.1.1.parent, e.1.1.child)}).Reachable
          (taxonVertex T q₁) (taxonVertex T q₃) := by
    rcases hsep with hforward | hreverse
    · exact not_reachable_of_below_not_below e.1.1
        ((taxonVertex_below_iff e.1.1 q₁).2 hforward.1)
        (by
          intro hbelow
          exact (Finset.mem_compl.mp hforward.2.2.1)
            ((taxonVertex_below_iff e.1.1 q₃).1 hbelow))
    · exact fun hreach =>
        not_reachable_of_below_not_below e.1.1
          ((taxonVertex_below_iff e.1.1 q₃).2 hreverse.2.2.1)
          (by
            intro hbelow
            exact (Finset.mem_compl.mp hreverse.1)
              ((taxonVertex_below_iff e.1.1 q₁).1 hbelow))
          hreach.symm
  exact (taxonPath T q₁ q₃).mem_edges_of_not_reachable_deleteEdges hnot

/-- The four cross paths are the exact path-theoretic description of an
active edge: an edge separates the first positional pair from the second if
and only if it occurs on every path joining one taxon of the first pair to one
taxon of the second. -/
theorem active_iff_mem_four_cross_paths
    (T : Tree.PhyloTree X)
    (q₁ q₂ q₃ q₄ : X)
    (e : RelevantEdge T) :
    e ∈ activeEdges T q₁ q₂ q₃ q₄ ↔
      (positionEdge e.1 :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
          (taxonPath T q₁ q₃).edges ∧
      (positionEdge e.1 :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
          (taxonPath T q₁ q₄).edges ∧
      (positionEdge e.1 :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
          (taxonPath T q₂ q₃).edges ∧
      (positionEdge e.1 :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
          (taxonPath T q₂ q₄).edges := by
  classical
  simp only [activeEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  have h13 := positionEdge_mem_taxonPath_iff e.1 q₁ q₃
  have h14 := positionEdge_mem_taxonPath_iff e.1 q₁ q₄
  have h23 := positionEdge_mem_taxonPath_iff e.1 q₂ q₃
  have h24 := positionEdge_mem_taxonPath_iff e.1 q₂ q₄
  change
    Positional.Separates e.1.cluster e.1.clusterᶜ q₁ q₂ q₃ q₄ ↔ _
  rw [h13, h14, h23, h24]
  constructor
  · rintro (h | h)
    · have hq₃ : q₃ ∉ e.1.cluster := Finset.mem_compl.mp h.2.2.1
      have hq₄ : q₄ ∉ e.1.cluster := Finset.mem_compl.mp h.2.2.2
      exact
        ⟨⟨fun _ => hq₃, fun _ => h.1⟩,
          ⟨fun _ => hq₄, fun _ => h.1⟩,
          ⟨fun _ => hq₃, fun _ => h.2.1⟩,
          ⟨fun _ => hq₄, fun _ => h.2.1⟩⟩
    · have hq₁ : q₁ ∉ e.1.cluster := Finset.mem_compl.mp h.1
      have hq₂ : q₂ ∉ e.1.cluster := Finset.mem_compl.mp h.2.1
      exact
        ⟨⟨fun hq₁' => False.elim (hq₁ hq₁'),
            fun hq₃' => False.elim (hq₃' h.2.2.1)⟩,
          ⟨fun hq₁' => False.elim (hq₁ hq₁'),
            fun hq₄' => False.elim (hq₄' h.2.2.2)⟩,
          ⟨fun hq₂' => False.elim (hq₂ hq₂'),
            fun hq₃' => False.elim (hq₃' h.2.2.1)⟩,
          ⟨fun hq₂' => False.elim (hq₂ hq₂'),
            fun hq₄' => False.elim (hq₄' h.2.2.2)⟩⟩
  · rintro ⟨h13, h14, h23, h24⟩
    by_cases hq₁ : q₁ ∈ e.1.cluster
    · have hq₃ : q₃ ∉ e.1.cluster := h13.mp hq₁
      have hq₄ : q₄ ∉ e.1.cluster := h14.mp hq₁
      have hq₂ : q₂ ∈ e.1.cluster := h23.mpr hq₃
      exact Or.inl
        ⟨hq₁, hq₂, Finset.mem_compl.mpr hq₃,
          Finset.mem_compl.mpr hq₄⟩
    · have hq₃ : q₃ ∈ e.1.cluster := by
        by_contra hq₃
        exact hq₁ (h13.mpr hq₃)
      have hq₄ : q₄ ∈ e.1.cluster := by
        by_contra hq₄
        exact hq₁ (h14.mpr hq₄)
      have hq₂ : q₂ ∉ e.1.cluster := by
        intro hq₂
        exact (h23.mp hq₂) hq₃
      exact Or.inr
        ⟨Finset.mem_compl.mpr hq₁, Finset.mem_compl.mpr hq₂,
          hq₃, hq₄⟩

/-- The component side of an edge that contains the first positional taxon. -/
noncomputable def firstSide
    {T : Tree.PhyloTree X}
    (p : EdgePosition T) (q₁ : X) : Finset X :=
  if q₁ ∈ p.cluster then p.cluster else p.clusterᶜ

@[simp] theorem mem_firstSide
    {T : Tree.PhyloTree X}
    (p : EdgePosition T) (q₁ : X) :
    q₁ ∈ firstSide p q₁ := by
  classical
  by_cases h : q₁ ∈ p.cluster <;> simp [firstSide, h]

theorem active_firstSide_membership
    (T : Tree.PhyloTree X)
    (q₁ q₂ q₃ q₄ : X)
    (e : ActiveEdge T q₁ q₂ q₃ q₄) :
    q₂ ∈ firstSide e.1.1 q₁ ∧
      q₃ ∉ firstSide e.1.1 q₁ ∧
      q₄ ∉ firstSide e.1.1 q₁ := by
  classical
  have hmem :
      Positional.Separates
        (ordinary T e.1).toSidePair.left
        (ordinary T e.1).toSidePair.right
        q₁ q₂ q₃ q₄ := by
    simpa only [activeEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using e.2
  have hsep :
      Positional.Separates e.1.1.cluster e.1.1.clusterᶜ
        q₁ q₂ q₃ q₄ := by
    simpa [ordinary, OrientedSplit.toSidePair,
      OrientedSplit.other] using hmem
  rcases hsep with hforward | hreverse
  · simp [firstSide, hforward.1, hforward.2.1,
      Finset.mem_compl.mp hforward.2.2.1,
      Finset.mem_compl.mp hforward.2.2.2]
  · have hq₁ : q₁ ∉ e.1.1.cluster :=
      Finset.mem_compl.mp hreverse.1
    have hq₂ : q₂ ∉ e.1.1.cluster :=
      Finset.mem_compl.mp hreverse.2.1
    simp [firstSide, hq₁, hq₂, hreverse.2.2.1,
      hreverse.2.2.2]

/-- Root-facing sides of two active edges are nested.  This is the rooted
laminar formulation of the fact that all active edges lie on one line. -/
theorem firstSide_comparable_of_active
    (T : Tree.PhyloTree X)
    (q₁ q₂ q₃ q₄ : X)
    (e f : ActiveEdge T q₁ q₂ q₃ q₄) :
    firstSide e.1.1 q₁ ⊆ firstSide f.1.1 q₁ ∨
      firstSide f.1.1 q₁ ⊆ firstSide e.1.1 q₁ := by
  classical
  have he := active_firstSide_membership T q₁ q₂ q₃ q₄ e
  have hf := active_firstSide_membership T q₁ q₂ q₃ q₄ f
  rcases e.1.1.clusters_laminar f.1.1 with hef | hfe | hdisj
  · by_cases he₁ : q₁ ∈ e.1.1.cluster
    · by_cases hf₁ : q₁ ∈ f.1.1.cluster
      · exact Or.inl (by simpa [firstSide, he₁, hf₁] using hef)
      · exact False.elim (hf₁ (hef he₁))
    · by_cases hf₁ : q₁ ∈ f.1.1.cluster
      · have heq₃ : q₃ ∈ e.1.1.cluster := by
          have h := he.2.1
          simpa [firstSide, he₁] using h
        have hfq₃ : q₃ ∉ f.1.1.cluster := by
          have h := hf.2.1
          simpa [firstSide, hf₁] using h
        exact False.elim (hfq₃ (hef heq₃))
      · exact Or.inr (by
          simpa [firstSide, he₁, hf₁] using
            (Finset.compl_subset_compl.mpr hef))
  · by_cases he₁ : q₁ ∈ e.1.1.cluster
    · by_cases hf₁ : q₁ ∈ f.1.1.cluster
      · exact Or.inr (by simpa [firstSide, he₁, hf₁] using hfe)
      · have heq₃ : q₃ ∉ e.1.1.cluster := by
          have h := he.2.1
          simpa [firstSide, he₁] using h
        have hfq₃ : q₃ ∈ f.1.1.cluster := by
          have h := hf.2.1
          simpa [firstSide, hf₁] using h
        exact False.elim (heq₃ (hfe hfq₃))
    · by_cases hf₁ : q₁ ∈ f.1.1.cluster
      · exact False.elim (he₁ (hfe hf₁))
      · exact Or.inl (by
          simpa [firstSide, he₁, hf₁] using
            (Finset.compl_subset_compl.mpr hfe))
  · by_cases he₁ : q₁ ∈ e.1.1.cluster
    · by_cases hf₁ : q₁ ∈ f.1.1.cluster
      · exact False.elim
          (Finset.disjoint_left.mp hdisj he₁ hf₁)
      · exact Or.inl (by
          simpa [firstSide, he₁, hf₁] using
            (Finset.subset_compl_iff_disjoint_right.mpr hdisj))
    · by_cases hf₁ : q₁ ∈ f.1.1.cluster
      · exact Or.inr (by
          simpa [firstSide, he₁, hf₁] using
            (Finset.subset_compl_iff_disjoint_left.mpr hdisj))
      · have heq₃ : q₃ ∈ e.1.1.cluster := by
          have h := he.2.1
          simpa [firstSide, he₁] using h
        have hfq₃ : q₃ ∈ f.1.1.cluster := by
          have h := hf.2.1
          simpa [firstSide, hf₁] using h
        exact False.elim
          (Finset.disjoint_left.mp hdisj heq₃ hfq₃)

end

end TreeEdgeGeometry

end QuartetV060
