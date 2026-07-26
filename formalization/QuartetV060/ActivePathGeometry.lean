import QuartetV060.PathLineGraph

/-!
# The common-path geometry of active quartet edges

For an ordered quartet `q₁ q₂ | q₃ q₄`, an edge is active exactly when it lies
on all four cross paths.  This file packages that intersection as an ambient
subgraph and proves the geometric facts needed to identify the active-edge
adjacency graph with the line graph of that common path segment.
-/

namespace QuartetV060

namespace ActivePathGeometry

open QuartetDistance PhyloOccurrences TreeKernel TreePathCounting
  TreeEdgeGeometry PathLineGraph
open SimpleGraph

noncomputable section

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

abbrev GraphOf (T : Tree.PhyloTree X) :=
  TreeAdequacy.PhyloTree.graph T

/-- The ambient subgraph traced by the unique taxon path from `a` to `b`. -/
def crossPathSubgraph (T : Tree.PhyloTree X) (a b : X) :
    (GraphOf T).Subgraph :=
  (taxonPath T a b).toSubgraph

/-- The common edge-and-vertex segment of the four cross paths belonging to
the ordered pairing `q₁ q₂ | q₃ q₄`. -/
def activePathSubgraph
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    (GraphOf T).Subgraph :=
  (((crossPathSubgraph T q₁ q₃ ⊓ crossPathSubgraph T q₁ q₄) ⊓
      crossPathSubgraph T q₂ q₃) ⊓
    crossPathSubgraph T q₂ q₄)

/-- For a relevant edge, membership in the common cross-path subgraph is
exactly the manuscript's active-edge condition. -/
theorem positionEdge_mem_activePathSubgraph_iff
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) (e : RelevantEdge T) :
    (positionEdge e.1 : Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
        (activePathSubgraph T q₁ q₂ q₃ q₄).edgeSet ↔
      e ∈ activeEdges T q₁ q₂ q₃ q₄ := by
  rw [active_iff_mem_four_cross_paths]
  simp only [activePathSubgraph, crossPathSubgraph,
    SimpleGraph.Subgraph.edgeSet_inf, Set.mem_inter_iff,
    SimpleGraph.Walk.mem_edges_toSubgraph]
  tauto

/-- If at least one active edge exists, the common cross-path subgraph is
connected.  The witness edge supplies a common vertex at each successive
intersection. -/
theorem activePathSubgraph_connected_of_active
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (e : ActiveEdge T q₁ q₂ q₃ q₄) :
    (activePathSubgraph T q₁ q₂ q₃ q₄).Connected := by
  have hpaths :=
    (active_iff_mem_four_cross_paths T q₁ q₂ q₃ q₄ e.1).mp e.2
  have h13 : (crossPathSubgraph T q₁ q₃).Adj
      e.1.1.parent e.1.1.child :=
    (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).2 hpaths.1
  have h14 : (crossPathSubgraph T q₁ q₄).Adj
      e.1.1.parent e.1.1.child :=
    (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).2 hpaths.2.1
  have h23 : (crossPathSubgraph T q₂ q₃).Adj
      e.1.1.parent e.1.1.child :=
    (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).2 hpaths.2.2.1
  have h24 : (crossPathSubgraph T q₂ q₄).Adj
      e.1.1.parent e.1.1.child :=
    (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).2 hpaths.2.2.2
  have h12 :
      (crossPathSubgraph T q₁ q₃ ⊓
        crossPathSubgraph T q₁ q₄).Connected :=
    connected_inf_of_isTree (TreeAdequacy.PhyloTree.graph_isTree T)
      (taxonPath T q₁ q₃).toSubgraph_connected
      (taxonPath T q₁ q₄).toSubgraph_connected
      ⟨e.1.1.parent, h13.fst_mem, h14.fst_mem⟩
  have h123 :
      ((crossPathSubgraph T q₁ q₃ ⊓
          crossPathSubgraph T q₁ q₄) ⊓
        crossPathSubgraph T q₂ q₃).Connected :=
    connected_inf_of_isTree (TreeAdequacy.PhyloTree.graph_isTree T)
      h12 (taxonPath T q₂ q₃).toSubgraph_connected
      ⟨e.1.1.parent, ⟨h13.fst_mem, h14.fst_mem⟩, h23.fst_mem⟩
  exact connected_inf_of_isTree
    (TreeAdequacy.PhyloTree.graph_isTree T)
    h123 (taxonPath T q₂ q₄).toSubgraph_connected
    ⟨e.1.1.parent,
      ⟨⟨h13.fst_mem, h14.fst_mem⟩, h23.fst_mem⟩, h24.fst_mem⟩

theorem two_le_card_of_mem_mem
    {s : Finset X} {a b : X}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    2 ≤ s.card := by
  have hlt : 1 < s.card :=
    Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  omega

/-- When the two labels on each side are distinct, every edge in the common
cross-path subgraph has at least two taxa on both sides and hence is relevant.
The distinctness assumptions are necessary: a repeated label can leave a
pendant edge in all four cross paths. -/
theorem edgePosition_relevant_of_mem_activePathSubgraph
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄)
    (p : EdgePosition T)
    (hp : (positionEdge p :
        Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
      (activePathSubgraph T q₁ q₂ q₃ q₄).edgeSet) :
    2 ≤ p.cluster.card ∧ 2 ≤ p.clusterᶜ.card := by
  have hpaths :
      (((positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
            (taxonPath T q₁ q₃).edges ∧
        (positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
            (taxonPath T q₁ q₄).edges) ∧
        (positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
            (taxonPath T q₂ q₃).edges) ∧
        (positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
            (taxonPath T q₂ q₄).edges := by
    simpa only [activePathSubgraph, crossPathSubgraph,
      SimpleGraph.Subgraph.edgeSet_inf, Set.mem_inter_iff,
      SimpleGraph.Walk.mem_edges_toSubgraph] using hp
  have h13 :=
    (positionEdge_mem_taxonPath_iff p q₁ q₃).mp hpaths.1.1.1
  have h14 :=
    (positionEdge_mem_taxonPath_iff p q₁ q₄).mp hpaths.1.1.2
  have h23 :=
    (positionEdge_mem_taxonPath_iff p q₂ q₃).mp hpaths.1.2
  by_cases hq₁ : q₁ ∈ p.cluster
  · have hq₃ : q₃ ∉ p.cluster := h13.mp hq₁
    have hq₄ : q₄ ∉ p.cluster := h14.mp hq₁
    have hq₂ : q₂ ∈ p.cluster := h23.mpr hq₃
    exact
      ⟨two_le_card_of_mem_mem hq₁ hq₂ hq12,
        two_le_card_of_mem_mem
          (Finset.mem_compl.mpr hq₃)
          (Finset.mem_compl.mpr hq₄) hq34⟩
  · have hq₃ : q₃ ∈ p.cluster := by
      by_contra hq₃
      exact hq₁ (h13.mpr hq₃)
    have hq₄ : q₄ ∈ p.cluster := by
      by_contra hq₄
      exact hq₁ (h14.mpr hq₄)
    have hq₂ : q₂ ∉ p.cluster := by
      intro hq₂
      exact (h23.mp hq₂) hq₃
    exact
      ⟨two_le_card_of_mem_mem hq₃ hq₄ hq34,
        two_le_card_of_mem_mem
          (Finset.mem_compl.mpr hq₁)
          (Finset.mem_compl.mpr hq₂) hq12⟩

/-- Send an active relevant edge to its occurrence as an ambient edge in the
common cross-path subgraph. -/
def activeEdgeToCommonEdge
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (e : ActiveEdge T q₁ q₂ q₃ q₄) :
    (activePathSubgraph T q₁ q₂ q₃ q₄).edgeSet :=
  ⟨positionEdge e.1.1,
    (positionEdge_mem_activePathSubgraph_iff
      T q₁ q₂ q₃ q₄ e.1).2 e.2⟩

theorem activeEdgeToCommonEdge_injective
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    Function.Injective
      (activeEdgeToCommonEdge T q₁ q₂ q₃ q₄) := by
  intro e f hef
  apply Subtype.ext
  apply Subtype.ext
  apply positionEdge_injective
  apply Subtype.ext
  exact Subtype.mk.inj hef

theorem activeEdgeToCommonEdge_surjective
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    Function.Surjective
      (activeEdgeToCommonEdge T q₁ q₂ q₃ q₄) := by
  intro e
  let eg : (GraphOf T).edgeSet :=
    ⟨e.1,
      (activePathSubgraph T q₁ q₂ q₃ q₄).edgeSet_subset e.2⟩
  let p : EdgePosition T :=
    (edgePositionEquivEdgeSet T).symm eg
  have hpedge : positionEdge p = eg :=
    (edgePositionEquivEdgeSet T).apply_symm_apply eg
  have hpmem :
      (positionEdge p :
        Sym2 (TreeAdequacy.PhyloTree.Vertex T)) ∈
        (activePathSubgraph T q₁ q₂ q₃ q₄).edgeSet := by
    rw [show (positionEdge p :
          Sym2 (TreeAdequacy.PhyloTree.Vertex T)) = e.1 by
      exact congrArg Subtype.val hpedge]
    exact e.2
  let r : RelevantEdge T :=
    ⟨p, edgePosition_relevant_of_mem_activePathSubgraph
      T q₁ q₂ q₃ q₄ hq12 hq34 p hpmem⟩
  have hractive : r ∈ activeEdges T q₁ q₂ q₃ q₄ :=
    (positionEdge_mem_activePathSubgraph_iff
      T q₁ q₂ q₃ q₄ r).1 hpmem
  refine ⟨⟨r, hractive⟩, ?_⟩
  apply Subtype.ext
  change (positionEdge p).1 = e.1
  exact congrArg Subtype.val hpedge

/-- Under pairwise distinctness within each displayed side, active relevant
edges are exactly all edges of the common cross-path subgraph. -/
noncomputable def activeEdgeEquivCommonEdge
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    ActiveEdge T q₁ q₂ q₃ q₄ ≃
      (activePathSubgraph T q₁ q₂ q₃ q₄).edgeSet :=
  Equiv.ofBijective
    (activeEdgeToCommonEdge T q₁ q₂ q₃ q₄)
    ⟨activeEdgeToCommonEdge_injective T q₁ q₂ q₃ q₄,
      activeEdgeToCommonEdge_surjective
        T q₁ q₂ q₃ q₄ hq12 hq34⟩

/-- Regard an edge of a subgraph's coefficient graph as an edge of the ambient
graph. -/
def coeEdgeAmbientMap
    {V : Type} {G : SimpleGraph V}
    (H : G.Subgraph) (e : H.coe.edgeSet) :
    G.edgeSet :=
  ⟨(coeEdgeMap H e).1,
    H.edgeSet_subset (coeEdgeMap H e).2⟩

theorem coeEdgeAmbientMap_injective
    {V : Type} {G : SimpleGraph V}
    (H : G.Subgraph) :
    Function.Injective (coeEdgeAmbientMap H) := by
  intro e f hef
  apply coeEdgeMap_injective H
  apply Subtype.ext
  exact Subtype.mk.inj hef

/-- Passing between a coefficient-graph edge and its ambient edge preserves
and reflects line-graph adjacency. -/
theorem coeEdgeAmbientMap_lineGraph_adj_iff
    {V : Type} {G : SimpleGraph V}
    (H : G.Subgraph) (e f : H.coe.edgeSet) :
    G.lineGraph.Adj
        (coeEdgeAmbientMap H e) (coeEdgeAmbientMap H f) ↔
      H.coe.lineGraph.Adj e f := by
  rw [SimpleGraph.lineGraph_adj_iff_exists,
    SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hve, hvf⟩
    have hne' : e ≠ f := by
      intro hef
      exact hne (congrArg (coeEdgeAmbientMap H) hef)
    change v ∈
      Sym2.map (fun x : H.verts => (x : V)) e.1 at hve
    change v ∈
      Sym2.map (fun x : H.verts => (x : V)) f.1 at hvf
    rw [Sym2.mem_map] at hve hvf
    rcases hve with ⟨x, hxe, hxv⟩
    rcases hvf with ⟨y, hyf, hyv⟩
    have hxy : x = y :=
      Subtype.ext (hxv.trans hyv.symm)
    exact ⟨hne', x, hxe, hxy ▸ hyf⟩
  · rintro ⟨hne, v, hve, hvf⟩
    refine
      ⟨fun h => hne (coeEdgeAmbientMap_injective H h),
        (v : V), ?_, ?_⟩
    · change (v : V) ∈
        Sym2.map (fun x : H.verts => (x : V)) e.1
      exact Sym2.mem_map.mpr ⟨v, hve, rfl⟩
    · change (v : V) ∈
        Sym2.map (fun x : H.verts => (x : V)) f.1
      exact Sym2.mem_map.mpr ⟨v, hvf, rfl⟩

/-- The preceding ambient-edge equivalence, expressed using the actual edge
type of the common subgraph's coefficient graph. -/
noncomputable def activeEdgeEquivCommonCoeEdge
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    ActiveEdge T q₁ q₂ q₃ q₄ ≃
      (activePathSubgraph T q₁ q₂ q₃ q₄).coe.edgeSet :=
  (activeEdgeEquivCommonEdge
      T q₁ q₂ q₃ q₄ hq12 hq34).trans
    (coeEdgeEquiv
      (activePathSubgraph T q₁ q₂ q₃ q₄)).symm

theorem coeEdgeAmbientMap_activeEdgeEquivCommonCoeEdge
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄)
    (e : ActiveEdge T q₁ q₂ q₃ q₄) :
    coeEdgeAmbientMap (activePathSubgraph T q₁ q₂ q₃ q₄)
        (activeEdgeEquivCommonCoeEdge
          T q₁ q₂ q₃ q₄ hq12 hq34 e) =
      positionEdge e.1.1 := by
  apply Subtype.ext
  have h :=
    (coeEdgeEquiv
      (activePathSubgraph T q₁ q₂ q₃ q₄)).apply_symm_apply
      (activeEdgeToCommonEdge T q₁ q₂ q₃ q₄ e)
  exact Subtype.mk.inj h

/-- The active-edge adjacency graph is not merely equinumerous with the common
path segment: it is graph-isomorphic to that segment's line graph. -/
noncomputable def activeAdjGraphIsoCommonLineGraph
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    activeAdjGraph T q₁ q₂ q₃ q₄ ≃g
      (activePathSubgraph T q₁ q₂ q₃ q₄).coe.lineGraph where
  toEquiv :=
    activeEdgeEquivCommonCoeEdge
      T q₁ q₂ q₃ q₄ hq12 hq34
  map_rel_iff' := by
    intro e f
    rw [← coeEdgeAmbientMap_lineGraph_adj_iff]
    rw [coeEdgeAmbientMap_activeEdgeEquivCommonCoeEdge,
      coeEdgeAmbientMap_activeEdgeEquivCommonCoeEdge]
    exact
      (edgeAdjacent_iff_lineGraph_adj e.1.1 f.1.1).symm

theorem activePathSubgraph_le_crossPath13
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    activePathSubgraph T q₁ q₂ q₃ q₄ ≤
      crossPathSubgraph T q₁ q₃ := by
  unfold activePathSubgraph
  exact inf_le_left.trans (inf_le_left.trans inf_le_left)

/-- The common segment's line graph is acyclic because it injects into the
line graph of the simple path from `q₁` to `q₃`. -/
theorem activePathLineGraph_isAcyclic
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    (activePathSubgraph
      T q₁ q₂ q₃ q₄).coe.lineGraph.IsAcyclic := by
  let hle :
      activePathSubgraph T q₁ q₂ q₃ q₄ ≤
        crossPathSubgraph T q₁ q₃ :=
    activePathSubgraph_le_crossPath13 T q₁ q₂ q₃ q₄
  let f :
      (activePathSubgraph T q₁ q₂ q₃ q₄).coe →g
        (crossPathSubgraph T q₁ q₃).coe :=
    SimpleGraph.Subgraph.inclusion hle
  exact lineGraph_isAcyclic_of_injectiveHom f
    (SimpleGraph.Subgraph.inclusion.injective hle)
    (lineGraph_toSubgraph_isAcyclic
      (taxonPath_isPath T q₁ q₃))

theorem activePathLineGraph_connected_of_active
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄)
    (e : ActiveEdge T q₁ q₂ q₃ q₄) :
    (activePathSubgraph
      T q₁ q₂ q₃ q₄).coe.lineGraph.Connected := by
  apply lineGraph_connected
  · exact
      (activePathSubgraph_connected_of_active
        T q₁ q₂ q₃ q₄ e).coe
  · exact
      ⟨(activeEdgeEquivCommonCoeEdge
          T q₁ q₂ q₃ q₄ hq12 hq34 e).1,
        (activeEdgeEquivCommonCoeEdge
          T q₁ q₂ q₃ q₄ hq12 hq34 e).2⟩

/-- A nonempty active-edge graph is a tree.  This is the precise graph-theory
closure behind the manuscript's statement that active relevant edges form one
contiguous path. -/
theorem activeAdjGraph_isTree_of_active
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄)
    (e : ActiveEdge T q₁ q₂ q₃ q₄) :
    (activeAdjGraph T q₁ q₂ q₃ q₄).IsTree := by
  apply
    (activeAdjGraphIsoCommonLineGraph
      T q₁ q₂ q₃ q₄ hq12 hq34).isTree_iff.mpr
  exact
    ⟨activePathLineGraph_connected_of_active
        T q₁ q₂ q₃ q₄ hq12 hq34 e,
      activePathLineGraph_isAcyclic T q₁ q₂ q₃ q₄⟩

/-- A nonempty common path has manuscript weight one. -/
theorem pathWeight_eq_one_of_activeEdges_nonempty
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄)
    (hne : (activeEdges T q₁ q₂ q₃ q₄).Nonempty) :
    pathWeight T q₁ q₂ q₃ q₄ = 1 := by
  rcases hne with ⟨e, he⟩
  exact pathWeight_eq_one_of_activeAdjGraph_isTree
    T q₁ q₂ q₃ q₄
    (activeAdjGraph_isTree_of_active
      T q₁ q₂ q₃ q₄ hq12 hq34 ⟨e, he⟩)

/-- For distinct labels within each displayed side, a positional path weight
is exactly zero or one. -/
theorem pathWeight_eq_zero_or_one
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    pathWeight T q₁ q₂ q₃ q₄ = 0 ∨
      pathWeight T q₁ q₂ q₃ q₄ = 1 := by
  classical
  by_cases h : activeEdges T q₁ q₂ q₃ q₄ = ∅
  · exact Or.inl
      (pathWeight_eq_zero_of_activeEdges_eq_empty
        T q₁ q₂ q₃ q₄ h)
  · exact Or.inr
      (pathWeight_eq_one_of_activeEdges_nonempty
        T q₁ q₂ q₃ q₄ hq12 hq34
        (Finset.nonempty_iff_ne_empty.mpr h))

/-- The value one occurs exactly when at least one relevant edge separates the
two displayed pairs. -/
theorem pathWeight_eq_one_iff_activeEdges_nonempty
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    pathWeight T q₁ q₂ q₃ q₄ = 1 ↔
      (activeEdges T q₁ q₂ q₃ q₄).Nonempty := by
  constructor
  · intro hweight
    by_contra hne
    have hempty : activeEdges T q₁ q₂ q₃ q₄ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero :=
      pathWeight_eq_zero_of_activeEdges_eq_empty
        T q₁ q₂ q₃ q₄ hempty
    linarith
  · exact pathWeight_eq_one_of_activeEdges_nonempty
      T q₁ q₂ q₃ q₄ hq12 hq34

/-- The direct graph-theoretic statement that one edge displays the ordered
pairing `q₁ q₂ | q₃ q₄`.  This is symmetric under exchange of the two sides. -/
def DisplaysPair
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) : Prop :=
  GraphQuartet.EdgeSeparates
    (TreeAdequacy.PhyloTree.graph T)
    (TreeAdequacy.PhyloTree.label? T)
    {q₁, q₂} {q₃, q₄}

/-- A displayed pair exists exactly when the active-edge set is nonempty.
Both directions retain the actual separating edge; no quartet-topology
uniqueness theorem is used here. -/
theorem activeEdges_nonempty_iff_displaysPair
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    (activeEdges T q₁ q₂ q₃ q₄).Nonempty ↔
      DisplaysPair T q₁ q₂ q₃ q₄ := by
  classical
  constructor
  · rintro ⟨e, he⟩
    have hsep :
        Positional.Separates e.1.cluster e.1.clusterᶜ
          q₁ q₂ q₃ q₄ := by
      simpa [activeEdges, ordinary,
        OrientedSplit.toSidePair, OrientedSplit.other] using he
    apply
      (GraphQuartet.PhyloTree.edgeSeparates_iff_exists_position_cluster
        T {q₁, q₂} {q₃, q₄}).mpr
    refine ⟨e.1, ?_⟩
    rcases hsep with hforward | hreverse
    · left
      constructor
      · intro a ha
        simp only [Finset.mem_insert,
          Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hforward.1
        · exact hforward.2.1
      · intro b hb
        simp only [Finset.mem_insert,
          Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact Finset.mem_compl.mp hforward.2.2.1
        · exact Finset.mem_compl.mp hforward.2.2.2
    · right
      constructor
      · intro b hb
        simp only [Finset.mem_insert,
          Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hreverse.2.2.1
        · exact hreverse.2.2.2
      · intro a ha
        simp only [Finset.mem_insert,
          Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact Finset.mem_compl.mp hreverse.1
        · exact Finset.mem_compl.mp hreverse.2.1
  · intro hdisplay
    obtain ⟨p, hp | hp⟩ :=
      (GraphQuartet.PhyloTree.edgeSeparates_iff_exists_position_cluster
        T {q₁, q₂} {q₃, q₄}).mp hdisplay
    · have hq₁ : q₁ ∈ p.cluster :=
        hp.1 q₁ (by simp)
      have hq₂ : q₂ ∈ p.cluster :=
        hp.1 q₂ (by simp)
      have hq₃ : q₃ ∉ p.cluster :=
        hp.2 q₃ (by simp)
      have hq₄ : q₄ ∉ p.cluster :=
        hp.2 q₄ (by simp)
      let e : RelevantEdge T :=
        ⟨p,
          ⟨two_le_card_of_mem_mem hq₁ hq₂ hq12,
            two_le_card_of_mem_mem
              (Finset.mem_compl.mpr hq₃)
              (Finset.mem_compl.mpr hq₄) hq34⟩⟩
      refine ⟨e, ?_⟩
      simp only [activeEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      change Positional.Separates p.cluster p.clusterᶜ
        q₁ q₂ q₃ q₄
      exact Or.inl
        ⟨hq₁, hq₂, Finset.mem_compl.mpr hq₃,
          Finset.mem_compl.mpr hq₄⟩
    · have hq₃ : q₃ ∈ p.cluster :=
        hp.1 q₃ (by simp)
      have hq₄ : q₄ ∈ p.cluster :=
        hp.1 q₄ (by simp)
      have hq₁ : q₁ ∉ p.cluster :=
        hp.2 q₁ (by simp)
      have hq₂ : q₂ ∉ p.cluster :=
        hp.2 q₂ (by simp)
      let e : RelevantEdge T :=
        ⟨p,
          ⟨two_le_card_of_mem_mem hq₃ hq₄ hq34,
            two_le_card_of_mem_mem
              (Finset.mem_compl.mpr hq₁)
              (Finset.mem_compl.mpr hq₂) hq12⟩⟩
      refine ⟨e, ?_⟩
      simp only [activeEdges, Finset.mem_filter,
        Finset.mem_univ, true_and]
      change Positional.Separates p.cluster p.clusterᶜ
        q₁ q₂ q₃ q₄
      exact Or.inr
        ⟨Finset.mem_compl.mpr hq₁,
          Finset.mem_compl.mpr hq₂, hq₃, hq₄⟩

/-- On the intended distinct-within-side domain, path weight one is exactly
the direct delete-edge displayed-pair predicate. -/
theorem pathWeight_eq_one_iff_displaysPair
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    pathWeight T q₁ q₂ q₃ q₄ = 1 ↔
      DisplaysPair T q₁ q₂ q₃ q₄ :=
  (pathWeight_eq_one_iff_activeEdges_nonempty
    T q₁ q₂ q₃ q₄ hq12 hq34).trans
      (activeEdges_nonempty_iff_displaysPair
        T q₁ q₂ q₃ q₄ hq12 hq34)

end

end ActivePathGeometry

end QuartetV060
