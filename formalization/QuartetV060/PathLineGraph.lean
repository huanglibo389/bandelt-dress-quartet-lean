import QuartetV060.TreeEdgeGeometry
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Intersections of paths and their line graphs

This file supplies the finite graph theory needed by the manuscript's
active-edge count.  It proves three facts without appealing to the quartet
semantics:

* nonempty intersections of connected subgraphs of a tree are connected;
* the line graph of a connected graph with at least one edge is connected;
* the line graph of the subgraph traced by a simple path is acyclic.

Together these facts turn a nonempty common edge segment of several paths
into a tree whose vertices are the edges of that segment.
-/

namespace QuartetV060

namespace PathLineGraph

open SimpleGraph

noncomputable section

/-- In a tree, a nonempty intersection of two connected subgraphs remains
connected.  Both subgraph paths reduce to the same unique ambient path. -/
theorem connected_inf_of_isTree
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V}
    (hG : G.IsTree) {H K : G.Subgraph}
    (hH : H.Connected) (hK : K.Connected)
    (hne : (H ⊓ K).verts.Nonempty) :
    (H ⊓ K).Connected := by
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  refine ⟨hne, ?_⟩
  intro u v hu hv
  have huH : u ∈ H.verts := hu.1
  have hvH : v ∈ H.verts := hv.1
  have huK : u ∈ K.verts := hu.2
  have hvK : v ∈ K.verts := hv.2
  obtain ⟨pH, hpH⟩ :=
    (Subgraph.preconnected_iff_forall_exists_walk_subgraph H).mp
      hH.preconnected huH hvH
  obtain ⟨pK, hpK⟩ :=
    (Subgraph.preconnected_iff_forall_exists_walk_subgraph K).mp
      hK.preconnected huK hvK
  have heq : pH.toPath = pK.toPath :=
    hG.isAcyclic.path_unique pH.toPath pK.toPath
  refine ⟨(pH.toPath : G.Walk u v), ?_⟩
  apply le_inf
  · exact SimpleGraph.Walk.toSubgraph_bypass_le_toSubgraph.trans hpH
  · rw [heq]
    exact SimpleGraph.Walk.toSubgraph_bypass_le_toSubgraph.trans hpK

private theorem edgeReachable_of_walk
    {V : Type} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v)
    (e f : G.edgeSet)
    (hu : u ∈ (e : Sym2 V))
    (hv : v ∈ (f : Sym2 V)) :
    G.lineGraph.Reachable e f := by
  induction p generalizing e f with
  | nil =>
      by_cases hef : e = f
      · subst f
        exact .refl e
      · exact
          (SimpleGraph.lineGraph_adj_iff_exists.mpr
            ⟨hef, _, hu, hv⟩).reachable
  | @cons u w v h p ih =>
      let g : G.edgeSet := ⟨s(u, w), h⟩
      have heg : G.lineGraph.Reachable e g := by
        by_cases heg : e = g
        · exact heg ▸ .refl e
        · exact
            (SimpleGraph.lineGraph_adj_iff_exists.mpr
              ⟨heg, u, hu, by simp [g]⟩).reachable
      exact heg.trans (ih g f (by simp [g]) hv)

/-- The line graph of a connected graph with a nonempty edge set is
connected. -/
theorem lineGraph_connected
    {V : Type} {G : SimpleGraph V}
    (hG : G.Connected) (hne : G.edgeSet.Nonempty) :
    G.lineGraph.Connected := by
  letI : Nonempty G.edgeSet := hne.to_subtype
  refine ⟨?_⟩
  intro e f
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      rcases f with ⟨f, hf⟩
      induction f using Sym2.inductionOn with
      | _ z w =>
          rcases hG.preconnected x z with ⟨p⟩
          exact edgeReachable_of_walk p
            ⟨s(x, y), he⟩ ⟨s(z, w), hf⟩ (by simp) (by simp)

/-- An injective graph homomorphism induces a graph homomorphism between the
corresponding line graphs.  Its vertices are mapped by the induced edge map. -/
def lineGraphHomOfInjectiveHom
    {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') (hinj : Function.Injective f) :
    G.lineGraph →g G'.lineGraph where
  toFun := f.mapEdgeSet
  map_rel' := by
    intro e g heg
    rw [SimpleGraph.lineGraph_adj_iff_exists] at heg ⊢
    rcases heg with ⟨hne, v, hve, hvg⟩
    refine
      ⟨fun h =>
          hne (SimpleGraph.Hom.mapEdgeSet.injective f hinj h),
        f v, ?_, ?_⟩
    · change f v ∈ Sym2.map f e.1
      exact Sym2.mem_map.mpr ⟨v, hve, rfl⟩
    · change f v ∈ Sym2.map f g.1
      exact Sym2.mem_map.mpr ⟨v, hvg, rfl⟩

theorem lineGraphHomOfInjectiveHom_injective
    {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') (hinj : Function.Injective f) :
    Function.Injective (lineGraphHomOfInjectiveHom f hinj) :=
  SimpleGraph.Hom.mapEdgeSet.injective f hinj

/-- A line graph that injects homomorphically into an acyclic line graph is
itself acyclic. -/
theorem lineGraph_isAcyclic_of_injectiveHom
    {V W : Type} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') (hinj : Function.Injective f)
    (hG' : G'.lineGraph.IsAcyclic) :
    G.lineGraph.IsAcyclic :=
  hG'.comap (lineGraphHomOfInjectiveHom f hinj)
    (lineGraphHomOfInjectiveHom_injective f hinj)

/-- Forget the subtype wrappers on the endpoints of an edge of a subgraph. -/
def coeEdgeMap
    {V : Type} {G : SimpleGraph V}
    (H : G.Subgraph) (e : H.coe.edgeSet) :
    H.edgeSet :=
  ⟨Sym2.map (fun x : H.verts => (x : V)) e.1, by
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        change s((x : V), (y : V)) ∈ H.edgeSet
        exact (SimpleGraph.Subgraph.mem_edgeSet).2 he⟩

theorem coeEdgeMap_injective
    {V : Type} {G : SimpleGraph V}
    (H : G.Subgraph) :
    Function.Injective (coeEdgeMap H) := by
  intro e f hef
  apply Subtype.ext
  have hmap :
      Sym2.map (fun x : H.verts => (x : V)) e.1 =
        Sym2.map (fun x : H.verts => (x : V)) f.1 :=
    Subtype.mk.inj hef
  exact Sym2.map.injective Subtype.val_injective hmap

theorem coeEdgeMap_surjective
    {V : Type} {G : SimpleGraph V}
    (H : G.Subgraph) :
    Function.Surjective (coeEdgeMap H) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : H.Adj x y :=
        (SimpleGraph.Subgraph.mem_edgeSet).1 he
      let e' : H.coe.edgeSet :=
        ⟨s(⟨x, hxy.fst_mem⟩, ⟨y, hxy.snd_mem⟩), hxy⟩
      refine ⟨e', Subtype.ext ?_⟩
      simp [coeEdgeMap, e']

/-- Edges of a subgraph's coefficient graph are canonically its ambient
subgraph edges. -/
noncomputable def coeEdgeEquiv
    {V : Type} {G : SimpleGraph V}
    (H : G.Subgraph) :
    H.coe.edgeSet ≃ H.edgeSet :=
  Equiv.ofBijective (coeEdgeMap H)
    ⟨coeEdgeMap_injective H, coeEdgeMap_surjective H⟩

/-- The edge of the path graph with smaller endpoint `i`. -/
def pathEdge (n : ℕ) (i : Fin n) :
    (pathGraph (n + 1)).edgeSet :=
  ⟨s(i.castSucc, i.succ), by
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj]
    exact Or.inl (by simp)⟩

theorem pathEdge_injective (n : ℕ) :
    Function.Injective (pathEdge n) := by
  intro i j hij
  have hsym :
      s(i.castSucc, i.succ) = s(j.castSucc, j.succ) :=
    Subtype.mk.inj hij
  rw [Sym2.eq_iff] at hsym
  rcases hsym with hsame | hswap
  · exact Fin.castSucc_inj.mp hsame.1
  · exfalso
    have h₁ := congrArg Fin.val hswap.1
    have h₂ := congrArg Fin.val hswap.2
    simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
    omega

theorem pathEdge_surjective (n : ℕ) :
    Function.Surjective (pathEdge n) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hadj : (pathGraph (n + 1)).Adj x y := he
      rw [SimpleGraph.pathGraph_adj] at hadj
      rcases hadj with hxy | hyx
      · let i : Fin n := ⟨x.val, by omega⟩
        refine ⟨i, Subtype.ext ?_⟩
        change s(i.castSucc, i.succ) = s(x, y)
        rw [Sym2.eq_iff]
        exact Or.inl
          ⟨Fin.ext (by simp [i]), Fin.ext (by simp [i, hxy])⟩
      · let i : Fin n := ⟨y.val, by omega⟩
        refine ⟨i, Subtype.ext ?_⟩
        change s(i.castSucc, i.succ) = s(x, y)
        rw [Sym2.eq_iff]
        exact Or.inr
          ⟨Fin.ext (by simp [i]), Fin.ext (by simp [i, hyx])⟩

/-- The `n` edges of `pathGraph (n+1)` are indexed by `Fin n`. -/
noncomputable def pathEdgeEquiv (n : ℕ) :
    Fin n ≃ (pathGraph (n + 1)).edgeSet :=
  Equiv.ofBijective (pathEdge n)
    ⟨pathEdge_injective n, pathEdge_surjective n⟩

theorem pathEdge_adj_iff {n : ℕ} (i j : Fin n) :
    (pathGraph n).Adj i j ↔
      (pathGraph (n + 1)).lineGraph.Adj
        (pathEdge n i) (pathEdge n j) := by
  rw [SimpleGraph.pathGraph_adj,
    SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · intro hij
    refine ⟨?_, ?_⟩
    · intro heq
      have hijEq := pathEdge_injective n heq
      subst j
      simp at hij
    · rcases hij with hij | hij
      · refine ⟨i.succ, by simp [pathEdge], ?_⟩
        have hs : i.succ = j.castSucc := Fin.ext hij
        simp [pathEdge, hs]
      · refine ⟨j.succ, ?_, by simp [pathEdge]⟩
        have hs : j.succ = i.castSucc := Fin.ext hij
        simp [pathEdge, hs]
  · rintro ⟨hne, v, hvi, hvj⟩
    simp only [pathEdge, Sym2.mem_iff] at hvi hvj
    rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
    · exfalso
      apply hne
      exact congrArg (pathEdge n)
        (Fin.castSucc_injective n (hvi.symm.trans hvj))
    · right
      have hval := congrArg Fin.val (hvi.symm.trans hvj)
      simpa using hval.symm
    · left
      have hval := congrArg Fin.val (hvi.symm.trans hvj)
      simpa using hval
    · exfalso
      apply hne
      exact congrArg (pathEdge n)
        (Fin.succ_injective n (hvi.symm.trans hvj))

/-- The line graph of a path on `n+1` vertices is a path on `n` vertices. -/
noncomputable def pathLineIso (n : ℕ) :
    pathGraph n ≃g (pathGraph (n + 1)).lineGraph where
  toEquiv := pathEdgeEquiv n
  map_rel_iff' := by
    intro i j
    simpa [pathEdgeEquiv] using (pathEdge_adj_iff i j).symm

theorem pathGraph_succ_isTree (n : ℕ) :
    (pathGraph (n + 1)).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.pathGraph_connected n, ?_⟩
  have hedge :
      Nat.card (pathGraph (n + 1)).edgeSet = n := by
    rw [← Nat.card_congr (pathEdgeEquiv n)]
    simp
  rw [hedge]
  simp

theorem pathGraph_isAcyclic (n : ℕ) :
    (pathGraph n).IsAcyclic := by
  cases n with
  | zero =>
      have hbot :
          pathGraph 0 = (⊥ : SimpleGraph (Fin 0)) :=
        Subsingleton.elim _ _
      rw [hbot]
      exact SimpleGraph.isAcyclic_bot
  | succ n =>
      exact (pathGraph_succ_isTree n).isAcyclic

theorem lineGraph_pathGraph_succ_isAcyclic (n : ℕ) :
    (pathGraph (n + 1)).lineGraph.IsAcyclic :=
  (pathLineIso n).isAcyclic_iff.mp (pathGraph_isAcyclic n)

/-- The line graph of the edge subgraph traced by a simple walk is acyclic. -/
theorem lineGraph_toSubgraph_isAcyclic
    {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) :
    p.toSubgraph.coe.lineGraph.IsAcyclic :=
  (hp.pathGraphIsoToSubgraph.lineGraph.isAcyclic_iff).mp
    (lineGraph_pathGraph_succ_isAcyclic p.length)

end

end PathLineGraph

end QuartetV060
