import QuartetV060.TreeEdgeGeometry

/-!
# Uniqueness of the leaf cluster carried by an oriented edge

The rooted edge positions of a binary leaf-labelled phylogenetic tree carry
distinct leaf clusters.  This fact rules out the otherwise troublesome case
in which two distinct adjacent edge positions would satisfy both cluster
inclusions.  It is the geometric input needed to prove the concrete bridge
reversal `(K,H,L) ↦ (L,H,K)`.
-/

namespace QuartetV060

namespace EdgeClusterInjective

open QuartetDistance
open PhyloOccurrences

noncomputable section

variable
    {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

omit [Fintype X] [Nonempty X] [DecidableEq X] in
theorem properSubtree_leaves_length_lt
    {t : Tree.FullTree X}
    (p : GraphQuartet.FullTree.ProperSubtree t) :
    p.tree.leaves.length < t.leaves.length := by
  induction p with
  | left l r =>
      simp only [GraphQuartet.FullTree.ProperSubtree.tree_left,
        Tree.FullTree.leaves, List.length_append]
      have hr : 0 < r.leaves.length :=
        List.length_pos_iff.mpr r.leaves_ne_nil
      omega
  | right l r =>
      simp only [GraphQuartet.FullTree.ProperSubtree.tree_right,
        Tree.FullTree.leaves, List.length_append]
      have hl : 0 < l.leaves.length :=
        List.length_pos_iff.mpr l.leaves_ne_nil
      omega
  | @inLeft l r p ih =>
      simp only [GraphQuartet.FullTree.ProperSubtree.tree_inLeft,
        Tree.FullTree.leaves, List.length_append]
      omega
  | @inRight l r p ih =>
      simp only [GraphQuartet.FullTree.ProperSubtree.tree_inRight,
        Tree.FullTree.leaves, List.length_append]
      omega

omit [Fintype X] [Nonempty X] in
theorem properSubtree_toFinset_ne_ambient
    {t : Tree.FullTree X}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (ht : t.leaves.Nodup) :
    p.tree.leaves.toFinset ≠ t.leaves.toFinset := by
  intro h
  have hpNodup := p.leaves_nodup ht
  have hcard := congrArg Finset.card h
  rw [List.toFinset_card_of_nodup hpNodup,
    List.toFinset_card_of_nodup ht] at hcard
  exact (Nat.ne_of_lt (properSubtree_leaves_length_lt p)) hcard

omit [Fintype X] [Nonempty X] in
theorem properSubtree_eq_of_toFinset_eq
    {t : Tree.FullTree X}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (ht : t.leaves.Nodup)
    (hcluster : p.tree.leaves.toFinset = q.tree.leaves.toFinset) :
    p = q := by
  induction t with
  | leaf x =>
      exact nomatch p
  | fork l r ihl ihr =>
      have hlNodup : l.leaves.Nodup := ht.of_append_left
      have hrNodup : r.leaves.Nodup := ht.of_append_right
      have hdisj : Disjoint l.leaves.toFinset r.leaves.toFinset := by
        rw [Finset.disjoint_left]
        intro x hxl hxr
        exact List.disjoint_left.mp ht.disjoint
          (by simpa using hxl) (by simpa using hxr)
      cases p with
      | left =>
          cases q with
          | left => rfl
          | right =>
              exfalso
              have hlNonempty : l.leaves.toFinset.Nonempty := by
                simpa using l.leaves_ne_nil
              obtain ⟨x, hx⟩ := hlNonempty
              exact Finset.disjoint_left.mp hdisj hx
                (hcluster ▸ hx)
          | inLeft q =>
              exfalso
              exact properSubtree_toFinset_ne_ambient q hlNodup
                hcluster.symm
          | inRight q =>
              exfalso
              have hlNonempty : l.leaves.toFinset.Nonempty := by
                simpa using l.leaves_ne_nil
              obtain ⟨x, hx⟩ := hlNonempty
              have hxq : x ∈ q.tree.leaves.toFinset := hcluster ▸ hx
              exact Finset.disjoint_left.mp hdisj hx
                (q.leaves_subset hxq)
      | right =>
          cases q with
          | left =>
              exfalso
              have hrNonempty : r.leaves.toFinset.Nonempty := by
                simpa using r.leaves_ne_nil
              obtain ⟨x, hx⟩ := hrNonempty
              exact Finset.disjoint_left.mp hdisj
                (hcluster ▸ hx) hx
          | right => rfl
          | inLeft q =>
              exfalso
              have hrNonempty : r.leaves.toFinset.Nonempty := by
                simpa using r.leaves_ne_nil
              obtain ⟨x, hx⟩ := hrNonempty
              have hxq : x ∈ q.tree.leaves.toFinset := hcluster ▸ hx
              exact Finset.disjoint_left.mp hdisj
                (q.leaves_subset hxq) hx
          | inRight q =>
              exfalso
              exact properSubtree_toFinset_ne_ambient q hrNodup
                hcluster.symm
      | inLeft p =>
          cases q with
          | left =>
              exfalso
              exact properSubtree_toFinset_ne_ambient p hlNodup hcluster
          | right =>
              exfalso
              have hpNonempty : p.tree.leaves.toFinset.Nonempty := by
                simpa using p.tree.leaves_ne_nil
              obtain ⟨x, hx⟩ := hpNonempty
              exact Finset.disjoint_left.mp hdisj
                (p.leaves_subset hx) (hcluster ▸ hx)
          | inLeft q =>
              congr
              exact ihl p q hlNodup hcluster
          | inRight q =>
              exfalso
              have hpNonempty : p.tree.leaves.toFinset.Nonempty := by
                simpa using p.tree.leaves_ne_nil
              obtain ⟨x, hx⟩ := hpNonempty
              have hxq : x ∈ q.tree.leaves.toFinset := hcluster ▸ hx
              exact Finset.disjoint_left.mp hdisj
                (p.leaves_subset hx) (q.leaves_subset hxq)
      | inRight p =>
          cases q with
          | left =>
              exfalso
              have hpNonempty : p.tree.leaves.toFinset.Nonempty := by
                simpa using p.tree.leaves_ne_nil
              obtain ⟨x, hx⟩ := hpNonempty
              exact Finset.disjoint_left.mp hdisj
                (hcluster ▸ hx) (p.leaves_subset hx)
          | right =>
              exfalso
              exact properSubtree_toFinset_ne_ambient p hrNodup hcluster
          | inLeft q =>
              exfalso
              have hpNonempty : p.tree.leaves.toFinset.Nonempty := by
                simpa using p.tree.leaves_ne_nil
              obtain ⟨x, hx⟩ := hpNonempty
              exact Finset.disjoint_left.mp hdisj
                (q.leaves_subset (hcluster ▸ hx)) (p.leaves_subset hx)
          | inRight q =>
              congr
              exact ihr p q hrNodup hcluster

/-- The map from a rooted edge position to its taxon cluster is injective. -/
theorem edgePosition_cluster_injective
    {T : Tree.PhyloTree X} :
    Function.Injective
      (fun p : EdgePosition T => p.cluster) := by
  intro p q hcluster
  cases p with
  | crown =>
      cases q with
      | crown => rfl
      | inside q =>
          exfalso
          have hraw :
              q.tree.leaves.toFinset = T.crown.leaves.toFinset := by
            simpa [GraphQuartet.PhyloTree.EdgePosition.cluster] using
              (Finset.image_injective Subtype.val_injective hcluster).symm
          exact properSubtree_toFinset_ne_ambient q T.nodup_leaves hraw
  | inside p =>
      cases q with
      | crown =>
          exfalso
          have hraw :
              p.tree.leaves.toFinset = T.crown.leaves.toFinset := by
            simpa [GraphQuartet.PhyloTree.EdgePosition.cluster] using
              (Finset.image_injective Subtype.val_injective hcluster)
          exact properSubtree_toFinset_ne_ambient p T.nodup_leaves hraw
      | inside q =>
          congr
          exact properSubtree_eq_of_toFinset_eq p q T.nodup_leaves
            (Finset.image_injective Subtype.val_injective hcluster)

end

end EdgeClusterInjective

end QuartetV060
