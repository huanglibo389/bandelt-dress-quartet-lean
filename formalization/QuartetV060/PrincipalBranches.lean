import QuartetV060.PhyloBridgeReversal

/-!
# The four branches incident with a principal edge

For an internal edge of a rooted binary phylogenetic tree, the two endpoints
carry four branches other than the edge itself.  This file constructs those
four branches directly from the recursive tree syntax.  It is the geometric
input for the manuscript's endpoint-atom and residual-block partition.
-/

namespace QuartetV060

namespace PrincipalBranches

open QuartetDistance
open PhyloOccurrences

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

namespace ProperSubtree

theorem fork_leaves_disjoint
    {α : Type} [DecidableEq α]
    {l r : Tree.FullTree α}
    (h : (Tree.FullTree.fork l r).leaves.Nodup) :
    Disjoint l.leaves.toFinset r.leaves.toFinset := by
  rw [Finset.disjoint_left]
  intro x hxl hxr
  exact List.disjoint_left.mp h.disjoint
    (by simpa using hxl) (by simpa using hxr)

/-- Embed a subtree occurrence of `p.tree` back into the ambient tree
containing `p`. -/
def lift
    {α : Type} :
    {t : Tree.FullTree α} →
      (p : GraphQuartet.FullTree.ProperSubtree t) →
      GraphQuartet.FullTree.ProperSubtree p.tree →
      GraphQuartet.FullTree.ProperSubtree t
  | _, .left _ _, q => .inLeft q
  | _, .right _ _, q => .inRight q
  | _, .inLeft p, q => .inLeft (lift p q)
  | _, .inRight p, q => .inRight (lift p q)

/-- The edge occurrence in the branch opposite `p` at its parent
endpoint. -/
def sibling
    {α : Type}
    {t : Tree.FullTree α} :
    GraphQuartet.FullTree.ProperSubtree t →
      GraphQuartet.FullTree.ProperSubtree t
  | .left l r => .right l r
  | .right l r => .left l r
  | .inLeft p => .inLeft (sibling p)
  | .inRight p => .inRight (sibling p)

/-- The edge immediately above `p`, when that edge is still internal to the
same full tree.  `none` means that the parent edge is the crown edge of the
ambient phylogenetic tree. -/
def parent?
    {α : Type}
    {t : Tree.FullTree α} :
    GraphQuartet.FullTree.ProperSubtree t →
      Option (GraphQuartet.FullTree.ProperSubtree t)
  | .left _ _ => none
  | .right _ _ => none
  | @GraphQuartet.FullTree.ProperSubtree.inLeft _ l r p =>
      match parent? p with
      | none => some (.left l r)
      | some q => some (.inLeft q)
  | @GraphQuartet.FullTree.ProperSubtree.inRight _ l r p =>
      match parent? p with
      | none => some (.right l r)
      | some q => some (.inRight q)

/-- The left child edge at the child endpoint of a full-tree root, when it
exists. -/
def localChildLeft?
    {α : Type} :
    (t : Tree.FullTree α) →
      Option (GraphQuartet.FullTree.ProperSubtree t)
  | .leaf _ => none
  | .fork l r => some (.left l r)

/-- The right child edge at the child endpoint of a full-tree root, when it
exists. -/
def localChildRight?
    {α : Type} :
    (t : Tree.FullTree α) →
      Option (GraphQuartet.FullTree.ProperSubtree t)
  | .leaf _ => none
  | .fork l r => some (.right l r)

/-- The left child edge of a subtree occurrence, lifted into the same ambient
tree. -/
def childLeft?
    {α : Type}
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t) :
    Option (GraphQuartet.FullTree.ProperSubtree t) :=
  (localChildLeft? p.tree).map (lift p)

/-- The right child edge of a subtree occurrence, lifted into the same ambient
tree. -/
def childRight?
    {α : Type}
    {t : Tree.FullTree α}
  (p : GraphQuartet.FullTree.ProperSubtree t) :
    Option (GraphQuartet.FullTree.ProperSubtree t) :=
  (localChildRight? p.tree).map (lift p)

theorem exists_localChildLeft?_of_two_le_card
    {α : Type} [DecidableEq α]
    (t : Tree.FullTree α)
    (hcard : 2 ≤ t.leaves.toFinset.card) :
    ∃ q : GraphQuartet.FullTree.ProperSubtree t,
      localChildLeft? t = some q := by
  cases t with
  | leaf x =>
      simp [Tree.FullTree.leaves] at hcard
  | fork l r =>
      exact ⟨.left l r, rfl⟩

theorem exists_localChildRight?_of_two_le_card
    {α : Type} [DecidableEq α]
    (t : Tree.FullTree α)
    (hcard : 2 ≤ t.leaves.toFinset.card) :
    ∃ q : GraphQuartet.FullTree.ProperSubtree t,
      localChildRight? t = some q := by
  cases t with
  | leaf x =>
      simp [Tree.FullTree.leaves] at hcard
  | fork l r =>
      exact ⟨.right l r, rfl⟩

theorem exists_childLeft?_of_two_le_card
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (hcard : 2 ≤ p.tree.leaves.toFinset.card) :
    ∃ q : GraphQuartet.FullTree.ProperSubtree t,
      childLeft? p = some q := by
  obtain ⟨q, hq⟩ :=
    exists_localChildLeft?_of_two_le_card p.tree hcard
  refine ⟨lift p q, ?_⟩
  simp [childLeft?, hq]

theorem exists_childRight?_of_two_le_card
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (hcard : 2 ≤ p.tree.leaves.toFinset.card) :
    ∃ q : GraphQuartet.FullTree.ProperSubtree t,
      childRight? p = some q := by
  obtain ⟨q, hq⟩ :=
    exists_localChildRight?_of_two_le_card p.tree hcard
  refine ⟨lift p q, ?_⟩
  simp [childRight?, hq]

theorem localChildLeft?_parent
    {α : Type}
    {t : Tree.FullTree α}
    (q : GraphQuartet.FullTree.ProperSubtree t)
    (h : localChildLeft? t = some q) :
    q.parent = TreeAdequacy.FullTree.rootVertex t := by
  cases t with
  | leaf x =>
      simp [localChildLeft?] at h
  | fork l r =>
      simp [localChildLeft?] at h
      subst q
      rfl

theorem localChildRight?_parent
    {α : Type}
    {t : Tree.FullTree α}
    (q : GraphQuartet.FullTree.ProperSubtree t)
    (h : localChildRight? t = some q) :
    q.parent = TreeAdequacy.FullTree.rootVertex t := by
  cases t with
  | leaf x =>
      simp [localChildRight?] at h
  | fork l r =>
      simp [localChildRight?] at h
      subst q
      rfl

theorem localChild?_eq_some_of_parent_eq_root
    {α : Type}
    {t : Tree.FullTree α}
    (q : GraphQuartet.FullTree.ProperSubtree t)
    (h :
      q.parent = TreeAdequacy.FullTree.rootVertex t) :
    localChildLeft? t = some q ∨
      localChildRight? t = some q := by
  cases t with
  | leaf x =>
      exact nomatch q
  | fork l r =>
      cases q with
      | left => exact Or.inl rfl
      | right => exact Or.inr rfl
      | inLeft q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
      | inRight q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h

/-- The two taxon branches at the parent endpoint of `p`, computed relative
to an additional taxon set lying outside the ambient full tree. -/
def parentBranches
    {α : Type} [DecidableEq α]
    (outside : Finset α) :
    {t : Tree.FullTree α} →
      GraphQuartet.FullTree.ProperSubtree t →
      Finset α × Finset α
  | .fork l r, .left _ _ => (r.leaves.toFinset, outside)
  | .fork l r, .right _ _ => (l.leaves.toFinset, outside)
  | .fork l r, .inLeft p =>
      parentBranches (outside ∪ r.leaves.toFinset) p
  | .fork l r, .inRight p =>
      parentBranches (outside ∪ l.leaves.toFinset) p

@[simp] theorem lift_tree
    {α : Type}
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (q : GraphQuartet.FullTree.ProperSubtree p.tree) :
    (lift p q).tree = q.tree := by
  induction p with
  | left => rfl
  | right => rfl
  | inLeft p ih =>
      simpa [lift] using ih q
  | inRight p ih =>
      simpa [lift] using ih q

theorem lift_injective
    {α : Type}
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t) :
    Function.Injective (lift p) := by
  induction p with
  | left =>
      intro q r h
      exact GraphQuartet.FullTree.ProperSubtree.inLeft.inj h
  | right =>
      intro q r h
      exact GraphQuartet.FullTree.ProperSubtree.inRight.inj h
  | inLeft p ih =>
      intro q r h
      exact ih
        (GraphQuartet.FullTree.ProperSubtree.inLeft.inj h)
  | inRight p ih =>
      intro q r h
      exact ih
        (GraphQuartet.FullTree.ProperSubtree.inRight.inj h)

theorem parent_lift_eq_child
    {α : Type}
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (q : GraphQuartet.FullTree.ProperSubtree p.tree)
    (hq :
      q.parent = TreeAdequacy.FullTree.rootVertex p.tree) :
    (lift p q).parent = p.child := by
  induction p with
  | left l r =>
      have hq' :
          q.parent = TreeAdequacy.FullTree.rootVertex l := by
        simpa only [
          GraphQuartet.FullTree.ProperSubtree.tree_left] using hq
      exact congrArg (fun x => Sum.inl (Sum.inr x)) hq'
  | right l r =>
      have hq' :
          q.parent = TreeAdequacy.FullTree.rootVertex r := by
        simpa only [
          GraphQuartet.FullTree.ProperSubtree.tree_right] using hq
      exact congrArg Sum.inr hq'
  | inLeft p ih =>
      change
        Sum.inl (Sum.inr (lift p q).parent) =
          Sum.inl (Sum.inr p.child)
      rw [ih q hq]
  | inRight p ih =>
      change Sum.inr (lift p q).parent = Sum.inr p.child
      rw [ih q hq]

theorem childLeft?_parent
    {α : Type}
    {t : Tree.FullTree α}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (h : childLeft? p = some q) :
    q.parent = p.child := by
  rw [childLeft?] at h
  obtain ⟨q₀, hq₀, hq⟩ := Option.map_eq_some_iff.mp h
  rw [← hq]
  exact parent_lift_eq_child p q₀
    (localChildLeft?_parent q₀ hq₀)

theorem childRight?_parent
    {α : Type}
    {t : Tree.FullTree α}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (h : childRight? p = some q) :
    q.parent = p.child := by
  rw [childRight?] at h
  obtain ⟨q₀, hq₀, hq⟩ := Option.map_eq_some_iff.mp h
  rw [← hq]
  exact parent_lift_eq_child p q₀
    (localChildRight?_parent q₀ hq₀)

theorem child?_eq_some_of_parent_eq_child
    {α : Type}
    {t : Tree.FullTree α}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (h : q.parent = p.child) :
    childLeft? p = some q ∨ childRight? p = some q := by
  induction p with
  | left l r =>
      cases q with
      | left =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed,
            TreeAdequacy.FullTree.rootVertex] at h
      | right =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed,
            TreeAdequacy.FullTree.rootVertex] at h
      | inLeft q =>
          have h' :
              q.parent =
                TreeAdequacy.FullTree.rootVertex l :=
            Sum.inr.inj (Sum.inl.inj h)
          rcases localChild?_eq_some_of_parent_eq_root q h' with
            hq | hq
          · exact Or.inl (by
              simpa [childLeft?, lift] using hq)
          · exact Or.inr (by
              simpa [childRight?, lift] using hq)
      | inRight q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed] at h
  | right l r =>
      cases q with
      | left =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed,
            TreeAdequacy.FullTree.rootVertex] at h
      | right =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed,
            TreeAdequacy.FullTree.rootVertex] at h
      | inLeft q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed] at h
      | inRight q =>
          have h' :
              q.parent =
                TreeAdequacy.FullTree.rootVertex r :=
            Sum.inr.inj h
          rcases localChild?_eq_some_of_parent_eq_root q h' with
            hq | hq
          · exact Or.inl (by
              simpa [childLeft?, lift] using hq)
          · exact Or.inr (by
              simpa [childRight?, lift] using hq)

  | @inLeft l r p ih =>
      cases q with
      | left =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed,
            TreeAdequacy.FullTree.rootVertex] at h
      | right =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed,
            TreeAdequacy.FullTree.rootVertex] at h
      | inLeft q =>
          have h' : q.parent = p.child :=
            Sum.inr.inj (Sum.inl.inj h)
          rcases ih q h' with hq | hq
          · exact Or.inl (by
              simpa [childLeft?, lift] using hq)
          · exact Or.inr (by
              simpa [childRight?, lift] using hq)
      | inRight q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed] at h
  | @inRight l r p ih =>
      cases q with
      | left =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed,
            TreeAdequacy.FullTree.rootVertex] at h
      | right =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed,
            TreeAdequacy.FullTree.rootVertex] at h
      | inLeft q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            GraphQuartet.FullTree.ProperSubtree.child,
            GraphQuartet.FullTree.ProperSubtree.embed] at h
      | inRight q =>
          have h' : q.parent = p.child := Sum.inr.inj h
          rcases ih q h' with hq | hq
          · exact Or.inl (by
              simpa [childLeft?, lift] using hq)
          · exact Or.inr (by
              simpa [childRight?, lift] using hq)

theorem localChildLeft?_ne_localChildRight?_of_two_le_card
    {α : Type} [DecidableEq α]
    (t : Tree.FullTree α)
    (hcard : 2 ≤ t.leaves.toFinset.card) :
    localChildLeft? t ≠ localChildRight? t := by
  cases t with
  | leaf x =>
      simp [Tree.FullTree.leaves] at hcard
  | fork l r =>
      simp [localChildLeft?, localChildRight?]

theorem childLeft?_ne_childRight?_of_two_le_card
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (hcard : 2 ≤ p.tree.leaves.toFinset.card) :
    childLeft? p ≠ childRight? p := by
  intro h
  rw [childLeft?, childRight?] at h
  exact
    localChildLeft?_ne_localChildRight?_of_two_le_card
      p.tree hcard
      ((Option.map_inj_right (lift_injective p)).mp h)

theorem sibling_parent
    {α : Type}
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t) :
    (sibling p).parent = p.parent := by
  induction p with
  | left =>
      rfl
  | right =>
      rfl
  | inLeft p ih =>
      change
        Sum.inl (Sum.inr (sibling p).parent) =
          Sum.inl (Sum.inr p.parent)
      rw [ih]
  | inRight p ih =>
      change Sum.inr (sibling p).parent = Sum.inr p.parent
      rw [ih]

theorem sibling_ne
    {α : Type}
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t) :
    sibling p ≠ p := by
  induction p with
  | left =>
      intro h
      cases h
  | right =>
      intro h
      cases h
  | inLeft p ih =>
      intro h
      exact ih (GraphQuartet.FullTree.ProperSubtree.inLeft.inj h)
  | inRight p ih =>
      intro h
      exact ih (GraphQuartet.FullTree.ProperSubtree.inRight.inj h)

theorem eq_or_sibling_of_parent_eq
    {α : Type}
    {t : Tree.FullTree α}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (h : q.parent = p.parent) :
    q = p ∨ q = sibling p := by
  induction p with
  | left l r =>
      cases q with
      | left => exact Or.inl rfl
      | right => exact Or.inr rfl
      | inLeft q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
      | inRight q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
  | right l r =>
      cases q with
      | left => exact Or.inr rfl
      | right => exact Or.inl rfl
      | inLeft q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
      | inRight q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
  | @inLeft l r p ih =>
      cases q with
      | left =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
      | right =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
      | inLeft q =>
          have h' : q.parent = p.parent := Sum.inr.inj (Sum.inl.inj h)
          rcases ih q h' with hqp | hqs
          · exact Or.inl (congrArg
              GraphQuartet.FullTree.ProperSubtree.inLeft hqp)
          · exact Or.inr (congrArg
              GraphQuartet.FullTree.ProperSubtree.inLeft hqs)
      | inRight q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent] at h
  | @inRight l r p ih =>
      cases q with
      | left =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
      | right =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent,
            TreeAdequacy.FullTree.rootVertex] at h
      | inLeft q =>
          simp [GraphQuartet.FullTree.ProperSubtree.parent] at h
      | inRight q =>
          have h' : q.parent = p.parent := Sum.inr.inj h
          rcases ih q h' with hqp | hqs
          · exact Or.inl (congrArg
              GraphQuartet.FullTree.ProperSubtree.inRight hqp)
          · exact Or.inr (congrArg
              GraphQuartet.FullTree.ProperSubtree.inRight hqs)

theorem parent_eq_root_of_parent?_eq_none
    {α : Type}
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (h : parent? p = none) :
    p.parent = TreeAdequacy.FullTree.rootVertex t := by
  cases p with
  | left =>
      rfl
  | right =>
      rfl
  | inLeft p =>
      cases hp : parent? p <;> simp [parent?, hp] at h
  | inRight p =>
      cases hp : parent? p <;> simp [parent?, hp] at h

theorem parent?_child
    {α : Type}
    {t : Tree.FullTree α}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (h : parent? p = some q) :
    q.child = p.parent := by
  induction p with
  | left =>
      simp [parent?] at h
  | right =>
      simp [parent?] at h
  | @inLeft l r p ih =>
      cases hp : parent? p with
      | none =>
          simp [parent?, hp] at h
          subst q
          change
            Sum.inl
                (Sum.inr
                  (TreeAdequacy.FullTree.rootVertex l)) =
              Sum.inl (Sum.inr p.parent)
          rw [parent_eq_root_of_parent?_eq_none p hp]
      | some q' =>
          simp [parent?, hp] at h
          subst q
          change
            Sum.inl (Sum.inr q'.child) =
              Sum.inl (Sum.inr p.parent)
          rw [ih q' hp]
  | @inRight l r p ih =>
      cases hp : parent? p with
      | none =>
          simp [parent?, hp] at h
          subst q
          change
            Sum.inr
                (TreeAdequacy.FullTree.rootVertex r) =
              Sum.inr p.parent
          rw [parent_eq_root_of_parent?_eq_none p hp]
      | some q' =>
          simp [parent?, hp] at h
          subst q
          change Sum.inr q'.child = Sum.inr p.parent
          rw [ih q' hp]

theorem sibling_leaves_eq_parentBranches_first
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (outside : Finset α)
    (p : GraphQuartet.FullTree.ProperSubtree t) :
    (sibling p).tree.leaves.toFinset =
      (parentBranches outside p).1 := by
  induction p generalizing outside with
  | left =>
      rfl
  | right =>
      rfl
  | @inLeft l r p ih =>
      simpa [sibling, parentBranches] using
        ih (outside ∪ r.leaves.toFinset)
  | @inRight l r p ih =>
      simpa [sibling, parentBranches] using
        ih (outside ∪ l.leaves.toFinset)

theorem parentBranches_second_eq_empty_of_parent?_eq_none
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (h : parent? p = none) :
    (parentBranches ∅ p).2 = ∅ := by
  cases p with
  | left =>
      rfl
  | right =>
      rfl
  | inLeft p =>
      cases hp : parent? p <;>
        simp [parent?, hp] at h
  | inRight p =>
      cases hp : parent? p <;>
        simp [parent?, hp] at h

theorem ambient_leaves_eq_principal_union_sibling_of_parent?_eq_none
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (h : parent? p = none) :
    t.leaves.toFinset =
      p.tree.leaves.toFinset ∪
        (sibling p).tree.leaves.toFinset := by
  cases p with
  | left l r =>
      simp [parent?, sibling, Tree.FullTree.leaves,
        Finset.union_comm]
  | right l r =>
      simp [parent?, sibling, Tree.FullTree.leaves,
        Finset.union_comm]
  | inLeft p =>
      cases hp : parent? p <;>
        simp [parent?, hp] at h
  | inRight p =>
      cases hp : parent? p <;>
        simp [parent?, hp] at h

theorem parent?_tree_leaves
    {α : Type} [DecidableEq α]
    (outside : Finset α)
    {t : Tree.FullTree α}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (h : parent? p = some q) :
    q.tree.leaves.toFinset =
      p.tree.leaves.toFinset ∪
        (parentBranches outside p).1 := by
  induction p generalizing outside with
  | left =>
      simp [parent?] at h
  | right =>
      simp [parent?] at h
  | @inLeft l r p ih =>
      cases hp : parent? p with
      | none =>
          simp [parent?, hp] at h
          subst q
          calc
            l.leaves.toFinset =
                p.tree.leaves.toFinset ∪
                  (sibling p).tree.leaves.toFinset :=
              ambient_leaves_eq_principal_union_sibling_of_parent?_eq_none
                p hp
            _ = p.tree.leaves.toFinset ∪
                  (parentBranches
                    (outside ∪ r.leaves.toFinset) p).1 := by
              rw [sibling_leaves_eq_parentBranches_first
                (outside ∪ r.leaves.toFinset) p]
            _ = (GraphQuartet.FullTree.ProperSubtree.inLeft
                    (r := r) p).tree.leaves.toFinset ∪
                  (parentBranches outside
                    (GraphQuartet.FullTree.ProperSubtree.inLeft
                      (r := r) p)).1 := by
              rfl
      | some q₀ =>
          simp [parent?, hp] at h
          subst q
          simpa [parentBranches] using
            ih (outside ∪ r.leaves.toFinset) q₀ hp
  | @inRight l r p ih =>
      cases hp : parent? p with
      | none =>
          simp [parent?, hp] at h
          subst q
          calc
            r.leaves.toFinset =
                p.tree.leaves.toFinset ∪
                  (sibling p).tree.leaves.toFinset :=
              ambient_leaves_eq_principal_union_sibling_of_parent?_eq_none
                p hp
            _ = p.tree.leaves.toFinset ∪
                  (parentBranches
                    (outside ∪ l.leaves.toFinset) p).1 := by
              rw [sibling_leaves_eq_parentBranches_first
                (outside ∪ l.leaves.toFinset) p]
            _ = (GraphQuartet.FullTree.ProperSubtree.inRight
                    (l := l) p).tree.leaves.toFinset ∪
                  (parentBranches outside
                    (GraphQuartet.FullTree.ProperSubtree.inRight
                      (l := l) p)).1 := by
              rfl
      | some q₀ =>
          simp [parent?, hp] at h
          subst q
          simpa [parentBranches] using
            ih (outside ∪ l.leaves.toFinset) q₀ hp

theorem parentBranches_cover
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (outside : Finset α)
    (p : GraphQuartet.FullTree.ProperSubtree t) :
    (parentBranches outside p).1 ∪
        (parentBranches outside p).2 ∪
        p.tree.leaves.toFinset =
      outside ∪ t.leaves.toFinset := by
  induction p generalizing outside with
  | left l r =>
      ext x
      simp [parentBranches, Tree.FullTree.leaves]
      tauto
  | right l r =>
      ext x
      simp [parentBranches, Tree.FullTree.leaves]
      tauto
  | @inLeft l r p ih =>
      simpa [parentBranches, Tree.FullTree.leaves,
        Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
        ih (outside := outside ∪ r.leaves.toFinset)
  | @inRight l r p ih =>
      simpa [parentBranches, Tree.FullTree.leaves,
        Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
        ih (outside := outside ∪ l.leaves.toFinset)

theorem parentBranches_pairwise_disjoint
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (outside : Finset α)
    (p : GraphQuartet.FullTree.ProperSubtree t)
    (ht : t.leaves.Nodup)
    (hout : Disjoint outside t.leaves.toFinset) :
    Disjoint (parentBranches outside p).1
        (parentBranches outside p).2 ∧
      Disjoint (parentBranches outside p).1
        p.tree.leaves.toFinset ∧
      Disjoint (parentBranches outside p).2
        p.tree.leaves.toFinset := by
  induction p generalizing outside with
  | left l r =>
      have hlr := fork_leaves_disjoint ht
      have hor : Disjoint outside r.leaves.toFinset :=
        hout.mono_right (by
          intro x hx
          simp [Tree.FullTree.leaves, hx])
      have hol : Disjoint outside l.leaves.toFinset :=
        hout.mono_right (by
          intro x hx
          simp [Tree.FullTree.leaves, hx])
      exact ⟨hor.symm, hlr.symm, hol⟩
  | right l r =>
      have hlr := fork_leaves_disjoint ht
      have hol : Disjoint outside l.leaves.toFinset :=
        hout.mono_right (by
          intro x hx
          simp [Tree.FullTree.leaves, hx])
      have hor : Disjoint outside r.leaves.toFinset :=
        hout.mono_right (by
          intro x hx
          simp [Tree.FullTree.leaves, hx])
      exact ⟨hol.symm, hlr, hor⟩
  | @inLeft l r p ih =>
      have hlr := fork_leaves_disjoint ht
      have houtl : Disjoint outside l.leaves.toFinset :=
        hout.mono_right (by
          intro x hx
          simp [Tree.FullTree.leaves, hx])
      have hout' :
          Disjoint (outside ∪ r.leaves.toFinset)
            l.leaves.toFinset := by
        rw [Finset.disjoint_union_left]
        exact ⟨houtl, hlr.symm⟩
      simpa [parentBranches] using
        ih (outside := outside ∪ r.leaves.toFinset)
          ht.of_append_left hout'
  | @inRight l r p ih =>
      have hlr := fork_leaves_disjoint ht
      have houtr : Disjoint outside r.leaves.toFinset :=
        hout.mono_right (by
          intro x hx
          simp [Tree.FullTree.leaves, hx])
      have hout' :
          Disjoint (outside ∪ l.leaves.toFinset)
            r.leaves.toFinset := by
        rw [Finset.disjoint_union_left]
        exact ⟨houtr, hlr⟩
      simpa [parentBranches] using
        ih (outside := outside ∪ l.leaves.toFinset)
          ht.of_append_right hout'

end ProperSubtree

/-- The two branches at the child endpoint of the edge represented by
`t`.  The leaf case is included only to make the definition total; a
quartet-relevant edge cannot have a leaf below it. -/
def childBranches
    {α : Type} [DecidableEq α] :
    Tree.FullTree α → Finset α × Finset α
  | .leaf _ => (∅, ∅)
  | .fork l r => (l.leaves.toFinset, r.leaves.toFinset)

theorem localChildLeft?_leaves
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (q : GraphQuartet.FullTree.ProperSubtree t)
    (h : ProperSubtree.localChildLeft? t = some q) :
    q.tree.leaves.toFinset = (childBranches t).1 := by
  cases t with
  | leaf x =>
      simp [ProperSubtree.localChildLeft?] at h
  | fork l r =>
      simp [ProperSubtree.localChildLeft?] at h
      subst q
      rfl

theorem localChildRight?_leaves
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (q : GraphQuartet.FullTree.ProperSubtree t)
    (h : ProperSubtree.localChildRight? t = some q) :
    q.tree.leaves.toFinset = (childBranches t).2 := by
  cases t with
  | leaf x =>
      simp [ProperSubtree.localChildRight?] at h
  | fork l r =>
      simp [ProperSubtree.localChildRight?] at h
      subst q
      rfl

theorem childLeft?_leaves
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (h : ProperSubtree.childLeft? p = some q) :
    q.tree.leaves.toFinset =
      (childBranches p.tree).1 := by
  rw [ProperSubtree.childLeft?] at h
  obtain ⟨q₀, hq₀, hq⟩ := Option.map_eq_some_iff.mp h
  rw [← hq, ProperSubtree.lift_tree]
  exact localChildLeft?_leaves q₀ hq₀

theorem childRight?_leaves
    {α : Type} [DecidableEq α]
    {t : Tree.FullTree α}
    (p q : GraphQuartet.FullTree.ProperSubtree t)
    (h : ProperSubtree.childRight? p = some q) :
    q.tree.leaves.toFinset =
      (childBranches p.tree).2 := by
  rw [ProperSubtree.childRight?] at h
  obtain ⟨q₀, hq₀, hq⟩ := Option.map_eq_some_iff.mp h
  rw [← hq, ProperSubtree.lift_tree]
  exact localChildRight?_leaves q₀ hq₀

theorem childBranches_disjoint
    {α : Type} [DecidableEq α]
    (t : Tree.FullTree α)
    (ht : t.leaves.Nodup) :
    Disjoint (childBranches t).1 (childBranches t).2 := by
  cases t with
  | leaf x =>
      simp [childBranches]
  | fork l r =>
      simpa [childBranches] using ProperSubtree.fork_leaves_disjoint ht

theorem childBranches_cover_of_two_le_card
    {α : Type} [DecidableEq α]
    (t : Tree.FullTree α)
    (hcard : 2 ≤ t.leaves.toFinset.card) :
    (childBranches t).1 ∪ (childBranches t).2 =
      t.leaves.toFinset := by
  cases t with
  | leaf x =>
      simp [Tree.FullTree.leaves] at hcard
  | fork l r =>
      simp [childBranches, Tree.FullTree.leaves]

theorem crown_cluster_eq_erase_root
    (T : Tree.PhyloTree X) :
    (GraphQuartet.PhyloTree.EdgePosition.crown (T := T)).cluster =
      Finset.univ.erase T.root := by
  ext x
  constructor
  · intro hx
    simp only [GraphQuartet.PhyloTree.EdgePosition.cluster,
      Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp [y.property]
  · intro hx
    have hne : x ≠ T.root := (Finset.mem_erase.mp hx).1
    simp only [GraphQuartet.PhyloTree.EdgePosition.cluster,
      Finset.mem_image]
    exact ⟨⟨x, hne⟩, by simpa using T.exhaustive ⟨x, hne⟩, rfl⟩

theorem relevantEdge_ne_crown
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    e.1 ≠ GraphQuartet.PhyloTree.EdgePosition.crown := by
  intro he
  have hcard := e.2.2
  rw [he] at hcard
  rw [crown_cluster_eq_erase_root] at hcard
  simpa using hcard

theorem exists_principalProper
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    ∃ p : GraphQuartet.FullTree.ProperSubtree T.crown,
      e.1 = GraphQuartet.PhyloTree.EdgePosition.inside p := by
  cases hpos : e.1 with
  | crown =>
      exact False.elim (relevantEdge_ne_crown e hpos)
  | inside p =>
      exact ⟨p, rfl⟩

/-- The proper-subtree occurrence below a relevant edge. -/
noncomputable def principalProper
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    GraphQuartet.FullTree.ProperSubtree T.crown :=
  Classical.choose (exists_principalProper e)

@[simp] theorem edge_eq_inside_principalProper
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    e.1 =
      GraphQuartet.PhyloTree.EdgePosition.inside
        (principalProper e) :=
  Classical.choose_spec (exists_principalProper e)

/-- Forget the proof that a crown taxon differs from the distinguished root. -/
def mapCrownTaxa
    (T : Tree.PhyloTree X)
    (s : Finset {x : X // x ≠ T.root}) : Finset X :=
  s.image Subtype.val

@[simp] theorem mapCrownTaxa_empty
    (T : Tree.PhyloTree X) :
    mapCrownTaxa T ∅ = ∅ := by
  simp [mapCrownTaxa]

@[simp] theorem mapCrownTaxa_union
    (T : Tree.PhyloTree X)
    (s t : Finset {x : X // x ≠ T.root}) :
    mapCrownTaxa T (s ∪ t) =
      mapCrownTaxa T s ∪ mapCrownTaxa T t := by
  exact Finset.image_union s t

theorem mapCrownTaxa_disjoint
    (T : Tree.PhyloTree X)
    {s t : Finset {x : X // x ≠ T.root}}
    (h : Disjoint s t) :
    Disjoint (mapCrownTaxa T s) (mapCrownTaxa T t) := by
  simpa [mapCrownTaxa] using
    (Finset.disjoint_image Subtype.val_injective).2 h

theorem root_not_mem_mapCrownTaxa
    (T : Tree.PhyloTree X)
    (s : Finset {x : X // x ≠ T.root}) :
    T.root ∉ mapCrownTaxa T s := by
  intro hx
  simp only [mapCrownTaxa, Finset.mem_image] at hx
  obtain ⟨y, -, hy⟩ := hx
  exact y.property hy

theorem mapCrownTaxa_disjoint_insert_root
    (T : Tree.PhyloTree X)
    {s t : Finset {x : X // x ≠ T.root}}
    (h : Disjoint s t) :
    Disjoint (mapCrownTaxa T s)
      (insert T.root (mapCrownTaxa T t)) := by
  rw [Finset.disjoint_left]
  intro x hxs hxt
  rcases Finset.mem_insert.mp hxt with hroot | hxt
  · subst x
    exact root_not_mem_mapCrownTaxa T s hxs
  · exact Finset.disjoint_left.mp
      (mapCrownTaxa_disjoint T h) hxs hxt

/-- The four concrete branch positions around a principal edge. -/
inductive Slot where
  | childLeft
  | childRight
  | parentSibling
  | parentAbove
  deriving DecidableEq, Fintype, Repr

/-- The actual graph-edge position reached through one of the four incident
slots. -/
noncomputable def neighborPosition
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) : Slot →
      Option (EdgePosition T)
  | .childLeft =>
      (ProperSubtree.childLeft? (principalProper e)).map
        GraphQuartet.PhyloTree.EdgePosition.inside
  | .childRight =>
      (ProperSubtree.childRight? (principalProper e)).map
        GraphQuartet.PhyloTree.EdgePosition.inside
  | .parentSibling =>
      some (.inside (ProperSubtree.sibling (principalProper e)))
  | .parentAbove =>
      some <| match ProperSubtree.parent? (principalProper e) with
        | none => .crown
        | some p => .inside p

/-- The four taxon branches incident with a relevant principal edge. -/
noncomputable def branch
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) : Slot → Finset X
  | .childLeft =>
      mapCrownTaxa T
        (childBranches (principalProper e).tree).1
  | .childRight =>
      mapCrownTaxa T
        (childBranches (principalProper e).tree).2
  | .parentSibling =>
      mapCrownTaxa T
        (ProperSubtree.parentBranches ∅ (principalProper e)).1
  | .parentAbove =>
      insert T.root
        (mapCrownTaxa T
          (ProperSubtree.parentBranches ∅ (principalProper e)).2)

theorem principalProper_card
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    2 ≤ (principalProper e).tree.leaves.toFinset.card := by
  have h := e.2.1
  rw [edge_eq_inside_principalProper e] at h
  simp only [GraphQuartet.PhyloTree.EdgePosition.cluster] at h
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  exact h

theorem exists_neighborPosition
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    ∃ q : EdgePosition T, neighborPosition e s = some q := by
  cases s with
  | childLeft =>
      obtain ⟨q, hq⟩ :=
        ProperSubtree.exists_childLeft?_of_two_le_card
          (principalProper e) (principalProper_card e)
      exact ⟨.inside q, by simp [neighborPosition, hq]⟩
  | childRight =>
      obtain ⟨q, hq⟩ :=
        ProperSubtree.exists_childRight?_of_two_le_card
          (principalProper e) (principalProper_card e)
      exact ⟨.inside q, by simp [neighborPosition, hq]⟩
  | parentSibling =>
      exact
        ⟨.inside (ProperSubtree.sibling (principalProper e)), rfl⟩
  | parentAbove =>
      cases hp : ProperSubtree.parent? (principalProper e) with
      | none =>
          exact ⟨.crown, by simp [neighborPosition, hp]⟩
      | some p =>
          exact ⟨.inside p, by simp [neighborPosition, hp]⟩

/-- The total edge-position realization of an incident slot.  The existence
proof is substantive only for the two child slots: relevance of the principal
edge forces at least two leaves below it, hence a binary fork and two child
edges. -/
noncomputable def neighborEdgePosition
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) : EdgePosition T :=
  Classical.choose (exists_neighborPosition e s)

@[simp] theorem neighborPosition_eq_some
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    neighborPosition e s = some (neighborEdgePosition e s) :=
  Classical.choose_spec (exists_neighborPosition e s)

theorem childLeft_neighbor_parent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    (neighborEdgePosition e .childLeft).parent =
      e.1.child := by
  have h := neighborPosition_eq_some e .childLeft
  simp only [neighborPosition, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, hqe⟩ := h
  rw [← hqe, edge_eq_inside_principalProper e]
  change Sum.inr q.parent = Sum.inr (principalProper e).child
  exact congrArg Sum.inr
    (ProperSubtree.childLeft?_parent
      (principalProper e) q hq)

theorem childRight_neighbor_parent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    (neighborEdgePosition e .childRight).parent =
      e.1.child := by
  have h := neighborPosition_eq_some e .childRight
  simp only [neighborPosition, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, hqe⟩ := h
  rw [← hqe, edge_eq_inside_principalProper e]
  change Sum.inr q.parent = Sum.inr (principalProper e).child
  exact congrArg Sum.inr
    (ProperSubtree.childRight?_parent
      (principalProper e) q hq)

theorem childLeft_branch_eq_neighbor_cluster
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .childLeft =
      (neighborEdgePosition e .childLeft).cluster := by
  have hn := neighborPosition_eq_some e .childLeft
  simp only [neighborPosition, Option.map_eq_some_iff] at hn
  obtain ⟨q, hq, hqe⟩ := hn
  have hleaves :=
    childLeft?_leaves (principalProper e) q hq
  have hmap := congrArg (mapCrownTaxa T) hleaves
  rw [← hqe]
  simpa [branch, mapCrownTaxa,
    GraphQuartet.PhyloTree.EdgePosition.cluster] using hmap.symm

theorem childRight_branch_eq_neighbor_cluster
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .childRight =
      (neighborEdgePosition e .childRight).cluster := by
  have hn := neighborPosition_eq_some e .childRight
  simp only [neighborPosition, Option.map_eq_some_iff] at hn
  obtain ⟨q, hq, hqe⟩ := hn
  have hleaves :=
    childRight?_leaves (principalProper e) q hq
  have hmap := congrArg (mapCrownTaxa T) hleaves
  rw [← hqe]
  simpa [branch, mapCrownTaxa,
    GraphQuartet.PhyloTree.EdgePosition.cluster] using hmap.symm

theorem parentSibling_neighbor_parent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    (neighborEdgePosition e .parentSibling).parent =
      e.1.parent := by
  have h := neighborPosition_eq_some e .parentSibling
  simp only [neighborPosition, Option.some.injEq] at h
  rw [← h, edge_eq_inside_principalProper e]
  change
    Sum.inr (ProperSubtree.sibling (principalProper e)).parent =
      Sum.inr (principalProper e).parent
  exact congrArg Sum.inr
    (ProperSubtree.sibling_parent (principalProper e))

theorem parentSibling_branch_eq_neighbor_cluster
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .parentSibling =
      (neighborEdgePosition e .parentSibling).cluster := by
  have hn := neighborPosition_eq_some e .parentSibling
  simp only [neighborPosition, Option.some.injEq] at hn
  have hleaves :=
    ProperSubtree.sibling_leaves_eq_parentBranches_first
      (∅ : Finset {x : X // x ≠ T.root}) (principalProper e)
  have hmap := congrArg (mapCrownTaxa T) hleaves
  rw [← hn]
  simpa [branch, mapCrownTaxa,
    GraphQuartet.PhyloTree.EdgePosition.cluster] using hmap.symm

theorem parentAbove_neighbor_child
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    (neighborEdgePosition e .parentAbove).child =
      e.1.parent := by
  cases hp :
      ProperSubtree.parent? (principalProper e) with
  | none =>
      have hn := neighborPosition_eq_some e .parentAbove
      simp only [neighborPosition, hp, Option.some.injEq] at hn
      rw [← hn, edge_eq_inside_principalProper e]
      simp only [GraphQuartet.PhyloTree.EdgePosition.child,
        GraphQuartet.PhyloTree.EdgePosition.embed,
        GraphQuartet.PhyloTree.EdgePosition.tree_crown,
        GraphQuartet.PhyloTree.EdgePosition.parent]
      change
        Sum.inr (TreeAdequacy.FullTree.rootVertex T.crown) =
          Sum.inr (principalProper e).parent
      exact congrArg Sum.inr
        (ProperSubtree.parent_eq_root_of_parent?_eq_none
          (principalProper e) hp).symm
  | some q =>
      have hn := neighborPosition_eq_some e .parentAbove
      simp only [neighborPosition, hp, Option.some.injEq] at hn
      rw [← hn, edge_eq_inside_principalProper e]
      simp only [GraphQuartet.PhyloTree.EdgePosition.child,
        GraphQuartet.PhyloTree.EdgePosition.embed,
        GraphQuartet.PhyloTree.EdgePosition.tree_inside,
        GraphQuartet.PhyloTree.EdgePosition.parent]
      change
        Sum.inr q.child =
          Sum.inr (principalProper e).parent
      exact congrArg Sum.inr
        (ProperSubtree.parent?_child (principalProper e) q hp)

theorem parentAbove_neighbor_cluster
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    (neighborEdgePosition e .parentAbove).cluster =
      e.1.cluster ∪ branch e .parentSibling := by
  cases hp :
      ProperSubtree.parent? (principalProper e) with
  | none =>
      have hn := neighborPosition_eq_some e .parentAbove
      simp only [neighborPosition, hp, Option.some.injEq] at hn
      have hraw :=
        ProperSubtree.ambient_leaves_eq_principal_union_sibling_of_parent?_eq_none
          (principalProper e) hp
      rw [ProperSubtree.sibling_leaves_eq_parentBranches_first
        (∅ : Finset {x : X // x ≠ T.root})
        (principalProper e)] at hraw
      have hmap := congrArg (mapCrownTaxa T) hraw
      rw [mapCrownTaxa_union] at hmap
      rw [← hn, edge_eq_inside_principalProper e]
      simpa [branch, mapCrownTaxa,
        GraphQuartet.PhyloTree.EdgePosition.cluster] using hmap
  | some q =>
      have hn := neighborPosition_eq_some e .parentAbove
      simp only [neighborPosition, hp, Option.some.injEq] at hn
      have hraw :=
        ProperSubtree.parent?_tree_leaves
          (∅ : Finset {x : X // x ≠ T.root})
          (principalProper e) q hp
      have hmap := congrArg (mapCrownTaxa T) hraw
      rw [mapCrownTaxa_union] at hmap
      rw [← hn, edge_eq_inside_principalProper e]
      simpa [branch, mapCrownTaxa,
        GraphQuartet.PhyloTree.EdgePosition.cluster] using hmap

theorem childLeft_edgeAdjacent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    EdgeAdjacent e.1
      (neighborEdgePosition e .childLeft) := by
  have hshared := childLeft_neighbor_parent e
  refine ⟨?_, Or.inr (Or.inr (Or.inl hshared.symm))⟩
  intro heq
  rw [← heq] at hshared
  exact e.1.adj_parent_child.ne hshared

theorem childRight_edgeAdjacent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    EdgeAdjacent e.1
      (neighborEdgePosition e .childRight) := by
  have hshared := childRight_neighbor_parent e
  refine ⟨?_, Or.inr (Or.inr (Or.inl hshared.symm))⟩
  intro heq
  rw [← heq] at hshared
  exact e.1.adj_parent_child.ne hshared

theorem parentSibling_edgeAdjacent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    EdgeAdjacent e.1
      (neighborEdgePosition e .parentSibling) := by
  have hshared := parentSibling_neighbor_parent e
  refine ⟨?_, Or.inl hshared.symm⟩
  intro heq
  have hn := neighborPosition_eq_some e .parentSibling
  simp only [neighborPosition, Option.some.injEq] at hn
  rw [edge_eq_inside_principalProper e, ← hn] at heq
  have hp :
      principalProper e =
        ProperSubtree.sibling (principalProper e) :=
    GraphQuartet.PhyloTree.EdgePosition.inside.inj heq
  exact ProperSubtree.sibling_ne (principalProper e) hp.symm

theorem parentAbove_edgeAdjacent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    EdgeAdjacent e.1
      (neighborEdgePosition e .parentAbove) := by
  have hshared := parentAbove_neighbor_child e
  refine ⟨?_, Or.inr (Or.inl hshared.symm)⟩
  intro heq
  rw [← heq] at hshared
  exact e.1.adj_parent_child.ne hshared.symm

/-- Every one of the four syntactic incident slots is realized by a distinct
graph edge adjacent to the principal edge. -/
theorem neighbor_edgeAdjacent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    EdgeAdjacent e.1 (neighborEdgePosition e s) := by
  cases s with
  | childLeft => exact childLeft_edgeAdjacent e
  | childRight => exact childRight_edgeAdjacent e
  | parentSibling => exact parentSibling_edgeAdjacent e
  | parentAbove => exact parentAbove_edgeAdjacent e

/-- Conversely, every edge adjacent to the principal edge occupies exactly
one of the four syntactic slots. -/
theorem exists_slot_of_edgeAdjacent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (q : EdgePosition T)
    (h : EdgeAdjacent e.1 q) :
    ∃ s : Slot, q = neighborEdgePosition e s := by
  rcases h with ⟨hne, hshare⟩
  rcases hshare with hpp | hpc | hcp | hcc
  · cases q with
    | crown =>
        rw [edge_eq_inside_principalProper e] at hpp
        simp [GraphQuartet.PhyloTree.EdgePosition.parent] at hpp
    | inside q =>
        have hqparent :
            q.parent = (principalProper e).parent := by
          rw [edge_eq_inside_principalProper e] at hpp
          exact (Sum.inr.inj hpp).symm
        rcases
            ProperSubtree.eq_or_sibling_of_parent_eq
              (principalProper e) q hqparent with hqe | hqs
        · exfalso
          apply hne
          rw [edge_eq_inside_principalProper e]
          exact congrArg
            GraphQuartet.PhyloTree.EdgePosition.inside hqe.symm
        · refine ⟨.parentSibling, ?_⟩
          have hn := neighborPosition_eq_some e .parentSibling
          simp only [neighborPosition, Option.some.injEq] at hn
          exact
            (congrArg GraphQuartet.PhyloTree.EdgePosition.inside hqs).trans hn
  · refine ⟨.parentAbove, ?_⟩
    apply TreeEdgeGeometry.edgePosition_eq_of_child_eq
    calc
      q.child = e.1.parent := hpc.symm
      _ = (neighborEdgePosition e .parentAbove).child :=
        (parentAbove_neighbor_child e).symm
  · cases q with
    | crown =>
        rw [edge_eq_inside_principalProper e] at hcp
        simp [GraphQuartet.PhyloTree.EdgePosition.child,
          GraphQuartet.PhyloTree.EdgePosition.embed,
          GraphQuartet.PhyloTree.EdgePosition.parent] at hcp
    | inside q =>
        have hqparent :
            q.parent = (principalProper e).child := by
          rw [edge_eq_inside_principalProper e] at hcp
          exact (Sum.inr.inj hcp).symm
        rcases
            ProperSubtree.child?_eq_some_of_parent_eq_child
              (principalProper e) q hqparent with hq | hq
        · refine ⟨.childLeft, ?_⟩
          have hn := neighborPosition_eq_some e .childLeft
          simp only [neighborPosition] at hn
          rw [hq] at hn
          exact Option.some.inj hn
        · refine ⟨.childRight, ?_⟩
          have hn := neighborPosition_eq_some e .childRight
          simp only [neighborPosition] at hn
          rw [hq] at hn
          exact Option.some.inj hn
  · exfalso
    apply hne
    exact TreeEdgeGeometry.edgePosition_eq_of_child_eq e.1 q hcc

theorem edgePosition_eq_of_swapped_endpoints
    {T : Tree.PhyloTree X}
    (p q : EdgePosition T)
    (hp : p.parent = q.child)
    (hc : p.child = q.parent) :
    p = q := by
  apply TreeEdgeGeometry.positionEdge_injective
  apply Subtype.ext
  simp only [TreeEdgeGeometry.positionEdge, hp, hc]
  exact Sym2.eq_swap

theorem childLeft_neighbor_ne_childRight
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    neighborEdgePosition e .childLeft ≠
      neighborEdgePosition e .childRight := by
  intro h
  have hl := neighborPosition_eq_some e .childLeft
  have hr := neighborPosition_eq_some e .childRight
  simp only [neighborPosition] at hl hr
  rw [h] at hl
  have hmap :
      Option.map GraphQuartet.PhyloTree.EdgePosition.inside
          (ProperSubtree.childLeft? (principalProper e)) =
        Option.map GraphQuartet.PhyloTree.EdgePosition.inside
          (ProperSubtree.childRight? (principalProper e)) :=
    hl.trans hr.symm
  have hoptions :=
    (Option.map_inj_right
      (fun x y hxy =>
        GraphQuartet.PhyloTree.EdgePosition.inside.inj hxy)).mp hmap
  exact
    ProperSubtree.childLeft?_ne_childRight?_of_two_le_card
      (principalProper e) (principalProper_card e) hoptions

theorem childLeft_neighbor_ne_parentSibling
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    neighborEdgePosition e .childLeft ≠
      neighborEdgePosition e .parentSibling := by
  intro h
  have hc := childLeft_neighbor_parent e
  have hs := parentSibling_neighbor_parent e
  rw [h] at hc
  have hep : e.1.child = e.1.parent := hc.symm.trans hs
  exact e.1.adj_parent_child.ne hep.symm

theorem childRight_neighbor_ne_parentSibling
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    neighborEdgePosition e .childRight ≠
      neighborEdgePosition e .parentSibling := by
  intro h
  have hc := childRight_neighbor_parent e
  have hs := parentSibling_neighbor_parent e
  rw [h] at hc
  have hep : e.1.child = e.1.parent := hc.symm.trans hs
  exact e.1.adj_parent_child.ne hep.symm

theorem childLeft_neighbor_ne_parentAbove
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    neighborEdgePosition e .childLeft ≠
      neighborEdgePosition e .parentAbove := by
  intro h
  have hc := childLeft_neighbor_parent e
  have ha := parentAbove_neighbor_child e
  rw [h] at hc
  have hne :
      neighborEdgePosition e .parentAbove = e.1 :=
    edgePosition_eq_of_swapped_endpoints
      (neighborEdgePosition e .parentAbove) e.1
      hc ha
  exact (neighbor_edgeAdjacent e .parentAbove).1 hne.symm

theorem childRight_neighbor_ne_parentAbove
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    neighborEdgePosition e .childRight ≠
      neighborEdgePosition e .parentAbove := by
  intro h
  have hc := childRight_neighbor_parent e
  have ha := parentAbove_neighbor_child e
  rw [h] at hc
  have hne :
      neighborEdgePosition e .parentAbove = e.1 :=
    edgePosition_eq_of_swapped_endpoints
      (neighborEdgePosition e .parentAbove) e.1
      hc ha
  exact (neighbor_edgeAdjacent e .parentAbove).1 hne.symm

theorem parentSibling_neighbor_ne_parentAbove
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    neighborEdgePosition e .parentSibling ≠
      neighborEdgePosition e .parentAbove := by
  intro h
  have hs := parentSibling_neighbor_parent e
  have ha := parentAbove_neighbor_child e
  rw [h] at hs
  have hloop :
      (neighborEdgePosition e .parentAbove).parent =
        (neighborEdgePosition e .parentAbove).child :=
    hs.trans ha.symm
  exact
    (neighborEdgePosition e .parentAbove).adj_parent_child.ne hloop

/-- The four slots give four different neighboring graph edges. -/
theorem neighborEdgePosition_injective
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Function.Injective (neighborEdgePosition e) := by
  intro s t h
  cases s <;> cases t
  all_goals try rfl
  · exact False.elim (childLeft_neighbor_ne_childRight e h)
  · exact False.elim (childLeft_neighbor_ne_parentSibling e h)
  · exact False.elim (childLeft_neighbor_ne_parentAbove e h)
  · exact False.elim
      (childLeft_neighbor_ne_childRight e h.symm)
  · exact False.elim (childRight_neighbor_ne_parentSibling e h)
  · exact False.elim (childRight_neighbor_ne_parentAbove e h)
  · exact False.elim
      (childLeft_neighbor_ne_parentSibling e h.symm)
  · exact False.elim
      (childRight_neighbor_ne_parentSibling e h.symm)
  · exact False.elim (parentSibling_neighbor_ne_parentAbove e h)
  · exact False.elim
      (childLeft_neighbor_ne_parentAbove e h.symm)
  · exact False.elim
      (childRight_neighbor_ne_parentAbove e h.symm)
  · exact False.elim
      (parentSibling_neighbor_ne_parentAbove e h.symm)

theorem childBranches_union
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .childLeft ∪ branch e .childRight =
      e.1.cluster := by
  have hraw :=
    childBranches_cover_of_two_le_card
      (principalProper e).tree (principalProper_card e)
  have hmap := congrArg (mapCrownTaxa T) hraw
  rw [mapCrownTaxa_union] at hmap
  simpa [branch, mapCrownTaxa,
    edge_eq_inside_principalProper e,
    GraphQuartet.PhyloTree.EdgePosition.cluster] using hmap

theorem parentBranches_union_principal
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .parentSibling ∪
        (branch e .parentAbove \ {T.root}) ∪
        e.1.cluster =
      Finset.univ.erase T.root := by
  let p := principalProper e
  have hraw :=
    ProperSubtree.parentBranches_cover
      (∅ : Finset {x : X // x ≠ T.root}) p
  have hmap := congrArg (mapCrownTaxa T) hraw
  rw [mapCrownTaxa_union, mapCrownTaxa_union,
    mapCrownTaxa_union] at hmap
  simp only [mapCrownTaxa_empty, Finset.empty_union] at hmap
  have hcrown :
      mapCrownTaxa T T.crown.leaves.toFinset =
        Finset.univ.erase T.root := by
    simpa [mapCrownTaxa,
      GraphQuartet.PhyloTree.EdgePosition.cluster] using
      crown_cluster_eq_erase_root T
  rw [hcrown] at hmap
  have hroot :
      T.root ∉
        mapCrownTaxa T
          (ProperSubtree.parentBranches ∅ p).2 := by
    intro hx
    simp only [mapCrownTaxa, Finset.mem_image] at hx
    obtain ⟨y, -, hy⟩ := hx
    exact y.property hy
  have habove :
      branch e .parentAbove \ {T.root} =
        mapCrownTaxa T
          (ProperSubtree.parentBranches ∅ p).2 := by
    ext x
    simp only [branch, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hne⟩
      · exact False.elim (hne hx)
      · exact hx
    · intro hx
      refine ⟨Or.inr ?_, ?_⟩
      · simpa [p] using hx
      · intro hxr
        subst x
        exact hroot (by simpa [p] using hx)
  rw [habove]
  simpa [p, branch, mapCrownTaxa,
    edge_eq_inside_principalProper e,
    GraphQuartet.PhyloTree.EdgePosition.cluster] using hmap

/-- The four incident branch blocks are exhaustive. -/
theorem branch_cover
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .childLeft ∪ branch e .childRight ∪
        branch e .parentSibling ∪ branch e .parentAbove =
      Finset.univ := by
  have hchild := childBranches_union e
  have hparent := parentBranches_union_principal e
  rw [hchild]
  ext x
  by_cases hx : x = T.root
  · subst x
    simp [branch]
  · have hnot :
        x ∉ ({T.root} : Finset X) := by simpa
    have habove :
        x ∈ branch e .parentAbove ↔
          x ∈ branch e .parentAbove \ {T.root} := by
      simp [hnot]
    rw [Finset.ext_iff] at hparent
    have hp := hparent x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true] at hp ⊢
    have hunivErase : x ∈ Finset.univ.erase T.root := by simp [hx]
    rcases hp.mpr hunivErase with (hps | ha) | hecluster
    · exact Or.inl (Or.inr hps)
    · exact Or.inr (habove.mpr ha)
    · exact Or.inl (Or.inl hecluster)

theorem childLeft_disjoint_childRight
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint (branch e .childLeft) (branch e .childRight) := by
  have hraw :=
    childBranches_disjoint (principalProper e).tree
      ((principalProper e).leaves_nodup T.nodup_leaves)
  exact mapCrownTaxa_disjoint T hraw

theorem parent_pairwise_raw
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint
        (ProperSubtree.parentBranches ∅ (principalProper e)).1
        (ProperSubtree.parentBranches ∅ (principalProper e)).2 ∧
      Disjoint
        (ProperSubtree.parentBranches ∅ (principalProper e)).1
        (principalProper e).tree.leaves.toFinset ∧
      Disjoint
        (ProperSubtree.parentBranches ∅ (principalProper e)).2
        (principalProper e).tree.leaves.toFinset := by
  apply ProperSubtree.parentBranches_pairwise_disjoint
      (∅ : Finset {x : X // x ≠ T.root})
      (principalProper e) T.nodup_leaves
  simp

theorem parentSibling_disjoint_principal
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint (branch e .parentSibling) e.1.cluster := by
  have hraw := (parent_pairwise_raw e).2.1
  simpa [branch, mapCrownTaxa,
    edge_eq_inside_principalProper e,
    GraphQuartet.PhyloTree.EdgePosition.cluster] using
      mapCrownTaxa_disjoint T hraw

theorem principal_disjoint_parentAbove
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint e.1.cluster (branch e .parentAbove) := by
  have hraw := (parent_pairwise_raw e).2.2
  simpa [branch, mapCrownTaxa,
    edge_eq_inside_principalProper e,
    GraphQuartet.PhyloTree.EdgePosition.cluster] using
      mapCrownTaxa_disjoint_insert_root T hraw.symm

theorem parentSibling_disjoint_parentAbove
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint (branch e .parentSibling)
      (branch e .parentAbove) := by
  have hraw := (parent_pairwise_raw e).1
  simpa [branch] using
    mapCrownTaxa_disjoint_insert_root T hraw

theorem parentAbove_branch_eq_other_compl
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .parentAbove =
      (e.1.cluster ∪ branch e .parentSibling)ᶜ := by
  have hcover := branch_cover e
  rw [childBranches_union e] at hcover
  have hdisj :
      Disjoint (e.1.cluster ∪ branch e .parentSibling)
        (branch e .parentAbove) := by
    rw [Finset.disjoint_union_left]
    exact
      ⟨principal_disjoint_parentAbove e,
        parentSibling_disjoint_parentAbove e⟩
  ext x
  simp only [Finset.mem_compl]
  constructor
  · intro hx hother
    exact Finset.disjoint_left.mp hdisj hother hx
  · intro hnot
    have hxuniv : x ∈ Finset.univ := Finset.mem_univ x
    rw [← hcover] at hxuniv
    rcases Finset.mem_union.mp hxuniv with hother | habove
    · exact False.elim (hnot hother)
    · exact habove

theorem parentAbove_branch_eq_neighbor_cluster_compl
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .parentAbove =
      (neighborEdgePosition e .parentAbove).clusterᶜ := by
  rw [parentAbove_branch_eq_other_compl e,
    parentAbove_neighbor_cluster e]

theorem childLeft_subset_principal
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .childLeft ⊆ e.1.cluster := by
  rw [← childBranches_union e]
  exact Finset.subset_union_left

theorem childRight_subset_principal
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    branch e .childRight ⊆ e.1.cluster := by
  rw [← childBranches_union e]
  exact Finset.subset_union_right

theorem childLeft_disjoint_parentSibling
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint (branch e .childLeft)
      (branch e .parentSibling) :=
  (parentSibling_disjoint_principal e).symm.mono_left
    (childLeft_subset_principal e)

theorem childRight_disjoint_parentSibling
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint (branch e .childRight)
      (branch e .parentSibling) :=
  (parentSibling_disjoint_principal e).symm.mono_left
    (childRight_subset_principal e)

theorem childLeft_disjoint_parentAbove
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint (branch e .childLeft)
      (branch e .parentAbove) :=
  (principal_disjoint_parentAbove e).mono_left
    (childLeft_subset_principal e)

theorem childRight_disjoint_parentAbove
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Disjoint (branch e .childRight)
      (branch e .parentAbove) :=
  (principal_disjoint_parentAbove e).mono_left
    (childRight_subset_principal e)

/-- Distinct incident slots have disjoint taxon blocks. -/
theorem branch_disjoint
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    {s t : Slot} (hst : s ≠ t) :
    Disjoint (branch e s) (branch e t) := by
  cases s <;> cases t
  all_goals try contradiction
  · exact childLeft_disjoint_childRight e
  · exact childLeft_disjoint_parentSibling e
  · exact childLeft_disjoint_parentAbove e
  · exact (childLeft_disjoint_childRight e).symm
  · exact childRight_disjoint_parentSibling e
  · exact childRight_disjoint_parentAbove e
  · exact (childLeft_disjoint_parentSibling e).symm
  · exact (childRight_disjoint_parentSibling e).symm
  · exact parentSibling_disjoint_parentAbove e
  · exact (childLeft_disjoint_parentAbove e).symm
  · exact (childRight_disjoint_parentAbove e).symm
  · exact (parentSibling_disjoint_parentAbove e).symm

theorem branch_nonempty
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    (branch e s).Nonempty := by
  cases s with
  | childLeft =>
      rw [childLeft_branch_eq_neighbor_cluster]
      exact cluster_nonempty T _
  | childRight =>
      rw [childRight_branch_eq_neighbor_cluster]
      exact cluster_nonempty T _
  | parentSibling =>
      rw [parentSibling_branch_eq_neighbor_cluster]
      exact cluster_nonempty T _
  | parentAbove =>
      refine ⟨T.root, ?_⟩
      simp [branch]

/-- Slots whose neighboring edge is itself quartet-relevant.  These are
exactly the endpoint atoms of the manuscript; the remaining slots are the
residual branches at the two endpoints. -/
def EndpointSlot
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :=
  {s : Slot //
    2 ≤ (neighborEdgePosition e s).cluster.card ∧
      2 ≤ (neighborEdgePosition e s).clusterᶜ.card}

/-- Ordered adjacent correction occurrences having fixed first edge `e`. -/
def CorrectionsFrom
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :=
  {a : AdjacentCorrection T // first a = e}

/-- The correction occurrence indexed by a relevant incident slot. -/
noncomputable def endpointCorrection
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    (s : EndpointSlot e) : AdjacentCorrection T :=
  ⟨(e, ⟨neighborEdgePosition e s.1, s.2⟩),
    neighbor_edgeAdjacent e s.1⟩

theorem correctionK_endpointCorrection
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    (s : EndpointSlot e) :
    correctionK (endpointCorrection e s) = branch e s.1 := by
  rcases s with ⟨s, hs⟩
  cases s with
  | childLeft =>
      have hsub :
          (neighborEdgePosition e .childLeft).cluster ⊆
            e.1.cluster := by
        rw [← childLeft_branch_eq_neighbor_cluster]
        exact childLeft_subset_principal e
      change
        (if (neighborEdgePosition e .childLeft).cluster ⊆
              e.1.cluster then
            (neighborEdgePosition e .childLeft).cluster
          else if e.1.cluster ⊆
              (neighborEdgePosition e .childLeft).cluster then
            (neighborEdgePosition e .childLeft).clusterᶜ
          else
            (neighborEdgePosition e .childLeft).cluster) =
          branch e .childLeft
      rw [if_pos hsub]
      exact (childLeft_branch_eq_neighbor_cluster e).symm
  | childRight =>
      have hsub :
          (neighborEdgePosition e .childRight).cluster ⊆
            e.1.cluster := by
        rw [← childRight_branch_eq_neighbor_cluster]
        exact childRight_subset_principal e
      change
        (if (neighborEdgePosition e .childRight).cluster ⊆
              e.1.cluster then
            (neighborEdgePosition e .childRight).cluster
          else if e.1.cluster ⊆
              (neighborEdgePosition e .childRight).cluster then
            (neighborEdgePosition e .childRight).clusterᶜ
          else
            (neighborEdgePosition e .childRight).cluster) =
          branch e .childRight
      rw [if_pos hsub]
      exact (childRight_branch_eq_neighbor_cluster e).symm
  | parentSibling =>
      have hdisj :
          Disjoint
            (neighborEdgePosition e .parentSibling).cluster
            e.1.cluster := by
        rw [← parentSibling_branch_eq_neighbor_cluster]
        exact parentSibling_disjoint_principal e
      have hnot₁ :
          ¬(neighborEdgePosition e .parentSibling).cluster ⊆
            e.1.cluster := by
        intro hsub
        obtain ⟨x, hx⟩ :=
          cluster_nonempty T
            (neighborEdgePosition e .parentSibling)
        exact Finset.disjoint_left.mp hdisj hx (hsub hx)
      have hnot₂ :
          ¬e.1.cluster ⊆
            (neighborEdgePosition e .parentSibling).cluster := by
        intro hsub
        obtain ⟨x, hx⟩ := cluster_nonempty T e.1
        exact Finset.disjoint_left.mp hdisj (hsub hx) hx
      change
        (if (neighborEdgePosition e .parentSibling).cluster ⊆
              e.1.cluster then
            (neighborEdgePosition e .parentSibling).cluster
          else if e.1.cluster ⊆
              (neighborEdgePosition e .parentSibling).cluster then
            (neighborEdgePosition e .parentSibling).clusterᶜ
          else
            (neighborEdgePosition e .parentSibling).cluster) =
          branch e .parentSibling
      rw [if_neg hnot₁, if_neg hnot₂]
      exact (parentSibling_branch_eq_neighbor_cluster e).symm
  | parentAbove =>
      have hsub :
          e.1.cluster ⊆
            (neighborEdgePosition e .parentAbove).cluster := by
        rw [parentAbove_neighbor_cluster]
        exact Finset.subset_union_left
      have hnot :
          ¬(neighborEdgePosition e .parentAbove).cluster ⊆
            e.1.cluster := by
        intro hbad
        obtain ⟨x, hx⟩ := branch_nonempty e .parentSibling
        have hxin :
            x ∈ (neighborEdgePosition e .parentAbove).cluster := by
          rw [parentAbove_neighbor_cluster]
          exact Finset.mem_union_right _ hx
        have hxprincipal : x ∈ e.1.cluster := hbad hxin
        exact Finset.disjoint_left.mp
          (parentSibling_disjoint_principal e) hx hxprincipal
      change
        (if (neighborEdgePosition e .parentAbove).cluster ⊆
              e.1.cluster then
            (neighborEdgePosition e .parentAbove).cluster
          else if e.1.cluster ⊆
              (neighborEdgePosition e .parentAbove).cluster then
            (neighborEdgePosition e .parentAbove).clusterᶜ
          else
            (neighborEdgePosition e .parentAbove).cluster) =
          branch e .parentAbove
      rw [if_neg hnot, if_pos hsub]
      exact
        (parentAbove_branch_eq_neighbor_cluster_compl e).symm

/-- The same occurrence, with its fixed-first-edge proof retained. -/
noncomputable def endpointCorrectionFrom
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    EndpointSlot e → CorrectionsFrom e :=
  fun s => ⟨endpointCorrection e s, rfl⟩

theorem endpointCorrectionFrom_injective
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Function.Injective (endpointCorrectionFrom e) := by
  intro s t h
  apply Subtype.ext
  apply neighborEdgePosition_injective e
  have hpairs :
      (endpointCorrection e s).1 =
        (endpointCorrection e t).1 :=
    congrArg (fun z : CorrectionsFrom e => z.1.1) h
  exact congrArg (fun z => z.2.1) hpairs

theorem endpointCorrectionFrom_surjective
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Function.Surjective (endpointCorrectionFrom e) := by
  intro a
  have hadj :
      EdgeAdjacent e.1 (second a.1).1 := by
    have hfirst :
        (first a.1).1 = e.1 :=
      congrArg Subtype.val a.2
    unfold first at hfirst
    unfold second
    rw [← hfirst]
    exact a.1.2
  obtain ⟨s, hs⟩ :=
    exists_slot_of_edgeAdjacent e (second a.1).1 hadj
  have hrel :
      2 ≤ (neighborEdgePosition e s).cluster.card ∧
        2 ≤ (neighborEdgePosition e s).clusterᶜ.card := by
    rw [← hs]
    exact (second a.1).2
  let s' : EndpointSlot e := ⟨s, hrel⟩
  refine ⟨s', ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact a.2.symm
  · apply Subtype.ext
    exact hs.symm

/-- Formal version of the manuscript's multiplicity-one map
`h ↦ k(e,h)`: relevant incident slots and ordered adjacent corrections with
first edge `e` are in bijection. -/
noncomputable def endpointSlotEquivCorrectionsFrom
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    EndpointSlot e ≃ CorrectionsFrom e :=
  Equiv.ofBijective (endpointCorrectionFrom e)
    ⟨endpointCorrectionFrom_injective e,
      endpointCorrectionFrom_surjective e⟩

end

end PrincipalBranches

end QuartetV060
