import QuartetV060.PrincipalBranches

/-!
# Principal-edge endpoint atoms and residual blocks

This file turns the four geometric branches incident with a relevant
principal edge into the atom partition used in Appendix A.  A branch whose
neighboring edge is relevant is kept as an endpoint atom.  The remaining
branches at each endpoint are merged into one residual block.  The resulting
blocks are proved nonempty, pairwise disjoint, and exhaustive.
-/

namespace QuartetV060

namespace PrincipalAtoms

open QuartetDistance
open PhyloOccurrences
open PrincipalBranches

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

/-- The two endpoints of a principal edge, viewed as sides of its four-slot
branch decomposition. -/
inductive Side where
  | child
  | parent
  deriving DecidableEq, Fintype, Repr

/-- The endpoint carrying a slot. -/
def slotSide : Slot → Side
  | .childLeft | .childRight => .child
  | .parentSibling | .parentAbove => .parent

/-- The two slots incident with one endpoint of the principal edge. -/
def sideSlots : Side → Finset Slot
  | .child => {.childLeft, .childRight}
  | .parent => {.parentSibling, .parentAbove}

@[simp] theorem slot_mem_own_side (s : Slot) :
    s ∈ sideSlots (slotSide s) := by
  cases s <;> simp [slotSide, sideSlots]

/-- A slot is retained as an endpoint atom precisely when the neighboring
edge is quartet-relevant. -/
def slotRelevant
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) : Prop :=
  2 ≤ (neighborEdgePosition e s).cluster.card ∧
    2 ≤ (neighborEdgePosition e s).clusterᶜ.card

noncomputable instance slotRelevantDecidable
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    Decidable (slotRelevant e s) :=
  Classical.propDecidable _

/-- Raw names for endpoint atoms and the two possible residual blocks. -/
inductive AtomTag where
  | endpoint (s : Slot)
  | residual (q : Side)
  deriving DecidableEq, Fintype, Repr

/-- The slots represented by an atom name.  An endpoint atom represents one
relevant slot; a residual block represents all nonrelevant slots at one
endpoint. -/
def support
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) : AtomTag → Finset Slot
  | .endpoint s => {s}
  | .residual q =>
      (sideSlots q).filter fun s => ¬slotRelevant e s

/-- Valid atom names.  Endpoint names must be relevant, while a residual name
is retained only when at least one nonrelevant slot is present on that side. -/
def Valid
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) : AtomTag → Prop
  | .endpoint s => slotRelevant e s
  | .residual q => (support e (.residual q)).Nonempty

noncomputable instance validDecidable
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : AtomTag) :
    Decidable (Valid e a) :=
  Classical.propDecidable _

/-- The finite atom index set of the principal chart at `e`. -/
def Atom
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :=
  {a : AtomTag // Valid e a}

noncomputable instance atomFintype
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Fintype (Atom e) :=
  Fintype.ofInjective
    (fun a : Atom e => a.1) Subtype.val_injective

noncomputable instance atomDecidableEq
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    DecidableEq (Atom e) :=
  Classical.decEq (Atom e)

/-- The taxon block carried by one chart atom. -/
def block
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) : Finset X :=
  (support e a.1).biUnion (branch e)

/-- The endpoint atom attached to a relevant incident slot. -/
def endpointAtom
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : EndpointSlot e) : Atom e :=
  ⟨.endpoint s.1, s.2⟩

@[simp] theorem support_endpoint
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    support e (.endpoint s) = {s} :=
  rfl

@[simp] theorem block_endpointAtom
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : EndpointSlot e) :
    block e (endpointAtom e s) = branch e s.1 := by
  simp [block, endpointAtom, support]

theorem endpointAtom_injective
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Function.Injective (endpointAtom e) := by
  intro s t h
  exact Subtype.ext
    (AtomTag.endpoint.inj
      (congrArg (fun a : Atom e => a.1) h))

/-- Every slot belongs to the support of exactly the atom obtained by keeping
it when relevant and otherwise sending it to its endpoint residual block. -/
noncomputable def atomOfSlot
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) : Atom e := by
  by_cases hs : slotRelevant e s
  · exact ⟨.endpoint s, hs⟩
  · refine ⟨.residual (slotSide s), ?_⟩
    exact ⟨s, by simp [support, slot_mem_own_side, hs]⟩

theorem slot_mem_atomOfSlot_support
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    s ∈ support e (atomOfSlot e s).1 := by
  classical
  by_cases hs : slotRelevant e s
  · simp [atomOfSlot, hs, support]
  · simp [atomOfSlot, hs, support, slot_mem_own_side]

theorem branch_subset_atomOfSlot_block
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    branch e s ⊆ block e (atomOfSlot e s) := by
  intro x hx
  exact Finset.mem_biUnion.mpr
    ⟨s, slot_mem_atomOfSlot_support e s, hx⟩

/-- Every taxon lies in one of the principal-chart atoms. -/
theorem mem_some_block
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (x : X) :
    ∃ a : Atom e, x ∈ block e a := by
  have hx : x ∈
      branch e .childLeft ∪ branch e .childRight ∪
        branch e .parentSibling ∪ branch e .parentAbove := by
    rw [branch_cover e]
    exact Finset.mem_univ x
  simp only [Finset.mem_union] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact
      ⟨atomOfSlot e .childLeft,
        branch_subset_atomOfSlot_block e .childLeft hx⟩
  · exact
      ⟨atomOfSlot e .childRight,
        branch_subset_atomOfSlot_block e .childRight hx⟩
  · exact
      ⟨atomOfSlot e .parentSibling,
        branch_subset_atomOfSlot_block e .parentSibling hx⟩
  · exact
      ⟨atomOfSlot e .parentAbove,
        branch_subset_atomOfSlot_block e .parentAbove hx⟩

/-- The principal-chart atoms cover the entire leaf set. -/
theorem block_cover
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    Finset.univ.biUnion (block e) = Finset.univ := by
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    obtain ⟨a, hxa⟩ := mem_some_block e x
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ a, hxa⟩

theorem support_endpoint_mem
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    {s t : Slot}
    (h : t ∈ support e (.endpoint s)) :
    t = s := by
  simpa [support] using h

theorem support_residual_side
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    {q : Side} {s : Slot}
    (h : s ∈ support e (.residual q)) :
    slotSide s = q ∧ ¬slotRelevant e s := by
  have hs := Finset.mem_filter.mp h
  constructor
  · cases q <;> cases s <;>
      simp [sideSlots, slotSide] at hs ⊢
  · exact hs.2

/-- Two distinct valid atoms have disjoint slot supports. -/
theorem support_disjoint
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    {a b : Atom e} (hab : a ≠ b) :
    Disjoint (support e a.1) (support e b.1) := by
  rw [Finset.disjoint_left]
  intro s hsa hsb
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | endpoint u =>
      have hsu : s = u := support_endpoint_mem e hsa
      subst s
      cases b with
      | endpoint v =>
          have huv : u = v := support_endpoint_mem e hsb
          subst v
          exact hab rfl
      | residual q =>
          exact (support_residual_side e hsb).2 ha
  | residual q =>
      cases b with
      | endpoint v =>
          have hsv : s = v := support_endpoint_mem e hsb
          subst s
          exact (support_residual_side e hsa).2 hb
      | residual r =>
          have hq := support_residual_side e hsa
          have hr := support_residual_side e hsb
          have hqr : q = r := hq.1.symm.trans hr.1
          subst r
          exact hab rfl

/-- Distinct chart atoms carry disjoint taxon blocks. -/
theorem block_disjoint
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    {a b : Atom e} (hab : a ≠ b) :
    Disjoint (block e a) (block e b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rcases Finset.mem_biUnion.mp hxa with ⟨s, hsa, hxs⟩
  rcases Finset.mem_biUnion.mp hxb with ⟨t, htb, hxt⟩
  have hst : s ≠ t := by
    intro h
    subst t
    exact Finset.disjoint_left.mp
      (support_disjoint e hab) hsa htb
  exact Finset.disjoint_left.mp (branch_disjoint e hst) hxs hxt

/-- Every valid atom block is nonempty. -/
theorem block_nonempty
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) :
    (block e a).Nonempty := by
  cases a with
  | mk a ha =>
      cases a with
      | endpoint s =>
          exact ⟨Classical.choose (branch_nonempty e s),
            by
              apply Finset.mem_biUnion.mpr
              exact
                ⟨s, by simp [support],
                  Classical.choose_spec (branch_nonempty e s)⟩⟩
      | residual q =>
          obtain ⟨s, hs⟩ := ha
          exact ⟨Classical.choose (branch_nonempty e s),
            by
              apply Finset.mem_biUnion.mpr
              exact
                ⟨s, hs,
                  Classical.choose_spec (branch_nonempty e s)⟩⟩

/-- Concrete bridge-ledger ownership at an endpoint: the `K`-block of the
ordered adjacent correction is exactly the endpoint atom block indexed by
that correction. -/
theorem correctionK_eq_endpoint_block
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : EndpointSlot e) :
    correctionK (endpointCorrection e s) =
      block e (endpointAtom e s) := by
  rw [correctionK_endpointCorrection, block_endpointAtom]

theorem correctionL_endpoint_childLeft
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    (hrel : slotRelevant e .childLeft) :
    correctionL
        (endpointCorrection e
          (⟨.childLeft, hrel⟩ : EndpointSlot e)) =
      e.1.clusterᶜ := by
  have hsub :
      (neighborEdgePosition e .childLeft).cluster ⊆
        e.1.cluster := by
    rw [← childLeft_branch_eq_neighbor_cluster]
    exact childLeft_subset_principal e
  change
    (if (neighborEdgePosition e .childLeft).cluster ⊆
          e.1.cluster then e.1.clusterᶜ
      else e.1.cluster) =
      e.1.clusterᶜ
  rw [if_pos hsub]

theorem correctionL_endpoint_childRight
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    (hrel : slotRelevant e .childRight) :
    correctionL
        (endpointCorrection e
          (⟨.childRight, hrel⟩ : EndpointSlot e)) =
      e.1.clusterᶜ := by
  have hsub :
      (neighborEdgePosition e .childRight).cluster ⊆
        e.1.cluster := by
    rw [← childRight_branch_eq_neighbor_cluster]
    exact childRight_subset_principal e
  change
    (if (neighborEdgePosition e .childRight).cluster ⊆
          e.1.cluster then e.1.clusterᶜ
      else e.1.cluster) =
      e.1.clusterᶜ
  rw [if_pos hsub]

theorem correctionL_endpoint_parentSibling
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    (hrel : slotRelevant e .parentSibling) :
    correctionL
        (endpointCorrection e
          (⟨.parentSibling, hrel⟩ : EndpointSlot e)) =
      e.1.cluster := by
  have hdisj :
      Disjoint
        (neighborEdgePosition e .parentSibling).cluster
        e.1.cluster := by
    rw [← parentSibling_branch_eq_neighbor_cluster]
    exact parentSibling_disjoint_principal e
  have hnot :
      ¬(neighborEdgePosition e .parentSibling).cluster ⊆
        e.1.cluster := by
    intro hsub
    obtain ⟨x, hx⟩ :=
      cluster_nonempty T
        (neighborEdgePosition e .parentSibling)
    exact Finset.disjoint_left.mp hdisj hx (hsub hx)
  change
    (if (neighborEdgePosition e .parentSibling).cluster ⊆
          e.1.cluster then e.1.clusterᶜ
      else e.1.cluster) =
      e.1.cluster
  rw [if_neg hnot]

theorem correctionL_endpoint_parentAbove
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T)
    (hrel : slotRelevant e .parentAbove) :
    correctionL
        (endpointCorrection e
          (⟨.parentAbove, hrel⟩ : EndpointSlot e)) =
      e.1.cluster := by
  have hnot :
      ¬(neighborEdgePosition e .parentAbove).cluster ⊆
        e.1.cluster := by
    intro hsub
    obtain ⟨x, hx⟩ := branch_nonempty e .parentSibling
    have hxin :
        x ∈ (neighborEdgePosition e .parentAbove).cluster := by
      rw [parentAbove_neighbor_cluster]
      exact Finset.mem_union_right _ hx
    have hxprincipal : x ∈ e.1.cluster := hsub hxin
    exact Finset.disjoint_left.mp
      (parentSibling_disjoint_principal e) hx hxprincipal
  change
    (if (neighborEdgePosition e .parentAbove).cluster ⊆
          e.1.cluster then e.1.clusterᶜ
      else e.1.cluster) =
      e.1.cluster
  rw [if_neg hnot]

/-- Regard an ordered adjacent correction as an occurrence in the fiber over
its own first edge. -/
def correctionFromFirst
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    CorrectionsFrom (first a) :=
  ⟨a, rfl⟩

/-- The endpoint slot of the first-edge principal chart selected by an
ordered adjacent correction. -/
noncomputable def correctionSlot
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    EndpointSlot (first a) :=
  (endpointSlotEquivCorrectionsFrom (first a)).symm
    (correctionFromFirst a)

@[simp] theorem endpointCorrection_correctionSlot
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    endpointCorrection (first a) (correctionSlot a) = a := by
  have h :=
    (endpointSlotEquivCorrectionsFrom
      (first a)).apply_symm_apply (correctionFromFirst a)
  exact congrArg (fun z : CorrectionsFrom (first a) => z.1) h

/-- The side opposite the endpoint slot selected by a correction is exactly
the outer block `L` of that ordered correction. -/
theorem selectedOppositeSide_eq_correctionL
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    (match slotSide (correctionSlot a).1 with
      | .child => (first a).1.clusterᶜ
      | .parent => (first a).1.cluster) =
      correctionL a := by
  calc
    (match slotSide (correctionSlot a).1 with
      | .child => (first a).1.clusterᶜ
      | .parent => (first a).1.cluster) =
        correctionL
          (endpointCorrection (first a) (correctionSlot a)) := by
            let s := correctionSlot a
            change
              (match slotSide s.1 with
                | .child => (first a).1.clusterᶜ
                | .parent => (first a).1.cluster) =
                correctionL (endpointCorrection (first a) s)
            rcases s with ⟨s, hs⟩
            cases s with
            | childLeft =>
                exact
                  (correctionL_endpoint_childLeft
                    (first a) hs).symm
            | childRight =>
                exact
                  (correctionL_endpoint_childRight
                    (first a) hs).symm
            | parentSibling =>
                exact
                  (correctionL_endpoint_parentSibling
                    (first a) hs).symm
            | parentAbove =>
                exact
                  (correctionL_endpoint_parentAbove
                    (first a) hs).symm
    _ = correctionL a := by
      rw [endpointCorrection_correctionSlot]

/-- The selected endpoint atom of the source chart is the concrete `K` block
of the ordered bridge. -/
theorem correctionK_eq_selectedAtomBlock
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    correctionK a =
      block (first a)
        (endpointAtom (first a) (correctionSlot a)) := by
  calc
    correctionK a =
        correctionK
          (endpointCorrection (first a) (correctionSlot a)) := by
            rw [endpointCorrection_correctionSlot]
    _ =
        block (first a)
          (endpointAtom (first a) (correctionSlot a)) :=
      correctionK_eq_endpoint_block
        (first a) (correctionSlot a)

/-- In the reversed principal chart, the selected endpoint atom is the
original bridge's `L` block. -/
theorem correctionL_eq_reversedSelectedAtomBlock
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    correctionL a =
      block (second a)
        (endpointAtom (second a)
          (correctionSlot
            (PhyloBridgeReversal.reverseCorrection a))) := by
  rw [← PhyloBridgeReversal.correctionK_reverseCorrection a]
  exact correctionK_eq_selectedAtomBlock
    (PhyloBridgeReversal.reverseCorrection a)

end

end PrincipalAtoms

end QuartetV060
