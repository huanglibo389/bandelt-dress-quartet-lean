import QuartetV060.PrincipalAtoms
import QuartetV060.LocalTable
import QuartetV060.ResidualPartition

/-!
# Concrete principal charts

The abstract local table used in Appendix A is instantiated here from two
actual relevant edges, one in each phylogenetic tree.  Its rows and columns
are the nonempty atom partitions constructed in `PrincipalAtoms`.
-/

namespace QuartetV060

namespace PrincipalChart

open scoped BigOperators

open QuartetDistance
open PhyloOccurrences
open PrincipalBranches
open PrincipalAtoms

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

/-- A taxon belongs to at most one atom block. -/
theorem atom_unique
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (x : X)
    {a b : Atom e}
    (hxa : x ∈ block e a) (hxb : x ∈ block e b) :
    a = b := by
  by_contra hab
  exact Finset.disjoint_left.mp (block_disjoint e hab) hxa hxb

/-- The unique atom containing a taxon. -/
noncomputable def atomAt
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (x : X) : Atom e :=
  Classical.choose (mem_some_block e x)

@[simp] theorem atomAt_mem
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (x : X) :
    x ∈ block e (atomAt e x) :=
  Classical.choose_spec (mem_some_block e x)

theorem mem_block_iff_atomAt_eq
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (x : X) (a : Atom e) :
    x ∈ block e a ↔ atomAt e x = a := by
  constructor
  · intro hxa
    exact atom_unique e x (atomAt_mem e x) hxa
  · intro h
    rw [← h]
    exact atomAt_mem e x

/-- The manuscript sectors `a,b,c,d`: endpoint atoms at the two endpoints
of the principal edge are `a,b`, and their residual blocks are `c,d`. -/
def atomSector
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) : Sector :=
  match a.1 with
  | .endpoint s =>
      match slotSide s with
      | .child => .a
      | .parent => .b
  | .residual q =>
      match q with
      | .child => .c
      | .parent => .d

/-- The concrete four-sector structure of one principal edge. -/
def fourSector
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) : FourSector (Atom e) where
  sector := atomSector e

/-- The endpoint side underlying an atom, independently of whether the atom
is an endpoint atom or a residual block. -/
def atomSide
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) : Side :=
  match a.1 with
  | .endpoint s => slotSide s
  | .residual q => q

theorem sameSide_iff_atomSide_eq
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a b : Atom e) :
    (fourSector e).sameSide a b ↔
      atomSide e a = atomSide e b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | endpoint s =>
      cases hs : slotSide s <;>
        cases b with
        | endpoint t =>
            cases ht : slotSide t <;>
              simp [FourSector.sameSide, fourSector, atomSector,
                atomSide, hs, ht, FourSector.isLeftSector]
        | residual q =>
            cases q <;>
              simp [FourSector.sameSide, fourSector, atomSector,
                atomSide, hs, FourSector.isLeftSector]
  | residual q =>
      cases q <;>
        cases b with
        | endpoint t =>
            cases ht : slotSide t <;>
              simp [FourSector.sameSide, fourSector, atomSector,
                atomSide, ht, FourSector.isLeftSector]
        | residual r =>
            cases r <;>
              simp [FourSector.sameSide, fourSector, atomSector,
                atomSide, FourSector.isLeftSector]

theorem atomOfSlot_side
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot) :
    atomSide e (atomOfSlot e s) = slotSide s := by
  classical
  by_cases hs : slotRelevant e s
  · simp [atomOfSlot, hs, atomSide]
  · simp [atomOfSlot, hs, atomSide]

/-- A fixed incident slot on the endpoint opposite a given side. -/
def oppositeWitnessSlot : Side → Slot
  | .child => .parentSibling
  | .parent => .childLeft

@[simp] theorem oppositeWitnessSlot_side (q : Side) :
    slotSide (oppositeWitnessSlot q) ≠ q := by
  cases q <;> simp [oppositeWitnessSlot, slotSide]

/-- Every atom has a concrete atom on the opposite side. -/
def oppositeWitness
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) : Atom e :=
  atomOfSlot e (oppositeWitnessSlot (atomSide e a))

theorem oppositeWitness_not_sameSide
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) :
    ¬(fourSector e).sameSide a (oppositeWitness e a) := by
  rw [sameSide_iff_atomSide_eq]
  change
    ¬atomSide e a =
      atomSide e
        (atomOfSlot e
          (oppositeWitnessSlot (atomSide e a)))
  rw [atomOfSlot_side]
  exact Ne.symm (oppositeWitnessSlot_side (atomSide e a))

theorem oppositeWitness_mem_oppositeSideBlock
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) :
    oppositeWitness e a ∈
      (fourSector e).oppositeSideBlock a := by
  exact (FourSector.mem_oppositeSideBlock_iff
    (fourSector e) a (oppositeWitness e a)).2
      (oppositeWitness_not_sameSide e a)

theorem support_slotSide_eq_atomSide
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e)
    {s : Slot} (hs : s ∈ support e a.1) :
    slotSide s = atomSide e a := by
  rcases a with ⟨a, ha⟩
  cases a with
  | endpoint t =>
      have hst : s = t :=
        support_endpoint_mem e hs
      subst s
      rfl
  | residual q =>
      exact (support_residual_side e hs).1

theorem branch_subset_cluster_of_child
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot)
    (hs : slotSide s = .child) :
    branch e s ⊆ e.1.cluster := by
  cases s with
  | childLeft => exact childLeft_subset_principal e
  | childRight => exact childRight_subset_principal e
  | parentSibling => simp [slotSide] at hs
  | parentAbove => simp [slotSide] at hs

theorem branch_subset_cluster_compl_of_parent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : Slot)
    (hs : slotSide s = .parent) :
    branch e s ⊆ e.1.clusterᶜ := by
  intro x hx
  apply Finset.mem_compl.mpr
  cases s with
  | childLeft => simp [slotSide] at hs
  | childRight => simp [slotSide] at hs
  | parentSibling =>
      exact fun hxe =>
        Finset.disjoint_left.mp
          (parentSibling_disjoint_principal e) hx hxe
  | parentAbove =>
      exact fun hxe =>
        Finset.disjoint_left.mp
          (principal_disjoint_parentAbove e) hxe hx

theorem block_subset_cluster_of_child
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e)
    (ha : atomSide e a = .child) :
    block e a ⊆ e.1.cluster := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨s, hs, hxs⟩
  exact branch_subset_cluster_of_child e s
    ((support_slotSide_eq_atomSide e a hs).trans ha) hxs

theorem block_subset_cluster_compl_of_parent
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e)
    (ha : atomSide e a = .parent) :
    block e a ⊆ e.1.clusterᶜ := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨s, hs, hxs⟩
  exact branch_subset_cluster_compl_of_parent e s
    ((support_slotSide_eq_atomSide e a hs).trans ha) hxs

theorem atomAt_side_child_iff_mem_cluster
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (x : X) :
    atomSide e (atomAt e x) = .child ↔
      x ∈ e.1.cluster := by
  constructor
  · intro hside
    exact block_subset_cluster_of_child e (atomAt e x) hside
      (atomAt_mem e x)
  · intro hx
    cases hside : atomSide e (atomAt e x) with
    | child => rfl
    | parent =>
        have hxcompl :=
          block_subset_cluster_compl_of_parent
            e (atomAt e x) hside (atomAt_mem e x)
        exact False.elim ((Finset.mem_compl.mp hxcompl) hx)

theorem atomAt_side_parent_iff_mem_cluster_compl
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (x : X) :
    atomSide e (atomAt e x) = .parent ↔
      x ∈ e.1.clusterᶜ := by
  constructor
  · intro hside
    exact block_subset_cluster_compl_of_parent
      e (atomAt e x) hside (atomAt_mem e x)
  · intro hx
    cases hside : atomSide e (atomAt e x) with
    | parent => rfl
    | child =>
        have hxcluster :=
          block_subset_cluster_of_child
            e (atomAt e x) hside (atomAt_mem e x)
        exact False.elim ((Finset.mem_compl.mp hx) hxcluster)

/-- Taxon union of a finite set of principal-chart atoms. -/
def aggregateBlock
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (S : Finset (Atom e)) :
    Finset X :=
  S.biUnion (block e)

theorem mem_aggregateBlock_iff
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (S : Finset (Atom e))
    (x : X) :
    x ∈ aggregateBlock e S ↔ atomAt e x ∈ S := by
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨a, haS, hxa⟩
    rw [mem_block_iff_atomAt_eq] at hxa
    rwa [hxa]
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨atomAt e x, hx, atomAt_mem e x⟩

theorem aggregateBlock_opposite_eq
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) :
    aggregateBlock e ((fourSector e).oppositeSideBlock a) =
      match atomSide e a with
      | .child => e.1.clusterᶜ
      | .parent => e.1.cluster := by
  ext x
  rw [mem_aggregateBlock_iff]
  rw [FourSector.mem_oppositeSideBlock_iff]
  rw [sameSide_iff_atomSide_eq]
  cases ha : atomSide e a with
  | child =>
      simp only [ha]
      constructor
      · intro hne
        cases hx : atomSide e (atomAt e x) with
        | child => exact False.elim (hne hx.symm)
        | parent =>
            exact
              (atomAt_side_parent_iff_mem_cluster_compl e x).1 hx
      · intro hx
        have hp :=
          (atomAt_side_parent_iff_mem_cluster_compl e x).2 hx
        exact fun h => by simpa [hp] using h
  | parent =>
      simp only [ha]
      constructor
      · intro hne
        cases hx : atomSide e (atomAt e x) with
        | child =>
            exact
              (atomAt_side_child_iff_mem_cluster e x).1 hx
        | parent => exact False.elim (hne hx.symm)
      · intro hx
        have hc :=
          (atomAt_side_child_iff_mem_cluster e x).2 hx
        exact fun h => by simpa [hc] using h

/-- For the endpoint atom selected by an ordered adjacent correction, the
aggregate opposite-side block in the source chart is exactly the bridge
block `L`. -/
theorem aggregateBlock_opposite_selected_eq_correctionL
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    aggregateBlock (first a)
        ((fourSector (first a)).oppositeSideBlock
          (endpointAtom (first a) (correctionSlot a))) =
      correctionL a := by
  rw [aggregateBlock_opposite_eq]
  exact selectedOppositeSide_eq_correctionL a

@[simp] theorem endpointAtom_sector
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : EndpointSlot e) :
    (fourSector e).sector (endpointAtom e s) =
      match slotSide s.1 with
      | .child => .a
      | .parent => .b := by
  rfl

theorem endpointAtom_isEndpoint
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (s : EndpointSlot e) :
    (fourSector e).isEndpoint (endpointAtom e s) := by
  unfold FourSector.isEndpoint
  rw [endpointAtom_sector]
  cases slotSide s.1 <;> simp

theorem residualAtom_isResidual
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (q : Side)
    (h : (support e (.residual q)).Nonempty) :
    (fourSector e).isResidual
      (⟨.residual q, h⟩ : Atom e) := by
  cases q <;>
    simp [FourSector.isResidual, fourSector, atomSector]

/-- Endpoint atoms, viewed as the subtype cut out by the four-sector
predicate. -/
def EndpointAtomIndex
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :=
  {a : Atom e // (fourSector e).isEndpoint a}

/-- The geometric endpoint-slot indexing and the four-sector endpoint-atom
indexing are the same finite type. -/
noncomputable def endpointAtomEquiv
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    EndpointSlot e ≃ EndpointAtomIndex e := by
  refine Equiv.ofBijective
    (fun s => ⟨endpointAtom e s, endpointAtom_isEndpoint e s⟩)
    ⟨?_, ?_⟩
  · intro s t h
    apply endpointAtom_injective e
    exact congrArg Subtype.val h
  · intro a
    rcases a with ⟨a, ha⟩
    rcases a with ⟨a, hvalid⟩
    cases a with
    | endpoint s =>
        let es : EndpointSlot e := ⟨s, hvalid⟩
        refine ⟨es, ?_⟩
        apply Subtype.ext
        rfl
    | residual q =>
        cases q <;>
          simp [FourSector.isEndpoint, fourSector, atomSector] at ha

/-- The concrete `I,D,Δ_E` residual partition on one principal-edge atom
set.  Its endpoint set is exactly `a ∪ b`, and the opposite of an endpoint
atom is the full central side across the principal split. -/
def residualPartition
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) :
    ResidualPartition (Atom e) where
  endpoint :=
    Finset.univ.filter fun a => (fourSector e).isEndpoint a
  opposite := (fourSector e).oppositeSideBlock
  self_not_mem := by
    intro a ha
    rw [FourSector.mem_oppositeSideBlock_iff]
    exact not_not_intro <| by
      unfold FourSector.sameSide
      rfl

@[simp] theorem mem_residualPartition_endpoint
    {T : Tree.PhyloTree X}
    (e : RelevantEdge T) (a : Atom e) :
    a ∈ (residualPartition e).endpoint ↔
      (fourSector e).isEndpoint a := by
  simp [residualPartition]

/-- The row-column fiber of a pair of atoms. -/
def cellFiber
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (k : Atom f) : Finset X :=
  Finset.univ.filter fun x =>
    atomAt e x = i ∧ atomAt f x = k

theorem mem_cellFiber_iff
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (k : Atom f) (x : X) :
    x ∈ cellFiber e f i k ↔
      x ∈ block e i ∩ block f k := by
  simp [cellFiber, mem_block_iff_atomAt_eq]

/-- The normalized mass of one row-column atom intersection. -/
def cellMass
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (k : Atom f) : ℚ :=
  (∑ x : X,
      if atomAt e x = i ∧ atomAt f x = k
      then (1 : ℚ) else 0) /
    Fintype.card X

theorem cellMass_nonneg
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (k : Atom f) :
    0 ≤ cellMass e f i k := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact Nat.cast_nonneg _

theorem card_X_pos : 0 < Fintype.card X :=
  Fintype.card_pos_iff.mpr inferInstance

theorem sum_atom_pair_indicator
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (x : X) :
    (∑ i : Atom e, ∑ k : Atom f,
      if atomAt e x = i ∧ atomAt f x = k
      then (1 : ℚ) else 0) = 1 := by
  calc
    (∑ i : Atom e, ∑ k : Atom f,
        if atomAt e x = i ∧ atomAt f x = k
        then (1 : ℚ) else 0) =
        ∑ i : Atom e,
          if atomAt e x = i then (1 : ℚ) else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : atomAt e x = i
            · simp [hi]
            · simp [hi]
    _ = 1 := by simp

theorem sum_cellIndicators
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    (∑ i : Atom e, ∑ k : Atom f,
      ∑ x : X,
        if atomAt e x = i ∧ atomAt f x = k
        then (1 : ℚ) else 0) =
      (Fintype.card X : ℚ) := by
  calc
    (∑ i : Atom e, ∑ k : Atom f,
        ∑ x : X,
          if atomAt e x = i ∧ atomAt f x = k
          then (1 : ℚ) else 0) =
        ∑ i : Atom e, ∑ x : X, ∑ k : Atom f,
          if atomAt e x = i ∧ atomAt f x = k
          then (1 : ℚ) else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ = ∑ x : X, ∑ i : Atom e, ∑ k : Atom f,
          if atomAt e x = i ∧ atomAt f x = k
          then (1 : ℚ) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : X, (1 : ℚ) := by
          apply Finset.sum_congr rfl
          intro x _
          exact sum_atom_pair_indicator e f x
    _ = (Fintype.card X : ℚ) := by simp

/-- The concrete normalized joint mass table of the principal chart
`χ=(e,f)`. -/
def jointMass
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    JointMass (Atom e) (Atom f) where
  a := cellMass e f
  nonneg := cellMass_nonneg e f
  total := by
    unfold cellMass
    calc
      (∑ i : Atom e, ∑ k : Atom f,
          (∑ x : X,
            if atomAt e x = i ∧ atomAt f x = k
            then (1 : ℚ) else 0) /
            (Fintype.card X : ℚ)) =
          ∑ i : Atom e,
            (∑ k : Atom f, ∑ x : X,
              if atomAt e x = i ∧ atomAt f x = k
              then (1 : ℚ) else 0) /
              (Fintype.card X : ℚ) := by
                apply Finset.sum_congr rfl
                intro i _
                exact
                  (Finset.sum_div Finset.univ
                    (fun k : Atom f =>
                      ∑ x : X,
                        if atomAt e x = i ∧ atomAt f x = k
                        then (1 : ℚ) else 0)
                    (Fintype.card X : ℚ)).symm
      _ =
          (∑ i : Atom e, ∑ k : Atom f, ∑ x : X,
            if atomAt e x = i ∧ atomAt f x = k
            then (1 : ℚ) else 0) /
            (Fintype.card X : ℚ) := by
              exact
                (Finset.sum_div Finset.univ
                  (fun i : Atom e =>
                    ∑ k : Atom f, ∑ x : X,
                      if atomAt e x = i ∧ atomAt f x = k
                      then (1 : ℚ) else 0)
                  (Fintype.card X : ℚ)).symm
      _ = 1 := by
        rw [sum_cellIndicators e f]
        exact div_self
          (by exact_mod_cast (card_X_pos (X := X)).ne')

@[simp] theorem jointMass_a
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (k : Atom f) :
    (jointMass e f).a i k =
      (block e i ∩ block f k).card / Fintype.card X := by
  unfold jointMass cellMass
  have hfiber :
      cellFiber e f i k = block e i ∩ block f k := by
    ext x
    exact mem_cellFiber_iff e f i k x
  rw [← hfiber]
  congr 1
  simpa [cellFiber] using
    (Finset.sum_boole
      (fun x : X => atomAt e x = i ∧ atomAt f x = k)
      (Finset.univ : Finset X))

/-- A concrete column mass is the normalized cardinality of its taxon
block. -/
theorem jointMass_colMass_eq
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (k : Atom f) :
    (jointMass e f).colMass k =
      (block f k).card / Fintype.card X := by
  have hpair :
      ((Finset.univ : Finset (Atom e)) : Set (Atom e)).PairwiseDisjoint
        (fun i => block e i ∩ block f k) := by
    intro i _ j _ hij
    change Disjoint (block e i ∩ block f k)
      (block e j ∩ block f k)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    exact Finset.disjoint_left.mp (block_disjoint e hij)
      (Finset.mem_inter.mp hxi).1
      (Finset.mem_inter.mp hxj).1
  have hunion :
      (Finset.univ : Finset (Atom e)).biUnion
          (fun i => block e i ∩ block f k) =
        block f k := by
    ext x
    simp [mem_block_iff_atomAt_eq]
  unfold JointMass.colMass
  simp_rw [jointMass_a]
  rw [← Finset.sum_div]
  rw [← Nat.cast_sum]
  rw [← Finset.card_biUnion hpair]
  rw [hunion]

/-- The mass of an aggregate column block is the normalized cardinality of
the union of its atom blocks. -/
theorem jointMass_colBlockMass_eq
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (S : Finset (Atom f)) :
    (jointMass e f).colBlockMass S =
      (aggregateBlock f S).card / Fintype.card X := by
  have hpair :
      (S : Set (Atom f)).PairwiseDisjoint (block f) := by
    intro k _ l _ hkl
    exact block_disjoint f hkl
  unfold JointMass.colBlockMass
  simp_rw [jointMass_colMass_eq]
  rw [← Finset.sum_div]
  rw [← Nat.cast_sum]
  rw [← Finset.card_biUnion hpair]
  rfl

/-- A mixed row/aggregate-column mass is the normalized cardinality of the
corresponding taxon intersection. -/
theorem jointMass_mixedBlockMass_eq
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (S : Finset (Atom f)) :
    (jointMass e f).mixedBlockMass i S =
      (block e i ∩ aggregateBlock f S).card /
        Fintype.card X := by
  have hpair :
      (S : Set (Atom f)).PairwiseDisjoint
        (fun k => block e i ∩ block f k) := by
    intro k _ l _ hkl
    change Disjoint (block e i ∩ block f k)
      (block e i ∩ block f l)
    rw [Finset.disjoint_left]
    intro x hxk hxl
    exact Finset.disjoint_left.mp (block_disjoint f hkl)
      (Finset.mem_inter.mp hxk).2
      (Finset.mem_inter.mp hxl).2
  unfold JointMass.mixedBlockMass
  simp_rw [jointMass_a]
  rw [← Finset.sum_div]
  rw [← Nat.cast_sum]
  rw [← Finset.card_biUnion hpair]
  rw [← Finset.inter_biUnion]
  rfl

/-- Summing the row/column cells over two atom blocks gives the normalized
mass of the corresponding taxon rectangle. -/
theorem jointMass_rectangleMass_eq
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) (U : Finset (Atom f)) :
    (∑ i ∈ V, (jointMass e f).mixedBlockMass i U) =
      normalizedCard (aggregateBlock e V ∩ aggregateBlock f U) := by
  have hpair :
      (V : Set (Atom e)).PairwiseDisjoint
        (fun i => block e i ∩ aggregateBlock f U) := by
    intro i _ j _ hij
    change Disjoint (block e i ∩ aggregateBlock f U)
      (block e j ∩ aggregateBlock f U)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    exact Finset.disjoint_left.mp (block_disjoint e hij)
      (Finset.mem_inter.mp hxi).1
      (Finset.mem_inter.mp hxj).1
  have hunion :
      V.biUnion (fun i => block e i ∩ aggregateBlock f U) =
        aggregateBlock e V ∩ aggregateBlock f U := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, aggregateBlock]
    constructor
    · rintro ⟨i, hiV, hxi, hxU⟩
      exact ⟨⟨i, hiV, hxi⟩, hxU⟩
    · rintro ⟨⟨i, hiV, hxi⟩, hxU⟩
      exact ⟨i, hiV, hxi, hxU⟩
  simp_rw [jointMass_mixedBlockMass_eq e f]
  unfold normalizedCard
  rw [← Finset.sum_div]
  rw [← Nat.cast_sum]
  rw [← Finset.card_biUnion hpair]
  rw [hunion]

/-- The total row mass carried by an atom block is the normalized mass of
its taxon union. -/
theorem jointMass_rowBlockMass_eq
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) :
    (∑ i ∈ V, (jointMass e f).rowMass i) =
      normalizedCard (aggregateBlock e V) := by
  have h :=
    jointMass_rectangleMass_eq e f V
      (Finset.univ : Finset (Atom f))
  simpa [JointMass.mixedBlockMass, JointMass.rowMass,
    aggregateBlock, block_cover] using h

/-- A concrete centered rectangle in the local joint table is exactly the
centered normalized mass of the corresponding two taxon blocks. -/
theorem jointMass_centeredRectangleMass_eq
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) (U : Finset (Atom f)) :
    (jointMass e f).centeredRectangleMass V U =
      normalizedCard (aggregateBlock e V ∩ aggregateBlock f U) -
        normalizedCard (aggregateBlock e V) *
          normalizedCard (aggregateBlock f U) := by
  unfold JointMass.centeredRectangleMass JointMass.centered
  calc
    (∑ i ∈ V, ∑ k ∈ U,
        ((jointMass e f).a i k -
          (jointMass e f).rowMass i *
            (jointMass e f).colMass k)) =
        (∑ i ∈ V, (jointMass e f).mixedBlockMass i U) -
          (∑ i ∈ V, (jointMass e f).rowMass i) *
            (jointMass e f).colBlockMass U := by
              simp only [Finset.sum_sub_distrib]
              unfold JointMass.mixedBlockMass JointMass.colBlockMass
              rw [Finset.sum_mul]
              apply congrArg₂ (· - ·)
              · rfl
              · apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
    _ =
        normalizedCard (aggregateBlock e V ∩ aggregateBlock f U) -
          normalizedCard (aggregateBlock e V) *
            normalizedCard (aggregateBlock f U) := by
              rw [jointMass_rectangleMass_eq e f V U]
              rw [jointMass_rowBlockMass_eq e f V]
              rw [jointMass_colBlockMass_eq e f U]
              rfl

theorem jointMass_a_pos_of_mem
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (k : Atom f) (x : X)
    (hxi : x ∈ block e i) (hxk : x ∈ block f k) :
    0 < (jointMass e f).a i k := by
  rw [jointMass_a]
  have hnonempty :
      (block e i ∩ block f k).Nonempty :=
    ⟨x, Finset.mem_inter.mpr ⟨hxi, hxk⟩⟩
  exact div_pos
    (by exact_mod_cast (Finset.card_pos.mpr hnonempty))
    (by exact_mod_cast card_X_pos (X := X))

theorem jointMass_rowMass_pos
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) :
    0 < (jointMass e f).rowMass i := by
  obtain ⟨x, hxi⟩ := block_nonempty e i
  unfold JointMass.rowMass
  apply Finset.sum_pos'
  · intro k _
    exact (jointMass e f).nonneg i k
  · refine
      ⟨atomAt f x, Finset.mem_univ _, ?_⟩
    exact jointMass_a_pos_of_mem e f i (atomAt f x) x
      hxi (atomAt_mem f x)

theorem jointMass_colMass_pos
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (k : Atom f) :
    0 < (jointMass e f).colMass k := by
  obtain ⟨x, hxk⟩ := block_nonempty f k
  unfold JointMass.colMass
  apply Finset.sum_pos'
  · intro i _
    exact (jointMass e f).nonneg i k
  · refine
      ⟨atomAt e x, Finset.mem_univ _, ?_⟩
    exact jointMass_a_pos_of_mem e f (atomAt e x) k x
      (atomAt_mem e x) hxk

theorem jointMass_oppositeBlockMass_pos
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (k : Atom f) :
    0 <
      (jointMass e f).colBlockMass
        ((fourSector f).oppositeSideBlock k) := by
  unfold JointMass.colBlockMass
  apply Finset.sum_pos'
  · intro l _
    exact (jointMass e f).colMass_nonneg l
  · refine
      ⟨oppositeWitness f k,
        oppositeWitness_mem_oppositeSideBlock f k,
        jointMass_colMass_pos e f (oppositeWitness f k)⟩

/-- Concrete row-coordinate instance of the manuscript's residual identity
`(A.15a)`.  The atom set, endpoint range, opposite-side blocks, and weights
all come from the actual principal chart `(e,f)`. -/
theorem row_exact_residual_identity
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (U V : Atom e → ℚ) (Usq : ℚ)
    (hUsq : ∀ i, U i ^ 2 = Usq) :
    Usq
      - (∑ i ∈ (residualPartition e).endpoint,
          ((jointMass e f).rowMass i * U i -
            (residualPartition e).oppositeWeight
              (jointMass e f).rowMass i * V i) ^ 2)
      =
      (∑ z ∈ (residualPartition e).I,
        (jointMass e f).rowMass z.1 *
          (jointMass e f).rowMass z.2 * U z.1 ^ 2)
      + (∑ z ∈ (residualPartition e).D,
        (jointMass e f).rowMass z.1 *
          (jointMass e f).rowMass z.2 *
          (U z.1 + V z.1) ^ 2)
      - ∑ i ∈ (residualPartition e).endpoint,
          (residualPartition e).oppositeWeight
              (jointMass e f).rowMass i *
            ((jointMass e f).rowMass i +
              (residualPartition e).oppositeWeight
                (jointMass e f).rowMass i) *
            V i ^ 2 := by
  exact
    (residualPartition e).exact_residual_identity
      (jointMass e f).rowMass U V Usq
      (jointMass e f).sum_rowMass hUsq

/-- Concrete column-coordinate instance of `(A.15b)`. -/
theorem column_exact_residual_identity
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (U V : Atom f → ℚ) (Usq : ℚ)
    (hUsq : ∀ k, U k ^ 2 = Usq) :
    Usq
      - (∑ k ∈ (residualPartition f).endpoint,
          ((jointMass e f).colMass k * U k -
            (residualPartition f).oppositeWeight
              (jointMass e f).colMass k * V k) ^ 2)
      =
      (∑ z ∈ (residualPartition f).I,
        (jointMass e f).colMass z.1 *
          (jointMass e f).colMass z.2 * U z.1 ^ 2)
      + (∑ z ∈ (residualPartition f).D,
        (jointMass e f).colMass z.1 *
          (jointMass e f).colMass z.2 *
          (U z.1 + V z.1) ^ 2)
      - ∑ k ∈ (residualPartition f).endpoint,
          (residualPartition f).oppositeWeight
              (jointMass e f).colMass k *
            ((jointMass e f).colMass k +
              (residualPartition f).oppositeWeight
                (jointMass e f).colMass k) *
            V k ^ 2 := by
  exact
    (residualPartition f).exact_residual_identity
      (jointMass e f).colMass U V Usq
      (jointMass e f).sum_colMass hUsq

end

end PrincipalChart

end QuartetV060
