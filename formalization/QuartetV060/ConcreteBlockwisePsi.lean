import QuartetV060.ConcreteGlobalPackage

/-!
# Concrete blockwise residue and the coefficient `Psi`

This file instantiates `(A.30a)`, `(A.30b)`, and `(A.29g)` in one actual
principal chart.  In particular, `Psi` below is the six-row formula from
the manuscript, not an abstract coefficient chosen to make the final
identity true.
-/

namespace QuartetV060

namespace ConcreteBlockwisePsi

open scoped BigOperators

open QuartetDistance
open PhyloOccurrences
open PrincipalAtoms
open PrincipalChart
open LocalCoordinates
open ConcreteRetainedSquares
open ConcreteRowSettlement
open ConcretePackageSettlement
open ConcreteGlobalPackage

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

variable
    {T₁ T₂ : Tree.PhyloTree X}

def sameSet
    (f : RelevantEdge T₂) (u : Atom f) : Finset (Atom f) :=
  (Fc f).sameSideBlock u

def oppositeSet
    (f : RelevantEdge T₂) (u : Atom f) : Finset (Atom f) :=
  (Fc f).oppositeSideBlock u

def MSset
    (f : RelevantEdge T₂) (u : Atom f) : Finset (Atom f) :=
  Finset.univ.filter fun l =>
    (Fc f).pairClass u l = .sameEndpoint

def MDset
    (f : RelevantEdge T₂) (u : Atom f) : Finset (Atom f) :=
  Finset.univ.filter fun l =>
    (Fc f).pairClass u l = .oppositeResidual

@[simp] theorem mem_sameSet
    (f : RelevantEdge T₂) (u l : Atom f) :
    l ∈ sameSet f u ↔ (Fc f).sameSide u l := by
  simp [sameSet]

@[simp] theorem mem_oppositeSet
    (f : RelevantEdge T₂) (u l : Atom f) :
    l ∈ oppositeSet f u ↔ ¬(Fc f).sameSide u l := by
  simp [oppositeSet]

@[simp] theorem mem_MSset
    (f : RelevantEdge T₂) (u l : Atom f) :
    l ∈ MSset f u ↔
      (Fc f).isEndpoint u ∧ (Fc f).sameSide u l ∧ u ≠ l := by
  simpa only [MSset, Finset.mem_filter, Finset.mem_univ,
    true_and, FourSector.MS] using
      ((Fc f).MS_iff u l)

@[simp] theorem mem_MDset
    (f : RelevantEdge T₂) (u l : Atom f) :
    l ∈ MDset f u ↔
      (Fc f).isResidual u ∧ ¬(Fc f).sameSide u l := by
  simpa only [MDset, Finset.mem_filter, Finset.mem_univ,
    true_and, FourSector.MD] using
      ((Fc f).MD_iff u l)

theorem endpoint_not_residual
    (f : RelevantEdge T₂) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    ¬(Fc f).isResidual u := by
  change (fourSector f).isEndpoint u at hu
  change ¬(fourSector f).isResidual u
  change
    (fourSector f).sector u = .a ∨
      (fourSector f).sector u = .b at hu
  change
    ¬((fourSector f).sector u = .c ∨
      (fourSector f).sector u = .d)
  rcases hu with hu | hu <;> rw [hu] <;> simp

theorem residual_not_endpoint
    (f : RelevantEdge T₂) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    ¬(Fc f).isEndpoint u := by
  change (fourSector f).isResidual u at hu
  change ¬(fourSector f).isEndpoint u
  change
    (fourSector f).sector u = .c ∨
      (fourSector f).sector u = .d at hu
  change
    ¬((fourSector f).sector u = .a ∨
      (fourSector f).sector u = .b)
  rcases hu with hu | hu <;> rw [hu] <;> simp

theorem endpoint_or_residual
    (f : RelevantEdge T₂) (u : Atom f) :
    (Fc f).isEndpoint u ∨ (Fc f).isResidual u := by
  unfold FourSector.isEndpoint FourSector.isResidual
  cases h : (Fc f).sector u <;> simp

theorem self_mem_sameSet
    (f : RelevantEdge T₂) (u : Atom f) :
    u ∈ sameSet f u := by
  simp [sameSet, FourSector.sameSide]

theorem MSset_eq_erase_of_endpoint
    (f : RelevantEdge T₂) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    MSset f u = (sameSet f u).erase u := by
  ext l
  simp [hu, eq_comm, and_comm]

theorem MSset_eq_empty_of_residual
    (f : RelevantEdge T₂) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    MSset f u = ∅ := by
  ext l
  simp [residual_not_endpoint f u hu]

theorem MDset_eq_empty_of_endpoint
    (f : RelevantEdge T₂) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    MDset f u = ∅ := by
  ext l
  simp [endpoint_not_residual f u hu]

theorem MDset_eq_opposite_of_residual
    (f : RelevantEdge T₂) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    MDset f u = oppositeSet f u := by
  ext l
  simp [hu]

theorem sameSet_disjoint_oppositeSet
    (f : RelevantEdge T₂) (u : Atom f) :
    Disjoint (sameSet f u) (oppositeSet f u) :=
  (Fc f).sameSideBlock_disjoint_opposite u

theorem sameSet_union_oppositeSet
    (f : RelevantEdge T₂) (u : Atom f) :
    sameSet f u ∪ oppositeSet f u = Finset.univ :=
  (Fc f).sameSideBlock_union_opposite u

def cSame
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) : ℚ :=
  (J e f).colBlockMass (sameSet f u)

def aSame
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) : ℚ :=
  (J e f).mixedBlockMass i (sameSet f u)

def aOpp
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) : ℚ :=
  (J e f).mixedBlockMass i (oppositeSet f u)

theorem cSame_add_cbar
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) :
    cSame e f u + cbar e f u = 1 := by
  exact (J e f).colBlockMass_same_add_opposite (Fc f) u

theorem cSame_pos
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) :
    0 < cSame e f u := by
  unfold cSame JointMass.colBlockMass
  exact Finset.sum_pos'
    (fun k hk => le_of_lt (c_pos e f k))
    ⟨u, self_mem_sameSet f u, c_pos e f u⟩

theorem cSame_eq_one_sub_cbar
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) :
    cSame e f u = 1 - cbar e f u := by
  linarith [cSame_add_cbar e f u]

theorem aOpp_eq_mixed
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) :
    aOpp e f i u =
      (J e f).mixedBlockMass i ((Fc f).oppositeSideBlock u) := by
  rfl

theorem oppositeSet_eq_of_same
    (f : RelevantEdge T₂) (u l : Atom f)
    (hl : l ∈ sameSet f u) :
    oppositeSet f l = oppositeSet f u := by
  unfold oppositeSet
  exact (FourSector.oppositeSideBlock_eq_of_sameSide
    (Fc f) (mem_sameSet f u l |>.mp hl)).symm

theorem oppositeSet_eq_sameSet_of_opposite
    (f : RelevantEdge T₂) (u l : Atom f)
    (hl : l ∈ oppositeSet f u) :
    oppositeSet f l = sameSet f u := by
  have hul : ¬(Fc f).sameSide u l :=
    (mem_oppositeSet f u l).mp hl
  have hlu : ¬(Fc f).sameSide l u := by
    unfold FourSector.sameSide at hul ⊢
    exact fun h => hul h.symm
  unfold oppositeSet sameSet
  exact
    FourSector.oppositeSideBlock_eq_sameSideBlock_of_not_sameSide
      (Fc f) hlu

theorem cbar_eq_of_mem_same
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u l : Atom f) (hl : l ∈ sameSet f u) :
    cbar e f l = cbar e f u := by
  unfold cbar
  exact congrArg ((J e f).colBlockMass)
    (oppositeSet_eq_of_same f u l hl)

theorem cbar_eq_cSame_of_mem_opposite
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u l : Atom f) (hl : l ∈ oppositeSet f u) :
    cbar e f l = cSame e f u := by
  unfold cbar cSame
  exact congrArg ((J e f).colBlockMass)
    (oppositeSet_eq_sameSet_of_opposite f u l hl)

theorem aOpp_eq_of_mem_same
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u l : Atom f) (hl : l ∈ sameSet f u) :
    aOpp e f i l = aOpp e f i u := by
  unfold aOpp
  exact congrArg ((J e f).mixedBlockMass i)
    (oppositeSet_eq_of_same f u l hl)

theorem aOpp_eq_aSame_of_mem_opposite
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u l : Atom f) (hl : l ∈ oppositeSet f u) :
    aOpp e f i l = aSame e f i u := by
  unfold aOpp aSame
  exact congrArg ((J e f).mixedBlockMass i)
    (oppositeSet_eq_sameSet_of_opposite f u l hl)

@[simp] theorem sum_c_same
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) :
    (∑ l ∈ sameSet f u, c e f l) = cSame e f u := by
  rfl

@[simp] theorem sum_c_opposite
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) :
    (∑ l ∈ oppositeSet f u, c e f l) = cbar e f u := by
  rfl

@[simp] theorem sum_a_same
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) :
    (∑ l ∈ sameSet f u, (J e f).a i l) =
      aSame e f i u := by
  rfl

@[simp] theorem sum_a_opposite
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) :
    (∑ l ∈ oppositeSet f u, (J e f).a i l) =
      aOpp e f i u := by
  rfl

theorem sum_MS_of_endpoint
    (f : RelevantEdge T₂) (u : Atom f)
    (g : Atom f → ℚ)
    (hu : (Fc f).isEndpoint u) :
    (∑ l ∈ MSset f u, g l) =
      (∑ l ∈ sameSet f u, g l) - g u := by
  rw [MSset_eq_erase_of_endpoint f u hu]
  have h :=
    Finset.sum_erase_add
      (sameSet f u) g (self_mem_sameSet f u)
  linarith

theorem ID_union_eq_delete_endpoint_diagonal
    (f : RelevantEdge T₂) :
    (Pc f).I ∪ (Pc f).D =
      (Pc f).allPairs.filter fun z =>
        ¬(z.1 ∈ (Pc f).endpoint ∧ z.2 = z.1) := by
  ext z
  simp only [Finset.mem_union, Finset.mem_filter,
    ResidualPartition.mem_allPairs, true_and]
  rw [show
    (z.1 ∈ (Pc f).endpoint ∧ z.2 = z.1) ↔
      z ∈ (Pc f).deltaE by
        exact ((Pc f).mem_deltaE_iff z).symm]
  by_cases hD : z ∈ (Pc f).D
  · have hdelta : z ∉ (Pc f).deltaE :=
      Finset.disjoint_left.mp (Pc f).disjoint_D_deltaE hD
    simp [hD, hdelta]
  · simp [ResidualPartition.I, hD]

def availableQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) : ℚ :=
  ∑ z ∈ (Pc f).I ∪ (Pc f).D,
    if z.1 = u then
      c e f z.1 * c e f z.2 *
        r e f i z.1 * r e f j z.2
    else 0

theorem availableCoefficient_eq_cast_availableQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    availableCoefficient e f i j u =
      (availableQ e f i j u : ℝ) := by
  rfl

theorem availableQ_eq_sum_without_endpoint_diagonal
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    availableQ e f i j u =
      ∑ l : Atom f,
        if u ∈ (Pc f).endpoint ∧ l = u then 0
        else c e f u * c e f l *
          r e f i u * r e f j l := by
  unfold availableQ
  rw [ID_union_eq_delete_endpoint_diagonal f]
  rw [Finset.sum_filter]
  unfold ResidualPartition.allPairs
  change
    (∑ z ∈ (Finset.univ ×ˢ Finset.univ),
      if ¬(z.1 ∈ (Pc f).endpoint ∧ z.2 = z.1) then
        if z.1 = u then
          c e f z.1 * c e f z.2 *
            r e f i z.1 * r e f j z.2
        else 0
      else 0) = _
  rw [Finset.sum_product]
  simp only [Finset.mem_univ, true_and]
  rw [Finset.sum_eq_single u]
  · apply Fintype.sum_congr
    intro l
    by_cases hdiag :
        u ∈ (Pc f).endpoint ∧ l = u
    · simp [hdiag]
    · simp [hdiag]
  · intro x hx hxu
    simp [hxu]
  · simp

def positiveQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u l : Atom f) : ℚ :=
  4 * c e f u * c e f l *
    r e f i u * r e f j l

def fourthQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u l : Atom f) : ℚ :=
  c e f u * c e f l /
      (cbar e f u * cbar e f l) *
    aOpp e f i u * aOpp e f j l

/-- The six displayed rows of the manuscript's coefficient `(A.30a)`,
with every mass and aggregate evaluated in the fixed chart `(e,f)`. -/
def psiQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) : ℚ :=
  (∑ l ∈ MSset f u,
      cbar e f u / cSame e f u *
        (J e f).a i u * (J e f).a j l) +
  (∑ l ∈ sameSet f u, positiveQ e f i j u l) +
  (if (Fc f).isResidual u then
      (J e f).a i u * aOpp e f j u +
        aOpp e f i u * (J e f).a j u
    else 0) -
  (∑ l ∈ MSset f u, fourthQ e f i j u l) -
  (if (Fc f).isEndpoint u then
      positiveQ e f i j u u
    else 0) +
  (∑ l ∈ MDset f u,
      (c e f u / cbar e f u *
            aOpp e f i u * (J e f).a j l +
          c e f l / cbar e f l *
            (J e f).a i u * aOpp e f j l))

def psi
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) : ℝ :=
  (psiQ e f i j u : ℝ)

/-- The first-square coefficient of the completed package, written purely
over `ℚ`.  It is zero away from an endpoint, exactly as in `(A.29f)`. -/
def demandQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) : ℚ :=
  if (Fc f).isEndpoint u then
    (1 / 4 : ℚ) * c e f u * (1 - c e f u) /
        cbar e f u ^ 2 *
        aOpp e f i u * aOpp e f j u +
      (1 / 4 : ℚ) * cbar e f u / cSame e f u *
        (J e f).a i u * (J e f).a j u +
      (1 / 4 : ℚ) *
        (J e f).a i u * aOpp e f j u +
      (1 / 4 : ℚ) *
        aOpp e f i u * (J e f).a j u
  else 0

theorem demandCoefficient_eq_cast_demandQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    demandCoefficient e f i j u =
      (demandQ e f i j u : ℝ) := by
  by_cases hu : (Fc f).isEndpoint u
  · have hu' : u ∈ (Pc f).endpoint := by
      change u ∈ (residualPartition f).endpoint
      rw [mem_residualPartition_endpoint]
      exact hu
    simp only [demandCoefficient, hu', if_pos]
    simp only [demandQ, hu, if_pos]
    rw [cSame_eq_one_sub_cbar]
    unfold aOpp oppositeSet
    unfold localEndpointData
      CompletedSquares.EndpointData.packageCoeff
      CompletedSquares.EndpointData.coeff22
      CompletedSquares.EndpointData.coeff23
      CompletedSquares.EndpointData.coeff24
      CompletedSquares.EndpointData.coeff25
    dsimp
    push_cast
    ring
  · have hu' : u ∉ (Pc f).endpoint := by
      change u ∉ (residualPartition f).endpoint
      rw [mem_residualPartition_endpoint]
      exact hu
    simp [demandCoefficient, demandQ, hu, hu']

theorem availableQ_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    availableQ e f i j u =
      ∑ l : Atom f,
        if l = u then 0
        else c e f u * c e f l *
          r e f i u * r e f j l := by
  rw [availableQ_eq_sum_without_endpoint_diagonal]
  have hu' : u ∈ (Pc f).endpoint := by
    change u ∈ (residualPartition f).endpoint
    rw [mem_residualPartition_endpoint]
    exact hu
  apply Fintype.sum_congr
  intro l
  by_cases hlu : l = u <;> simp [hu', hlu]

theorem availableQ_residual
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    availableQ e f i j u =
      ∑ l : Atom f,
        c e f u * c e f l *
          r e f i u * r e f j l := by
  rw [availableQ_eq_sum_without_endpoint_diagonal]
  have hu' : u ∉ (Pc f).endpoint := by
    change u ∉ (residualPartition f).endpoint
    rw [mem_residualPartition_endpoint]
    exact residual_not_endpoint f u hu
  apply Fintype.sum_congr
  intro l
  simp [hu']

theorem sum_univ_eq_same_add_opposite
    (f : RelevantEdge T₂) (u : Atom f)
    (g : Atom f → ℚ) :
    (∑ l : Atom f, g l) =
      (∑ l ∈ sameSet f u, g l) +
        ∑ l ∈ oppositeSet f u, g l := by
  calc
    (∑ l : Atom f, g l) =
        ∑ l ∈ sameSet f u ∪ oppositeSet f u, g l := by
      rw [sameSet_union_oppositeSet f u]
    _ =
        (∑ l ∈ sameSet f u, g l) +
          ∑ l ∈ oppositeSet f u, g l := by
      exact Finset.sum_union
        (sameSet_disjoint_oppositeSet f u)

theorem sum_omit_one
    {C : Type*} [Fintype C] [DecidableEq C]
    (g : C → ℚ) (u : C) :
    (∑ l : C, if l = u then 0 else g l) =
      (∑ l : C, g l) - g u := by
  have hpoint :
      ∀ l : C,
        (if l = u then 0 else g l) =
          g l - if l = u then g l else 0 := by
    intro l
    by_cases hlu : l = u <;> simp [hlu]
  calc
    (∑ l : C, if l = u then 0 else g l) =
        ∑ l : C, (g l - if l = u then g l else 0) := by
      apply Fintype.sum_congr
      exact hpoint
    _ =
        (∑ l : C, g l) -
          ∑ l : C, if l = u then g l else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ l : C, g l) - g u := by
      simp

theorem four_available_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    4 * availableQ e f i j u =
      (∑ l ∈ sameSet f u, positiveQ e f i j u l) -
        positiveQ e f i j u u +
        ∑ l ∈ oppositeSet f u, positiveQ e f i j u l := by
  rw [availableQ_endpoint e f i j u hu]
  rw [Finset.mul_sum]
  calc
    (∑ l : Atom f,
        4 *
          (if l = u then 0
          else c e f u * c e f l *
            r e f i u * r e f j l)) =
        ∑ l : Atom f,
          if l = u then 0 else positiveQ e f i j u l := by
      apply Fintype.sum_congr
      intro l
      by_cases hlu : l = u <;>
        simp [hlu, positiveQ] <;> ring
    _ =
        (∑ l : Atom f, positiveQ e f i j u l) -
          positiveQ e f i j u u := by
      exact sum_omit_one
        (fun l => positiveQ e f i j u l) u
    _ =
        (∑ l ∈ sameSet f u, positiveQ e f i j u l) -
          positiveQ e f i j u u +
          ∑ l ∈ oppositeSet f u,
            positiveQ e f i j u l := by
      rw [sum_univ_eq_same_add_opposite f u]
      ring

theorem four_available_residual
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    4 * availableQ e f i j u =
      (∑ l ∈ sameSet f u, positiveQ e f i j u l) +
        ∑ l ∈ oppositeSet f u, positiveQ e f i j u l := by
  rw [availableQ_residual e f i j u hu]
  rw [Finset.mul_sum]
  calc
    (∑ l : Atom f,
        4 * (c e f u * c e f l *
          r e f i u * r e f j l)) =
        ∑ l : Atom f, positiveQ e f i j u l := by
      apply Fintype.sum_congr
      intro l
      unfold positiveQ
      ring
    _ =
        (∑ l ∈ sameSet f u, positiveQ e f i j u l) +
          ∑ l ∈ oppositeSet f u,
            positiveQ e f i j u l :=
      sum_univ_eq_same_add_opposite f u _

@[simp] theorem sum_c_MS_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) (hu : (Fc f).isEndpoint u) :
    (∑ l ∈ MSset f u, c e f l) =
      cSame e f u - c e f u := by
  rw [sum_MS_of_endpoint f u (c e f) hu]
  rw [sum_c_same]

@[simp] theorem sum_a_MS_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    (∑ l ∈ MSset f u, (J e f).a j l) =
      aSame e f j u - (J e f).a j u := by
  rw [sum_MS_of_endpoint f u (fun l => (J e f).a j l) hu]
  rw [sum_a_same]

theorem firstRow_sum_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    (∑ l ∈ MSset f u,
      cbar e f u / cSame e f u *
        (J e f).a i u * (J e f).a j l) =
      cbar e f u / cSame e f u *
        (J e f).a i u *
          (aSame e f j u - (J e f).a j u) := by
  rw [← Finset.mul_sum]
  rw [sum_a_MS_endpoint e f j u hu]

theorem fourth_sum_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    (∑ l ∈ MSset f u, fourthQ e f i j u l) =
      c e f u * (cSame e f u - c e f u) /
          cbar e f u ^ 2 *
        aOpp e f i u * aOpp e f j u := by
  calc
    (∑ l ∈ MSset f u, fourthQ e f i j u l) =
        ∑ l ∈ MSset f u,
          (c e f u / cbar e f u ^ 2 *
            aOpp e f i u * aOpp e f j u) *
              c e f l := by
      apply Finset.sum_congr rfl
      intro l hl
      have hsame : l ∈ sameSet f u := by
        exact (mem_sameSet f u l).mpr
          ((mem_MSset f u l).mp hl |>.2.1)
      unfold fourthQ
      rw [cbar_eq_of_mem_same e f u l hsame]
      rw [aOpp_eq_of_mem_same e f j u l hsame]
      ring
    _ =
        (c e f u / cbar e f u ^ 2 *
          aOpp e f i u * aOpp e f j u) *
            ∑ l ∈ MSset f u, c e f l := by
      rw [Finset.mul_sum]
    _ =
        c e f u * (cSame e f u - c e f u) /
            cbar e f u ^ 2 *
          aOpp e f i u * aOpp e f j u := by
      rw [sum_c_MS_endpoint e f u hu]
      ring

theorem sixthRow_sum_residual
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    (∑ l ∈ MDset f u,
      (c e f u / cbar e f u *
            aOpp e f i u * (J e f).a j l +
          c e f l / cbar e f l *
            (J e f).a i u * aOpp e f j l)) =
      c e f u / cbar e f u *
          aOpp e f i u * aOpp e f j u +
        cbar e f u / cSame e f u *
          (J e f).a i u * aSame e f j u := by
  rw [MDset_eq_opposite_of_residual f u hu]
  calc
    (∑ l ∈ oppositeSet f u,
      (c e f u / cbar e f u *
            aOpp e f i u * (J e f).a j l +
          c e f l / cbar e f l *
            (J e f).a i u * aOpp e f j l)) =
        (∑ l ∈ oppositeSet f u,
          c e f u / cbar e f u *
            aOpp e f i u * (J e f).a j l) +
        ∑ l ∈ oppositeSet f u,
          c e f l / cbar e f l *
            (J e f).a i u * aOpp e f j l := by
      rw [Finset.sum_add_distrib]
    _ =
        c e f u / cbar e f u *
            aOpp e f i u *
              (∑ l ∈ oppositeSet f u, (J e f).a j l) +
          ∑ l ∈ oppositeSet f u,
            (c e f l / cSame e f u *
              (J e f).a i u * aSame e f j u) := by
      congr 1
      · rw [← Finset.mul_sum]
      · apply Finset.sum_congr rfl
        intro l hl
        rw [cbar_eq_cSame_of_mem_opposite e f u l hl]
        rw [aOpp_eq_aSame_of_mem_opposite e f j u l hl]
    _ =
        c e f u / cbar e f u *
            aOpp e f i u * aOpp e f j u +
          cbar e f u / cSame e f u *
            (J e f).a i u * aSame e f j u := by
      rw [sum_a_opposite]
      calc
        c e f u / cbar e f u *
              aOpp e f i u * aOpp e f j u +
            ∑ l ∈ oppositeSet f u,
              c e f l / cSame e f u *
                (J e f).a i u * aSame e f j u =
            c e f u / cbar e f u *
                aOpp e f i u * aOpp e f j u +
              (∑ l ∈ oppositeSet f u, c e f l) /
                cSame e f u *
                  (J e f).a i u * aSame e f j u := by
          congr 1
          rw [Finset.sum_div]
          rw [Finset.sum_mul]
          rw [Finset.sum_mul]
        _ = _ := by rw [sum_c_opposite]

theorem psiQ_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    psiQ e f i j u =
      cbar e f u / cSame e f u *
          (J e f).a i u *
            (aSame e f j u - (J e f).a j u) +
        (∑ l ∈ sameSet f u, positiveQ e f i j u l) -
        c e f u * (cSame e f u - c e f u) /
            cbar e f u ^ 2 *
          aOpp e f i u * aOpp e f j u -
        positiveQ e f i j u u := by
  unfold psiQ
  rw [firstRow_sum_endpoint e f i j u hu]
  rw [fourth_sum_endpoint e f i j u hu]
  rw [MDset_eq_empty_of_endpoint f u hu]
  have hnres := endpoint_not_residual f u hu
  simp [hu, hnres]

theorem psiQ_residual
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    psiQ e f i j u =
      (∑ l ∈ sameSet f u, positiveQ e f i j u l) +
        (J e f).a i u * aOpp e f j u +
        aOpp e f i u * (J e f).a j u +
        c e f u / cbar e f u *
          aOpp e f i u * aOpp e f j u +
        cbar e f u / cSame e f u *
          (J e f).a i u * aSame e f j u := by
  unfold psiQ
  rw [MSset_eq_empty_of_residual f u hu]
  rw [sixthRow_sum_residual e f i j u hu]
  have hnep := residual_not_endpoint f u hu
  simp [hu, hnep]
  ring

theorem positiveQ_expansion
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u l : Atom f) :
    positiveQ e f i j u l =
      (J e f).a i u * (J e f).a j l +
      c e f l / cbar e f l *
        (J e f).a i u * aOpp e f j l +
      c e f u / cbar e f u *
        aOpp e f i u * (J e f).a j l +
      c e f u * c e f l /
          (cbar e f u * cbar e f l) *
        aOpp e f i u * aOpp e f j l := by
  simpa [positiveQ, c, cbar, r, aOpp, oppositeSet] using
    (JointMass.domination_expansion
      (J e f) (Fc f) i j u l
      (ne_of_gt (c_pos e f u))
      (ne_of_gt (c_pos e f l))
      (ne_of_gt (cbar_pos e f u))
      (ne_of_gt (cbar_pos e f l)))

theorem positiveQ_of_mem_opposite
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u l : Atom f)
    (hl : l ∈ oppositeSet f u) :
    positiveQ e f i j u l =
      (J e f).a i u * (J e f).a j l +
      c e f l / cSame e f u *
        (J e f).a i u * aSame e f j u +
      c e f u / cbar e f u *
        aOpp e f i u * (J e f).a j l +
      c e f u * c e f l /
          (cbar e f u * cSame e f u) *
        aOpp e f i u * aSame e f j u := by
  rw [positiveQ_expansion]
  rw [cbar_eq_cSame_of_mem_opposite e f u l hl]
  rw [aOpp_eq_aSame_of_mem_opposite e f j u l hl]

theorem sum_positive_opposite_expansion
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    (∑ l ∈ oppositeSet f u, positiveQ e f i j u l) =
      (J e f).a i u * aOpp e f j u +
      cbar e f u / cSame e f u *
        (J e f).a i u * aSame e f j u +
      c e f u / cbar e f u *
        aOpp e f i u * aOpp e f j u +
      c e f u / cSame e f u *
        aOpp e f i u * aSame e f j u := by
  have hcbar : cbar e f u ≠ 0 :=
    ne_of_gt (cbar_pos e f u)
  have hsame : cSame e f u ≠ 0 :=
    ne_of_gt (cSame_pos e f u)
  calc
    (∑ l ∈ oppositeSet f u, positiveQ e f i j u l) =
        ∑ l ∈ oppositeSet f u,
          ((J e f).a i u * (J e f).a j l +
          c e f l / cSame e f u *
            (J e f).a i u * aSame e f j u +
          c e f u / cbar e f u *
            aOpp e f i u * (J e f).a j l +
          c e f u * c e f l /
              (cbar e f u * cSame e f u) *
            aOpp e f i u * aSame e f j u) := by
      apply Finset.sum_congr rfl
      intro l hl
      exact positiveQ_of_mem_opposite e f i j u l hl
    _ =
        (∑ l ∈ oppositeSet f u,
          (J e f).a i u * (J e f).a j l) +
        (∑ l ∈ oppositeSet f u,
          c e f l / cSame e f u *
            (J e f).a i u * aSame e f j u) +
        (∑ l ∈ oppositeSet f u,
          c e f u / cbar e f u *
            aOpp e f i u * (J e f).a j l) +
        (∑ l ∈ oppositeSet f u,
          c e f u * c e f l /
              (cbar e f u * cSame e f u) *
            aOpp e f i u * aSame e f j u) := by
      simp only [Finset.sum_add_distrib]
    _ =
        (J e f).a i u * aOpp e f j u +
        cbar e f u / cSame e f u *
          (J e f).a i u * aSame e f j u +
        c e f u / cbar e f u *
          aOpp e f i u * aOpp e f j u +
        c e f u / cSame e f u *
          aOpp e f i u * aSame e f j u := by
      rw [← Finset.mul_sum]
      rw [sum_a_opposite]
      rw [← Finset.mul_sum]
      rw [sum_a_opposite]
      have hcb :
          (∑ l ∈ oppositeSet f u,
            c e f l / cSame e f u *
              (J e f).a i u * aSame e f j u) =
            cbar e f u / cSame e f u *
              (J e f).a i u * aSame e f j u := by
        calc
          (∑ l ∈ oppositeSet f u,
              c e f l / cSame e f u *
                (J e f).a i u * aSame e f j u) =
              (∑ l ∈ oppositeSet f u, c e f l) /
                cSame e f u *
                  (J e f).a i u * aSame e f j u := by
            rw [Finset.sum_div]
            rw [Finset.sum_mul]
            rw [Finset.sum_mul]
          _ = _ := by rw [sum_c_opposite]
      rw [hcb]
      have hlast :
          (∑ l ∈ oppositeSet f u,
            c e f u * c e f l /
                (cbar e f u * cSame e f u) *
              aOpp e f i u * aSame e f j u) =
            c e f u / cSame e f u *
              aOpp e f i u * aSame e f j u := by
        calc
          (∑ l ∈ oppositeSet f u,
              c e f u * c e f l /
                  (cbar e f u * cSame e f u) *
                aOpp e f i u * aSame e f j u) =
              c e f u *
                (∑ l ∈ oppositeSet f u, c e f l) /
                  (cbar e f u * cSame e f u) *
                aOpp e f i u * aSame e f j u := by
            rw [Finset.mul_sum]
            rw [Finset.sum_div]
            rw [Finset.sum_mul]
            rw [Finset.sum_mul]
          _ = _ := by
            rw [sum_c_opposite]
            field_simp
      rw [hlast]

def discrepancyQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) : ℚ :=
  aOpp e f i u *
    (c e f u / cSame e f u * aSame e f j u -
      (J e f).a j u)

theorem pointwise_settlement_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    4 * (availableQ e f i j u - demandQ e f i j u) =
      psiQ e f i j u + discrepancyQ e f i j u := by
  rw [mul_sub]
  rw [four_available_endpoint e f i j u hu]
  rw [psiQ_endpoint e f i j u hu]
  rw [sum_positive_opposite_expansion e f i j u]
  unfold demandQ discrepancyQ
  rw [if_pos hu]
  have hcbar : cbar e f u ≠ 0 :=
    ne_of_gt (cbar_pos e f u)
  have hsame : cSame e f u ≠ 0 :=
    ne_of_gt (cSame_pos e f u)
  rw [cSame_eq_one_sub_cbar]
  field_simp
  ring

theorem pointwise_settlement_residual
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    4 * (availableQ e f i j u - demandQ e f i j u) =
      psiQ e f i j u + discrepancyQ e f i j u := by
  rw [mul_sub]
  rw [four_available_residual e f i j u hu]
  rw [psiQ_residual e f i j u hu]
  rw [sum_positive_opposite_expansion e f i j u]
  unfold demandQ discrepancyQ
  rw [if_neg (residual_not_endpoint f u hu)]
  ring

theorem pointwise_settlement
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    4 * (availableQ e f i j u - demandQ e f i j u) =
      psiQ e f i j u + discrepancyQ e f i j u := by
  rcases endpoint_or_residual f u with hu | hu
  · exact pointwise_settlement_endpoint e f i j u hu
  · exact pointwise_settlement_residual e f i j u hu

theorem pointwise_settlement_real
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    4 * (availableCoefficient e f i j u -
      demandCoefficient e f i j u) =
      psi e f i j u + (discrepancyQ e f i j u : ℝ) := by
  have h := congrArg (fun x : ℚ => (x : ℝ))
    (pointwise_settlement e f i j u)
  push_cast at h
  simpa only [availableCoefficient_eq_cast_availableQ,
    demandCoefficient_eq_cast_demandQ, psi] using h

theorem sameSet_eq_of_mem_same
    (f : RelevantEdge T₂) (s u : Atom f)
    (hu : u ∈ sameSet f s) :
    sameSet f u = sameSet f s := by
  unfold sameSet
  exact
    (FourSector.sameSideBlock_eq_of_sameSide
      (Fc f) ((mem_sameSet f s u).mp hu)).symm

theorem cSame_eq_of_mem_same
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (s u : Atom f) (hu : u ∈ sameSet f s) :
    cSame e f u = cSame e f s := by
  unfold cSame
  exact congrArg ((J e f).colBlockMass)
    (sameSet_eq_of_mem_same f s u hu)

theorem aSame_eq_of_mem_same
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (j : Atom e) (s u : Atom f)
    (hu : u ∈ sameSet f s) :
    aSame e f j u = aSame e f j s := by
  unfold aSame
  exact congrArg ((J e f).mixedBlockMass j)
    (sameSet_eq_of_mem_same f s u hu)

theorem blockSum_c_eq_cSame
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (s : Atom f) :
    BlockwiseLedger.blockSum (sameSet f s)
      (fun u => (c e f u : ℝ)) =
        (cSame e f s : ℝ) := by
  unfold BlockwiseLedger.blockSum cSame
    JointMass.colBlockMass c
  push_cast
  rfl

theorem blockSum_a_eq_aSame
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (j : Atom e) (s : Atom f) :
    BlockwiseLedger.blockSum (sameSet f s)
      (fun u => ((J e f).a j u : ℝ)) =
        (aSame e f j s : ℝ) := by
  unfold BlockwiseLedger.blockSum aSame
    JointMass.mixedBlockMass
  push_cast
  rfl

theorem discrepancy_cast_eq_blockwise
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (s u : Atom f)
    (hu : u ∈ sameSet f s) :
    (discrepancyQ e f i j u : ℝ) =
      BlockwiseLedger.discrepancy
        (sameSet f s)
        (fun l => (c e f l : ℝ))
        (fun l => ((J e f).a j l : ℝ))
        (aOpp e f i s : ℝ) u := by
  have hc := cSame_eq_of_mem_same e f s u hu
  have haS := aSame_eq_of_mem_same e f j s u hu
  have haO := aOpp_eq_of_mem_same e f i s u hu
  unfold discrepancyQ BlockwiseLedger.discrepancy
  rw [blockSum_c_eq_cSame]
  rw [blockSum_a_eq_aSame]
  rw [hc, haS, haO]
  push_cast
  rfl

theorem sameSet_eq_opposite_of_mem_opposite
    (f : RelevantEdge T₂) (s u : Atom f)
    (hu : u ∈ oppositeSet f s) :
    sameSet f u = oppositeSet f s := by
  have hnot : ¬(Fc f).sameSide s u :=
    (mem_oppositeSet f s u).mp hu
  unfold sameSet oppositeSet
  exact
    (FourSector.oppositeSideBlock_eq_sameSideBlock_of_not_sameSide
      (Fc f) hnot).symm

theorem cSame_eq_cbar_of_mem_opposite
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (s u : Atom f) (hu : u ∈ oppositeSet f s) :
    cSame e f u = cbar e f s := by
  unfold cSame cbar
  exact congrArg ((J e f).colBlockMass)
    (sameSet_eq_opposite_of_mem_opposite f s u hu)

theorem aSame_eq_aOpp_of_mem_opposite
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (j : Atom e) (s u : Atom f)
    (hu : u ∈ oppositeSet f s) :
    aSame e f j u = aOpp e f j s := by
  unfold aSame aOpp
  exact congrArg ((J e f).mixedBlockMass j)
    (sameSet_eq_opposite_of_mem_opposite f s u hu)

theorem blockSum_c_opposite_eq_cbar
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (s : Atom f) :
    BlockwiseLedger.blockSum (oppositeSet f s)
      (fun u => (c e f u : ℝ)) =
        (cbar e f s : ℝ) := by
  unfold BlockwiseLedger.blockSum cbar
    JointMass.colBlockMass c oppositeSet
  push_cast
  rfl

theorem blockSum_a_opposite_eq_aOpp
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (j : Atom e) (s : Atom f) :
    BlockwiseLedger.blockSum (oppositeSet f s)
      (fun u => ((J e f).a j u : ℝ)) =
        (aOpp e f j s : ℝ) := by
  unfold BlockwiseLedger.blockSum aOpp
    JointMass.mixedBlockMass oppositeSet
  push_cast
  rfl

theorem discrepancy_cast_eq_blockwise_opposite
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (s u : Atom f)
    (hu : u ∈ oppositeSet f s) :
    (discrepancyQ e f i j u : ℝ) =
      BlockwiseLedger.discrepancy
        (oppositeSet f s)
        (fun l => (c e f l : ℝ))
        (fun l => ((J e f).a j l : ℝ))
        (aSame e f i s : ℝ) u := by
  have hc := cSame_eq_cbar_of_mem_opposite e f s u hu
  have haS := aSame_eq_aOpp_of_mem_opposite e f j s u hu
  have haO := aOpp_eq_aSame_of_mem_opposite e f i s u hu
  unfold discrepancyQ BlockwiseLedger.discrepancy
  rw [blockSum_c_opposite_eq_cbar]
  rw [blockSum_a_opposite_eq_aOpp]
  rw [hc, haS, haO]
  push_cast
  rfl

theorem ZI_square_independent
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u s : Atom f) :
    (ZI e f i u : ℝ) ^ 2 =
      (ZI e f i s : ℝ) ^ 2 := by
  have h :=
    LocalCoordinates.xBarOpp_sq_independent_col
      (J e f) (Fr e) (Fc f) i u s
  exact_mod_cast h

theorem ZD_square_independent
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u s : Atom f) :
    (ZD e f i u : ℝ) ^ 2 =
      (ZD e f i s : ℝ) ^ 2 := by
  have h :=
    LocalCoordinates.xBarOpp_add_xOpp_sq_independent_col
      (J e f) (Fr e) (Fc f) i u s
  exact_mod_cast h

/-- Concrete `(A.30b)` on the two same-side blocks of one chart, including
the common square carried by each block. -/
theorem chart_two_block_settlement
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (s : Atom f)
    (Z : Atom f → ℝ)
    (hZ : ∀ u : Atom f, Z u ^ 2 = Z s ^ 2) :
    2 * (∑ u ∈ sameSet f s ∪ oppositeSet f s,
      (availableCoefficient e f i j u -
        demandCoefficient e f i j u) * Z u ^ 2) =
      (1 / 2 : ℝ) *
        ∑ u ∈ sameSet f s ∪ oppositeSet f s,
          psi e f i j u * Z u ^ 2 := by
  have hcSpos :
      0 <
        BlockwiseLedger.blockSum (sameSet f s)
          (fun u => (c e f u : ℝ)) := by
    rw [blockSum_c_eq_cSame]
    exact_mod_cast cSame_pos e f s
  have hcTpos :
      0 <
        BlockwiseLedger.blockSum (oppositeSet f s)
          (fun u => (c e f u : ℝ)) := by
    rw [blockSum_c_opposite_eq_cbar]
    exact_mod_cast cbar_pos e f s
  apply BlockwiseLedger.two_blocks_with_square
    (sameSet f s) (oppositeSet f s)
    (sameSet_disjoint_oppositeSet f s)
    (fun u => (c e f u : ℝ))
    (fun u => ((J e f).a j u : ℝ))
    (availableCoefficient e f i j)
    (demandCoefficient e f i j)
    (psi e f i j)
    Z
    (aOpp e f i s : ℝ)
    (aSame e f i s : ℝ)
    (Z s) (Z s)
    (ne_of_gt hcSpos) (ne_of_gt hcTpos)
  · intro u hu
    rw [← discrepancy_cast_eq_blockwise e f i j s u hu]
    exact pointwise_settlement_real e f i j u
  · intro u hu
    rw [← discrepancy_cast_eq_blockwise_opposite
      e f i j s u hu]
    exact pointwise_settlement_real e f i j u
  · intro u hu
    exact hZ u
  · intro u hu
    exact hZ u

theorem chart_row_I_ledger
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) :
    2 * (∑ u : Atom f,
      (availableCoefficient e f i j u -
        demandCoefficient e f i j u) *
          (ZI e f i u : ℝ) ^ 2) =
      (1 / 2 : ℝ) * ∑ u : Atom f,
        psi e f i j u * (ZI e f i u : ℝ) ^ 2 := by
  let s := anchorCol f
  have h :=
    chart_two_block_settlement e f i j s
      (fun u => (ZI e f i u : ℝ))
      (fun u => ZI_square_independent e f i u s)
  rw [sameSet_union_oppositeSet f s] at h
  simpa using h

theorem chart_row_D_ledger
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) :
    2 * (∑ u : Atom f,
      (availableCoefficient e f i j u -
        demandCoefficient e f i j u) *
          (ZD e f i u : ℝ) ^ 2) =
      (1 / 2 : ℝ) * ∑ u : Atom f,
        psi e f i j u * (ZD e f i u : ℝ) ^ 2 := by
  let s := anchorCol f
  have h :=
    chart_two_block_settlement e f i j s
      (fun u => (ZD e f i u : ℝ))
      (fun u => ZD_square_independent e f i u s)
  rw [sameSet_union_oppositeSet f s] at h
  simpa using h

/-- Concrete global row-`I` package identity `(A.29g)`. -/
theorem global_row_I_ledger
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂,
      (directRowI e f (i, j) : ℝ)) =
      (∑ a : AdjacentCorrection T₂, packageI e i j a) +
        (1 / 2 : ℝ) *
          ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            psi e f i j u * (ZI e f i u : ℝ) ^ 2 := by
  rw [global_package_ledger_I]
  congr 1
  calc
    2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
        (availableCoefficient e f i j u -
          demandCoefficient e f i j u) *
            (ZI e f i u : ℝ) ^ 2 =
        ∑ f : RelevantEdge T₂,
          2 * ∑ u : Atom f,
            (availableCoefficient e f i j u -
              demandCoefficient e f i j u) *
                (ZI e f i u : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ =
        ∑ f : RelevantEdge T₂,
          (1 / 2 : ℝ) * ∑ u : Atom f,
            psi e f i j u * (ZI e f i u : ℝ) ^ 2 := by
      apply Fintype.sum_congr
      intro f
      exact chart_row_I_ledger e f i j
    _ =
        (1 / 2 : ℝ) *
          ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            psi e f i j u * (ZI e f i u : ℝ) ^ 2 := by
      rw [Finset.mul_sum]

/-- Concrete global row-`D` package identity `(A.29g)`. -/
theorem global_row_D_ledger
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂,
      (directRowD e f (i, j) : ℝ)) =
      (∑ a : AdjacentCorrection T₂, packageD e i j a) +
        (1 / 2 : ℝ) *
          ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            psi e f i j u * (ZD e f i u : ℝ) ^ 2 := by
  rw [global_package_ledger_D]
  congr 1
  calc
    2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
        (availableCoefficient e f i j u -
          demandCoefficient e f i j u) *
            (ZD e f i u : ℝ) ^ 2 =
        ∑ f : RelevantEdge T₂,
          2 * ∑ u : Atom f,
            (availableCoefficient e f i j u -
              demandCoefficient e f i j u) *
                (ZD e f i u : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ =
        ∑ f : RelevantEdge T₂,
          (1 / 2 : ℝ) * ∑ u : Atom f,
            psi e f i j u * (ZD e f i u : ℝ) ^ 2 := by
      apply Fintype.sum_congr
      intro f
      exact chart_row_D_ledger e f i j
    _ =
        (1 / 2 : ℝ) *
          ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            psi e f i j u * (ZD e f i u : ℝ) ^ 2 := by
      rw [Finset.mul_sum]

theorem refinement_identityQ
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) :
    2 * c e f u * r e f i u =
      (J e f).a i u +
        c e f u / cbar e f u * aOpp e f i u := by
  have hc : c e f u ≠ 0 :=
    ne_of_gt (c_pos e f u)
  have hb : cbar e f u ≠ 0 :=
    ne_of_gt (cbar_pos e f u)
  unfold r JointMass.symmetricRowCoefficient
  change
    2 * c e f u *
        ((1 / 2 : ℚ) *
          ((J e f).a i u / c e f u +
            aOpp e f i u / cbar e f u)) =
      (J e f).a i u +
        c e f u / cbar e f u * aOpp e f i u
  field_simp [hc, hb]

theorem refinement_identity
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) :
    2 * (c e f u : ℝ) * r e f i u =
      ((J e f).a i u : ℝ) +
        (c e f u : ℝ) / cbar e f u *
          (aOpp e f i u : ℝ) := by
  exact_mod_cast refinement_identityQ e f i u

theorem c_nonneg_real
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) :
    0 ≤ (c e f u : ℝ) := by
  exact_mod_cast le_of_lt (c_pos e f u)

theorem cbar_nonneg_real
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) :
    0 ≤ (cbar e f u : ℝ) := by
  exact_mod_cast le_of_lt (cbar_pos e f u)

theorem r_nonneg_real
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) :
    0 ≤ (r e f i u : ℝ) := by
  exact_mod_cast r_nonneg e f i u

theorem a_nonneg_real
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) :
    0 ≤ ((J e f).a i u : ℝ) := by
  exact_mod_cast (J e f).nonneg i u

theorem aOpp_nonneg_real
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) :
    0 ≤ (aOpp e f i u : ℝ) := by
  unfold aOpp
  exact_mod_cast
    (J e f).mixedBlockMass_nonneg i (oppositeSet f u)

theorem cSame_nonneg_real
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (u : Atom f) :
    0 ≤ (cSame e f u : ℝ) := by
  exact_mod_cast le_of_lt (cSame_pos e f u)

theorem endpoint_core_nonnegative
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    0 ≤
      (∑ l ∈ sameSet f u,
        (positiveQ e f i j u l : ℝ)) -
      (∑ l ∈ MSset f u,
        (fourthQ e f i j u l : ℝ)) -
      (positiveQ e f i j u u : ℝ) := by
  have hcore :=
    PsiNonnegative.endpoint_A32_nonneg
      (sameSet f u) (MSset f u) u
      (c e f u : ℝ) (cbar e f u : ℝ)
      (r e f i u : ℝ)
      ((J e f).a i u : ℝ)
      (aOpp e f i u : ℝ)
      (fun l => (c e f l : ℝ))
      (fun l => (cbar e f l : ℝ))
      (fun l => (r e f j l : ℝ))
      (fun l => ((J e f).a j l : ℝ))
      (fun l => (aOpp e f j l : ℝ))
      (by
        intro l hl
        exact (mem_sameSet f u l).mpr
          ((mem_MSset f u l).mp hl |>.2.1))
      (self_mem_sameSet f u)
      (by simp)
      (refinement_identity e f i u)
      (by
        intro l hl
        exact refinement_identity e f j l)
      (c_nonneg_real e f u)
      (cbar_nonneg_real e f u)
      (r_nonneg_real e f i u)
      (a_nonneg_real e f i u)
      (aOpp_nonneg_real e f i u)
      (by
        intro l hl
        exact c_nonneg_real e f l)
      (by
        intro l hl
        exact cbar_nonneg_real e f l)
      (by
        intro l hl
        exact r_nonneg_real e f j l)
      (by
        intro l hl
        exact a_nonneg_real e f j l)
      (by
        intro l hl
        exact aOpp_nonneg_real e f j l)
  simpa only [PsiNonnegative.positiveTerm,
    PsiNonnegative.fourthTerm, positiveQ, fourthQ,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div,
    Rat.cast_pow] using hcore

theorem endpoint_first_row_nonnegative
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    0 ≤
      (∑ l ∈ MSset f u,
        (cbar e f u / cSame e f u *
          (J e f).a i u * (J e f).a j l : ℚ) : ℝ) := by
  push_cast
  apply Finset.sum_nonneg
  intro l hl
  have hratio :
      0 ≤ (cbar e f u : ℝ) / cSame e f u :=
    div_nonneg
      (cbar_nonneg_real e f u)
      (cSame_nonneg_real e f u)
  exact mul_nonneg
    (mul_nonneg hratio (a_nonneg_real e f i u))
    (a_nonneg_real e f j l)

theorem psi_nonnegative_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isEndpoint u) :
    0 ≤ psi e f i j u := by
  have hformula := congrArg (fun x : ℚ => (x : ℝ))
    (psiQ_endpoint e f i j u hu)
  push_cast at hformula
  unfold psi
  rw [hformula]
  have hrow := endpoint_first_row_nonnegative e f i j u
  have hcore := endpoint_core_nonnegative e f i j u hu
  have hfirst := congrArg (fun x : ℚ => (x : ℝ))
    (firstRow_sum_endpoint e f i j u hu)
  have hfourth := congrArg (fun x : ℚ => (x : ℝ))
    (fourth_sum_endpoint e f i j u hu)
  push_cast at hfirst hfourth
  push_cast at hrow
  rw [hfirst] at hrow
  rw [hfourth] at hcore
  linarith

theorem residual_core_nonnegative
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    0 ≤
      ∑ l ∈ sameSet f u,
        (positiveQ e f i j u l : ℝ) := by
  have hcore :=
    PsiNonnegative.residual_A32_nonneg
      (sameSet f u)
      (c e f u : ℝ)
      (r e f i u : ℝ)
      (fun l => (c e f l : ℝ))
      (fun l => (r e f j l : ℝ))
      (c_nonneg_real e f u)
      (r_nonneg_real e f i u)
      (by
        intro l hl
        exact c_nonneg_real e f l)
      (by
        intro l hl
        exact r_nonneg_real e f j l)
  simpa only [PsiNonnegative.positiveTerm, positiveQ,
    Rat.cast_mul, Rat.cast_ofNat] using hcore

theorem psi_nonnegative_residual
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f)
    (hu : (Fc f).isResidual u) :
    0 ≤ psi e f i j u := by
  have hformula := congrArg (fun x : ℚ => (x : ℝ))
    (psiQ_residual e f i j u hu)
  push_cast at hformula
  unfold psi
  rw [hformula]
  have hcore := residual_core_nonnegative e f i j u
  have hai := a_nonneg_real e f i u
  have haj := a_nonneg_real e f j u
  have haiO := aOpp_nonneg_real e f i u
  have hajO := aOpp_nonneg_real e f j u
  have haiS :
      0 ≤ (aSame e f i u : ℝ) := by
    unfold aSame
    exact_mod_cast
      (J e f).mixedBlockMass_nonneg i (sameSet f u)
  have hajS :
      0 ≤ (aSame e f j u : ℝ) := by
    unfold aSame
    exact_mod_cast
      (J e f).mixedBlockMass_nonneg j (sameSet f u)
  have hratioO :
      0 ≤ (c e f u : ℝ) / cbar e f u :=
    div_nonneg
      (c_nonneg_real e f u)
      (cbar_nonneg_real e f u)
  have hratioS :
      0 ≤ (cbar e f u : ℝ) / cSame e f u :=
    div_nonneg
      (cbar_nonneg_real e f u)
      (cSame_nonneg_real e f u)
  positivity

theorem psi_nonnegative
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    0 ≤ psi e f i j u := by
  rcases endpoint_or_residual f u with hu | hu
  · exact psi_nonnegative_endpoint e f i j u hu
  · exact psi_nonnegative_residual e f i j u hu

end

end ConcreteBlockwisePsi

end QuartetV060
