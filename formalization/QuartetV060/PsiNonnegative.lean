import QuartetV060.BlockwiseLedger

/-!
# Nonnegativity of the remaining coefficient `Psi` `(A.32)`

The proof is split exactly as in the manuscript.  On an endpoint target, the
fourth term of each symmetric-product expansion is removed on `M_S`, and the
whole diagonal summand is removed at `u`.  On a residual target, both
subtractions are absent.  What remains is a sum of explicitly nonnegative
terms.
-/

namespace QuartetV060

open scoped BigOperators

namespace PsiNonnegative

noncomputable section

variable
    {C : Type*}
    [Fintype C] [DecidableEq C]

def positiveTerm
    (cu ri : ℝ)
    (cL rj : C → ℝ)
    (l : C) : ℝ :=
  4 * cu * cL l * ri * rj l

def fourthTerm
    (cu cBarU aiBarU : ℝ)
    (cL cBarL ajBarL : C → ℝ)
    (l : C) : ℝ :=
  cu * cL l / (cBarU * cBarL l) * aiBarU * ajBarL l

def firstThree
    (cu cBarU aiU aiBarU : ℝ)
    (cL cBarL ajL ajBarL : C → ℝ)
    (l : C) : ℝ :=
  aiU * ajL l +
    cL l / cBarL l * aiU * ajBarL l +
    cu / cBarU * aiBarU * ajL l

/-- The complete four-term expansion used in `(A.32)`. -/
theorem positiveTerm_eq_firstThree_add_fourth
    (cu cBarU ri aiU aiBarU : ℝ)
    (cL cBarL rj ajL ajBarL : C → ℝ)
    (l : C)
    (hri : 2 * cu * ri = aiU + cu / cBarU * aiBarU)
    (hrj :
      2 * cL l * rj l =
        ajL l + cL l / cBarL l * ajBarL l) :
    positiveTerm cu ri cL rj l =
      firstThree cu cBarU aiU aiBarU cL cBarL ajL ajBarL l +
        fourthTerm cu cBarU aiBarU cL cBarL ajBarL l := by
  unfold positiveTerm firstThree fourthTerm
  calc
    4 * cu * cL l * ri * rj l =
        (2 * cu * ri) * (2 * cL l * rj l) := by ring
    _ =
        (aiU + cu / cBarU * aiBarU) *
          (ajL l + cL l / cBarL l * ajBarL l) := by
            rw [hri, hrj]
    _ =
      aiU * ajL l +
        cL l / cBarL l * aiU * ajBarL l +
        cu / cBarU * aiBarU * ajL l +
        cu * cL l / (cBarU * cBarL l) *
          aiBarU * ajBarL l := by ring

theorem firstThree_nonneg
    (cu cBarU aiU aiBarU : ℝ)
    (cL cBarL ajL ajBarL : C → ℝ)
    (l : C)
    (hcu : 0 ≤ cu) (hcBarU : 0 ≤ cBarU)
    (haiU : 0 ≤ aiU) (haiBarU : 0 ≤ aiBarU)
    (hcL : 0 ≤ cL l) (hcBarL : 0 ≤ cBarL l)
    (hajL : 0 ≤ ajL l) (hajBarL : 0 ≤ ajBarL l) :
    0 ≤ firstThree cu cBarU aiU aiBarU
      cL cBarL ajL ajBarL l := by
  unfold firstThree
  have hratioL : 0 ≤ cL l / cBarL l :=
    div_nonneg hcL hcBarL
  have hratioU : 0 ≤ cu / cBarU :=
    div_nonneg hcu hcBarU
  positivity

/-- Pure finite-set form of the endpoint cancellation. -/
theorem endpoint_core_nonneg
    (S MS : Finset C) (u : C)
    (pos neg : C → ℝ)
    (hMS : MS ⊆ S)
    (huS : u ∈ S)
    (huMS : u ∉ MS)
    (hpos : ∀ l ∈ S, 0 ≤ pos l)
    (hremainder : ∀ l ∈ MS, 0 ≤ pos l - neg l) :
    0 ≤
      (∑ l ∈ S, pos l) -
        (∑ l ∈ MS, neg l) - pos u := by
  let U : Finset C := insert u MS
  have hUS : U ⊆ S := by
    intro l hl
    simp only [U, Finset.mem_insert] at hl
    rcases hl with rfl | hl
    · exact huS
    · exact hMS hl
  have hdisj : Disjoint U (S \ U) :=
    Finset.disjoint_sdiff
  have hunion : U ∪ (S \ U) = S :=
    Finset.union_sdiff_of_subset hUS
  have hsumS :
      (∑ l ∈ S, pos l) =
        (∑ l ∈ U, pos l) + ∑ l ∈ S \ U, pos l := by
    calc
      (∑ l ∈ S, pos l) =
          ∑ l ∈ U ∪ (S \ U), pos l := by rw [hunion]
      _ = (∑ l ∈ U, pos l) + ∑ l ∈ S \ U, pos l :=
        Finset.sum_union hdisj
  have hsumU :
      (∑ l ∈ U, pos l) = pos u + ∑ l ∈ MS, pos l := by
    simp only [U]
    rw [Finset.sum_insert huMS]
  have hremSum :
      0 ≤ ∑ l ∈ MS, (pos l - neg l) := by
    apply Finset.sum_nonneg
    intro l hl
    exact hremainder l hl
  have hrest :
      0 ≤ ∑ l ∈ S \ U, pos l := by
    apply Finset.sum_nonneg
    intro l hl
    exact hpos l (Finset.mem_sdiff.mp hl).1
  rw [hsumS, hsumU]
  rw [Finset.sum_sub_distrib] at hremSum
  linarith

/-- Direct endpoint case of the core bracket `(A.32)`. -/
theorem endpoint_A32_nonneg
    (S MS : Finset C) (u : C)
    (cu cBarU ri aiU aiBarU : ℝ)
    (cL cBarL rj ajL ajBarL : C → ℝ)
    (hMS : MS ⊆ S)
    (huS : u ∈ S)
    (huMS : u ∉ MS)
    (hri : 2 * cu * ri = aiU + cu / cBarU * aiBarU)
    (hrj :
      ∀ l ∈ MS,
        2 * cL l * rj l =
          ajL l + cL l / cBarL l * ajBarL l)
    (hcu : 0 ≤ cu) (hcBarU : 0 ≤ cBarU)
    (hri0 : 0 ≤ ri) (haiU : 0 ≤ aiU)
    (haiBarU : 0 ≤ aiBarU)
    (hcL : ∀ l ∈ S, 0 ≤ cL l)
    (hcBarL : ∀ l ∈ MS, 0 ≤ cBarL l)
    (hrj0 : ∀ l ∈ S, 0 ≤ rj l)
    (hajL : ∀ l ∈ MS, 0 ≤ ajL l)
    (hajBarL : ∀ l ∈ MS, 0 ≤ ajBarL l) :
    0 ≤
      (∑ l ∈ S, positiveTerm cu ri cL rj l) -
        (∑ l ∈ MS,
          fourthTerm cu cBarU aiBarU cL cBarL ajBarL l) -
        positiveTerm cu ri cL rj u := by
  apply endpoint_core_nonneg S MS u
    (positiveTerm cu ri cL rj)
    (fourthTerm cu cBarU aiBarU cL cBarL ajBarL)
    hMS huS huMS
  · intro l hl
    have hcLl : 0 ≤ cL l := hcL l hl
    have hrjl : 0 ≤ rj l := hrj0 l hl
    unfold positiveTerm
    positivity
  · intro l hl
    rw [positiveTerm_eq_firstThree_add_fourth
      cu cBarU ri aiU aiBarU cL cBarL rj ajL ajBarL
      l hri (hrj l hl)]
    ring_nf
    exact firstThree_nonneg cu cBarU aiU aiBarU
      cL cBarL ajL ajBarL l hcu hcBarU haiU haiBarU
      (hcL l (hMS hl)) (hcBarL l hl) (hajL l hl) (hajBarL l hl)

/-- Direct residual case of `(A.32)`: `M_S` is empty and there is no
endpoint diagonal subtraction. -/
theorem residual_A32_nonneg
    (S : Finset C)
    (cu ri : ℝ) (cL rj : C → ℝ)
    (hcu : 0 ≤ cu) (hri : 0 ≤ ri)
    (hcL : ∀ l ∈ S, 0 ≤ cL l)
    (hrj : ∀ l ∈ S, 0 ≤ rj l) :
    0 ≤ ∑ l ∈ S, positiveTerm cu ri cL rj l := by
  apply Finset.sum_nonneg
  intro l hl
  have hcLl : 0 ≤ cL l := hcL l hl
  have hrjl : 0 ≤ rj l := hrj l hl
  unfold positiveTerm
  positivity

/-- The remaining three rows of `Psi` are termwise nonnegative, so adding
them to the nonnegative core bracket preserves nonnegativity. -/
theorem psi_nonneg_of_core
    (sameEndpoint residual opposite core : ℝ)
    (hSame : 0 ≤ sameEndpoint)
    (hResidual : 0 ≤ residual)
    (hOpposite : 0 ≤ opposite)
    (hCore : 0 ≤ core) :
    0 ≤ sameEndpoint + residual + opposite + core := by
  positivity

end

end PsiNonnegative

end QuartetV060
