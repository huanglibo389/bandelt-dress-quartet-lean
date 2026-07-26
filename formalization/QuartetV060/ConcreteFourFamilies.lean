import QuartetV060.ConcreteBlockwisePsi

/-!
# The concrete four square families and the auxiliary functional

This file is the concrete exit from the chartwise settlement proved in
`ConcreteBlockwisePsi`.  The four families below have exactly the ranges and
the coefficients of `(A.30)`: `S₁` and `S₂` are completed packages on the
`D`- and `I`-row classes, while `S₃` and `S₄` are the two remaining
`Psi`-square sums, each with the factor `1/4` built into its definition.
-/

namespace QuartetV060

namespace ConcreteFourFamilies

open scoped BigOperators

open QuartetDistance
open PhyloOccurrences
open PrincipalAtoms
open PrincipalChart
open ConcreteRetainedSquares
open ConcreteRowSettlement
open ConcretePackageSettlement
open ConcreteBlockwisePsi

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

variable
    {T₁ T₂ : Tree.PhyloTree X}

/-- The plus-row completed-package family `S₁`. -/
def S1 : ℝ :=
  ∑ e : RelevantEdge T₁, ∑ z ∈ (Pr e).D,
    ∑ a : AdjacentCorrection T₂, packageD e z.1 z.2 a

/-- The identity-row completed-package family `S₂`. -/
def S2 : ℝ :=
  ∑ e : RelevantEdge T₁, ∑ z ∈ (Pr e).I,
    ∑ a : AdjacentCorrection T₂, packageI e z.1 z.2 a

/-- The plus-row remaining-square family `S₃`. -/
def S3 : ℝ :=
  (1 / 4 : ℝ) *
    ∑ e : RelevantEdge T₁, ∑ z ∈ (Pr e).D,
      ∑ f : RelevantEdge T₂, ∑ u : Atom f,
        psi e f z.1 z.2 u * (ZD e f z.1 u : ℝ) ^ 2

/-- The identity-row remaining-square family `S₄`. -/
def S4 : ℝ :=
  (1 / 4 : ℝ) *
    ∑ e : RelevantEdge T₁, ∑ z ∈ (Pr e).I,
      ∑ f : RelevantEdge T₂, ∑ u : Atom f,
        psi e f z.1 z.2 u * (ZI e f z.1 u : ℝ) ^ 2

/-- The right side of the unscaled global ledger `(A.29h)`. -/
def rawLedger : ℝ :=
  S1 (T₁ := T₁) (T₂ := T₂) +
    2 * S2 (T₁ := T₁) (T₂ := T₂) +
    2 * S3 (T₁ := T₁) (T₂ := T₂) +
    4 * S4 (T₁ := T₁) (T₂ := T₂)

/-- The right side of the final four-family formula `(A.30)`. -/
def scaledLedger : ℝ :=
  (1 / 4 : ℝ) * S1 (T₁ := T₁) (T₂ := T₂) +
    (1 / 2 : ℝ) * S2 (T₁ := T₁) (T₂ := T₂) +
    (1 / 2 : ℝ) * S3 (T₁ := T₁) (T₂ := T₂) +
    S4 (T₁ := T₁) (T₂ := T₂)

theorem four_mul_scaledLedger :
    4 * scaledLedger (T₁ := T₁) (T₂ := T₂) =
      rawLedger (T₁ := T₁) (T₂ := T₂) := by
  unfold scaledLedger rawLedger
  ring

theorem packageI_nonnegative
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) :
    0 ≤ packageI e i j a := by
  unfold packageI
  exact
    (ConcreteBridgeLedger.endpointData e a i j).package_nonneg
      (ConcreteBridgeLedger.endpointData_nonnegative e a i j)
      (correctionZI e i a) (correctionWI e i a)

theorem packageD_nonnegative
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) :
    0 ≤ packageD e i j a := by
  unfold packageD
  exact
    (ConcreteBridgeLedger.endpointData e a i j).package_nonneg
      (ConcreteBridgeLedger.endpointData_nonnegative e a i j)
      (correctionZD e i a) (correctionWD e i a)

theorem S1_nonnegative :
    0 ≤ S1 (T₁ := T₁) (T₂ := T₂) := by
  unfold S1
  apply Finset.sum_nonneg
  intro e he
  apply Finset.sum_nonneg
  intro z hz
  apply Finset.sum_nonneg
  intro a ha
  exact packageD_nonnegative e z.1 z.2 a

theorem S2_nonnegative :
    0 ≤ S2 (T₁ := T₁) (T₂ := T₂) := by
  unfold S2
  apply Finset.sum_nonneg
  intro e he
  apply Finset.sum_nonneg
  intro z hz
  apply Finset.sum_nonneg
  intro a ha
  exact packageI_nonnegative e z.1 z.2 a

theorem S3_nonnegative :
    0 ≤ S3 (T₁ := T₁) (T₂ := T₂) := by
  unfold S3
  apply mul_nonneg
  · norm_num
  · apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro z hz
    apply Finset.sum_nonneg
    intro f hf
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg
      (psi_nonnegative e f z.1 z.2 u)
      (sq_nonneg _)

theorem S4_nonnegative :
    0 ≤ S4 (T₁ := T₁) (T₂ := T₂) := by
  unfold S4
  apply mul_nonneg
  · norm_num
  · apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro z hz
    apply Finset.sum_nonneg
    intro f hf
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg
      (psi_nonnegative e f z.1 z.2 u)
      (sq_nonneg _)

theorem scaledLedger_nonnegative :
    0 ≤ scaledLedger (T₁ := T₁) (T₂ := T₂) := by
  unfold scaledLedger
  have h1 := S1_nonnegative (T₁ := T₁) (T₂ := T₂)
  have h2 := S2_nonnegative (T₁ := T₁) (T₂ := T₂)
  have h3 := S3_nonnegative (T₁ := T₁) (T₂ := T₂)
  have h4 := S4_nonnegative (T₁ := T₁) (T₂ := T₂)
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num) h1)
        (mul_nonneg (by norm_num) h2))
      (mul_nonneg (by norm_num) h3))
    h4

private def rowIPackages
    (e : RelevantEdge T₁) : ℝ :=
  ∑ z ∈ (Pr e).I,
    ∑ a : AdjacentCorrection T₂, packageI e z.1 z.2 a

private def rowDPackages
    (e : RelevantEdge T₁) : ℝ :=
  ∑ z ∈ (Pr e).D,
    ∑ a : AdjacentCorrection T₂, packageD e z.1 z.2 a

private def rowIPsi
    (e : RelevantEdge T₁) : ℝ :=
  ∑ z ∈ (Pr e).I,
    ∑ f : RelevantEdge T₂, ∑ u : Atom f,
      psi e f z.1 z.2 u * (ZI e f z.1 u : ℝ) ^ 2

private def rowDPsi
    (e : RelevantEdge T₁) : ℝ :=
  ∑ z ∈ (Pr e).D,
    ∑ f : RelevantEdge T₂, ∑ u : Atom f,
      psi e f z.1 z.2 u * (ZD e f z.1 u : ℝ) ^ 2

theorem fixed_row_I_settlement
    (e : RelevantEdge T₁) :
    (∑ z ∈ (Pr e).I, ∑ f : RelevantEdge T₂,
      (directRowI e f z : ℝ)) =
      rowIPackages (T₂ := T₂) e +
        (1 / 2 : ℝ) * rowIPsi (T₂ := T₂) e := by
  unfold rowIPackages rowIPsi
  simp_rw [global_row_I_ledger (T₂ := T₂)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]

theorem fixed_row_D_settlement
    (e : RelevantEdge T₁) :
    (∑ z ∈ (Pr e).D, ∑ f : RelevantEdge T₂,
      (directRowD e f z : ℝ)) =
      rowDPackages (T₂ := T₂) e +
        (1 / 2 : ℝ) * rowDPsi (T₂ := T₂) e := by
  unfold rowDPackages rowDPsi
  simp_rw [global_row_D_ledger (T₂ := T₂)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]

private theorem fixed_edge_settlement
    (e : RelevantEdge T₁) :
    (∑ f : RelevantEdge T₂, (settledChart e f : ℝ)) =
      2 * rowIPackages (T₂ := T₂) e +
        rowDPackages (T₂ := T₂) e +
        rowIPsi (T₂ := T₂) e +
        (1 / 2 : ℝ) * rowDPsi (T₂ := T₂) e := by
  simp only [settledChart, Rat.cast_add, Rat.cast_mul,
    Rat.cast_ofNat]
  push_cast
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm
    (f := fun f : RelevantEdge T₂ =>
      fun z : Atom e × Atom e => (directRowI e f z : ℝ))]
  rw [Finset.sum_comm
    (f := fun f : RelevantEdge T₂ =>
      fun z : Atom e × Atom e => (directRowD e f z : ℝ))]
  rw [fixed_row_I_settlement (T₂ := T₂)]
  rw [fixed_row_D_settlement (T₂ := T₂)]
  ring

/-- Concrete global settlement of the four determinant levels into the
unscaled four-family ledger `(A.29h)`. -/
theorem global_settledChart_eq_rawLedger :
    (∑ e : RelevantEdge T₁, ∑ f : RelevantEdge T₂,
      (settledChart e f : ℝ)) =
      rawLedger (T₁ := T₁) (T₂ := T₂) := by
  simp_rw [fixed_edge_settlement (T₂ := T₂)]
  unfold rawLedger S1 S2 S3 S4
  unfold rowIPackages rowDPackages rowIPsi rowDPsi
  simp_rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Pointwise scaling of the four determinant levels. -/
theorem four_mul_auxiliaryFunctional :
    4 *
        auxiliaryFunctional
          (correctionSystem T₁) (correctionSystem T₂) =
      ∑ e : RelevantEdge T₁, ∑ f : RelevantEdge T₂,
        fourLevelChart e f := by
  unfold auxiliaryFunctional fourLevelChart
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  ring

/-- The exact concrete `(A.29h)` numerator identity. -/
theorem four_mul_auxiliaryFunctional_real_eq_rawLedger :
    4 *
        (auxiliaryFunctional
          (correctionSystem T₁) (correctionSystem T₂) : ℝ) =
      rawLedger (T₁ := T₁) (T₂ := T₂) := by
  calc
    4 *
        (auxiliaryFunctional
          (correctionSystem T₁) (correctionSystem T₂) : ℝ) =
        ((∑ e : RelevantEdge T₁, ∑ f : RelevantEdge T₂,
          fourLevelChart e f : ℚ) : ℝ) := by
            exact_mod_cast
              four_mul_auxiliaryFunctional (T₁ := T₁) (T₂ := T₂)
    _ =
        ((∑ e : RelevantEdge T₁, ∑ f : RelevantEdge T₂,
          settledChart e f : ℚ) : ℝ) := by
            exact_mod_cast
              ConcreteRowSettlement.global_fourLevel_eq_directRow
                (T₁ := T₁) (T₂ := T₂)
    _ =
        ∑ e : RelevantEdge T₁, ∑ f : RelevantEdge T₂,
          (settledChart e f : ℝ) := by norm_cast
    _ = rawLedger (T₁ := T₁) (T₂ := T₂) :=
      global_settledChart_eq_rawLedger (T₁ := T₁) (T₂ := T₂)

/-- Concrete formula `(A.30)`: the manuscript's auxiliary functional is
exactly the sum of the four nonnegative square families with coefficients
`1/4,1/2,1/2,1`. -/
theorem auxiliaryFunctional_real_eq_scaledLedger :
    (auxiliaryFunctional
      (correctionSystem T₁) (correctionSystem T₂) : ℝ) =
      scaledLedger (T₁ := T₁) (T₂ := T₂) := by
  have hraw :=
    four_mul_auxiliaryFunctional_real_eq_rawLedger
      (T₁ := T₁) (T₂ := T₂)
  have hscaled :=
    four_mul_scaledLedger (T₁ := T₁) (T₂ := T₂)
  linarith

theorem auxiliaryFunctional_nonnegative_real :
    0 ≤
      (auxiliaryFunctional
        (correctionSystem T₁) (correctionSystem T₂) : ℝ) := by
  rw [auxiliaryFunctional_real_eq_scaledLedger
    (T₁ := T₁) (T₂ := T₂)]
  exact scaledLedger_nonnegative (T₁ := T₁) (T₂ := T₂)

theorem auxiliaryFunctional_nonnegative :
    0 ≤
      auxiliaryFunctional
        (correctionSystem T₁) (correctionSystem T₂) := by
  exact_mod_cast
    auxiliaryFunctional_nonnegative_real (T₁ := T₁) (T₂ := T₂)

end

end ConcreteFourFamilies

end QuartetV060
