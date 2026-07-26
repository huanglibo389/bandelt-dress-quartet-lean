import QuartetV060.PsiNonnegative

/-!
# The four nonnegative square families and the scaling in `(A.30)`

The data in this file keep every finite range and every polynomial argument
visible.  `S₁` and `S₂` are sums of the completed package `P`; `S₃` and `S₄`
are the two remaining `Psi`-square sums, including the factor `1/4` from the
paper's definitions.  The final theorem proves the passage from the unscaled
ledger `(A.29h)` to `(A.30)`.
-/

namespace QuartetV060

open scoped BigOperators

namespace FourFamilyLedger

noncomputable section

/-- All chart-indexed ingredients that occur in the four families.

`Row` indexes retained row relations, `Endpoint` indexes `a ∪ b`, and
`Target` indexes the full column target set.  The coordinates `XI,YI` are the
single-form arguments and `XD,YD` are the plus-form arguments. -/
structure ChartData (Row Endpoint Target : Type*) where
  I : Finset Row
  D : Finset Row
  endpoints : Finset Endpoint
  targets : Finset Target
  packageData : Row → Endpoint → CompletedSquares.EndpointData
  XI : Row → Endpoint → ℝ
  YI : Row → Endpoint → ℝ
  XD : Row → Endpoint → ℝ
  YD : Row → Endpoint → ℝ
  Psi : Row → Target → ℝ
  ZI : Row → Target → ℝ
  ZD : Row → Target → ℝ

namespace ChartData

variable
    {Row Endpoint Target : Type*}
    [DecidableEq Row] [DecidableEq Endpoint] [DecidableEq Target]
    (d : ChartData Row Endpoint Target)

def packageI (r : Row) (k : Endpoint) : ℝ :=
  (d.packageData r k).package (d.XI r k) (d.YI r k)

def packageD (r : Row) (k : Endpoint) : ℝ :=
  (d.packageData r k).package (d.XD r k) (d.YD r k)

def psiSquareI (r : Row) (u : Target) : ℝ :=
  d.Psi r u * d.ZI r u ^ 2

def psiSquareD (r : Row) (u : Target) : ℝ :=
  d.Psi r u * d.ZD r u ^ 2

/-- `S₂`: identity-row completed packages. -/
def S2 : ℝ :=
  ∑ r ∈ d.I, ∑ k ∈ d.endpoints, d.packageI r k

/-- `S₁`: plus-row completed packages. -/
def S1 : ℝ :=
  ∑ r ∈ d.D, ∑ k ∈ d.endpoints, d.packageD r k

/-- `S₄`: identity-row remaining squares. -/
def S4 : ℝ :=
  (1 / 4 : ℝ) *
    ∑ r ∈ d.I, ∑ u ∈ d.targets, d.psiSquareI r u

/-- `S₃`: plus-row remaining squares. -/
def S3 : ℝ :=
  (1 / 4 : ℝ) *
    ∑ r ∈ d.D, ∑ u ∈ d.targets, d.psiSquareD r u

/-- The right side of the unscaled ledger `(A.29h)`, before the four
families are named. -/
def rawLedger : ℝ :=
  (∑ r ∈ d.D, ∑ k ∈ d.endpoints, d.packageD r k) +
    2 * (∑ r ∈ d.I, ∑ k ∈ d.endpoints, d.packageI r k) +
    (1 / 2 : ℝ) *
      (∑ r ∈ d.D, ∑ u ∈ d.targets, d.psiSquareD r u) +
    (∑ r ∈ d.I, ∑ u ∈ d.targets, d.psiSquareI r u)

/-- The chart contribution on the right side of `(A.30)`. -/
def scaledLedger : ℝ :=
  (1 / 4 : ℝ) * d.S1 +
    (1 / 2 : ℝ) * d.S2 +
    (1 / 2 : ℝ) * d.S3 +
    d.S4

/-- The four terms in `(A.29h)` are exactly
`S₁ + 2 S₂ + 2 S₃ + 4 S₄`. -/
theorem rawLedger_eq_four_families :
    d.rawLedger = d.S1 + 2 * d.S2 + 2 * d.S3 + 4 * d.S4 := by
  unfold rawLedger S1 S2 S3 S4
  ring

theorem four_mul_scaledLedger :
    4 * d.scaledLedger = d.rawLedger := by
  rw [d.rawLedger_eq_four_families]
  unfold scaledLedger
  ring

theorem S2_nonneg
    (hpackage :
      ∀ r ∈ d.I, ∀ k ∈ d.endpoints,
        (d.packageData r k).Nonnegative) :
    0 ≤ d.S2 := by
  unfold S2
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro k hk
  exact (d.packageData r k).package_nonneg
    (hpackage r hr k hk) (d.XI r k) (d.YI r k)

theorem S1_nonneg
    (hpackage :
      ∀ r ∈ d.D, ∀ k ∈ d.endpoints,
        (d.packageData r k).Nonnegative) :
    0 ≤ d.S1 := by
  unfold S1
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro k hk
  exact (d.packageData r k).package_nonneg
    (hpackage r hr k hk) (d.XD r k) (d.YD r k)

theorem S4_nonneg
    (hPsi : ∀ r ∈ d.I, ∀ u ∈ d.targets, 0 ≤ d.Psi r u) :
    0 ≤ d.S4 := by
  unfold S4 psiSquareI
  apply mul_nonneg
  · norm_num
  · apply Finset.sum_nonneg
    intro r hr
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (hPsi r hr u hu) (sq_nonneg _)

theorem S3_nonneg
    (hPsi : ∀ r ∈ d.D, ∀ u ∈ d.targets, 0 ≤ d.Psi r u) :
    0 ≤ d.S3 := by
  unfold S3 psiSquareD
  apply mul_nonneg
  · norm_num
  · apply Finset.sum_nonneg
    intro r hr
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (hPsi r hr u hu) (sq_nonneg _)

end ChartData

section Global

variable
    {Chart Row Endpoint Target : Type*}
    [Fintype Chart] [DecidableEq Chart]
    [DecidableEq Row] [DecidableEq Endpoint] [DecidableEq Target]

def globalRaw
    (d : Chart → ChartData Row Endpoint Target) : ℝ :=
  ∑ χ, (d χ).rawLedger

def globalScaled
    (d : Chart → ChartData Row Endpoint Target) : ℝ :=
  ∑ χ, (d χ).scaledLedger

theorem four_mul_globalScaled
    (d : Chart → ChartData Row Endpoint Target) :
    4 * globalScaled d = globalRaw d := by
  unfold globalScaled globalRaw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact (d χ).four_mul_scaledLedger

/-- Exact algebraic exit from the unscaled global ledger to `(A.30)`.
The premise is the already-settled numerator identity
`4 f₁ = Σχ rawLedgerχ`; no division or chart range is suppressed. -/
theorem exact_four_class_identity
    (f1 : ℝ)
    (d : Chart → ChartData Row Endpoint Target)
    (hnumerator : 4 * f1 = globalRaw d) :
    f1 = globalScaled d := by
  have hscaled := four_mul_globalScaled d
  linarith

theorem globalScaled_nonneg
    (d : Chart → ChartData Row Endpoint Target)
    (hS1 : ∀ χ, 0 ≤ (d χ).S1)
    (hS2 : ∀ χ, 0 ≤ (d χ).S2)
    (hS3 : ∀ χ, 0 ≤ (d χ).S3)
    (hS4 : ∀ χ, 0 ≤ (d χ).S4) :
    0 ≤ globalScaled d := by
  unfold globalScaled
  apply Finset.sum_nonneg
  intro χ hχ
  unfold ChartData.scaledLedger
  have h1 := hS1 χ
  have h2 := hS2 χ
  have h3 := hS3 χ
  have h4 := hS4 χ
  positivity

/-- End-to-end abstract exit from the settled numerator to nonnegativity.

Every hypothesis has the same indexing range as the corresponding summand:
completed packages are checked separately on the `D` and `I` row classes,
and the remaining coefficient is checked separately on those two classes.
Thus this theorem does not hide a pointwise-to-blockwise inference or a
fixed-chart reversal.  A concrete tree application must still construct
`d` and prove `hnumerator` on the complete chart range. -/
theorem exact_four_class_nonneg
    (f1 : ℝ)
    (d : Chart → ChartData Row Endpoint Target)
    (hnumerator : 4 * f1 = globalRaw d)
    (hpackageD :
      ∀ χ, ∀ r ∈ (d χ).D, ∀ k ∈ (d χ).endpoints,
        ((d χ).packageData r k).Nonnegative)
    (hpackageI :
      ∀ χ, ∀ r ∈ (d χ).I, ∀ k ∈ (d χ).endpoints,
        ((d χ).packageData r k).Nonnegative)
    (hPsiD :
      ∀ χ, ∀ r ∈ (d χ).D, ∀ u ∈ (d χ).targets,
        0 ≤ (d χ).Psi r u)
    (hPsiI :
      ∀ χ, ∀ r ∈ (d χ).I, ∀ u ∈ (d χ).targets,
        0 ≤ (d χ).Psi r u) :
    0 ≤ f1 := by
  have hidentity : f1 = globalScaled d :=
    exact_four_class_identity f1 d hnumerator
  rw [hidentity]
  apply globalScaled_nonneg d
  · intro χ
    exact (d χ).S1_nonneg (hpackageD χ)
  · intro χ
    exact (d χ).S2_nonneg (hpackageI χ)
  · intro χ
    exact (d χ).S3_nonneg (hPsiD χ)
  · intro χ
    exact (d χ).S4_nonneg (hPsiI χ)

end Global

end

end FourFamilyLedger

end QuartetV060
