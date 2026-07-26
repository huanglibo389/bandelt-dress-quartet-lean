import QuartetV060.RetainedSquares

/-!
# The completed-square package `(A.21a)`--`(A.25)`

This file formalizes the coefficient calculation that absorbs the mixed
face in the representative-square ledger.  Each of the four squares is
recorded together with its `X²`, `XY`, and `Y²` coefficients.  The final
theorems prove the four coefficient transports under bridge reversal; these
are cross-chart identities, not substitutions inside one fixed chart.
-/

namespace QuartetV060

namespace CompletedSquares

noncomputable section

/-- Coefficients of a homogeneous quadratic polynomial
`xx * X² + xy * X * Y + yy * Y²`. -/
@[ext]
structure QuadraticCoeff where
  xx : ℝ
  xy : ℝ
  yy : ℝ

namespace QuadraticCoeff

def eval (q : QuadraticCoeff) (X Y : ℝ) : ℝ :=
  q.xx * X ^ 2 + q.xy * X * Y + q.yy * Y ^ 2

instance : Add QuadraticCoeff where
  add p q :=
    ⟨p.xx + q.xx, p.xy + q.xy, p.yy + q.yy⟩

@[simp] theorem add_xx (p q : QuadraticCoeff) :
    (p + q).xx = p.xx + q.xx := rfl

@[simp] theorem add_xy (p q : QuadraticCoeff) :
    (p + q).xy = p.xy + q.xy := rfl

@[simp] theorem add_yy (p q : QuadraticCoeff) :
    (p + q).yy = p.yy + q.yy := rfl

@[simp] theorem eval_add (p q : QuadraticCoeff) (X Y : ℝ) :
    (p + q).eval X Y = p.eval X Y + q.eval X Y := by
  unfold eval
  simp only [add_xx, add_xy, add_yy]
  ring

end QuadraticCoeff

/-- The masses and four local `a`-entries belonging to one endpoint
occurrence in one chart.  `K` denotes the selected endpoint atom and `B`
its opposite block. -/
@[ext]
structure EndpointData where
  cK : ℝ
  cB : ℝ
  cKplus : ℝ
  aiK : ℝ
  ajK : ℝ
  aiB : ℝ
  ajB : ℝ

namespace EndpointData

variable (d : EndpointData)

/-- All masses and table entries used by one completed-square package are
nonnegative.  Strict positivity is imposed separately only when a coefficient
identity divides by one of these masses. -/
def Nonnegative : Prop :=
  0 ≤ d.cK ∧ 0 ≤ d.cB ∧ 0 ≤ d.cKplus ∧
    0 ≤ d.aiK ∧ 0 ≤ d.ajK ∧ 0 ≤ d.aiB ∧ 0 ≤ d.ajB

/-- The `(A.22)` summand. -/
def term22 (X Y : ℝ) : ℝ :=
  (1 / 4 : ℝ) * d.cK * (d.aiB * d.ajB / d.cB) *
    (Real.sqrt ((1 - d.cK) / d.cB) * X +
      Real.sqrt (d.cB / (1 - d.cK)) * Y) ^ 2

/-- The `(A.23)` summand. -/
def term23 (X Y : ℝ) : ℝ :=
  (1 / 4 : ℝ) * d.cB * (d.aiK * d.ajK / d.cK) *
    (Real.sqrt (d.cK / d.cKplus) * X +
      Real.sqrt (d.cKplus / d.cK) * Y) ^ 2

/-- The `(A.24)` summand. -/
def term24 (X Y : ℝ) : ℝ :=
  (1 / 4 : ℝ) * d.aiK * d.ajB * (X + Y) ^ 2

/-- The `(A.25)` summand. -/
def term25 (X Y : ℝ) : ℝ :=
  (1 / 4 : ℝ) * d.aiB * d.ajK * (X + Y) ^ 2

def coeff22 : QuadraticCoeff where
  xx :=
    (1 / 4 : ℝ) * d.cK * (1 - d.cK) / d.cB ^ 2 *
      d.aiB * d.ajB
  xy :=
    (1 / 2 : ℝ) * d.cK / d.cB * d.aiB * d.ajB
  yy :=
    (1 / 4 : ℝ) * d.cK / (1 - d.cK) * d.aiB * d.ajB

def coeff23 : QuadraticCoeff where
  xx :=
    (1 / 4 : ℝ) * d.cB / d.cKplus * d.aiK * d.ajK
  xy :=
    (1 / 2 : ℝ) * d.cB / d.cK * d.aiK * d.ajK
  yy :=
    (1 / 4 : ℝ) * d.cB * d.cKplus / d.cK ^ 2 *
      d.aiK * d.ajK

def coeff24 : QuadraticCoeff where
  xx := (1 / 4 : ℝ) * d.aiK * d.ajB
  xy := (1 / 2 : ℝ) * d.aiK * d.ajB
  yy := (1 / 4 : ℝ) * d.aiK * d.ajB

def coeff25 : QuadraticCoeff where
  xx := (1 / 4 : ℝ) * d.aiB * d.ajK
  xy := (1 / 2 : ℝ) * d.aiB * d.ajK
  yy := (1 / 4 : ℝ) * d.aiB * d.ajK

/-- The twelve displayed coefficients following `(A.22)`--`(A.25)`. -/
def packageCoeff : QuadraticCoeff :=
  d.coeff22 + d.coeff23 + d.coeff24 + d.coeff25

/-- The completed-square package `P_{ij,k}`. -/
def package (X Y : ℝ) : ℝ :=
  d.term22 X Y + d.term23 X Y + d.term24 X Y + d.term25 X Y

theorem term22_nonneg
    (h : d.Nonnegative) (X Y : ℝ) :
    0 ≤ d.term22 X Y := by
  rcases h with ⟨hcK, hcB, _, _, _, haiB, hajB⟩
  unfold term22
  have hquot : 0 ≤ d.aiB * d.ajB / d.cB :=
    div_nonneg (mul_nonneg haiB hajB) hcB
  positivity

theorem term23_nonneg
    (h : d.Nonnegative) (X Y : ℝ) :
    0 ≤ d.term23 X Y := by
  rcases h with ⟨hcK, hcB, _, haiK, hajK, _, _⟩
  unfold term23
  have hquot : 0 ≤ d.aiK * d.ajK / d.cK :=
    div_nonneg (mul_nonneg haiK hajK) hcK
  positivity

theorem term24_nonneg
    (h : d.Nonnegative) (X Y : ℝ) :
    0 ≤ d.term24 X Y := by
  rcases h with ⟨_, _, _, haiK, _, _, hajB⟩
  unfold term24
  positivity

theorem term25_nonneg
    (h : d.Nonnegative) (X Y : ℝ) :
    0 ≤ d.term25 X Y := by
  rcases h with ⟨_, _, _, _, hajK, haiB, _⟩
  unfold term25
  positivity

/-- Every completed-square package is nonnegative before any summation over
charts or occurrences. -/
theorem package_nonneg
    (h : d.Nonnegative) (X Y : ℝ) :
    0 ≤ d.package X Y := by
  unfold package
  exact add_nonneg
    (add_nonneg
      (add_nonneg (d.term22_nonneg h X Y) (d.term23_nonneg h X Y))
      (d.term24_nonneg h X Y))
    (d.term25_nonneg h X Y)

private theorem sqrt_ratio_mul_sqrt_reverse
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := by
  rw [← Real.sqrt_mul (le_of_lt (div_pos ha hb))]
  have hab : a / b * (b / a) = 1 := by
    field_simp [ne_of_gt ha, ne_of_gt hb]
  rw [hab, Real.sqrt_one]

theorem term22_eq_eval
    (hK : d.cK < 1) (hB : 0 < d.cB) (X Y : ℝ) :
    d.term22 X Y = d.coeff22.eval X Y := by
  have hcomp : 0 < 1 - d.cK := sub_pos.mpr hK
  have hsquare₁ :
      Real.sqrt ((1 - d.cK) / d.cB) ^ 2 =
        (1 - d.cK) / d.cB :=
    Real.sq_sqrt (le_of_lt (div_pos hcomp hB))
  have hsquare₂ :
      Real.sqrt (d.cB / (1 - d.cK)) ^ 2 =
        d.cB / (1 - d.cK) :=
    Real.sq_sqrt (le_of_lt (div_pos hB hcomp))
  have hcross :
      Real.sqrt ((1 - d.cK) / d.cB) *
        Real.sqrt (d.cB / (1 - d.cK)) = 1 :=
    sqrt_ratio_mul_sqrt_reverse hcomp hB
  unfold term22 coeff22 QuadraticCoeff.eval
  rw [show
    (Real.sqrt ((1 - d.cK) / d.cB) * X +
      Real.sqrt (d.cB / (1 - d.cK)) * Y) ^ 2 =
      Real.sqrt ((1 - d.cK) / d.cB) ^ 2 * X ^ 2 +
      2 * (Real.sqrt ((1 - d.cK) / d.cB) *
        Real.sqrt (d.cB / (1 - d.cK))) * X * Y +
      Real.sqrt (d.cB / (1 - d.cK)) ^ 2 * Y ^ 2 by ring]
  rw [hsquare₁, hsquare₂, hcross]
  field_simp [ne_of_gt hB, ne_of_gt hcomp]
  ring

theorem term23_eq_eval
    (hK : 0 < d.cK) (hKplus : 0 < d.cKplus) (X Y : ℝ) :
    d.term23 X Y = d.coeff23.eval X Y := by
  have hsquare₁ :
      Real.sqrt (d.cK / d.cKplus) ^ 2 =
        d.cK / d.cKplus :=
    Real.sq_sqrt (le_of_lt (div_pos hK hKplus))
  have hsquare₂ :
      Real.sqrt (d.cKplus / d.cK) ^ 2 =
        d.cKplus / d.cK :=
    Real.sq_sqrt (le_of_lt (div_pos hKplus hK))
  have hcross :
      Real.sqrt (d.cK / d.cKplus) *
        Real.sqrt (d.cKplus / d.cK) = 1 :=
    sqrt_ratio_mul_sqrt_reverse hK hKplus
  unfold term23 coeff23 QuadraticCoeff.eval
  rw [show
    (Real.sqrt (d.cK / d.cKplus) * X +
      Real.sqrt (d.cKplus / d.cK) * Y) ^ 2 =
      Real.sqrt (d.cK / d.cKplus) ^ 2 * X ^ 2 +
      2 * (Real.sqrt (d.cK / d.cKplus) *
        Real.sqrt (d.cKplus / d.cK)) * X * Y +
      Real.sqrt (d.cKplus / d.cK) ^ 2 * Y ^ 2 by ring]
  rw [hsquare₁, hsquare₂, hcross]
  field_simp [ne_of_gt hK, ne_of_gt hKplus]
  ring

theorem term24_eq_eval (X Y : ℝ) :
    d.term24 X Y = d.coeff24.eval X Y := by
  unfold term24 coeff24 QuadraticCoeff.eval
  ring

theorem term25_eq_eval (X Y : ℝ) :
    d.term25 X Y = d.coeff25.eval X Y := by
  unfold term25 coeff25 QuadraticCoeff.eval
  ring

/-- The four manuscript squares have exactly the twelve listed
coefficients. -/
theorem package_eq_eval
    (hK0 : 0 < d.cK) (hK1 : d.cK < 1)
    (hB : 0 < d.cB) (hKplus : 0 < d.cKplus)
    (X Y : ℝ) :
    d.package X Y = d.packageCoeff.eval X Y := by
  unfold package packageCoeff
  rw [d.term22_eq_eval hK1 hB, d.term23_eq_eval hK0 hKplus,
    d.term24_eq_eval, d.term25_eq_eval]
  simp only [QuadraticCoeff.eval_add]

/-- The refinement product identity `(A.21a)`. -/
theorem refinement_product
    (ri rj : ℝ)
    (hK : d.cK ≠ 0) (hB : d.cB ≠ 0)
    (hi :
      2 * d.cK * ri =
        d.aiK + d.cK / d.cB * d.aiB)
    (hj :
      2 * d.cK * rj =
        d.ajK + d.cK / d.cB * d.ajB) :
    ri * rj * d.cK * d.cB =
      (1 / 4 : ℝ) *
        (d.cB / d.cK * d.aiK * d.ajK +
          d.aiK * d.ajB + d.aiB * d.ajK +
          d.cK / d.cB * d.aiB * d.ajB) := by
  have hri :
      ri =
        (d.aiK + d.cK / d.cB * d.aiB) /
          (2 * d.cK) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hK)).2
    nlinarith [hi]
  have hrj :
      rj =
        (d.ajK + d.cK / d.cB * d.ajB) /
          (2 * d.cK) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hK)).2
    nlinarith [hj]
  rw [hri, hrj]
  field_simp [hK, hB]
  ring

/-- The four mixed coefficients add to the retained mixed face `(A.20)`. -/
theorem packageCoeff_xy
    (ri rj : ℝ)
    (hK : d.cK ≠ 0) (hB : d.cB ≠ 0)
    (hi :
      2 * d.cK * ri =
        d.aiK + d.cK / d.cB * d.aiB)
    (hj :
      2 * d.cK * rj =
        d.ajK + d.cK / d.cB * d.ajB) :
    d.packageCoeff.xy = 2 * d.cK * d.cB * ri * rj := by
  have hprod := d.refinement_product ri rj hK hB hi hj
  unfold packageCoeff coeff22 coeff23 coeff24 coeff25
  dsimp
  calc
    (1 / 2 : ℝ) * d.cK / d.cB * d.aiB * d.ajB +
          (1 / 2 : ℝ) * d.cB / d.cK * d.aiK * d.ajK +
          (1 / 2 : ℝ) * d.aiK * d.ajB +
          (1 / 2 : ℝ) * d.aiB * d.ajK =
        2 * ((1 / 4 : ℝ) *
          (d.cB / d.cK * d.aiK * d.ajK +
            d.aiK * d.ajB + d.aiB * d.ajK +
            d.cK / d.cB * d.aiB * d.ajB)) := by ring
    _ = 2 * (ri * rj * d.cK * d.cB) := by rw [← hprod]
    _ = 2 * d.cK * d.cB * ri * rj := by ring

/-- The four-term expansion `(A.26)`--`(A.29)`. -/
theorem available_coefficient_expansion
    (ri rj cL cLbar ajL ajLbar : ℝ)
    (hi :
      2 * d.cK * ri =
        d.aiK + d.cK / d.cB * d.aiB)
    (hj :
      2 * cL * rj =
        ajL + cL / cLbar * ajLbar) :
    4 * ri * d.cK * rj * cL =
      d.aiK * ajL +
        cL / cLbar * d.aiK * ajLbar +
        d.cK / d.cB * d.aiB * ajL +
        d.cK * cL / (d.cB * cLbar) * d.aiB * ajLbar := by
  calc
    4 * ri * d.cK * rj * cL =
        (2 * d.cK * ri) * (2 * cL * rj) := by ring
    _ =
        (d.aiK + d.cK / d.cB * d.aiB) *
          (ajL + cL / cLbar * ajLbar) := by rw [hi, hj]
    _ =
      d.aiK * ajL +
        cL / cLbar * d.aiK * ajLbar +
        d.cK / d.cB * d.aiB * ajL +
        d.cK * cL / (d.cB * cLbar) * d.aiB * ajLbar := by
          ring

/-- Reversal sends `(K,H,L)` to `(L,H,K)`.  The reversed selected atom is
the old opposite block; the reversed opposite block is the old selected
atom. -/
def reverse : EndpointData where
  cK := d.cB
  cB := d.cK
  cKplus := 1 - d.cK
  aiK := d.aiB
  ajK := d.ajB
  aiB := d.aiK
  ajB := d.ajK

@[simp] theorem reverse_cK : d.reverse.cK = d.cB := rfl
@[simp] theorem reverse_cB : d.reverse.cB = d.cK := rfl
@[simp] theorem reverse_cKplus :
    d.reverse.cKplus = 1 - d.cK := rfl
@[simp] theorem reverse_aiK : d.reverse.aiK = d.aiB := rfl
@[simp] theorem reverse_ajK : d.reverse.ajK = d.ajB := rfl
@[simp] theorem reverse_aiB : d.reverse.aiB = d.aiK := rfl
@[simp] theorem reverse_ajB : d.reverse.ajB = d.ajK := rfl

/-- `(A.22)` second face in a chart is `(A.23)` first face in the reversed
chart. -/
theorem coeff22_yy_eq_reverse_coeff23_xx :
    d.coeff22.yy = d.reverse.coeff23.xx := by
  rfl

/-- `(A.23)` second face in a chart is `(A.22)` first face in the reversed
chart.  Here `cKplus = 1 - cB` is the three-block mass identity. -/
theorem coeff23_yy_eq_reverse_coeff22_xx
    (hKplus : d.cKplus = 1 - d.cB) :
    d.coeff23.yy = d.reverse.coeff22.xx := by
  unfold coeff23 coeff22 reverse
  dsimp
  rw [hKplus]

/-- `(A.24)` second face in a chart is `(A.25)` first face in the reversed
chart. -/
theorem coeff24_yy_eq_reverse_coeff25_xx :
    d.coeff24.yy = d.reverse.coeff25.xx := by
  rfl

/-- `(A.25)` second face in a chart is `(A.24)` first face in the reversed
chart. -/
theorem coeff25_yy_eq_reverse_coeff24_xx :
    d.coeff25.yy = d.reverse.coeff24.xx := by
  rfl

/-- The total second-square coefficient of one completed package is the
total first-square coefficient of the reversed package. -/
theorem packageCoeff_yy_eq_reverse_xx
    (hKplus : d.cKplus = 1 - d.cB) :
    d.packageCoeff.yy = d.reverse.packageCoeff.xx := by
  unfold packageCoeff
  simp only [QuadraticCoeff.add_yy, QuadraticCoeff.add_xx]
  rw [d.coeff22_yy_eq_reverse_coeff23_xx]
  rw [d.coeff23_yy_eq_reverse_coeff22_xx hKplus]
  rw [d.coeff24_yy_eq_reverse_coeff25_xx]
  rw [d.coeff25_yy_eq_reverse_coeff24_xx]
  ring

end EndpointData

end

end CompletedSquares

end QuartetV060
