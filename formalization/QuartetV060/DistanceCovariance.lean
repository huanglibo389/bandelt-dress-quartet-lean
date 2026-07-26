import QuartetV060.Determinant

/-!
# Appendix B: split determinants and empirical distance covariance

This file formalizes Proposition `distance-covariance-split` from Appendix B
of the v0.60 manuscript.  It is logically independent of the quartet-distance
proof in Appendix A.

The taxon type is finite and nonempty.  A split is represented by one of its
two sides; changing that representative does not change the induced split
pseudometric.  Edge lengths are real, so the statement covers the
edge-weighted pseudometrics used in the manuscript.
-/

namespace QuartetV060

open scoped BigOperators

namespace DistanceCovariance

variable {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]

/-- Empirical mean on a finite nonempty taxon set. -/
noncomputable def empiricalMean (f : X → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card X : ℝ)

@[simp] theorem empiricalMean_const (c : ℝ) :
    empiricalMean (fun _ : X => c) = c := by
  simp [empiricalMean, Fintype.card_ne_zero]

theorem empiricalMean_add (f g : X → ℝ) :
    empiricalMean (fun x => f x + g x) =
      empiricalMean f + empiricalMean g := by
  simp [empiricalMean, Finset.sum_add_distrib, add_div]

theorem empiricalMean_sub (f g : X → ℝ) :
    empiricalMean (fun x => f x - g x) =
      empiricalMean f - empiricalMean g := by
  simp [empiricalMean, Finset.sum_sub_distrib, sub_div]

theorem empiricalMean_const_mul (c : ℝ) (f : X → ℝ) :
    empiricalMean (fun x => c * f x) = c * empiricalMean f := by
  unfold empiricalMean
  rw [← Finset.mul_sum]
  ring

theorem empiricalMean_mul_const (f : X → ℝ) (c : ℝ) :
    empiricalMean (fun x => f x * c) = empiricalMean f * c := by
  unfold empiricalMean
  rw [← Finset.sum_mul]
  ring

theorem empiricalMean_sum
    {E : Type*} [Fintype E] (f : E → X → ℝ) :
    empiricalMean (fun x => ∑ e, f e x) =
      ∑ e, empiricalMean (f e) := by
  simp only [empiricalMean, Finset.sum_div]
  rw [Finset.sum_comm]

/-- The `0`-`1` indicator of one chosen side of a split. -/
noncomputable def sideIndicator (P : Finset X) (x : X) : ℝ :=
  if x ∈ P then 1 else 0

@[simp] theorem sideIndicator_sq (P : Finset X) (x : X) :
    sideIndicator P x ^ 2 = sideIndicator P x := by
  classical
  simp [sideIndicator]

theorem sideIndicator_inter (P Q : Finset X) (x : X) :
    sideIndicator (P ∩ Q) x =
      sideIndicator P x * sideIndicator Q x := by
  classical
  by_cases hP : x ∈ P <;> by_cases hQ : x ∈ Q <;>
    simp [sideIndicator, hP, hQ]

theorem sideIndicator_compl (P : Finset X) (x : X) :
    sideIndicator Pᶜ x = 1 - sideIndicator P x := by
  classical
  by_cases hP : x ∈ P <;> simp [sideIndicator, hP]

/-- The normalized mass of the chosen side. -/
noncomputable def sideMass (P : Finset X) : ℝ :=
  empiricalMean (sideIndicator P)

/-- Real-valued normalized cardinality, used to connect the indicator
definitions directly to the table entries displayed in Appendix B. -/
noncomputable def normalizedCardReal (P : Finset X) : ℝ :=
  (P.card : ℝ) / (Fintype.card X : ℝ)

theorem sideMass_eq_normalizedCardReal (P : Finset X) :
    sideMass P = normalizedCardReal P := by
  classical
  simp [sideMass, empiricalMean, sideIndicator, normalizedCardReal]

/-- The centered indicator `I_P - |P|/|X|`. -/
noncomputable def centeredIndicator (P : Finset X) (x : X) : ℝ :=
  sideIndicator P x - sideMass P

theorem empiricalMean_centeredIndicator (P : Finset X) :
    empiricalMean (centeredIndicator P) = 0 := by
  rw [show centeredIndicator P =
      fun x => sideIndicator P x - (fun _ : X => sideMass P) x by
        funext x
        rfl]
  rw [empiricalMean_sub, empiricalMean_const]
  unfold sideMass
  ring

/-- The `0`-`1` split pseudometric associated with one side of a split. -/
noncomputable def splitPseudometric (P : Finset X) (i j : X) : ℝ :=
  (sideIndicator P i - sideIndicator P j) ^ 2

theorem splitPseudometric_compl (P : Finset X) (i j : X) :
    splitPseudometric Pᶜ i j = splitPseudometric P i j := by
  unfold splitPseudometric
  rw [sideIndicator_compl, sideIndicator_compl]
  ring

theorem splitPseudometric_expand (P : Finset X) (i j : X) :
    splitPseudometric P i j =
      sideIndicator P i + sideIndicator P j -
        2 * sideIndicator P i * sideIndicator P j := by
  unfold splitPseudometric
  calc
    (sideIndicator P i - sideIndicator P j) ^ 2 =
        sideIndicator P i ^ 2 + sideIndicator P j ^ 2 -
          2 * sideIndicator P i * sideIndicator P j := by ring
    _ = sideIndicator P i + sideIndicator P j -
          2 * sideIndicator P i * sideIndicator P j := by
            rw [sideIndicator_sq, sideIndicator_sq]

/-- Row mean of a finite matrix. -/
noncomputable def rowMean (M : X → X → ℝ) (i : X) : ℝ :=
  empiricalMean (M i)

/-- Column mean of a finite matrix. -/
noncomputable def columnMean (M : X → X → ℝ) (j : X) : ℝ :=
  empiricalMean (fun i => M i j)

/-- Grand mean of a finite matrix. -/
noncomputable def grandMean (M : X → X → ℝ) : ℝ :=
  empiricalMean (rowMean M)

/-- Double centering of a finite matrix. -/
noncomputable def doubleCentered (M : X → X → ℝ) (i j : X) : ℝ :=
  M i j - rowMean M i - columnMean M j + grandMean M

theorem splitPseudometric_rowMean (P : Finset X) (i : X) :
    rowMean (splitPseudometric P) i =
      sideMass P + (1 - 2 * sideMass P) * sideIndicator P i := by
  let I := sideIndicator P
  let p := sideMass P
  calc
    rowMean (splitPseudometric P) i
        = empiricalMean
            (fun j => I i + I j - (2 * I i) * I j) := by
              apply congrArg empiricalMean
              funext j
              simpa [I] using splitPseudometric_expand P i j
    _ = empiricalMean (fun _ : X => I i) +
          empiricalMean I -
          empiricalMean (fun j => (2 * I i) * I j) := by
            rw [empiricalMean_sub, empiricalMean_add]
    _ = I i + p - (2 * I i) * p := by
          rw [empiricalMean_const, empiricalMean_const_mul]
          rfl
    _ = p + (1 - 2 * p) * I i := by ring

theorem splitPseudometric_columnMean (P : Finset X) (j : X) :
    columnMean (splitPseudometric P) j =
      sideMass P + (1 - 2 * sideMass P) * sideIndicator P j := by
  let I := sideIndicator P
  let p := sideMass P
  calc
    columnMean (splitPseudometric P) j
        = empiricalMean
            (fun i => I i + I j - I i * (2 * I j)) := by
              apply congrArg empiricalMean
              funext i
              rw [splitPseudometric_expand]
              simp only [I]
              ring
    _ = empiricalMean I +
          empiricalMean (fun _ : X => I j) -
          empiricalMean (fun i => I i * (2 * I j)) := by
            rw [empiricalMean_sub, empiricalMean_add]
    _ = p + I j - p * (2 * I j) := by
          rw [empiricalMean_const, empiricalMean_mul_const]
          rfl
    _ = p + (1 - 2 * p) * I j := by ring

theorem splitPseudometric_grandMean (P : Finset X) :
    grandMean (splitPseudometric P) =
      2 * sideMass P * (1 - sideMass P) := by
  let I := sideIndicator P
  let p := sideMass P
  calc
    grandMean (splitPseudometric P)
        = empiricalMean (fun i => p + (1 - 2 * p) * I i) := by
            apply congrArg empiricalMean
            funext i
            simpa [p, I] using splitPseudometric_rowMean P i
    _ = empiricalMean (fun _ : X => p) +
          empiricalMean (fun i => (1 - 2 * p) * I i) := by
            rw [empiricalMean_add]
    _ = p + (1 - 2 * p) * p := by
          rw [empiricalMean_const, empiricalMean_const_mul]
          rfl
    _ = 2 * p * (1 - p) := by ring

/-- The manuscript's elementary double-centering identity:
`δ̄_P(i,j) = -2 (I_P(i)-p)(I_P(j)-p)`. -/
theorem doubleCentered_splitPseudometric (P : Finset X) (i j : X) :
    doubleCentered (splitPseudometric P) i j =
      -2 * centeredIndicator P i * centeredIndicator P j := by
  rw [show doubleCentered (splitPseudometric P) i j =
      splitPseudometric P i j -
        rowMean (splitPseudometric P) i -
        columnMean (splitPseudometric P) j +
        grandMean (splitPseudometric P) by rfl]
  rw [splitPseudometric_expand, splitPseudometric_rowMean,
    splitPseudometric_columnMean, splitPseudometric_grandMean]
  simp only [centeredIndicator]
  ring

section WeightedMetrics

variable {E : Type*} [Fintype E]

/-- A finite weighted sum of split pseudometrics.  For an edge-indexed split
system this is exactly the induced tree pseudometric. -/
noncomputable def weightedSplitPseudometric
    (P : E → Finset X) (w : E → ℝ) (i j : X) : ℝ :=
  ∑ e, w e * splitPseudometric (P e) i j

theorem weightedSplitPseudometric_rowMean
    (P : E → Finset X) (w : E → ℝ) (i : X) :
    rowMean (weightedSplitPseudometric P w) i =
      ∑ e, w e * rowMean (splitPseudometric (P e)) i := by
  unfold rowMean weightedSplitPseudometric
  rw [empiricalMean_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact empiricalMean_const_mul (w e) (splitPseudometric (P e) i)

theorem weightedSplitPseudometric_columnMean
    (P : E → Finset X) (w : E → ℝ) (j : X) :
    columnMean (weightedSplitPseudometric P w) j =
      ∑ e, w e * columnMean (splitPseudometric (P e)) j := by
  unfold columnMean weightedSplitPseudometric
  rw [empiricalMean_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact empiricalMean_const_mul (w e)
    (fun i => splitPseudometric (P e) i j)

theorem weightedSplitPseudometric_grandMean
    (P : E → Finset X) (w : E → ℝ) :
    grandMean (weightedSplitPseudometric P w) =
      ∑ e, w e * grandMean (splitPseudometric (P e)) := by
  unfold grandMean
  rw [show rowMean (weightedSplitPseudometric P w) =
      fun i => ∑ e, w e * rowMean (splitPseudometric (P e)) i by
        funext i
        exact weightedSplitPseudometric_rowMean P w i]
  rw [empiricalMean_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact empiricalMean_const_mul (w e)
    (rowMean (splitPseudometric (P e)))

/-- Double centering commutes with a finite weighted split sum. -/
theorem doubleCentered_weightedSplitPseudometric
    (P : E → Finset X) (w : E → ℝ) (i j : X) :
    doubleCentered (weightedSplitPseudometric P w) i j =
      ∑ e, w e * doubleCentered (splitPseudometric (P e)) i j := by
  unfold doubleCentered
  rw [weightedSplitPseudometric_rowMean,
    weightedSplitPseudometric_columnMean,
    weightedSplitPseudometric_grandMean]
  unfold weightedSplitPseudometric
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]

/-- The double-centered weighted pseudometric in centered-indicator form. -/
theorem doubleCentered_weightedSplitPseudometric_eq
    (P : E → Finset X) (w : E → ℝ) (i j : X) :
    doubleCentered (weightedSplitPseudometric P w) i j =
      -2 * ∑ e, w e * centeredIndicator (P e) i *
        centeredIndicator (P e) j := by
  rw [doubleCentered_weightedSplitPseudometric]
  simp_rw [doubleCentered_splitPseudometric]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

end WeightedMetrics

/-- The empirical distance-covariance inner product of two finite
pseudometric matrices. -/
noncomputable def empiricalDistanceCovariance
    (M N : X → X → ℝ) : ℝ :=
  empiricalMean (fun i =>
    empiricalMean (fun j =>
      doubleCentered M i j * doubleCentered N i j))

/-- The normalized intersection table of the two represented splits. -/
noncomputable def splitIntersectionTable
    (P Q : Finset X) : Table2 ℝ where
  a := empiricalMean (fun x => sideIndicator P x * sideIndicator Q x)
  b := empiricalMean (fun x =>
    sideIndicator P x * (1 - sideIndicator Q x))
  c := empiricalMean (fun x =>
    (1 - sideIndicator P x) * sideIndicator Q x)
  d := empiricalMean (fun x =>
    (1 - sideIndicator P x) * (1 - sideIndicator Q x))

theorem splitIntersectionTable_compl_left (P Q : Finset X) :
    splitIntersectionTable Pᶜ Q =
      Table2.reverseRows (splitIntersectionTable P Q) := by
  ext <;>
    simp only [splitIntersectionTable, Table2.reverseRows,
      sideIndicator_compl]
  all_goals
    apply congrArg empiricalMean
    funext x
    ring

theorem splitIntersectionTable_compl_right (P Q : Finset X) :
    splitIntersectionTable P Qᶜ =
      Table2.reverseCols (splitIntersectionTable P Q) := by
  ext <;>
    simp only [splitIntersectionTable, Table2.reverseCols,
      sideIndicator_compl]
  all_goals
    apply congrArg empiricalMean
    funext x
    ring

@[simp] theorem splitIntersectionTable_detSquare_compl_left
    (P Q : Finset X) :
    Table2.detSquare (splitIntersectionTable Pᶜ Q) =
      Table2.detSquare (splitIntersectionTable P Q) := by
  rw [splitIntersectionTable_compl_left,
    Table2.detSquare_reverseRows]

@[simp] theorem splitIntersectionTable_detSquare_compl_right
    (P Q : Finset X) :
    Table2.detSquare (splitIntersectionTable P Qᶜ) =
      Table2.detSquare (splitIntersectionTable P Q) := by
  rw [splitIntersectionTable_compl_right,
    Table2.detSquare_reverseCols]

theorem splitIntersectionTable_a_eq (P Q : Finset X) :
    (splitIntersectionTable P Q).a =
      normalizedCardReal (P ∩ Q) := by
  change empiricalMean
      (fun x => sideIndicator P x * sideIndicator Q x) =
    normalizedCardReal (P ∩ Q)
  rw [show (fun x => sideIndicator P x * sideIndicator Q x) =
      sideIndicator (P ∩ Q) by
        funext x
        exact (sideIndicator_inter P Q x).symm]
  exact sideMass_eq_normalizedCardReal (P ∩ Q)

theorem splitIntersectionTable_b_eq (P Q : Finset X) :
    (splitIntersectionTable P Q).b =
      normalizedCardReal (P ∩ Qᶜ) := by
  change empiricalMean
      (fun x => sideIndicator P x * (1 - sideIndicator Q x)) =
    normalizedCardReal (P ∩ Qᶜ)
  rw [show
      (fun x => sideIndicator P x * (1 - sideIndicator Q x)) =
        sideIndicator (P ∩ Qᶜ) by
          funext x
          rw [sideIndicator_inter, sideIndicator_compl]]
  exact sideMass_eq_normalizedCardReal (P ∩ Qᶜ)

theorem splitIntersectionTable_c_eq (P Q : Finset X) :
    (splitIntersectionTable P Q).c =
      normalizedCardReal (Pᶜ ∩ Q) := by
  change empiricalMean
      (fun x => (1 - sideIndicator P x) * sideIndicator Q x) =
    normalizedCardReal (Pᶜ ∩ Q)
  rw [show
      (fun x => (1 - sideIndicator P x) * sideIndicator Q x) =
        sideIndicator (Pᶜ ∩ Q) by
          funext x
          rw [sideIndicator_inter, sideIndicator_compl]]
  exact sideMass_eq_normalizedCardReal (Pᶜ ∩ Q)

theorem splitIntersectionTable_d_eq (P Q : Finset X) :
    (splitIntersectionTable P Q).d =
      normalizedCardReal (Pᶜ ∩ Qᶜ) := by
  change empiricalMean
      (fun x => (1 - sideIndicator P x) *
        (1 - sideIndicator Q x)) =
    normalizedCardReal (Pᶜ ∩ Qᶜ)
  rw [show
      (fun x => (1 - sideIndicator P x) *
        (1 - sideIndicator Q x)) =
        sideIndicator (Pᶜ ∩ Qᶜ) by
          funext x
          rw [sideIndicator_inter, sideIndicator_compl,
            sideIndicator_compl]]
  exact sideMass_eq_normalizedCardReal (Pᶜ ∩ Qᶜ)

theorem splitIntersectionTable_a_add_b (P Q : Finset X) :
    (splitIntersectionTable P Q).a +
        (splitIntersectionTable P Q).b =
      sideMass P := by
  change empiricalMean
      (fun x => sideIndicator P x * sideIndicator Q x) +
      empiricalMean
        (fun x => sideIndicator P x * (1 - sideIndicator Q x)) =
    sideMass P
  rw [← empiricalMean_add]
  unfold sideMass
  apply congrArg empiricalMean
  funext x
  ring

theorem splitIntersectionTable_a_add_c (P Q : Finset X) :
    (splitIntersectionTable P Q).a +
        (splitIntersectionTable P Q).c =
      sideMass Q := by
  change empiricalMean
      (fun x => sideIndicator P x * sideIndicator Q x) +
      empiricalMean
        (fun x => (1 - sideIndicator P x) * sideIndicator Q x) =
    sideMass Q
  rw [← empiricalMean_add]
  unfold sideMass
  apply congrArg empiricalMean
  funext x
  ring

theorem splitIntersectionTable_c_add_d (P Q : Finset X) :
    (splitIntersectionTable P Q).c +
        (splitIntersectionTable P Q).d =
      1 - sideMass P := by
  change empiricalMean
      (fun x => (1 - sideIndicator P x) * sideIndicator Q x) +
      empiricalMean
        (fun x => (1 - sideIndicator P x) *
          (1 - sideIndicator Q x)) =
    1 - sideMass P
  rw [← empiricalMean_add]
  unfold sideMass
  rw [← (empiricalMean_const (X := X) 1), ← empiricalMean_sub]
  apply congrArg empiricalMean
  funext x
  simp only [empiricalMean_const]
  ring

theorem splitIntersectionTable_total (P Q : Finset X) :
    (splitIntersectionTable P Q).a +
        (splitIntersectionTable P Q).b +
        (splitIntersectionTable P Q).c +
        (splitIntersectionTable P Q).d = 1 := by
  rw [show
      (splitIntersectionTable P Q).a +
          (splitIntersectionTable P Q).b +
          (splitIntersectionTable P Q).c +
          (splitIntersectionTable P Q).d =
        ((splitIntersectionTable P Q).a +
          (splitIntersectionTable P Q).b) +
        ((splitIntersectionTable P Q).c +
          (splitIntersectionTable P Q).d) by ring]
  rw [splitIntersectionTable_a_add_b, splitIntersectionTable_c_add_d]
  ring

theorem centeredIndicator_product_mean (P Q : Finset X) :
    empiricalMean
        (fun x => centeredIndicator P x * centeredIndicator Q x) =
      (splitIntersectionTable P Q).a - sideMass P * sideMass Q := by
  let I := sideIndicator P
  let J := sideIndicator Q
  let p := sideMass P
  let q := sideMass Q
  calc
    empiricalMean
        (fun x => centeredIndicator P x * centeredIndicator Q x)
        = empiricalMean
            (fun x => I x * J x - p * J x - q * I x + p * q) := by
              apply congrArg empiricalMean
              funext x
              simp only [centeredIndicator, I, J, p, q]
              ring
    _ = empiricalMean (fun x => I x * J x) -
          empiricalMean (fun x => p * J x) -
          empiricalMean (fun x => q * I x) +
          empiricalMean (fun _ : X => p * q) := by
            rw [empiricalMean_add, empiricalMean_sub, empiricalMean_sub]
    _ = (splitIntersectionTable P Q).a - p * q - q * p + p * q := by
          rw [empiricalMean_const_mul, empiricalMean_const_mul,
            empiricalMean_const]
          rfl
    _ = (splitIntersectionTable P Q).a - p * q := by ring

/-- The centered-indicator covariance is the determinant of the normalized
split intersection table. -/
theorem centeredIndicator_product_mean_eq_det (P Q : Finset X) :
    empiricalMean
        (fun x => centeredIndicator P x * centeredIndicator Q x) =
      Table2.det (splitIntersectionTable P Q) := by
  rw [centeredIndicator_product_mean]
  rw [← splitIntersectionTable_a_add_b P Q,
    ← splitIntersectionTable_a_add_c P Q]
  exact Table2.centeredCovariance_eq_det
    (splitIntersectionTable P Q) (splitIntersectionTable_total P Q)

/-- Averaging a rank-one kernel over both coordinates gives the square of
its one-coordinate mean. -/
theorem empiricalMean_weighted_rankOne (c : ℝ) (u : X → ℝ) :
    empiricalMean (fun i =>
      empiricalMean (fun j => c * u i * u j)) =
      c * empiricalMean u ^ 2 := by
  calc
    empiricalMean (fun i =>
      empiricalMean (fun j => c * u i * u j))
        = empiricalMean (fun i => (c * u i) * empiricalMean u) := by
            apply congrArg empiricalMean
            funext i
            rw [show (fun j => c * u i * u j) =
                fun j => (c * u i) * u j by
                  funext j
                  rfl]
            rw [empiricalMean_const_mul]
    _ = empiricalMean (fun i => c * u i) * empiricalMean u := by
          rw [empiricalMean_mul_const]
    _ = c * empiricalMean u ^ 2 := by
          rw [empiricalMean_const_mul]
          ring

/-- Bilinear expansion of two finite sums of rank-one kernels. -/
theorem empiricalMean_pairwise_rankOne_sum
    {E F : Type*} [Fintype E] [Fintype F]
    (w : E → ℝ) (v : F → ℝ)
    (z : E → X → ℝ) (y : F → X → ℝ) :
    empiricalMean (fun i =>
      empiricalMean (fun j =>
        (∑ e, w e * z e i * z e j) *
          (∑ f, v f * y f i * y f j))) =
      ∑ e, ∑ f, w e * v f *
        empiricalMean (fun x => z e x * y f x) ^ 2 := by
  have hproduct (i j : X) :
      (∑ e, w e * z e i * z e j) *
          (∑ f, v f * y f i * y f j) =
        ∑ e, ∑ f, (w e * v f) *
          ((z e i * y f i) * (z e j * y f j)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    ring
  simp_rw [hproduct]
  rw [show
      (fun i => empiricalMean
        (fun j => ∑ e, ∑ f, (w e * v f) *
          ((z e i * y f i) * (z e j * y f j)))) =
      (fun i => ∑ e, ∑ f,
        empiricalMean (fun j => (w e * v f) *
          ((z e i * y f i) * (z e j * y f j)))) by
        funext i
        rw [empiricalMean_sum]
        apply Finset.sum_congr rfl
        intro e _
        rw [empiricalMean_sum]]
  rw [empiricalMean_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [empiricalMean_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [show
      (fun i => empiricalMean
        (fun j => (w e * v f) *
          ((z e i * y f i) * (z e j * y f j)))) =
      (fun i => empiricalMean
        (fun j => (w e * v f) *
          (z e i * y f i) * (z e j * y f j))) by
        funext i
        apply congrArg empiricalMean
        funext j
        ring]
  exact empiricalMean_weighted_rankOne
    (w e * v f) (fun x => z e x * y f x)

section SplitSystems

variable {E F : Type*} [Fintype E] [Fintype F]

/-- Appendix B's distance covariance for two finite weighted split systems. -/
noncomputable def splitSystemDistanceCovariance
    (P : E → Finset X) (w : E → ℝ)
    (Q : F → Finset X) (v : F → ℝ) : ℝ :=
  empiricalDistanceCovariance
    (weightedSplitPseudometric P w)
    (weightedSplitPseudometric Q v)

/-- Proposition B.1 (`distance-covariance-split`): the empirical
distance-covariance inner product of two weighted split pseudometrics is four
times the weighted sum of normalized split-determinant squares. -/
theorem splitSystemDistanceCovariance_eq_detSquare
    (P : E → Finset X) (w : E → ℝ)
    (Q : F → Finset X) (v : F → ℝ) :
    splitSystemDistanceCovariance P w Q v =
      4 * ∑ e, ∑ f, w e * v f *
        Table2.detSquare (splitIntersectionTable (P e) (Q f)) := by
  unfold splitSystemDistanceCovariance empiricalDistanceCovariance
  simp_rw [doubleCentered_weightedSplitPseudometric_eq]
  rw [show
      (fun i => empiricalMean
        (fun j =>
          (-2 * ∑ e, w e * centeredIndicator (P e) i *
              centeredIndicator (P e) j) *
            (-2 * ∑ f, v f * centeredIndicator (Q f) i *
              centeredIndicator (Q f) j))) =
      (fun i => 4 * empiricalMean
        (fun j =>
          (∑ e, w e * centeredIndicator (P e) i *
              centeredIndicator (P e) j) *
            (∑ f, v f * centeredIndicator (Q f) i *
              centeredIndicator (Q f) j))) by
        funext i
        rw [← empiricalMean_const_mul]
        apply congrArg empiricalMean
        funext j
        ring]
  rw [empiricalMean_const_mul,
    empiricalMean_pairwise_rankOne_sum]
  apply congrArg (fun t : ℝ => 4 * t)
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  rw [centeredIndicator_product_mean_eq_det]
  rfl

/-- The nonnegativity conclusion of Proposition B.1 for nonnegative edge
lengths. -/
theorem splitSystemDistanceCovariance_nonnegative
    (P : E → Finset X) (w : E → ℝ)
    (Q : F → Finset X) (v : F → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hv : ∀ f, 0 ≤ v f) :
    0 ≤ splitSystemDistanceCovariance P w Q v := by
  rw [splitSystemDistanceCovariance_eq_detSquare]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro e _
  apply Finset.sum_nonneg
  intro f _
  exact mul_nonneg (mul_nonneg (hw e) (hv f))
    (sq_nonneg (Table2.det (splitIntersectionTable (P e) (Q f))))

end SplitSystems

end DistanceCovariance

end QuartetV060
