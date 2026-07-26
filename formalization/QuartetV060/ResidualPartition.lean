import QuartetV060.BridgeReversal

/-!
# The one-coordinate residual identity

This is the finite algebraic identity used twice in Appendix A: first for
`(A.15a)` and then, for every fixed neighboring column endpoint, for
`(A.15b)`.  The ordered-pair classes `I`, `D`, and `Δ_E` are represented by
actual disjoint finsets, and every passage from a pair sum to an endpoint sum
is proved explicitly.
-/

namespace QuartetV060

open scoped BigOperators

/-- Data for the ordered-pair residual partition.  For an endpoint `i`,
`opposite i` is the whole central side opposite to `i`. -/
structure ResidualPartition (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  endpoint : Finset Ω
  opposite : Ω → Finset Ω
  self_not_mem : ∀ i ∈ endpoint, i ∉ opposite i

namespace ResidualPartition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The complete ordered-pair index set `Ω²`. -/
def allPairs (P : ResidualPartition Ω) : Finset (Ω × Ω) :=
  Finset.univ.product Finset.univ

/-- The paper's class `D = {(i,j) : i ∈ E, j ∈ bar i}`. -/
def D (P : ResidualPartition Ω) : Finset (Ω × Ω) :=
  P.allPairs.filter fun z => z.1 ∈ P.endpoint ∧ z.2 ∈ P.opposite z.1

private def diagonalEmbedding : Ω ↪ Ω × Ω where
  toFun i := (i, i)
  inj' := fun _ _ h => congrArg Prod.fst h

/-- The endpoint diagonal `Δ_E`. -/
def deltaE (P : ResidualPartition Ω) : Finset (Ω × Ω) :=
  P.endpoint.map diagonalEmbedding

/-- The retained class `I = Ω² \ (D ∪ Δ_E)`. -/
def I (P : ResidualPartition Ω) : Finset (Ω × Ω) :=
  P.allPairs \ (P.D ∪ P.deltaE)

/-- The aggregate weight `w_{bar i}`. -/
def oppositeWeight (P : ResidualPartition Ω) (w : Ω → ℚ) (i : Ω) : ℚ :=
  ∑ j ∈ P.opposite i, w j

@[simp] theorem mem_allPairs (P : ResidualPartition Ω) (z : Ω × Ω) :
    z ∈ P.allPairs := by
  simp [allPairs]

@[simp] theorem mem_D_iff (P : ResidualPartition Ω) (z : Ω × Ω) :
    z ∈ P.D ↔ z.1 ∈ P.endpoint ∧ z.2 ∈ P.opposite z.1 := by
  simp [D]

@[simp] theorem mem_deltaE_iff (P : ResidualPartition Ω) (z : Ω × Ω) :
    z ∈ P.deltaE ↔ z.1 ∈ P.endpoint ∧ z.2 = z.1 := by
  constructor
  · intro hz
    rcases Finset.mem_map.mp hz with ⟨i, hi, hiz⟩
    subst z
    exact ⟨hi, rfl⟩
  · rintro ⟨hz, hdiag⟩
    apply Finset.mem_map.mpr
    refine ⟨z.1, hz, ?_⟩
    apply Prod.ext
    · rfl
    · exact hdiag.symm

theorem disjoint_D_deltaE (P : ResidualPartition Ω) :
    Disjoint P.D P.deltaE := by
  rw [Finset.disjoint_left]
  intro z hzD hzDelta
  have hD := (P.mem_D_iff z).mp hzD
  have hDelta := (P.mem_deltaE_iff z).mp hzDelta
  rw [hDelta.2] at hD
  exact P.self_not_mem z.1 hDelta.1 hD.2

theorem disjoint_I_rest (P : ResidualPartition Ω) :
    Disjoint P.I (P.D ∪ P.deltaE) := by
  simpa [I] using
    (Finset.sdiff_disjoint :
      Disjoint (P.allPairs \ (P.D ∪ P.deltaE)) (P.D ∪ P.deltaE))

theorem union_partition (P : ResidualPartition Ω) :
    P.I ∪ (P.D ∪ P.deltaE) = P.allPairs := by
  apply Finset.sdiff_union_of_subset
  intro z _
  exact P.mem_allPairs z

/-- Exact finite partition of any ordered-pair sum into `I`, `D`, and
`Δ_E`. -/
theorem sum_partition (P : ResidualPartition Ω) (F : Ω × Ω → ℚ) :
    (∑ z ∈ P.allPairs, F z) =
      (∑ z ∈ P.I, F z) +
      (∑ z ∈ P.D, F z) +
      ∑ z ∈ P.deltaE, F z := by
  calc
    (∑ z ∈ P.allPairs, F z) =
        ∑ z ∈ P.I ∪ (P.D ∪ P.deltaE), F z := by
          rw [P.union_partition]
    _ = (∑ z ∈ P.I, F z) +
          ∑ z ∈ P.D ∪ P.deltaE, F z := by
          exact Finset.sum_union P.disjoint_I_rest
    _ = (∑ z ∈ P.I, F z) +
          ((∑ z ∈ P.D, F z) + ∑ z ∈ P.deltaE, F z) := by
          rw [Finset.sum_union P.disjoint_D_deltaE]
    _ = (∑ z ∈ P.I, F z) +
          (∑ z ∈ P.D, F z) +
          ∑ z ∈ P.deltaE, F z := by ring

/-- A `D`-sum whose summand depends on the second coordinate only through
its weight collapses to the aggregate coefficient `w_{bar i}`. -/
theorem sum_D_first
    (P : ResidualPartition Ω) (w F : Ω → ℚ) :
    (∑ z ∈ P.D, w z.1 * w z.2 * F z.1) =
      ∑ i ∈ P.endpoint, w i * P.oppositeWeight w i * F i := by
  rw [Finset.sum_finset_product P.D P.endpoint P.opposite]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [oppositeWeight]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  · intro z
    exact P.mem_D_iff z

/-- A diagonal sum is exactly the corresponding endpoint sum. -/
theorem sum_deltaE
    (P : ResidualPartition Ω) (F : Ω × Ω → ℚ) :
    (∑ z ∈ P.deltaE, F z) =
      ∑ i ∈ P.endpoint, F (i, i) := by
  exact Finset.sum_map P.endpoint diagonalEmbedding F

/-- Factorization of a complete ordered-pair sum. -/
theorem sum_allPairs_first
    (P : ResidualPartition Ω) (w F : Ω → ℚ) :
    (∑ z ∈ P.allPairs, w z.1 * w z.2 * F z.1) =
      (∑ i, w i * F i) * ∑ j, w j := by
  rw [Finset.sum_finset_product P.allPairs Finset.univ
      (fun _ : Ω => Finset.univ)]
  · calc
      (∑ i, ∑ j, w i * w j * F i) =
          ∑ i, (w i * F i) * ∑ j, w j := by
            apply Fintype.sum_congr
            intro i
            calc
              (∑ j, w i * w j * F i) =
                  ∑ j, (w i * F i) * w j := by
                    apply Fintype.sum_congr
                    intro j
                    ring
              _ = (w i * F i) * ∑ j, w j := by
                    rw [Finset.mul_sum]
      _ = (∑ i, w i * F i) * ∑ j, w j := by
            rw [Finset.sum_mul]
  · intro z
    simp [allPairs]

/-- Pure endpoint-wise square completion.  The proof is by finite induction,
so no distributivity of summation is left implicit. -/
theorem residual_square_algebra
    (E : Finset Ω)
    (w wbar X Y : Ω → ℚ)
    (Xsq : ℚ) :
    Xsq - (∑ i ∈ E, (w i * X i - wbar i * Y i) ^ 2) =
      Xsq
      - (∑ i ∈ E, w i * wbar i * X i ^ 2)
      - (∑ i ∈ E, w i ^ 2 * X i ^ 2)
      + (∑ i ∈ E, w i * wbar i * (X i + Y i) ^ 2)
      - ∑ i ∈ E, wbar i * (w i + wbar i) * Y i ^ 2 := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert i E hi ih =>
      simp only [Finset.sum_insert, hi, not_false_eq_true]
      nlinarith [ih]

/-- The exact one-coordinate residual identity from the manuscript. -/
theorem exact_residual_identity
    (P : ResidualPartition Ω)
    (w X Y : Ω → ℚ)
    (Xsq : ℚ)
    (hsum : (∑ i, w i) = 1)
    (hXsq : ∀ i, X i ^ 2 = Xsq) :
    Xsq
      - (∑ i ∈ P.endpoint,
          (w i * X i - P.oppositeWeight w i * Y i) ^ 2)
      =
      (∑ z ∈ P.I, w z.1 * w z.2 * X z.1 ^ 2)
      + (∑ z ∈ P.D,
          w z.1 * w z.2 * (X z.1 + Y z.1) ^ 2)
      - ∑ i ∈ P.endpoint,
          P.oppositeWeight w i *
            (w i + P.oppositeWeight w i) * Y i ^ 2 := by
  have htotal :
      (∑ z ∈ P.allPairs, w z.1 * w z.2 * X z.1 ^ 2) = Xsq := by
    rw [P.sum_allPairs_first w (fun i => X i ^ 2)]
    have hfirst : (∑ i, w i * X i ^ 2) = Xsq := by
      calc
        (∑ i, w i * X i ^ 2) = ∑ i, w i * Xsq := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hXsq i]
        _ = (∑ i, w i) * Xsq := by rw [Finset.sum_mul]
        _ = Xsq := by rw [hsum]; ring
    rw [hfirst, hsum]
    ring
  have hpart := P.sum_partition
    (fun z => w z.1 * w z.2 * X z.1 ^ 2)
  have hI :
      (∑ z ∈ P.I, w z.1 * w z.2 * X z.1 ^ 2) =
        Xsq
        - (∑ i ∈ P.endpoint,
            w i * P.oppositeWeight w i * X i ^ 2)
        - (∑ i ∈ P.endpoint, w i ^ 2 * X i ^ 2) := by
    rw [P.sum_D_first w (fun i => X i ^ 2)] at hpart
    rw [P.sum_deltaE
      (fun z => w z.1 * w z.2 * X z.1 ^ 2)] at hpart
    simp only at hpart
    have hdiag :
        (∑ i ∈ P.endpoint, w i * w i * X i ^ 2) =
          ∑ i ∈ P.endpoint, w i ^ 2 * X i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hdiag] at hpart
    rw [htotal] at hpart
    linarith
  rw [hI]
  rw [P.sum_D_first w (fun i => (X i + Y i) ^ 2)]
  exact residual_square_algebra P.endpoint w
    (fun i => P.oppositeWeight w i) X Y Xsq

end ResidualPartition

end QuartetV060
