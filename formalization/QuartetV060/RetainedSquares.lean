import QuartetV060.WeightedCancellation

/-!
# Retained-square expansions `(A.17)` and `(A.18)`

The definitions below retain every row-pair and column index.  Theorems
`r1Abstract_eq_expanded` and `r2Retained_eq_faces` expose, respectively, the
finite expansion of `omega_i omega_j` and all three faces of each neighboring
square.
-/

namespace QuartetV060

open scoped BigOperators

namespace RetainedSquares

variable
    {R C : Type*}
    [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C]

def atomWeight (r : R → C → ℚ) (c : C → ℚ) (i : R) (k : C) : ℚ :=
  r i k * c k

def omega (r : R → C → ℚ) (c : C → ℚ) (i : R) : ℚ :=
  ∑ k, atomWeight r c i k

theorem omega_mul
    (r : R → C → ℚ) (c : C → ℚ) (i j : R) :
    omega r c i * omega r c j =
      ∑ k, ∑ l, atomWeight r c i k * atomWeight r c j l := by
  unfold omega
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro k
  rw [Finset.mul_sum]

/-- The retained right-hand side of the abstract residual identity before
the column weights are expanded. -/
def r1Abstract
    (P : ResidualPartition R)
    (r : R → C → ℚ) (c : C → ℚ)
    (X Y : R → ℚ) : ℚ :=
  (∑ z ∈ P.I, omega r c z.1 * omega r c z.2 * X z.1 ^ 2) +
  ∑ z ∈ P.D,
    omega r c z.1 * omega r c z.2 * (X z.1 + Y z.1) ^ 2

/-- The fully exposed `(A.17)` expression. -/
def r1Expanded
    (P : ResidualPartition R)
    (r : R → C → ℚ) (c : C → ℚ)
    (Xbar Xsame : R → C → ℚ) : ℚ :=
  (∑ z ∈ P.I, ∑ k, ∑ l,
      atomWeight r c z.1 k * atomWeight r c z.2 l *
        Xbar z.1 k ^ 2) +
  ∑ z ∈ P.D, ∑ k, ∑ l,
    atomWeight r c z.1 k * atomWeight r c z.2 l *
      (Xbar z.1 k + Xsame z.1 k) ^ 2

/-- Exact expansion of `omega_i omega_j` followed by the common-sign
side relabeling `(A.16)`. -/
theorem r1Abstract_eq_expanded
    (P : ResidualPartition R)
    (r : R → C → ℚ) (c : C → ℚ)
    (X Y : R → ℚ)
    (Xbar Xsame : R → C → ℚ)
    (hX : ∀ i k, X i ^ 2 = Xbar i k ^ 2)
    (hplus :
      ∀ i k, (X i + Y i) ^ 2 =
        (Xbar i k + Xsame i k) ^ 2) :
    r1Abstract P r c X Y =
      r1Expanded P r c Xbar Xsame := by
  have hI :
      (∑ z ∈ P.I,
          omega r c z.1 * omega r c z.2 * X z.1 ^ 2) =
        ∑ z ∈ P.I, ∑ k, ∑ l,
          atomWeight r c z.1 k * atomWeight r c z.2 l *
            Xbar z.1 k ^ 2 := by
    apply Finset.sum_congr rfl
    intro z _
    calc
      omega r c z.1 * omega r c z.2 * X z.1 ^ 2 =
          (∑ k, ∑ l,
            atomWeight r c z.1 k * atomWeight r c z.2 l) *
              X z.1 ^ 2 := by
                rw [omega_mul]
      _ = ∑ k, ∑ l,
          atomWeight r c z.1 k * atomWeight r c z.2 l *
            X z.1 ^ 2 := by
              rw [Finset.sum_mul]
              apply Fintype.sum_congr
              intro k
              rw [Finset.sum_mul]
      _ = ∑ k, ∑ l,
          atomWeight r c z.1 k * atomWeight r c z.2 l *
            Xbar z.1 k ^ 2 := by
              apply Fintype.sum_congr
              intro k
              apply Fintype.sum_congr
              intro l
              rw [hX z.1 k]
  have hD :
      (∑ z ∈ P.D,
          omega r c z.1 * omega r c z.2 *
            (X z.1 + Y z.1) ^ 2) =
        ∑ z ∈ P.D, ∑ k, ∑ l,
          atomWeight r c z.1 k * atomWeight r c z.2 l *
            (Xbar z.1 k + Xsame z.1 k) ^ 2 := by
    apply Finset.sum_congr rfl
    intro z _
    calc
      omega r c z.1 * omega r c z.2 *
            (X z.1 + Y z.1) ^ 2 =
          (∑ k, ∑ l,
            atomWeight r c z.1 k * atomWeight r c z.2 l) *
              (X z.1 + Y z.1) ^ 2 := by
                rw [omega_mul]
      _ = ∑ k, ∑ l,
          atomWeight r c z.1 k * atomWeight r c z.2 l *
            (X z.1 + Y z.1) ^ 2 := by
              rw [Finset.sum_mul]
              apply Fintype.sum_congr
              intro k
              rw [Finset.sum_mul]
      _ = ∑ k, ∑ l,
          atomWeight r c z.1 k * atomWeight r c z.2 l *
            (Xbar z.1 k + Xsame z.1 k) ^ 2 := by
              apply Fintype.sum_congr
              intro k
              apply Fintype.sum_congr
              intro l
              rw [hplus z.1 k]
  unfold r1Abstract r1Expanded
  rw [hI, hD]

def neighboringU
    (c cbar : C → ℚ)
    (xBarOpp xBarSame : R → C → ℚ)
    (i : R) (k : C) : ℚ :=
  c k * xBarOpp i k - cbar k * xBarSame i k

def neighboringV
    (c cbar : C → ℚ)
    (xOpp xSame : R → C → ℚ)
    (i : R) (k : C) : ℚ :=
  c k * xOpp i k - cbar k * xSame i k

/-- The retained neighboring expression `(A.18)` before expanding either
square. -/
def r2Retained
    (P : ResidualPartition R) (endpointC : Finset C)
    (r : R → C → ℚ) (c cbar : C → ℚ)
    (xBarOpp xBarSame xOpp xSame : R → C → ℚ) : ℚ :=
  (∑ z ∈ P.I, ∑ k ∈ endpointC,
      r z.1 k * r z.2 k *
        neighboringU c cbar xBarOpp xBarSame z.1 k ^ 2) +
  ∑ z ∈ P.D, ∑ k ∈ endpointC,
    r z.1 k * r z.2 k *
      (neighboringU c cbar xBarOpp xBarSame z.1 k +
        neighboringV c cbar xOpp xSame z.1 k) ^ 2

/-- The six explicit first/mixed/second square faces of `(A.18)`. -/
def r2Faces
    (P : ResidualPartition R) (endpointC : Finset C)
    (r : R → C → ℚ) (c cbar : C → ℚ)
    (xBarOpp xBarSame xOpp xSame : R → C → ℚ) : ℚ :=
  (∑ z ∈ P.I, ∑ k ∈ endpointC,
      r z.1 k * r z.2 k *
        (c k ^ 2 * xBarOpp z.1 k ^ 2
         - 2 * c k * cbar k * xBarOpp z.1 k * xBarSame z.1 k
         + cbar k ^ 2 * xBarSame z.1 k ^ 2)) +
  ∑ z ∈ P.D, ∑ k ∈ endpointC,
    r z.1 k * r z.2 k *
      (c k ^ 2 * (xBarOpp z.1 k + xOpp z.1 k) ^ 2
       - 2 * c k * cbar k *
          (xBarOpp z.1 k + xOpp z.1 k) *
          (xBarSame z.1 k + xSame z.1 k)
       + cbar k ^ 2 *
          (xBarSame z.1 k + xSame z.1 k) ^ 2)

theorem r2Retained_eq_faces
    (P : ResidualPartition R) (endpointC : Finset C)
    (r : R → C → ℚ) (c cbar : C → ℚ)
    (xBarOpp xBarSame xOpp xSame : R → C → ℚ) :
    r2Retained P endpointC r c cbar
        xBarOpp xBarSame xOpp xSame =
      r2Faces P endpointC r c cbar
        xBarOpp xBarSame xOpp xSame := by
  unfold r2Retained r2Faces neighboringU neighboringV
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro k _
    ring

end RetainedSquares

end QuartetV060
