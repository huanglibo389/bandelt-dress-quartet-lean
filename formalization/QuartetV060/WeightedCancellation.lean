import QuartetV060.ResidualPartition

/-!
# Weighted centered cancellation `(A.14a)`

The manuscript first groups the atomwise side-reversal weights over the two
central sides and then observes that the extra centered term is common to two
rows of a determinant.  This file proves both stages.
-/

namespace QuartetV060

open scoped BigOperators

/-- A chosen side `S` of a two-side partition; `B` is its complement. -/
structure TwoSide (C : Type*) [Fintype C] [DecidableEq C] where
  S : Finset C

namespace TwoSide

variable {C : Type*} [Fintype C] [DecidableEq C]

def B (P : TwoSide C) : Finset C :=
  Finset.univ \ P.S

theorem disjoint_SB (P : TwoSide C) :
    Disjoint P.S P.B := by
  rw [Finset.disjoint_left]
  simp [B]

theorem union_SB (P : TwoSide C) :
    P.S ∪ P.B = Finset.univ := by
  ext p
  by_cases hp : p ∈ P.S <;> simp [B, hp]

def oppositeBlock (P : TwoSide C) (p : C) : Finset C :=
  if p ∈ P.S then P.B else P.S

@[simp] theorem oppositeBlock_of_mem_S
    (P : TwoSide C) {p : C} (hp : p ∈ P.S) :
    P.oppositeBlock p = P.B := by
  simp [oppositeBlock, hp]

@[simp] theorem oppositeBlock_of_mem_B
    (P : TwoSide C) {p : C} (hp : p ∈ P.B) :
    P.oppositeBlock p = P.S := by
  have hnot : p ∉ P.S := by
    simpa [B] using hp
  simp [oppositeBlock, hnot]

def blockSum (v : C → ℚ) (U : Finset C) : ℚ :=
  ∑ p ∈ U, v p

def total (v : C → ℚ) : ℚ :=
  ∑ p, v p

def centeredBlock
    (P : TwoSide C) (c a : C → ℚ) (U : Finset C) : ℚ :=
  blockSum a U - total a * blockSum c U

def symmetricCoefficient
    (P : TwoSide C) (c a : C → ℚ) (p : C) : ℚ :=
  (1 / 2 : ℚ) *
    (a p / c p +
      blockSum a (P.oppositeBlock p) /
        blockSum c (P.oppositeBlock p))

def weightedAverage
    (P : TwoSide C) (c a : C → ℚ) : ℚ :=
  ∑ p, c p * P.symmetricCoefficient c a p

def theta (P : TwoSide C) (c : C → ℚ) : ℚ :=
  (1 / 2 : ℚ) *
    (blockSum c P.S / blockSum c P.B -
      blockSum c P.B / blockSum c P.S)

theorem total_eq_sum_blocks (P : TwoSide C) (v : C → ℚ) :
    total v = blockSum v P.S + blockSum v P.B := by
  unfold total blockSum
  rw [← Finset.sum_union P.disjoint_SB]
  rw [P.union_SB]

/-- The atomwise definition of the weighted coefficient, grouped over the
two central sides. -/
theorem weightedAverage_eq_grouped
    (P : TwoSide C) (c a : C → ℚ)
    (hc : ∀ p, c p ≠ 0)
    (hcS : blockSum c P.S ≠ 0)
    (hcB : blockSum c P.B ≠ 0) :
    P.weightedAverage c a =
      (1 / 2 : ℚ) * total a +
      (1 / 2 : ℚ) *
        (blockSum c P.S / blockSum c P.B * blockSum a P.B +
         blockSum c P.B / blockSum c P.S * blockSum a P.S) := by
  have hS :
      (∑ p ∈ P.S, c p * P.symmetricCoefficient c a p) =
        (1 / 2 : ℚ) * blockSum a P.S +
        (1 / 2 : ℚ) *
          (blockSum c P.S / blockSum c P.B * blockSum a P.B) := by
    calc
      (∑ p ∈ P.S, c p * P.symmetricCoefficient c a p) =
          ∑ p ∈ P.S,
            ((1 / 2 : ℚ) * a p +
              (1 / 2 : ℚ) *
                (c p / blockSum c P.B * blockSum a P.B)) := by
            apply Finset.sum_congr rfl
            intro p hp
            unfold symmetricCoefficient
            rw [P.oppositeBlock_of_mem_S hp]
            field_simp [hc p, hcB]
      _ = (1 / 2 : ℚ) * blockSum a P.S +
          (1 / 2 : ℚ) *
            (blockSum c P.S / blockSum c P.B * blockSum a P.B) := by
            rw [Finset.sum_add_distrib]
            have hfirst :
                (∑ p ∈ P.S, (1 / 2 : ℚ) * a p) =
                  (1 / 2 : ℚ) * blockSum a P.S := by
              unfold blockSum
              rw [Finset.mul_sum]
            have hsecond :
                (∑ p ∈ P.S,
                    (1 / 2 : ℚ) *
                      (c p / blockSum c P.B * blockSum a P.B)) =
                  (1 / 2 : ℚ) *
                    (blockSum c P.S / blockSum c P.B *
                      blockSum a P.B) := by
              rw [← Finset.mul_sum]
              congr 1
              rw [← Finset.sum_mul]
              rw [← Finset.sum_div]
              rfl
            rw [hfirst, hsecond]
  have hB :
      (∑ p ∈ P.B, c p * P.symmetricCoefficient c a p) =
        (1 / 2 : ℚ) * blockSum a P.B +
        (1 / 2 : ℚ) *
          (blockSum c P.B / blockSum c P.S * blockSum a P.S) := by
    calc
      (∑ p ∈ P.B, c p * P.symmetricCoefficient c a p) =
          ∑ p ∈ P.B,
            ((1 / 2 : ℚ) * a p +
              (1 / 2 : ℚ) *
                (c p / blockSum c P.S * blockSum a P.S)) := by
            apply Finset.sum_congr rfl
            intro p hp
            unfold symmetricCoefficient
            rw [P.oppositeBlock_of_mem_B hp]
            field_simp [hc p, hcS]
      _ = (1 / 2 : ℚ) * blockSum a P.B +
          (1 / 2 : ℚ) *
            (blockSum c P.B / blockSum c P.S * blockSum a P.S) := by
            rw [Finset.sum_add_distrib]
            have hfirst :
                (∑ p ∈ P.B, (1 / 2 : ℚ) * a p) =
                  (1 / 2 : ℚ) * blockSum a P.B := by
              unfold blockSum
              rw [Finset.mul_sum]
            have hsecond :
                (∑ p ∈ P.B,
                    (1 / 2 : ℚ) *
                      (c p / blockSum c P.S * blockSum a P.S)) =
                  (1 / 2 : ℚ) *
                    (blockSum c P.B / blockSum c P.S *
                      blockSum a P.S) := by
              rw [← Finset.mul_sum]
              congr 1
              rw [← Finset.sum_mul]
              rw [← Finset.sum_div]
              rfl
            rw [hfirst, hsecond]
  unfold weightedAverage
  rw [← P.union_SB]
  rw [Finset.sum_union P.disjoint_SB]
  rw [hS, hB, P.total_eq_sum_blocks a]
  ring

/-- The grouped weighted coefficient differs from the ordinary row mass by
one scalar multiple of the centered mass on side `B`. -/
theorem weightedAverage_eq_total_add_theta
    (P : TwoSide C) (c a : C → ℚ)
    (hc : ∀ p, c p ≠ 0)
    (hcS : blockSum c P.S ≠ 0)
    (hcB : blockSum c P.B ≠ 0)
    (hctotal : total c = 1) :
    P.weightedAverage c a =
      total a + P.theta c * P.centeredBlock c a P.B := by
  rw [P.weightedAverage_eq_grouped c a hc hcS hcB]
  have hcpart := P.total_eq_sum_blocks c
  have hapart := P.total_eq_sum_blocks a
  have hcS_expr :
      blockSum c P.S = 1 - blockSum c P.B := by
    rw [hctotal] at hcpart
    linarith
  have hcS_expr_ne : 1 - blockSum c P.B ≠ 0 := by
    rw [← hcS_expr]
    exact hcS
  unfold theta centeredBlock
  rw [hapart, hcS_expr]
  field_simp [hcS_expr_ne, hcB]
  ring

/-- The common centered correction cancels from a two-row determinant. -/
theorem determinant_cancellation
    (rR rR' xR xR' θ : ℚ) :
    (rR + θ * xR) * xR' - (rR' + θ * xR') * xR =
      rR * xR' - rR' * xR := by
  ring

/-- `(A.14a)` before squaring: apply the previous theorem to any two row
blocks. -/
theorem weighted_determinant_cancellation
    (P : TwoSide C) (c aR aR' : C → ℚ)
    (hc : ∀ p, c p ≠ 0)
    (hcS : blockSum c P.S ≠ 0)
    (hcB : blockSum c P.B ≠ 0)
    (hctotal : total c = 1) :
    P.weightedAverage c aR * P.centeredBlock c aR' P.B -
        P.weightedAverage c aR' * P.centeredBlock c aR P.B =
      total aR * P.centeredBlock c aR' P.B -
        total aR' * P.centeredBlock c aR P.B := by
  rw [P.weightedAverage_eq_total_add_theta c aR hc hcS hcB hctotal]
  rw [P.weightedAverage_eq_total_add_theta c aR' hc hcS hcB hctotal]
  exact determinant_cancellation _ _ _ _ _

theorem weighted_determinant_square_cancellation
    (P : TwoSide C) (c aR aR' : C → ℚ)
    (hc : ∀ p, c p ≠ 0)
    (hcS : blockSum c P.S ≠ 0)
    (hcB : blockSum c P.B ≠ 0)
    (hctotal : total c = 1) :
    (P.weightedAverage c aR * P.centeredBlock c aR' P.B -
        P.weightedAverage c aR' * P.centeredBlock c aR P.B) ^ 2 =
      (total aR * P.centeredBlock c aR' P.B -
        total aR' * P.centeredBlock c aR P.B) ^ 2 := by
  rw [P.weighted_determinant_cancellation c aR aR'
    hc hcS hcB hctotal]

/-- Atomwise form of the same cancellation.  For one selected column atom
`p`, the two symmetric coefficients and the two centered neighboring forms
collapse exactly to the raw `2 x 2` determinant of the selected and opposite
row blocks.  This is the algebraic core of the corrected/corrected entry
level. -/
theorem symmetric_neighboring_determinant_cancellation
    (P : TwoSide C) (c aR aR' : C → ℚ) (p : C)
    (hcp : c p ≠ 0)
    (hcbar : blockSum c (P.oppositeBlock p) ≠ 0) :
    P.symmetricCoefficient c aR p *
          (c p * P.centeredBlock c aR' (P.oppositeBlock p) -
            blockSum c (P.oppositeBlock p) *
              P.centeredBlock c aR' {p}) -
        P.symmetricCoefficient c aR' p *
          (c p * P.centeredBlock c aR (P.oppositeBlock p) -
            blockSum c (P.oppositeBlock p) *
              P.centeredBlock c aR {p}) =
      aR p * blockSum aR' (P.oppositeBlock p) -
        blockSum aR (P.oppositeBlock p) * aR' p := by
  have hcb :
      (∑ q ∈ P.oppositeBlock p, c q) ≠ 0 := by
    simpa [blockSum] using hcbar
  unfold symmetricCoefficient centeredBlock
  simp only [blockSum, Finset.sum_singleton]
  field_simp [hcp, hcb]
  ring

end TwoSide

end QuartetV060
