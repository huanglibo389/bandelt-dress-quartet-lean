import QuartetV060.PackageLedger

/-!
# Blockwise first-face settlement `(A.30b)` and `(A.29g)`

The signed residue `A(u)-p(u)` is not asserted to be nonnegative pointwise.
Its discrepancy from `Psi(u)/4` is a centered block term.  This file proves
that the discrepancy sums to zero on one same-side block and that multiplying
by the common representative square preserves the identity.
-/

namespace QuartetV060

open scoped BigOperators

namespace BlockwiseLedger

noncomputable section

variable
    {C : Type*}
    [Fintype C] [DecidableEq C]

def blockSum (S : Finset C) (f : C → ℝ) : ℝ :=
  ∑ u ∈ S, f u

/-- The pointwise discrepancy in Step 3 of the manuscript. -/
def discrepancy
    (S : Finset C)
    (c aJ : C → ℝ)
    (aiOpp : ℝ)
    (u : C) : ℝ :=
  aiOpp *
    (c u / blockSum S c * blockSum S aJ - aJ u)

/-- The discrepancy is centered on its same-side block. -/
theorem sum_discrepancy_eq_zero
    (S : Finset C) (c aJ : C → ℝ) (aiOpp : ℝ)
    (hcS : blockSum S c ≠ 0) :
    (∑ u ∈ S, discrepancy S c aJ aiOpp u) = 0 := by
  have hcS' : (∑ v ∈ S, c v) ≠ 0 := by
    simpa [blockSum] using hcS
  unfold discrepancy blockSum
  calc
    (∑ u ∈ S,
        aiOpp *
          (c u / (∑ v ∈ S, c v) * (∑ v ∈ S, aJ v) - aJ u)) =
        aiOpp *
          ((∑ u ∈ S, c u / (∑ v ∈ S, c v) *
              (∑ v ∈ S, aJ v)) -
            ∑ u ∈ S, aJ u) := by
              rw [← Finset.mul_sum]
              congr 1
              rw [Finset.sum_sub_distrib]
    _ = 0 := by
      have hratio :
          (∑ u ∈ S, c u / (∑ v ∈ S, c v) *
              (∑ v ∈ S, aJ v)) =
            ∑ v ∈ S, aJ v := by
        rw [← Finset.sum_mul]
        rw [← Finset.sum_div]
        rw [div_self hcS']
        ring
      rw [hratio]
      ring

/-- Summing the two pointwise cases (endpoint and residual) gives exactly
the block coefficient identity `(A.30b)`. -/
theorem blockwise_first_face
    (S : Finset C)
    (c aJ A p Psi : C → ℝ)
    (aiOpp : ℝ)
    (hcS : blockSum S c ≠ 0)
    (hpoint :
      ∀ u ∈ S,
        4 * (A u - p u) =
          Psi u + discrepancy S c aJ aiOpp u) :
    4 * (blockSum S A - blockSum S p) =
      blockSum S Psi := by
  have hsum :
      (∑ u ∈ S, 4 * (A u - p u)) =
        ∑ u ∈ S, (Psi u + discrepancy S c aJ aiOpp u) := by
    apply Finset.sum_congr rfl
    intro u hu
    exact hpoint u hu
  rw [Finset.sum_add_distrib] at hsum
  rw [sum_discrepancy_eq_zero S c aJ aiOpp hcS] at hsum
  unfold blockSum
  rw [← Finset.mul_sum] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  linarith

/-- Every index in a same-side block carries the same representative square,
so `(A.30b)` can be multiplied by that square without changing its
coefficient bookkeeping. -/
theorem blockwise_first_face_with_square
    (S : Finset C)
    (c aJ A p Psi Z : C → ℝ)
    (aiOpp ZS : ℝ)
    (hcS : blockSum S c ≠ 0)
    (hpoint :
      ∀ u ∈ S,
        4 * (A u - p u) =
          Psi u + discrepancy S c aJ aiOpp u)
    (hZ : ∀ u ∈ S, Z u ^ 2 = ZS ^ 2) :
    2 * (∑ u ∈ S, (A u - p u) * Z u ^ 2) =
      (1 / 2 : ℝ) * ∑ u ∈ S, Psi u * Z u ^ 2 := by
  have hblock :=
    blockwise_first_face S c aJ A p Psi aiOpp hcS hpoint
  have hleft :
      (∑ u ∈ S, (A u - p u) * Z u ^ 2) =
        (blockSum S A - blockSum S p) * ZS ^ 2 := by
    calc
      (∑ u ∈ S, (A u - p u) * Z u ^ 2) =
          ∑ u ∈ S, (A u - p u) * ZS ^ 2 := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hZ u hu]
      _ = (∑ u ∈ S, (A u - p u)) * ZS ^ 2 := by
            rw [Finset.sum_mul]
      _ = (blockSum S A - blockSum S p) * ZS ^ 2 := by
            unfold blockSum
            rw [Finset.sum_sub_distrib]
  have hright :
      (∑ u ∈ S, Psi u * Z u ^ 2) =
        blockSum S Psi * ZS ^ 2 := by
    calc
      (∑ u ∈ S, Psi u * Z u ^ 2) =
          ∑ u ∈ S, Psi u * ZS ^ 2 := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hZ u hu]
      _ = blockSum S Psi * ZS ^ 2 := by
            unfold blockSum
            rw [Finset.sum_mul]
  rw [hleft, hright]
  nlinarith

/-- The two same-side blocks may now be joined without hiding a summation
range. -/
theorem two_blocks_with_square
    (S T : Finset C)
    (hdisj : Disjoint S T)
    (c aJ A p Psi Z : C → ℝ)
    (aiOppS aiOppT ZS ZT : ℝ)
    (hcS : blockSum S c ≠ 0)
    (hcT : blockSum T c ≠ 0)
    (hpointS :
      ∀ u ∈ S,
        4 * (A u - p u) =
          Psi u + discrepancy S c aJ aiOppS u)
    (hpointT :
      ∀ u ∈ T,
        4 * (A u - p u) =
          Psi u + discrepancy T c aJ aiOppT u)
    (hZS : ∀ u ∈ S, Z u ^ 2 = ZS ^ 2)
    (hZT : ∀ u ∈ T, Z u ^ 2 = ZT ^ 2) :
    2 * (∑ u ∈ S ∪ T, (A u - p u) * Z u ^ 2) =
      (1 / 2 : ℝ) * ∑ u ∈ S ∪ T, Psi u * Z u ^ 2 := by
  have hS := blockwise_first_face_with_square
    S c aJ A p Psi Z aiOppS ZS hcS hpointS hZS
  have hT := blockwise_first_face_with_square
    T c aJ A p Psi Z aiOppT ZT hcT hpointT hZT
  rw [Finset.sum_union hdisj, Finset.sum_union hdisj]
  linarith

end

end BlockwiseLedger

end QuartetV060
