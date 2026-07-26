import QuartetV060.FourSector

/-!
# Local row-column masses and the symmetric coefficient

This file formalizes the paper's local notation `r_i`, `c_k`, `a_{i,k}`,
`x_{i,k}`, all finite block aggregates, and the domination expansion obtained
from the symmetric coefficient `r_i^k`.
-/

namespace QuartetV060

open scoped BigOperators

/-- A nonnegative normalized joint mass table on finite row and column atom
types. -/
structure JointMass (R C : Type*) [Fintype R] [Fintype C] where
  a : R → C → ℚ
  nonneg : ∀ i k, 0 ≤ a i k
  total : ∑ i, ∑ k, a i k = 1

namespace JointMass

variable {R C : Type*} [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]

def rowMass (J : JointMass R C) (i : R) : ℚ :=
  ∑ k, J.a i k

def colMass (J : JointMass R C) (k : C) : ℚ :=
  ∑ i, J.a i k

def centered (J : JointMass R C) (i : R) (k : C) : ℚ :=
  J.a i k - J.rowMass i * J.colMass k

theorem rowMass_nonneg (J : JointMass R C) (i : R) :
    0 ≤ J.rowMass i := by
  unfold rowMass
  exact Finset.sum_nonneg fun k hk => J.nonneg i k

theorem colMass_nonneg (J : JointMass R C) (k : C) :
    0 ≤ J.colMass k := by
  unfold colMass
  exact Finset.sum_nonneg fun i hi => J.nonneg i k

theorem sum_rowMass (J : JointMass R C) :
    ∑ i, J.rowMass i = 1 := by
  simpa [rowMass] using J.total

theorem sum_colMass (J : JointMass R C) :
    ∑ k, J.colMass k = 1 := by
  unfold colMass
  rw [Finset.sum_comm]
  exact J.total

theorem sum_centered_col (J : JointMass R C) (k : C) :
    ∑ i, J.centered i k = 0 := by
  calc
    ∑ i, J.centered i k =
        (∑ i, J.a i k) - ∑ i, J.rowMass i * J.colMass k := by
          simp [centered, Finset.sum_sub_distrib]
    _ = J.colMass k - (∑ i, J.rowMass i) * J.colMass k := by
          simp [colMass, Finset.sum_mul]
    _ = 0 := by rw [J.sum_rowMass]; ring

theorem sum_centered_row (J : JointMass R C) (i : R) :
    ∑ k, J.centered i k = 0 := by
  calc
    ∑ k, J.centered i k =
        (∑ k, J.a i k) - ∑ k, J.rowMass i * J.colMass k := by
          simp [centered, Finset.sum_sub_distrib]
    _ = J.rowMass i - J.rowMass i * (∑ k, J.colMass k) := by
          simp [rowMass, Finset.mul_sum]
    _ = 0 := by rw [J.sum_colMass]; ring

def colBlockMass (J : JointMass R C) (U : Finset C) : ℚ :=
  ∑ k ∈ U, J.colMass k

def mixedBlockMass (J : JointMass R C) (i : R) (U : Finset C) : ℚ :=
  ∑ k ∈ U, J.a i k

def centeredBlockMass (J : JointMass R C) (i : R) (U : Finset C) : ℚ :=
  ∑ k ∈ U, J.centered i k

/-- A centered rectangle permits the row index to be an aggregate block,
as in `x_{bar i,A}` in Appendix A. -/
def centeredRectangleMass
    (J : JointMass R C) (V : Finset R) (U : Finset C) : ℚ :=
  ∑ i ∈ V, ∑ k ∈ U, J.centered i k

theorem colBlockMass_nonneg (J : JointMass R C) (U : Finset C) :
    0 ≤ J.colBlockMass U := by
  unfold colBlockMass
  exact Finset.sum_nonneg fun k hk => J.colMass_nonneg k

theorem mixedBlockMass_nonneg
    (J : JointMass R C) (i : R) (U : Finset C) :
    0 ≤ J.mixedBlockMass i U := by
  unfold mixedBlockMass
  exact Finset.sum_nonneg fun k hk => J.nonneg i k

theorem centeredBlockMass_eq
    (J : JointMass R C) (i : R) (U : Finset C) :
    J.centeredBlockMass i U =
      J.mixedBlockMass i U - J.rowMass i * J.colBlockMass U := by
  simp [centeredBlockMass, centered, mixedBlockMass, colBlockMass,
    Finset.sum_sub_distrib, Finset.mul_sum]

theorem colBlockMass_same_add_opposite
    (J : JointMass R C) (F : FourSector C) (u : C) :
    J.colBlockMass (F.sameSideBlock u) +
        J.colBlockMass (F.oppositeSideBlock u) = 1 := by
  unfold colBlockMass
  rw [← Finset.sum_union (F.sameSideBlock_disjoint_opposite u)]
  rw [F.sameSideBlock_union_opposite u]
  simpa using J.sum_colMass

theorem centeredRectangleMass_same_add_opposite
    (J : JointMass R C) (F : FourSector C)
    (V : Finset R) (u : C) :
    J.centeredRectangleMass V (F.sameSideBlock u) +
        J.centeredRectangleMass V (F.oppositeSideBlock u) = 0 := by
  unfold centeredRectangleMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.sum_union (F.sameSideBlock_disjoint_opposite u)]
  rw [F.sameSideBlock_union_opposite u]
  exact J.sum_centered_row i

theorem centeredRectangleMass_same_eq_neg_opposite
    (J : JointMass R C) (F : FourSector C)
    (V : Finset R) (u : C) :
    J.centeredRectangleMass V (F.sameSideBlock u) =
      -J.centeredRectangleMass V (F.oppositeSideBlock u) := by
  linarith [J.centeredRectangleMass_same_add_opposite F V u]

/-- First equality in `(A.16)`: complementary central sides produce the same
square for every aggregate row block. -/
theorem centeredRectangleMass_side_square
    (J : JointMass R C) (F : FourSector C)
    (V : Finset R) (u : C) :
    J.centeredRectangleMass V (F.sameSideBlock u) ^ 2 =
      J.centeredRectangleMass V (F.oppositeSideBlock u) ^ 2 := by
  rw [J.centeredRectangleMass_same_eq_neg_opposite F V u]
  ring

/-- Second equality in `(A.16)`: if two row blocks are placed in the same
plus form, reversing the column side changes both by the same sign. -/
theorem centeredRectangleMass_plus_square
    (J : JointMass R C) (F : FourSector C)
    (V W : Finset R) (u : C) :
    (J.centeredRectangleMass V (F.sameSideBlock u) +
        J.centeredRectangleMass W (F.sameSideBlock u)) ^ 2 =
      (J.centeredRectangleMass V (F.oppositeSideBlock u) +
        J.centeredRectangleMass W (F.oppositeSideBlock u)) ^ 2 := by
  rw [J.centeredRectangleMass_same_eq_neg_opposite F V u]
  rw [J.centeredRectangleMass_same_eq_neg_opposite F W u]
  ring

/-- The paper's symmetric coefficient
`r_i^k = 1/2 (a_{i,k}/c_k + a_{i,bar k}/c_{bar k})`. -/
def symmetricRowCoefficient
    (J : JointMass R C) (F : FourSector C) (i : R) (k : C) : ℚ :=
  (1 / 2 : ℚ) *
    (J.a i k / J.colMass k +
      J.mixedBlockMass i (F.oppositeSideBlock k) /
        J.colBlockMass (F.oppositeSideBlock k))

theorem sum_symmetricRowCoefficient
    (J : JointMass R C) (F : FourSector C) (k : C)
    (hk : J.colMass k ≠ 0)
    (hbar : J.colBlockMass (F.oppositeSideBlock k) ≠ 0) :
    ∑ i, J.symmetricRowCoefficient F i k = 1 := by
  unfold symmetricRowCoefficient
  rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_div]
  rw [← Finset.sum_div]
  have hcol : ∑ i, J.a i k = J.colMass k := rfl
  have hmix :
      ∑ i, J.mixedBlockMass i (F.oppositeSideBlock k) =
        J.colBlockMass (F.oppositeSideBlock k) := by
    unfold mixedBlockMass colBlockMass colMass
    rw [Finset.sum_comm]
  rw [hcol, hmix]
  field_simp
  norm_num

/-- Exact four-term expansion in the paper's domination lemma. -/
theorem domination_expansion
    (J : JointMass R C) (F : FourSector C)
    (i j : R) (k l : C)
    (hk : J.colMass k ≠ 0)
    (hl : J.colMass l ≠ 0)
    (hbark : J.colBlockMass (F.oppositeSideBlock k) ≠ 0)
    (hbarl : J.colBlockMass (F.oppositeSideBlock l) ≠ 0) :
    4 * J.colMass k * J.colMass l *
        J.symmetricRowCoefficient F i k *
        J.symmetricRowCoefficient F j l =
      J.a i k * J.a j l +
      J.colMass l / J.colBlockMass (F.oppositeSideBlock l) *
        J.a i k *
        J.mixedBlockMass j (F.oppositeSideBlock l) +
      J.colMass k / J.colBlockMass (F.oppositeSideBlock k) *
        J.mixedBlockMass i (F.oppositeSideBlock k) *
        J.a j l +
      (J.colMass k * J.colMass l) /
          (J.colBlockMass (F.oppositeSideBlock k) *
            J.colBlockMass (F.oppositeSideBlock l)) *
        J.mixedBlockMass i (F.oppositeSideBlock k) *
        J.mixedBlockMass j (F.oppositeSideBlock l) := by
  unfold symmetricRowCoefficient
  field_simp [hk, hl, hbark, hbarl]
  ring

/-- The inequality part of the domination lemma. -/
theorem domination_inequality
    (J : JointMass R C) (F : FourSector C)
    (i j : R) (k l : C)
    (hk : 0 < J.colMass k)
    (hl : 0 < J.colMass l)
    (hbark : 0 < J.colBlockMass (F.oppositeSideBlock k))
    (hbarl : 0 < J.colBlockMass (F.oppositeSideBlock l)) :
    (J.colMass k * J.colMass l) /
          (J.colBlockMass (F.oppositeSideBlock k) *
            J.colBlockMass (F.oppositeSideBlock l)) *
        J.mixedBlockMass i (F.oppositeSideBlock k) *
        J.mixedBlockMass j (F.oppositeSideBlock l)
      ≤
    4 * J.colMass k * J.colMass l *
        J.symmetricRowCoefficient F i k *
        J.symmetricRowCoefficient F j l := by
  rw [J.domination_expansion F i j k l hk.ne' hl.ne' hbark.ne' hbarl.ne']
  have haik : 0 ≤ J.a i k := J.nonneg i k
  have hajl : 0 ≤ J.a j l := J.nonneg j l
  have haibar :
      0 ≤ J.mixedBlockMass i (F.oppositeSideBlock k) :=
    J.mixedBlockMass_nonneg i _
  have hajbar :
      0 ≤ J.mixedBlockMass j (F.oppositeSideBlock l) :=
    J.mixedBlockMass_nonneg j _
  have hratioK :
      0 ≤ J.colMass k / J.colBlockMass (F.oppositeSideBlock k) := by
    positivity
  have hratioL :
      0 ≤ J.colMass l / J.colBlockMass (F.oppositeSideBlock l) := by
    positivity
  nlinarith [mul_nonneg haik hajl,
    mul_nonneg (mul_nonneg hratioL haik) hajbar,
    mul_nonneg (mul_nonneg hratioK haibar) hajl]

end JointMass

end QuartetV060
