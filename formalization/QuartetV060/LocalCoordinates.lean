import QuartetV060.ConcreteBridgeLedger
import QuartetV060.RetainedSquares

/-!
# Concrete local coordinates in a principal chart

This file defines the four centered coordinates

* `xBarOpp = x_{bar i,bar k}`,
* `xBarSame = x_{bar i,k}`,
* `xOpp = x_{i,bar k}`,
* `xSame = x_{i,k}`,

directly from a joint mass table and two four-sector structures.  It also
proves the sign-reversal square identities used in `(A.16)--(A.18)`.  No
representative side is identified by convention: every equality follows from
the vanishing row and column sums of the centered table.
-/

namespace QuartetV060

open scoped BigOperators

namespace FourSector

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem sameSideBlock_eq_of_sameSide
    (F : FourSector Ω) {u v : Ω}
    (h : F.sameSide u v) :
    F.sameSideBlock u = F.sameSideBlock v := by
  ext x
  simp only [mem_sameSideBlock_iff]
  unfold sameSide at h ⊢
  rw [h]

theorem oppositeSideBlock_eq_of_sameSide
    (F : FourSector Ω) {u v : Ω}
    (h : F.sameSide u v) :
    F.oppositeSideBlock u = F.oppositeSideBlock v := by
  ext x
  simp only [mem_oppositeSideBlock_iff]
  unfold sameSide at h ⊢
  rw [h]

theorem oppositeSideBlock_eq_sameSideBlock_of_not_sameSide
    (F : FourSector Ω) {u v : Ω}
    (h : ¬F.sameSide u v) :
    F.oppositeSideBlock u = F.sameSideBlock v := by
  ext x
  simp only [mem_oppositeSideBlock_iff, mem_sameSideBlock_iff]
  cases hu : F.sector u <;>
    cases hv : F.sector v <;>
      cases hx : F.sector x <;>
        simp_all [sameSide, isLeftSector]

end FourSector

namespace JointMass

variable
    {R C : Type*}
    [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C]

/-- The row-coordinate analogue of
`centeredRectangleMass_same_add_opposite`. -/
theorem centeredRectangleMass_row_same_add_opposite
    (J : JointMass R C) (F : FourSector R)
    (u : R) (U : Finset C) :
    J.centeredRectangleMass (F.sameSideBlock u) U +
        J.centeredRectangleMass (F.oppositeSideBlock u) U = 0 := by
  unfold centeredRectangleMass
  rw [← Finset.sum_union (F.sameSideBlock_disjoint_opposite u)]
  rw [F.sameSideBlock_union_opposite u]
  change (∑ i : R, ∑ k ∈ U, J.centered i k) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  exact J.sum_centered_col k

theorem centeredRectangleMass_row_same_eq_neg_opposite
    (J : JointMass R C) (F : FourSector R)
    (u : R) (U : Finset C) :
    J.centeredRectangleMass (F.sameSideBlock u) U =
      -J.centeredRectangleMass (F.oppositeSideBlock u) U := by
  linarith [J.centeredRectangleMass_row_same_add_opposite F u U]

theorem centeredRectangleMass_row_side_square
    (J : JointMass R C) (F : FourSector R)
    (u : R) (U : Finset C) :
    J.centeredRectangleMass (F.sameSideBlock u) U ^ 2 =
      J.centeredRectangleMass (F.oppositeSideBlock u) U ^ 2 := by
  rw [J.centeredRectangleMass_row_same_eq_neg_opposite F u U]
  ring

/-- The square of a centered rectangle on a complete column side is
independent of which atom is used to name that side. -/
theorem centeredRectangleMass_col_opposite_square_independent
    (J : JointMass R C) (F : FourSector C)
    (V : Finset R) (u v : C) :
    J.centeredRectangleMass V (F.oppositeSideBlock u) ^ 2 =
      J.centeredRectangleMass V (F.oppositeSideBlock v) ^ 2 := by
  by_cases h : F.sameSide u v
  · rw [F.oppositeSideBlock_eq_of_sameSide h]
  · rw [F.oppositeSideBlock_eq_sameSideBlock_of_not_sameSide h]
    exact J.centeredRectangleMass_side_square F V v

/-- The square of a centered rectangle on a complete row side is independent
of which row atom names that side. -/
theorem centeredRectangleMass_row_opposite_square_independent
    (J : JointMass R C) (F : FourSector R)
    (u v : R) (U : Finset C) :
    J.centeredRectangleMass (F.oppositeSideBlock u) U ^ 2 =
      J.centeredRectangleMass (F.oppositeSideBlock v) U ^ 2 := by
  by_cases h : F.sameSide u v
  · rw [F.oppositeSideBlock_eq_of_sameSide h]
  · rw [F.oppositeSideBlock_eq_sameSideBlock_of_not_sameSide h]
    exact J.centeredRectangleMass_row_side_square F v U

/-- Reversing a complete column side changes two row-block forms by the same
sign, hence preserves the square of their sum. -/
theorem centeredRectangleMass_col_opposite_plus_square_independent
    (J : JointMass R C) (F : FourSector C)
    (V W : Finset R) (u v : C) :
    (J.centeredRectangleMass V (F.oppositeSideBlock u) +
        J.centeredRectangleMass W (F.oppositeSideBlock u)) ^ 2 =
      (J.centeredRectangleMass V (F.oppositeSideBlock v) +
        J.centeredRectangleMass W (F.oppositeSideBlock v)) ^ 2 := by
  by_cases h : F.sameSide u v
  · rw [F.oppositeSideBlock_eq_of_sameSide h]
  · rw [F.oppositeSideBlock_eq_sameSideBlock_of_not_sameSide h]
    exact J.centeredRectangleMass_plus_square F V W v

/-- A fixed linear combination of two column-block coordinates changes by one
common sign when the complete row side is reversed. -/
theorem centeredRectangleMass_row_linear_square_independent
    (J : JointMass R C) (F : FourSector R)
    (u v : R) (A B : Finset C) (s t : ℚ) :
    (s * J.centeredRectangleMass (F.oppositeSideBlock u) A -
        t * J.centeredRectangleMass (F.oppositeSideBlock u) B) ^ 2 =
      (s * J.centeredRectangleMass (F.oppositeSideBlock v) A -
        t * J.centeredRectangleMass (F.oppositeSideBlock v) B) ^ 2 := by
  by_cases h : F.sameSide u v
  · rw [F.oppositeSideBlock_eq_of_sameSide h]
  · rw [F.oppositeSideBlock_eq_sameSideBlock_of_not_sameSide h]
    rw [J.centeredRectangleMass_row_same_eq_neg_opposite F v A]
    rw [J.centeredRectangleMass_row_same_eq_neg_opposite F v B]
    ring

end JointMass

namespace LocalCoordinates

variable
    {R C : Type*}
    [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C]

def xBarOpp
    (J : JointMass R C) (Fr : FourSector R) (Fc : FourSector C)
    (i : R) (k : C) : ℚ :=
  J.centeredRectangleMass
    (Fr.oppositeSideBlock i) (Fc.oppositeSideBlock k)

def xBarSame
    (J : JointMass R C) (Fr : FourSector R)
    (i : R) (k : C) : ℚ :=
  J.centeredRectangleMass (Fr.oppositeSideBlock i) {k}

def xOpp
    (J : JointMass R C) (Fc : FourSector C)
    (i : R) (k : C) : ℚ :=
  J.centeredBlockMass i (Fc.oppositeSideBlock k)

def xSame
    (J : JointMass R C) (i : R) (k : C) : ℚ :=
  J.centered i k

theorem xOpp_eq_rectangle
    (J : JointMass R C) (Fc : FourSector C)
    (i : R) (k : C) :
    xOpp J Fc i k =
      J.centeredRectangleMass {i} (Fc.oppositeSideBlock k) := by
  simp [xOpp, JointMass.centeredBlockMass,
    JointMass.centeredRectangleMass]

theorem xSame_eq_rectangle
    (J : JointMass R C) (i : R) (k : C) :
    xSame J i k = J.centeredRectangleMass {i} {k} := by
  simp [xSame, JointMass.centeredRectangleMass]

/-- Concrete first square in `(A.16)`, independent of the column atom used
to name the representative side. -/
theorem xBarOpp_sq_independent_col
    (J : JointMass R C) (Fr : FourSector R) (Fc : FourSector C)
    (i : R) (k l : C) :
    xBarOpp J Fr Fc i k ^ 2 =
      xBarOpp J Fr Fc i l ^ 2 := by
  exact J.centeredRectangleMass_col_opposite_square_independent
    Fc (Fr.oppositeSideBlock i) k l

/-- Concrete plus square in `(A.16)`, again independent of the representative
column atom. -/
theorem xBarOpp_add_xOpp_sq_independent_col
    (J : JointMass R C) (Fr : FourSector R) (Fc : FourSector C)
    (i : R) (k l : C) :
    (xBarOpp J Fr Fc i k + xOpp J Fc i k) ^ 2 =
      (xBarOpp J Fr Fc i l + xOpp J Fc i l) ^ 2 := by
  rw [xOpp_eq_rectangle, xOpp_eq_rectangle]
  exact J.centeredRectangleMass_col_opposite_plus_square_independent
    Fc (Fr.oppositeSideBlock i) {i} k l

/-- The ordinary representative square is independent of both the row and
column atoms used to name its two complete central sides. -/
theorem xBarOpp_sq_independent
    (J : JointMass R C) (Fr : FourSector R) (Fc : FourSector C)
    (i j : R) (k l : C) :
    xBarOpp J Fr Fc i k ^ 2 =
      xBarOpp J Fr Fc j l ^ 2 := by
  calc
    xBarOpp J Fr Fc i k ^ 2 =
        xBarOpp J Fr Fc i l ^ 2 :=
      xBarOpp_sq_independent_col J Fr Fc i k l
    _ = xBarOpp J Fr Fc j l ^ 2 := by
      exact J.centeredRectangleMass_row_opposite_square_independent
        Fr i j (Fc.oppositeSideBlock l)

/-- The neighboring `U_i(k)` square in `(A.15b)` is independent of the row
representative `i`. -/
theorem neighboringU_sq_independent_row
    (J : JointMass R C) (Fr : FourSector R) (Fc : FourSector C)
    (i j : R) (k : C) :
    RetainedSquares.neighboringU
        J.colMass
        (fun u => J.colBlockMass (Fc.oppositeSideBlock u))
        (xBarOpp J Fr Fc) (xBarSame J Fr) i k ^ 2 =
      RetainedSquares.neighboringU
        J.colMass
        (fun u => J.colBlockMass (Fc.oppositeSideBlock u))
        (xBarOpp J Fr Fc) (xBarSame J Fr) j k ^ 2 := by
  unfold RetainedSquares.neighboringU xBarOpp xBarSame
  exact J.centeredRectangleMass_row_linear_square_independent
    Fr i j (Fc.oppositeSideBlock k) {k}
      (J.colMass k)
      (J.colBlockMass (Fc.oppositeSideBlock k))

end LocalCoordinates

end QuartetV060
