import QuartetV060.LocalCoordinates
import QuartetV060.OccurrenceSettlement

/-!
# Concrete retained-square identities `(A.15)--(A.18)`

The abstract finite-sum identities are instantiated here in the actual
principal chart `(e,f)`.  In particular, the symmetric coefficient, its
weighted average, all four centered coordinates, and both residual partitions
come from the concrete normalized taxon table.
-/

namespace QuartetV060

open scoped BigOperators

namespace ConcreteRetainedSquares

open QuartetDistance
open PhyloOccurrences
open PrincipalAtoms
open PrincipalChart
open LocalCoordinates

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

variable
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)

abbrev RowAtom := Atom e
abbrev ColAtom := Atom f

def J : JointMass (RowAtom e) (ColAtom f) :=
  jointMass e f

def Fr : FourSector (RowAtom e) :=
  fourSector e

def Fc : FourSector (ColAtom f) :=
  fourSector f

def Pr : ResidualPartition (RowAtom e) :=
  residualPartition e

def Pc : ResidualPartition (ColAtom f) :=
  residualPartition f

def c (k : ColAtom f) : ℚ :=
  (J e f).colMass k

def cbar (k : ColAtom f) : ℚ :=
  (J e f).colBlockMass ((Fc f).oppositeSideBlock k)

/-- The concrete coefficient `r_i^k`. -/
def r (i : RowAtom e) (k : ColAtom f) : ℚ :=
  (J e f).symmetricRowCoefficient (Fc f) i k

/-- The manuscript coefficient `alpha_{i,k}=c_k r_i^k`. -/
def alpha (i : RowAtom e) (k : ColAtom f) : ℚ :=
  c e f k * r e f i k

/-- The ordinary-column weight `omega_i`. -/
def omega (i : RowAtom e) : ℚ :=
  ∑ k, alpha e f i k

/-- The manuscript order `c_k r_i^k` agrees with the reusable residual
identity's order `r_i^k c_k`. -/
theorem omega_eq_retainedOmega (i : RowAtom e) :
    omega e f i = RetainedSquares.omega (r e f) (c e f) i := by
  unfold omega alpha RetainedSquares.omega RetainedSquares.atomWeight
  apply Fintype.sum_congr
  intro k
  ring

/-- A concrete row and column anchor.  They only select representatives; all
resulting squares are proved independent of this choice. -/
def anchorRow : RowAtom e :=
  atomAt e (Classical.choice (inferInstance : Nonempty X))

def anchorCol : ColAtom f :=
  atomAt f (Classical.choice (inferInstance : Nonempty X))

def ordinaryX (i : RowAtom e) : ℚ :=
  xBarOpp (J e f) (Fr e) (Fc f) i (anchorCol f)

def ordinaryY (i : RowAtom e) : ℚ :=
  xOpp (J e f) (Fc f) i (anchorCol f)

def ordinarySquare : ℚ :=
  ordinaryX e f (anchorRow e) ^ 2

def neighborU (i : RowAtom e) (k : ColAtom f) : ℚ :=
  RetainedSquares.neighboringU
    (c e f) (cbar e f)
    (xBarOpp (J e f) (Fr e) (Fc f))
    (xBarSame (J e f) (Fr e)) i k

def neighborV (i : RowAtom e) (k : ColAtom f) : ℚ :=
  RetainedSquares.neighboringV
    (c e f) (cbar e f)
    (xOpp (J e f) (Fc f))
    (xSame (J e f)) i k

def neighborSquare (k : ColAtom f) : ℚ :=
  neighborU e f (anchorRow e) k ^ 2

theorem c_pos (k : ColAtom f) :
    0 < c e f k :=
  jointMass_colMass_pos e f k

theorem cbar_pos (k : ColAtom f) :
    0 < cbar e f k :=
  jointMass_oppositeBlockMass_pos e f k

theorem r_nonneg (i : RowAtom e) (k : ColAtom f) :
    0 ≤ r e f i k := by
  unfold r JointMass.symmetricRowCoefficient
  have hc : 0 ≤ (J e f).colMass k :=
    (J e f).colMass_nonneg k
  have hcbar :
      0 ≤
        (J e f).colBlockMass ((Fc f).oppositeSideBlock k) :=
    (J e f).colBlockMass_nonneg _
  have hai : 0 ≤ (J e f).a i k := (J e f).nonneg i k
  have haibar :
      0 ≤
        (J e f).mixedBlockMass i ((Fc f).oppositeSideBlock k) :=
    (J e f).mixedBlockMass_nonneg i _
  positivity

theorem sum_r (k : ColAtom f) :
    ∑ i, r e f i k = 1 := by
  exact
    (J e f).sum_symmetricRowCoefficient (Fc f) k
      (c_pos e f k).ne' (cbar_pos e f k).ne'

theorem sum_omega :
    ∑ i, omega e f i = 1 := by
  unfold omega alpha
  calc
    (∑ i : RowAtom e, ∑ k : ColAtom f,
        c e f k * r e f i k) =
        ∑ k : ColAtom f, c e f k * ∑ i : RowAtom e, r e f i k := by
          rw [Finset.sum_comm]
          apply Fintype.sum_congr
          intro k
          rw [Finset.mul_sum]
    _ = ∑ k : ColAtom f, c e f k := by
          apply Fintype.sum_congr
          intro k
          rw [sum_r e f k]
          ring
    _ = 1 := by
          exact (J e f).sum_colMass

theorem ordinaryX_sq (i : RowAtom e) :
    ordinaryX e f i ^ 2 = ordinarySquare e f := by
  unfold ordinaryX ordinarySquare
  exact
    xBarOpp_sq_independent (J e f) (Fr e) (Fc f)
      i (anchorRow e) (anchorCol f) (anchorCol f)

theorem neighborU_sq (i : RowAtom e) (k : ColAtom f) :
    neighborU e f i k ^ 2 = neighborSquare e f k := by
  unfold neighborU neighborSquare
  exact
    neighboringU_sq_independent_row
      (J e f) (Fr e) (Fc f) i (anchorRow e) k

def R1Abstract : ℚ :=
  RetainedSquares.r1Abstract
    (Pr e) (r e f) (c e f)
    (ordinaryX e f) (ordinaryY e f)

def R1Expanded : ℚ :=
  RetainedSquares.r1Expanded
    (Pr e) (r e f) (c e f)
    (xBarOpp (J e f) (Fr e) (Fc f))
    (xOpp (J e f) (Fc f))

/-- Concrete `(A.17)`: every column representative has been replaced using
the proved common-sign square identities. -/
theorem A17 :
    R1Abstract e f = R1Expanded e f := by
  apply RetainedSquares.r1Abstract_eq_expanded
  · intro i k
    unfold ordinaryX
    exact
      xBarOpp_sq_independent_col
        (J e f) (Fr e) (Fc f) i (anchorCol f) k
  · intro i k
    unfold ordinaryX ordinaryY
    exact
      xBarOpp_add_xOpp_sq_independent_col
        (J e f) (Fr e) (Fc f) i (anchorCol f) k

def R2Retained : ℚ :=
  RetainedSquares.r2Retained
    (Pr e) (Pc f).endpoint
    (r e f) (c e f) (cbar e f)
    (xBarOpp (J e f) (Fr e) (Fc f))
    (xBarSame (J e f) (Fr e))
    (xOpp (J e f) (Fc f))
    (xSame (J e f))

def R2Faces : ℚ :=
  RetainedSquares.r2Faces
    (Pr e) (Pc f).endpoint
    (r e f) (c e f) (cbar e f)
    (xBarOpp (J e f) (Fr e) (Fc f))
    (xBarSame (J e f) (Fr e))
    (xOpp (J e f) (Fc f))
    (xSame (J e f))

/-- Concrete `(A.18)`, with all first, mixed, and second square faces
displayed by `R2Faces`. -/
theorem A18 :
    R2Retained e f = R2Faces e f := by
  exact RetainedSquares.r2Retained_eq_faces
    (Pr e) (Pc f).endpoint
    (r e f) (c e f) (cbar e f)
    (xBarOpp (J e f) (Fr e) (Fc f))
    (xBarSame (J e f) (Fr e))
    (xOpp (J e f) (Fc f))
    (xSame (J e f))

def ordinaryNeighboring : ℚ :=
  OccurrenceSettlement.neighboringN
    (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f)

def Q1 : ℚ :=
  OccurrenceSettlement.omittedQ
    (Pr e) (omega e f) (ordinaryY e f)

/-- Concrete `(A.15a)` in residual-partition form. -/
theorem A15a :
    ordinarySquare e f - ordinaryNeighboring e f =
      R1Abstract e f - Q1 e f := by
  have homega :
      omega e f = RetainedSquares.omega (r e f) (c e f) :=
    funext (omega_eq_retainedOmega e f)
  have h :=
    (Pr e).exact_residual_identity
      (omega e f) (ordinaryX e f) (ordinaryY e f)
      (ordinarySquare e f) (sum_omega e f) (ordinaryX_sq e f)
  rw [homega] at h
  simpa [ordinaryNeighboring, Q1, R1Abstract,
    OccurrenceSettlement.neighboringN,
    OccurrenceSettlement.omittedQ,
    RetainedSquares.r1Abstract, homega] using h

def correctedNeighboring : ℚ :=
  ∑ k ∈ (Pc f).endpoint,
    OccurrenceSettlement.neighboringN
      (Pr e) (fun i => r e f i k)
      (fun i => neighborU e f i k)
      (fun i => neighborV e f i k)

def Q2 : ℚ :=
  ∑ k ∈ (Pc f).endpoint,
    OccurrenceSettlement.omittedQ
      (Pr e) (fun i => r e f i k)
      (fun i => neighborV e f i k)

/-- Concrete summed `(A.15b)`.  The equality is proved separately for every
endpoint `k` and only then summed over the complete endpoint range. -/
theorem A15b :
    (∑ k ∈ (Pc f).endpoint, neighborSquare e f k) -
        correctedNeighboring e f =
      R2Retained e f - Q2 e f := by
  have hpoint :
      ∀ k ∈ (Pc f).endpoint,
        neighborSquare e f k -
            OccurrenceSettlement.neighboringN
              (Pr e) (fun i => r e f i k)
              (fun i => neighborU e f i k)
              (fun i => neighborV e f i k)
          =
        OccurrenceSettlement.retainedI
              (Pr e) (fun i => r e f i k)
              (fun i => neighborU e f i k) +
            OccurrenceSettlement.retainedD
              (Pr e) (fun i => r e f i k)
              (fun i => neighborU e f i k)
              (fun i => neighborV e f i k) -
            OccurrenceSettlement.omittedQ
              (Pr e) (fun i => r e f i k)
              (fun i => neighborV e f i k) := by
    intro k hk
    have h :=
      (Pr e).exact_residual_identity
        (fun i => r e f i k)
        (fun i => neighborU e f i k)
        (fun i => neighborV e f i k)
        (neighborSquare e f k)
        (sum_r e f k) (fun i => neighborU_sq e f i k)
    simpa [OccurrenceSettlement.neighboringN,
      OccurrenceSettlement.retainedI,
      OccurrenceSettlement.retainedD,
      OccurrenceSettlement.omittedQ] using h
  have hsum :
      (∑ k ∈ (Pc f).endpoint,
        (neighborSquare e f k -
          OccurrenceSettlement.neighboringN
            (Pr e) (fun i => r e f i k)
            (fun i => neighborU e f i k)
            (fun i => neighborV e f i k))) =
      ∑ k ∈ (Pc f).endpoint,
        (OccurrenceSettlement.retainedI
            (Pr e) (fun i => r e f i k)
            (fun i => neighborU e f i k) +
          OccurrenceSettlement.retainedD
            (Pr e) (fun i => r e f i k)
            (fun i => neighborU e f i k)
            (fun i => neighborV e f i k) -
          OccurrenceSettlement.omittedQ
            (Pr e) (fun i => r e f i k)
            (fun i => neighborV e f i k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hpoint k hk
  rw [Finset.sum_sub_distrib] at hsum
  rw [Finset.sum_sub_distrib] at hsum
  rw [Finset.sum_add_distrib] at hsum
  unfold correctedNeighboring Q2
  unfold R2Retained RetainedSquares.r2Retained
  unfold OccurrenceSettlement.retainedI
    OccurrenceSettlement.retainedD at hsum
  rw [Finset.sum_comm] at hsum
  have hDcomm :
      (∑ k ∈ (Pc f).endpoint, ∑ z ∈ (Pr e).D,
          r e f z.1 k * r e f z.2 k *
            (neighborU e f z.1 k + neighborV e f z.1 k) ^ 2) =
        ∑ z ∈ (Pr e).D, ∑ k ∈ (Pc f).endpoint,
          r e f z.1 k * r e f z.2 k *
            (neighborU e f z.1 k + neighborV e f z.1 k) ^ 2 := by
    rw [Finset.sum_comm]
  rw [hDcomm] at hsum
  simpa [neighborU, neighborV] using hsum

end

end ConcreteRetainedSquares

end QuartetV060
