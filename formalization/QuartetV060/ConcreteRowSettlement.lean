import QuartetV060.ConcreteOccurrenceSettlement

/-!
# Concrete global row settlement `(A.29c)`--`(A.29d)`

This file passes from the actual four determinant levels to the two retained
row classes.  The column occurrence is never replaced by an unindexed
endpoint: the explicit correction/endpoint equivalence is used before the
fixed-chart polynomial is written.
-/

namespace QuartetV060

namespace ConcreteRowSettlement

open scoped BigOperators

open QuartetDistance
open PhyloOccurrences
open PrincipalBranches
open PrincipalAtoms
open PrincipalChart
open LocalCoordinates
open ConcreteRetainedSquares
open ConcreteDeterminantLevels
open ConcreteOccurrenceSettlement

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

variable
    {T₁ T₂ : Tree.PhyloTree X}

/-! ## The two concrete row representatives -/

def ZI
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) : ℚ :=
  xBarOpp (J e f) (Fr e) (Fc f) i u

def WI
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) : ℚ :=
  xBarSame (J e f) (Fr e) i u

def ZD
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) : ℚ :=
  xBarOpp (J e f) (Fr e) (Fc f) i u +
    xOpp (J e f) (Fc f) i u

def WD
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (u : Atom f) : ℚ :=
  xBarSame (J e f) (Fr e) i u +
    xSame (J e f) i u

/-! ## The fixed-chart direct row polynomials -/

def directRowI
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (z : Atom e × Atom e) : ℚ :=
  2 * (∑ u : Atom f, ∑ l : Atom f,
      alpha e f z.1 u * alpha e f z.2 l *
        ZI e f z.1 u ^ 2) -
    ∑ k ∈ (Pc f).endpoint,
      r e f z.1 k * r e f z.2 k *
        (c e f k * ZI e f z.1 k -
          cbar e f k * WI e f z.1 k) ^ 2

def directRowD
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (z : Atom e × Atom e) : ℚ :=
  2 * (∑ u : Atom f, ∑ l : Atom f,
      alpha e f z.1 u * alpha e f z.2 l *
        ZD e f z.1 u ^ 2) -
    ∑ k ∈ (Pc f).endpoint,
      r e f z.1 k * r e f z.2 k *
        (c e f k * ZD e f z.1 k -
          cbar e f k * WD e f z.1 k) ^ 2

def settledChart
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) : ℚ :=
  2 * (∑ z ∈ (Pr e).I, directRowI e f z) +
    ∑ z ∈ (Pr e).D, directRowD e f z

/-! ## Ordinary and corrected retained occurrences -/

def ordinaryI
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) : ℚ :=
  OccurrenceSettlement.retainedI
    (Pr e) (omega e f) (ordinaryX e f)

def ordinaryD
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) : ℚ :=
  OccurrenceSettlement.retainedD
    (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f)

def correctedI
    (e : RelevantEdge T₁) (b : AdjacentCorrection T₂) : ℚ :=
  OccurrenceSettlement.retainedI
    (Pr e)
    (fun i => r e (first b) i (selectedColumnAtom b))
    (fun i => neighborU e (first b) i (selectedColumnAtom b))

def correctedD
    (e : RelevantEdge T₁) (b : AdjacentCorrection T₂) : ℚ :=
  OccurrenceSettlement.retainedD
    (Pr e)
    (fun i => r e (first b) i (selectedColumnAtom b))
    (fun i => neighborU e (first b) i (selectedColumnAtom b))
    (fun i => neighborV e (first b) i (selectedColumnAtom b))

/-! ## Exact occurrence identifications `(A.29c₂)` -/

theorem ordinary_level_identification
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    2 * ordinaryOrdinary
          (correctionSystem T₁) (correctionSystem T₂) e f -
        correctedOrdinary
          (correctionSystem T₁) (correctionSystem T₂) e f =
      2 * ordinaryI e f + ordinaryD e f +
        OccurrenceSettlement.boundary
          (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f) := by
  rw [ordinaryOrdinary_eq_ordinarySquare]
  rw [correctedOrdinary_eq_ordinaryNeighboring]
  exact ordinary_twoE_sub_N e f

theorem sum_corrected_occurrence
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    (∑ b : CorrectionsFrom f,
      (2 * neighborSquare e f
          (correctionEquivEndpointAtom f b).1 -
        OccurrenceSettlement.neighboringN
          (Pr e)
          (fun i => r e f i (correctionEquivEndpointAtom f b).1)
          (fun i => neighborU e f i
            (correctionEquivEndpointAtom f b).1)
          (fun i => neighborV e f i
            (correctionEquivEndpointAtom f b).1))) =
      2 * ordinaryCorrected
          (correctionSystem T₁) (correctionSystem T₂) e f -
        correctedCorrected
          (correctionSystem T₁) (correctionSystem T₂) e f := by
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [ordinaryCorrected_eq_sum_neighborSquare]
  rw [correctedCorrected_eq_correctedNeighboring]
  unfold correctedNeighboring
  have hfirst :
      (∑ b : CorrectionsFrom f,
          neighborSquare e f (correctionEquivEndpointAtom f b).1) =
        ∑ k : EndpointAtomIndex f, neighborSquare e f k.1 := by
    exact Fintype.sum_equiv
      (correctionEquivEndpointAtom f)
      (fun b : CorrectionsFrom f =>
        neighborSquare e f (correctionEquivEndpointAtom f b).1)
      (fun k : EndpointAtomIndex f => neighborSquare e f k.1)
      (fun _ => rfl)
  have hsecond :
      (∑ b : CorrectionsFrom f,
          OccurrenceSettlement.neighboringN
            (Pr e)
            (fun i => r e f i (correctionEquivEndpointAtom f b).1)
            (fun i => neighborU e f i
              (correctionEquivEndpointAtom f b).1)
            (fun i => neighborV e f i
              (correctionEquivEndpointAtom f b).1)) =
        ∑ k : EndpointAtomIndex f,
          OccurrenceSettlement.neighboringN
            (Pr e)
            (fun i => r e f i k.1)
            (fun i => neighborU e f i k.1)
            (fun i => neighborV e f i k.1) := by
    exact Fintype.sum_equiv
      (correctionEquivEndpointAtom f)
      (fun b : CorrectionsFrom f =>
        OccurrenceSettlement.neighboringN
          (Pr e)
          (fun i => r e f i (correctionEquivEndpointAtom f b).1)
          (fun i => neighborU e f i
            (correctionEquivEndpointAtom f b).1)
          (fun i => neighborV e f i
            (correctionEquivEndpointAtom f b).1))
      (fun k : EndpointAtomIndex f =>
        OccurrenceSettlement.neighboringN
          (Pr e)
          (fun i => r e f i k.1)
          (fun i => neighborU e f i k.1)
          (fun i => neighborV e f i k.1))
      (fun _ => rfl)
  rw [hfirst, hsecond]
  have hsquare :
      (∑ k : EndpointAtomIndex f, neighborSquare e f k.1) =
        ∑ k ∈ (Pc f).endpoint, neighborSquare e f k := by
    simpa [Pc, Pr] using
      (sum_endpointAtomIndex_eq_endpoint f
        (fun k => neighborSquare e f k))
  have hneighbor :
      (∑ k : EndpointAtomIndex f,
          OccurrenceSettlement.neighboringN
            (Pr e)
            (fun i => r e f i k.1)
            (fun i => neighborU e f i k.1)
            (fun i => neighborV e f i k.1)) =
        ∑ k ∈ (Pc f).endpoint,
          OccurrenceSettlement.neighboringN
            (Pr e)
            (fun i => r e f i k)
            (fun i => neighborU e f i k)
            (fun i => neighborV e f i k) := by
    simpa [Pc, Pr] using
      (sum_endpointAtomIndex_eq_endpoint f
        (fun k =>
          OccurrenceSettlement.neighboringN
            (Pr e)
            (fun i => r e f i k)
            (fun i => neighborU e f i k)
            (fun i => neighborV e f i k)))
  rw [hsquare, hneighbor]

theorem corrected_level_identification
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    2 * ordinaryCorrected
          (correctionSystem T₁) (correctionSystem T₂) e f -
        correctedCorrected
          (correctionSystem T₁) (correctionSystem T₂) e f =
      ∑ b : CorrectionsFrom f,
        (2 * correctedI e b.1 + correctedD e b.1 +
          OccurrenceSettlement.boundary
            (Pr e)
            (fun i => r e f i
              (correctionEquivEndpointAtom f b).1)
            (fun i => neighborU e f i
              (correctionEquivEndpointAtom f b).1)
            (fun i => neighborV e f i
              (correctionEquivEndpointAtom f b).1)) := by
  rw [← sum_corrected_occurrence e f]
  apply Fintype.sum_congr
  intro b
  rcases b with ⟨b, hb⟩
  subst f
  simpa [correctedI, correctedD, selectedColumnAtom,
      correctionEquivEndpointAtom, correctionSlot,
      correctionFromFirst, endpointAtomEquiv] using
    corrected_twoE_sub_N e b

/-! ## Expansion of the two retained row classes -/

theorem omega_mul_eq_alpha_sum
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) :
    omega e f i * omega e f j =
      ∑ u : Atom f, ∑ l : Atom f,
        alpha e f i u * alpha e f j l := by
  unfold omega
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro u
  rw [Finset.mul_sum]

theorem ordinaryI_expanded
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    ordinaryI e f =
      ∑ z ∈ (Pr e).I, ∑ u : Atom f, ∑ l : Atom f,
        alpha e f z.1 u * alpha e f z.2 l *
          ZI e f z.1 u ^ 2 := by
  unfold ordinaryI OccurrenceSettlement.retainedI
  apply Finset.sum_congr rfl
  intro z hz
  calc
    omega e f z.1 * omega e f z.2 * ordinaryX e f z.1 ^ 2 =
        (∑ u : Atom f, ∑ l : Atom f,
          alpha e f z.1 u * alpha e f z.2 l) *
            ordinaryX e f z.1 ^ 2 := by
      rw [omega_mul_eq_alpha_sum]
    _ = ∑ u : Atom f, ∑ l : Atom f,
          alpha e f z.1 u * alpha e f z.2 l *
            ordinaryX e f z.1 ^ 2 := by
      rw [Finset.sum_mul]
      apply Fintype.sum_congr
      intro u
      rw [Finset.sum_mul]
    _ = ∑ u : Atom f, ∑ l : Atom f,
          alpha e f z.1 u * alpha e f z.2 l *
            ZI e f z.1 u ^ 2 := by
      apply Fintype.sum_congr
      intro u
      apply Fintype.sum_congr
      intro l
      unfold ordinaryX ZI
      rw [xBarOpp_sq_independent_col
        (J e f) (Fr e) (Fc f) z.1 (anchorCol f) u]

theorem ordinaryD_expanded
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    ordinaryD e f =
      ∑ z ∈ (Pr e).D, ∑ u : Atom f, ∑ l : Atom f,
        alpha e f z.1 u * alpha e f z.2 l *
          ZD e f z.1 u ^ 2 := by
  unfold ordinaryD OccurrenceSettlement.retainedD
  apply Finset.sum_congr rfl
  intro z hz
  calc
    omega e f z.1 * omega e f z.2 *
        (ordinaryX e f z.1 + ordinaryY e f z.1) ^ 2 =
        (∑ u : Atom f, ∑ l : Atom f,
          alpha e f z.1 u * alpha e f z.2 l) *
            (ordinaryX e f z.1 + ordinaryY e f z.1) ^ 2 := by
      rw [omega_mul_eq_alpha_sum]
    _ = ∑ u : Atom f, ∑ l : Atom f,
          alpha e f z.1 u * alpha e f z.2 l *
            (ordinaryX e f z.1 + ordinaryY e f z.1) ^ 2 := by
      rw [Finset.sum_mul]
      apply Fintype.sum_congr
      intro u
      rw [Finset.sum_mul]
    _ = ∑ u : Atom f, ∑ l : Atom f,
          alpha e f z.1 u * alpha e f z.2 l *
            ZD e f z.1 u ^ 2 := by
      apply Fintype.sum_congr
      intro u
      apply Fintype.sum_congr
      intro l
      unfold ordinaryX ordinaryY ZD
      rw [xBarOpp_add_xOpp_sq_independent_col
        (J e f) (Fr e) (Fc f) z.1 (anchorCol f) u]

theorem correctedI_from_eq
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (b : CorrectionsFrom f) :
    correctedI e b.1 =
      OccurrenceSettlement.retainedI
        (Pr e)
        (fun i => r e f i (correctionEquivEndpointAtom f b).1)
        (fun i => neighborU e f i
          (correctionEquivEndpointAtom f b).1) := by
  rcases b with ⟨b, hb⟩
  subst f
  simp [correctedI, selectedColumnAtom,
    correctionEquivEndpointAtom, correctionSlot,
    correctionFromFirst, endpointAtomEquiv]

theorem correctedD_from_eq
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (b : CorrectionsFrom f) :
    correctedD e b.1 =
      OccurrenceSettlement.retainedD
        (Pr e)
        (fun i => r e f i (correctionEquivEndpointAtom f b).1)
        (fun i => neighborU e f i
          (correctionEquivEndpointAtom f b).1)
        (fun i => neighborV e f i
          (correctionEquivEndpointAtom f b).1) := by
  rcases b with ⟨b, hb⟩
  subst f
  simp [correctedD, selectedColumnAtom,
    correctionEquivEndpointAtom, correctionSlot,
    correctionFromFirst, endpointAtomEquiv]

theorem sum_correctedI_eq_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    (∑ b : CorrectionsFrom f, correctedI e b.1) =
      ∑ z ∈ (Pr e).I, ∑ k ∈ (Pc f).endpoint,
        r e f z.1 k * r e f z.2 k *
          neighborU e f z.1 k ^ 2 := by
  calc
    (∑ b : CorrectionsFrom f, correctedI e b.1) =
        ∑ b : CorrectionsFrom f,
          OccurrenceSettlement.retainedI
            (Pr e)
            (fun i => r e f i (correctionEquivEndpointAtom f b).1)
            (fun i => neighborU e f i
              (correctionEquivEndpointAtom f b).1) := by
      apply Fintype.sum_congr
      intro b
      exact correctedI_from_eq e f b
    _ = ∑ k : EndpointAtomIndex f,
          OccurrenceSettlement.retainedI
            (Pr e)
            (fun i => r e f i k.1)
            (fun i => neighborU e f i k.1) := by
      exact Fintype.sum_equiv
        (correctionEquivEndpointAtom f)
        (fun b : CorrectionsFrom f =>
          OccurrenceSettlement.retainedI
            (Pr e)
            (fun i => r e f i (correctionEquivEndpointAtom f b).1)
            (fun i => neighborU e f i
              (correctionEquivEndpointAtom f b).1))
        (fun k : EndpointAtomIndex f =>
          OccurrenceSettlement.retainedI
            (Pr e)
            (fun i => r e f i k.1)
            (fun i => neighborU e f i k.1))
        (fun _ => rfl)
    _ = ∑ k ∈ (Pc f).endpoint,
          OccurrenceSettlement.retainedI
            (Pr e)
            (fun i => r e f i k)
            (fun i => neighborU e f i k) := by
      simpa [Pc, Pr] using
        (sum_endpointAtomIndex_eq_endpoint f
          (fun k =>
            OccurrenceSettlement.retainedI
              (Pr e)
              (fun i => r e f i k)
              (fun i => neighborU e f i k)))
    _ = ∑ z ∈ (Pr e).I, ∑ k ∈ (Pc f).endpoint,
          r e f z.1 k * r e f z.2 k *
            neighborU e f z.1 k ^ 2 := by
      unfold OccurrenceSettlement.retainedI
      rw [Finset.sum_comm]

theorem sum_correctedD_eq_endpoint
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    (∑ b : CorrectionsFrom f, correctedD e b.1) =
      ∑ z ∈ (Pr e).D, ∑ k ∈ (Pc f).endpoint,
        r e f z.1 k * r e f z.2 k *
          (neighborU e f z.1 k + neighborV e f z.1 k) ^ 2 := by
  calc
    (∑ b : CorrectionsFrom f, correctedD e b.1) =
        ∑ b : CorrectionsFrom f,
          OccurrenceSettlement.retainedD
            (Pr e)
            (fun i => r e f i (correctionEquivEndpointAtom f b).1)
            (fun i => neighborU e f i
              (correctionEquivEndpointAtom f b).1)
            (fun i => neighborV e f i
              (correctionEquivEndpointAtom f b).1) := by
      apply Fintype.sum_congr
      intro b
      exact correctedD_from_eq e f b
    _ = ∑ k : EndpointAtomIndex f,
          OccurrenceSettlement.retainedD
            (Pr e)
            (fun i => r e f i k.1)
            (fun i => neighborU e f i k.1)
            (fun i => neighborV e f i k.1) := by
      exact Fintype.sum_equiv
        (correctionEquivEndpointAtom f)
        (fun b : CorrectionsFrom f =>
          OccurrenceSettlement.retainedD
            (Pr e)
            (fun i => r e f i (correctionEquivEndpointAtom f b).1)
            (fun i => neighborU e f i
              (correctionEquivEndpointAtom f b).1)
            (fun i => neighborV e f i
              (correctionEquivEndpointAtom f b).1))
        (fun k : EndpointAtomIndex f =>
          OccurrenceSettlement.retainedD
            (Pr e)
            (fun i => r e f i k.1)
            (fun i => neighborU e f i k.1)
            (fun i => neighborV e f i k.1))
        (fun _ => rfl)
    _ = ∑ k ∈ (Pc f).endpoint,
          OccurrenceSettlement.retainedD
            (Pr e)
            (fun i => r e f i k)
            (fun i => neighborU e f i k)
            (fun i => neighborV e f i k) := by
      simpa [Pc, Pr] using
        (sum_endpointAtomIndex_eq_endpoint f
          (fun k =>
            OccurrenceSettlement.retainedD
              (Pr e)
              (fun i => r e f i k)
              (fun i => neighborU e f i k)
              (fun i => neighborV e f i k)))
    _ = ∑ z ∈ (Pr e).D, ∑ k ∈ (Pc f).endpoint,
          r e f z.1 k * r e f z.2 k *
            (neighborU e f z.1 k + neighborV e f z.1 k) ^ 2 := by
      unfold OccurrenceSettlement.retainedD
      rw [Finset.sum_comm]

theorem corrected_form_I
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (k : Atom f) :
    c e f k * ZI e f i k - cbar e f k * WI e f i k =
      neighborU e f i k := by
  rfl

theorem corrected_form_D
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i : Atom e) (k : Atom f) :
    c e f k * ZD e f i k - cbar e f k * WD e f i k =
      neighborU e f i k + neighborV e f i k := by
  unfold ZD WD neighborU neighborV
    RetainedSquares.neighboringU RetainedSquares.neighboringV
  ring

theorem sum_directRowI
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    (∑ z ∈ (Pr e).I, directRowI e f z) =
      2 * ordinaryI e f -
        ∑ b : CorrectionsFrom f, correctedI e b.1 := by
  unfold directRowI
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [← ordinaryI_expanded e f]
  rw [sum_correctedI_eq_endpoint e f]
  apply congrArg₂ (· - ·) rfl
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro k hk
  rw [corrected_form_I]

theorem sum_directRowD
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    (∑ z ∈ (Pr e).D, directRowD e f z) =
      2 * ordinaryD e f -
        ∑ b : CorrectionsFrom f, correctedD e b.1 := by
  unfold directRowD
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [← ordinaryD_expanded e f]
  rw [sum_correctedD_eq_endpoint e f]
  apply congrArg₂ (· - ·) rfl
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro k hk
  rw [corrected_form_D]

theorem settledChart_eq_retained
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    settledChart e f =
      2 * (2 * ordinaryI e f + ordinaryD e f) -
        ∑ b : CorrectionsFrom f,
          (2 * correctedI e b.1 + correctedD e b.1) := by
  unfold settledChart
  rw [sum_directRowI e f, sum_directRowD e f]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-! ## Global removal of the row-boundary polynomial -/

theorem sum_fixed_corrected_boundary_eq_zero
    (f : RelevantEdge T₂) (b : CorrectionsFrom f) :
    (∑ e : RelevantEdge T₁,
      OccurrenceSettlement.boundary
        (Pr e)
        (fun i => r e f i (correctionEquivEndpointAtom f b).1)
        (fun i => neighborU e f i
          (correctionEquivEndpointAtom f b).1)
        (fun i => neighborV e f i
          (correctionEquivEndpointAtom f b).1)) = 0 := by
  rcases b with ⟨b, hb⟩
  subst f
  simpa [selectedColumnAtom, correctionEquivEndpointAtom,
      correctionSlot, correctionFromFirst, endpointAtomEquiv] using
    (sum_corrected_boundary_eq_zero (T₁ := T₁) b)

theorem cancel_two_boundary_sums
    {E B : Type*} [Fintype E] [Fintype B]
    (O BO : E → ℚ) (C BC : E → B → ℚ)
    (hBO : (∑ e, BO e) = 0)
    (hBC : (∑ b, ∑ e, BC e b) = 0) :
    (∑ e, (2 * (O e + BO e) -
      ∑ b, (C e b + BC e b))) =
      ∑ e, (2 * O e - ∑ b, C e b) := by
  have hBC' : (∑ e, ∑ b, BC e b) = 0 := by
    rw [Finset.sum_comm]
    exact hBC
  have hBO2 : (∑ e, 2 * BO e) = 0 := by
    rw [← Finset.mul_sum, hBO]
    ring
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_add]
  simp only [Finset.sum_add_distrib]
  rw [hBO2, hBC']
  ring

def fourLevelChart
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) : ℚ :=
  4 * ordinaryOrdinary
      (correctionSystem T₁) (correctionSystem T₂) e f -
    2 * correctedOrdinary
      (correctionSystem T₁) (correctionSystem T₂) e f -
    2 * ordinaryCorrected
      (correctionSystem T₁) (correctionSystem T₂) e f +
    correctedCorrected
      (correctionSystem T₁) (correctionSystem T₂) e f

theorem sum_fourLevel_fixed_column
    (f : RelevantEdge T₂) :
    (∑ e : RelevantEdge T₁, fourLevelChart e f) =
      ∑ e : RelevantEdge T₁, settledChart e f := by
  have hord :
      (∑ e : RelevantEdge T₁,
        OccurrenceSettlement.boundary
          (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f)) = 0 :=
    sum_ordinary_boundary_eq_zero f
  have hcorr :
      (∑ b : CorrectionsFrom f, ∑ e : RelevantEdge T₁,
        OccurrenceSettlement.boundary
          (Pr e)
          (fun i => r e f i (correctionEquivEndpointAtom f b).1)
          (fun i => neighborU e f i
            (correctionEquivEndpointAtom f b).1)
          (fun i => neighborV e f i
            (correctionEquivEndpointAtom f b).1)) = 0 := by
    apply Fintype.sum_eq_zero
    intro b
    exact sum_fixed_corrected_boundary_eq_zero f b
  have hpoint :
      ∀ e : RelevantEdge T₁,
        fourLevelChart e f =
          2 * (2 * ordinaryI e f + ordinaryD e f +
            OccurrenceSettlement.boundary
              (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f)) -
          ∑ b : CorrectionsFrom f,
            (2 * correctedI e b.1 + correctedD e b.1 +
              OccurrenceSettlement.boundary
                (Pr e)
                (fun i => r e f i
                  (correctionEquivEndpointAtom f b).1)
                (fun i => neighborU e f i
                  (correctionEquivEndpointAtom f b).1)
                (fun i => neighborV e f i
                  (correctionEquivEndpointAtom f b).1)) := by
    intro e
    have ho := ordinary_level_identification e f
    have hc := corrected_level_identification e f
    unfold fourLevelChart
    rw [← ho, ← hc]
    ring
  calc
    (∑ e : RelevantEdge T₁, fourLevelChart e f) =
        ∑ e : RelevantEdge T₁,
          (2 * (2 * ordinaryI e f + ordinaryD e f +
            OccurrenceSettlement.boundary
              (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f)) -
          ∑ b : CorrectionsFrom f,
            (2 * correctedI e b.1 + correctedD e b.1 +
              OccurrenceSettlement.boundary
                (Pr e)
                (fun i => r e f i
                  (correctionEquivEndpointAtom f b).1)
                (fun i => neighborU e f i
                  (correctionEquivEndpointAtom f b).1)
                (fun i => neighborV e f i
                  (correctionEquivEndpointAtom f b).1))) := by
      apply Fintype.sum_congr
      exact hpoint
    _ =
        ∑ e : RelevantEdge T₁,
          (2 * (2 * ordinaryI e f + ordinaryD e f) -
            ∑ b : CorrectionsFrom f,
              (2 * correctedI e b.1 + correctedD e b.1)) := by
      exact cancel_two_boundary_sums
        (fun e : RelevantEdge T₁ =>
          2 * ordinaryI e f + ordinaryD e f)
        (fun e : RelevantEdge T₁ =>
          OccurrenceSettlement.boundary
            (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f))
        (fun e : RelevantEdge T₁ => fun b : CorrectionsFrom f =>
          2 * correctedI e b.1 + correctedD e b.1)
        (fun e : RelevantEdge T₁ => fun b : CorrectionsFrom f =>
          OccurrenceSettlement.boundary
            (Pr e)
            (fun i => r e f i
              (correctionEquivEndpointAtom f b).1)
            (fun i => neighborU e f i
              (correctionEquivEndpointAtom f b).1)
            (fun i => neighborV e f i
              (correctionEquivEndpointAtom f b).1))
        hord hcorr
    _ = ∑ e : RelevantEdge T₁, settledChart e f := by
      apply Fintype.sum_congr
      intro e
      exact (settledChart_eq_retained e f).symm

theorem global_fourLevel_eq_directRow :
    (∑ e : RelevantEdge T₁, ∑ f : RelevantEdge T₂,
      fourLevelChart e f) =
      ∑ e : RelevantEdge T₁, ∑ f : RelevantEdge T₂,
        settledChart e f := by
  rw [Finset.sum_comm]
  rw [Finset.sum_comm
    (f := fun e : RelevantEdge T₁ =>
      fun f : RelevantEdge T₂ => settledChart e f)]
  apply Fintype.sum_congr
  intro f
  exact sum_fourLevel_fixed_column f

end

end ConcreteRowSettlement

end QuartetV060
