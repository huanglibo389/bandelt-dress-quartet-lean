import QuartetV060.ConcreteRowSettlement

/-!
# Concrete endpoint-face reversal and completed-package data

This file formalizes the column-reversal interfaces used in
`(A.29e)`--`(A.29f)`.  All coefficients are attached to actual ordered
adjacent corrections.  Reversal swaps the concrete taxon blocks `K` and `L`;
no equality of complete fixed-chart subtotals is asserted.
-/

namespace QuartetV060

namespace ConcretePackageSettlement

open scoped BigOperators

open QuartetDistance
open PhyloOccurrences
open PhyloBridgeReversal
open PrincipalBranches
open PrincipalAtoms
open PrincipalChart
open LocalCoordinates
open ConcreteRetainedSquares
open ConcreteDeterminantLevels
open ConcreteOccurrenceSettlement
open ConcreteRowSettlement

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

variable
    {T₁ T₂ : Tree.PhyloTree X}

/-! ## Row and column taxon-block representatives -/

def rowOppositeBlock
    (e : RelevantEdge T₁) (i : Atom e) : Finset X :=
  aggregateBlock e ((fourSector e).oppositeSideBlock i)

def rowAtomBlock
    (e : RelevantEdge T₁) (i : Atom e) : Finset X :=
  block e i

def correctionZI
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) : ℚ :=
  centeredTaxonBlock (rowOppositeBlock e i) (correctionL a)

def correctionWI
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) : ℚ :=
  centeredTaxonBlock (rowOppositeBlock e i) (correctionK a)

def correctionZD
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) : ℚ :=
  centeredTaxonBlock (rowOppositeBlock e i) (correctionL a) +
    centeredTaxonBlock (rowAtomBlock e i) (correctionL a)

def correctionWD
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) : ℚ :=
  centeredTaxonBlock (rowOppositeBlock e i) (correctionK a) +
    centeredTaxonBlock (rowAtomBlock e i) (correctionK a)

theorem correctionZI_eq_chart
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionZI e i a =
      ZI e (first a) i (selectedColumnAtom a) := by
  unfold correctionZI rowOppositeBlock ZI
  rw [← aggregateBlock_opposite_selected_eq_correctionL a]
  exact
    centeredTaxonBlock_aggregateBlock
      e (first a)
      ((fourSector e).oppositeSideBlock i)
      ((fourSector (first a)).oppositeSideBlock
        (selectedColumnAtom a))

theorem correctionWI_eq_chart
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionWI e i a =
      WI e (first a) i (selectedColumnAtom a) := by
  unfold correctionWI rowOppositeBlock WI
  rw [← aggregateBlock_selected_singleton_eq_correctionK a]
  exact
    centeredTaxonBlock_aggregateBlock
      e (first a)
      ((fourSector e).oppositeSideBlock i)
      ({selectedColumnAtom a} :
        Finset (Atom (first a)))

theorem correctionZD_eq_chart
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionZD e i a =
      ZD e (first a) i (selectedColumnAtom a) := by
  have hrow : block e i = aggregateBlock e {i} := by
    ext x
    rw [mem_aggregateBlock_iff, mem_block_iff_atomAt_eq]
    simp
  unfold correctionZD rowOppositeBlock rowAtomBlock ZD
  rw [← aggregateBlock_opposite_selected_eq_correctionL a]
  rw [hrow]
  rw [centeredTaxonBlock_aggregateBlock]
  rw [centeredTaxonBlock_aggregateBlock]
  rw [xOpp_eq_rectangle]
  rfl

theorem correctionWD_eq_chart
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionWD e i a =
      WD e (first a) i (selectedColumnAtom a) := by
  have hrow : block e i = aggregateBlock e {i} := by
    ext x
    rw [mem_aggregateBlock_iff, mem_block_iff_atomAt_eq]
    simp
  unfold correctionWD rowOppositeBlock rowAtomBlock WD
  rw [← aggregateBlock_selected_singleton_eq_correctionK a]
  rw [hrow]
  rw [centeredTaxonBlock_aggregateBlock]
  rw [centeredTaxonBlock_aggregateBlock]
  rw [xSame_eq_rectangle]
  rfl

@[simp] theorem correctionZI_reverse
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionZI e i (reverseCorrection a) =
      correctionWI e i a := by
  simp [correctionZI, correctionWI]

@[simp] theorem correctionWI_reverse
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionWI e i (reverseCorrection a) =
      correctionZI e i a := by
  simp [correctionZI, correctionWI]

@[simp] theorem correctionZD_reverse
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionZD e i (reverseCorrection a) =
      correctionWD e i a := by
  simp [correctionZD, correctionWD]

@[simp] theorem correctionWD_reverse
    (e : RelevantEdge T₁) (i : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionWD e i (reverseCorrection a) =
      correctionZD e i a := by
  simp [correctionZD, correctionWD]

/-! ## Coefficients of the endpoint square and mixed faces -/

def endpointRi (d : CompletedSquares.EndpointData) : ℝ :=
  (1 / 2 : ℝ) * (d.aiK / d.cK + d.aiB / d.cB)

def endpointRj (d : CompletedSquares.EndpointData) : ℝ :=
  (1 / 2 : ℝ) * (d.ajK / d.cK + d.ajB / d.cB)

def firstFaceCoeff (d : CompletedSquares.EndpointData) : ℝ :=
  d.cK ^ 2 * endpointRi d * endpointRj d

def mixedFaceCoeff (d : CompletedSquares.EndpointData) : ℝ :=
  2 * d.cK * d.cB * endpointRi d * endpointRj d

def secondFaceCoeff (d : CompletedSquares.EndpointData) : ℝ :=
  d.cB ^ 2 * endpointRi d * endpointRj d

@[simp] theorem endpointRi_reverse
    (d : CompletedSquares.EndpointData) :
    endpointRi d.reverse = endpointRi d := by
  unfold endpointRi CompletedSquares.EndpointData.reverse
  dsimp
  ring

@[simp] theorem endpointRj_reverse
    (d : CompletedSquares.EndpointData) :
    endpointRj d.reverse = endpointRj d := by
  unfold endpointRj CompletedSquares.EndpointData.reverse
  dsimp
  ring

theorem firstFaceCoeff_reverse
    (d : CompletedSquares.EndpointData) :
    firstFaceCoeff d.reverse = secondFaceCoeff d := by
  simp [firstFaceCoeff, secondFaceCoeff]

theorem secondFaceCoeff_reverse
    (d : CompletedSquares.EndpointData) :
    secondFaceCoeff d.reverse = firstFaceCoeff d := by
  simp [firstFaceCoeff, secondFaceCoeff]

theorem mixedFaceCoeff_reverse
    (d : CompletedSquares.EndpointData) :
    mixedFaceCoeff d.reverse = mixedFaceCoeff d := by
  unfold mixedFaceCoeff
  rw [endpointRi_reverse, endpointRj_reverse]
  simp only [CompletedSquares.EndpointData.reverse_cK,
    CompletedSquares.EndpointData.reverse_cB]
  ring

theorem endpointRi_refinement
    (d : CompletedSquares.EndpointData)
    (hK : d.cK ≠ 0) (hB : d.cB ≠ 0) :
    2 * d.cK * endpointRi d =
      d.aiK + d.cK / d.cB * d.aiB := by
  unfold endpointRi
  field_simp [hK, hB]

theorem endpointRj_refinement
    (d : CompletedSquares.EndpointData)
    (hK : d.cK ≠ 0) (hB : d.cB ≠ 0) :
    2 * d.cK * endpointRj d =
      d.ajK + d.cK / d.cB * d.ajB := by
  unfold endpointRj
  field_simp [hK, hB]

theorem packageCoeff_xy_eq_mixedFaceCoeff
    (d : CompletedSquares.EndpointData)
    (hK : d.cK ≠ 0) (hB : d.cB ≠ 0) :
    d.packageCoeff.xy = mixedFaceCoeff d := by
  exact d.packageCoeff_xy
    (endpointRi d) (endpointRj d)
    hK hB
    (endpointRi_refinement d hK hB)
    (endpointRj_refinement d hK hB)

/-! ## Identification with the source chart -/

theorem endpointRi_eq_r
    (e : RelevantEdge T₁) (a : AdjacentCorrection T₂)
    (i j : Atom e) :
    endpointRi (ConcreteBridgeLedger.endpointData e a i j) =
      (r e (first a) i (selectedColumnAtom a) : ℝ) := by
  rw [ConcreteBridgeLedger.endpointData_eq_chartEndpointData]
  unfold endpointRi ConcreteBridgeLedger.chartEndpointData
  dsimp [selectedColumnAtom]
  unfold r J Fc JointMass.symmetricRowCoefficient
  push_cast
  ring

theorem endpointRj_eq_r
    (e : RelevantEdge T₁) (a : AdjacentCorrection T₂)
    (i j : Atom e) :
    endpointRj (ConcreteBridgeLedger.endpointData e a i j) =
      (r e (first a) j (selectedColumnAtom a) : ℝ) := by
  rw [ConcreteBridgeLedger.endpointData_eq_chartEndpointData]
  unfold endpointRj ConcreteBridgeLedger.chartEndpointData
  dsimp [selectedColumnAtom]
  unfold r J Fc JointMass.symmetricRowCoefficient
  push_cast
  ring

theorem firstFaceCoeff_eq_chart
    (e : RelevantEdge T₁) (a : AdjacentCorrection T₂)
    (i j : Atom e) :
    firstFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) =
      ((c e (first a) (selectedColumnAtom a) ^ 2 *
        r e (first a) i (selectedColumnAtom a) *
        r e (first a) j (selectedColumnAtom a) : ℚ) : ℝ) := by
  unfold firstFaceCoeff
  rw [endpointRi_eq_r, endpointRj_eq_r]
  rw [ConcreteBridgeLedger.endpointData_eq_chartEndpointData]
  unfold ConcreteBridgeLedger.chartEndpointData c J
  dsimp [selectedColumnAtom]
  norm_cast

theorem secondFaceCoeff_eq_chart
    (e : RelevantEdge T₁) (a : AdjacentCorrection T₂)
    (i j : Atom e) :
    secondFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) =
      ((cbar e (first a) (selectedColumnAtom a) ^ 2 *
        r e (first a) i (selectedColumnAtom a) *
        r e (first a) j (selectedColumnAtom a) : ℚ) : ℝ) := by
  unfold secondFaceCoeff
  rw [endpointRi_eq_r, endpointRj_eq_r]
  rw [ConcreteBridgeLedger.endpointData_eq_chartEndpointData]
  unfold ConcreteBridgeLedger.chartEndpointData cbar J Fc
  dsimp [selectedColumnAtom]
  norm_cast

theorem mixedFaceCoeff_eq_chart
    (e : RelevantEdge T₁) (a : AdjacentCorrection T₂)
    (i j : Atom e) :
    mixedFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) =
      ((2 * c e (first a) (selectedColumnAtom a) *
        cbar e (first a) (selectedColumnAtom a) *
        r e (first a) i (selectedColumnAtom a) *
        r e (first a) j (selectedColumnAtom a) : ℚ) : ℝ) := by
  unfold mixedFaceCoeff
  rw [endpointRi_eq_r, endpointRj_eq_r]
  rw [ConcreteBridgeLedger.endpointData_eq_chartEndpointData]
  unfold ConcreteBridgeLedger.chartEndpointData c cbar J Fc
  dsimp [selectedColumnAtom]
  norm_cast

theorem packageCoeff_xy_eq_chart
    (e : RelevantEdge T₁) (a : AdjacentCorrection T₂)
    (i j : Atom e) :
    (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy =
      ((2 * c e (first a) (selectedColumnAtom a) *
        cbar e (first a) (selectedColumnAtom a) *
        r e (first a) i (selectedColumnAtom a) *
        r e (first a) j (selectedColumnAtom a) : ℚ) : ℝ) := by
  rw [packageCoeff_xy_eq_mixedFaceCoeff
    (ConcreteBridgeLedger.endpointData e a i j)
    (ne_of_gt (ConcreteBridgeLedger.endpointData_cK_pos e a i j))
    (ne_of_gt (ConcreteBridgeLedger.endpointData_cB_pos e a i j))]
  exact mixedFaceCoeff_eq_chart e a i j

/-! ## Exact endpoint-face cancellation `(A.29e)` -/

theorem endpoint_faces_I_eq_zero
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ a : AdjacentCorrection T₂,
      (firstFaceCoeff
          (ConcreteBridgeLedger.endpointData e a i j) *
            (correctionZI e i a : ℝ) ^ 2 -
        secondFaceCoeff
          (ConcreteBridgeLedger.endpointData e a i j) *
            (correctionWI e i a : ℝ) ^ 2)) = 0 := by
  apply PackageLedger.sum_endpoint_signed_eq_zero
    (ConcreteBridgeLedger.reversalEquiv T₂)
    (fun a =>
      firstFaceCoeff
        (ConcreteBridgeLedger.endpointData e a i j))
    (fun a =>
      secondFaceCoeff
        (ConcreteBridgeLedger.endpointData e a i j))
    (fun a => (correctionZI e i a : ℝ))
    (fun a => (correctionWI e i a : ℝ))
  · intro a
    simp only [ConcreteBridgeLedger.reversalEquiv_apply]
    rw [ConcreteBridgeLedger.endpointData_reverse]
    exact firstFaceCoeff_reverse
      (ConcreteBridgeLedger.endpointData e a i j)
  · intro a
    simp only [ConcreteBridgeLedger.reversalEquiv_apply]
    rw [correctionZI_reverse]

theorem endpoint_faces_D_eq_zero
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ a : AdjacentCorrection T₂,
      (firstFaceCoeff
          (ConcreteBridgeLedger.endpointData e a i j) *
            (correctionZD e i a : ℝ) ^ 2 -
        secondFaceCoeff
          (ConcreteBridgeLedger.endpointData e a i j) *
            (correctionWD e i a : ℝ) ^ 2)) = 0 := by
  apply PackageLedger.sum_endpoint_signed_eq_zero
    (ConcreteBridgeLedger.reversalEquiv T₂)
    (fun a =>
      firstFaceCoeff
        (ConcreteBridgeLedger.endpointData e a i j))
    (fun a =>
      secondFaceCoeff
        (ConcreteBridgeLedger.endpointData e a i j))
    (fun a => (correctionZD e i a : ℝ))
    (fun a => (correctionWD e i a : ℝ))
  · intro a
    simp only [ConcreteBridgeLedger.reversalEquiv_apply]
    rw [ConcreteBridgeLedger.endpointData_reverse]
    exact firstFaceCoeff_reverse
      (ConcreteBridgeLedger.endpointData e a i j)
  · intro a
    simp only [ConcreteBridgeLedger.reversalEquiv_apply]
    rw [correctionZD_reverse]

/-! ## Completed-package extraction `(A.29f)` -/

def availableCoefficient
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) : ℝ :=
  ((∑ z ∈ (Pc f).I ∪ (Pc f).D,
      if z.1 = u then
        c e f z.1 * c e f z.2 *
          r e f i z.1 * r e f j z.2
      else 0 : ℚ) : ℝ)

def correctionAvailableCoefficient
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) : ℝ :=
  availableCoefficient e (first a) i j (selectedColumnAtom a)

def packageI
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) : ℝ :=
  (ConcreteBridgeLedger.endpointData e a i j).package
    (correctionZI e i a) (correctionWI e i a)

def packageD
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) : ℝ :=
  (ConcreteBridgeLedger.endpointData e a i j).package
    (correctionZD e i a) (correctionWD e i a)

theorem packageI_eq_eval
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) :
    packageI e i j a =
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.eval
        (correctionZI e i a) (correctionWI e i a) := by
  unfold packageI
  exact
    (ConcreteBridgeLedger.endpointData e a i j).package_eq_eval
      (ConcreteBridgeLedger.endpointData_cK_pos e a i j)
      (ConcreteBridgeLedger.endpointData_cK_lt_one e a i j)
      (ConcreteBridgeLedger.endpointData_cB_pos e a i j)
      (ConcreteBridgeLedger.endpointData_cKplus_pos e a i j)
      _ _

theorem packageD_eq_eval
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) :
    packageD e i j a =
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.eval
        (correctionZD e i a) (correctionWD e i a) := by
  unfold packageD
  exact
    (ConcreteBridgeLedger.endpointData e a i j).package_eq_eval
      (ConcreteBridgeLedger.endpointData_cK_pos e a i j)
      (ConcreteBridgeLedger.endpointData_cK_lt_one e a i j)
      (ConcreteBridgeLedger.endpointData_cB_pos e a i j)
      (ConcreteBridgeLedger.endpointData_cKplus_pos e a i j)
      _ _

theorem global_package_extraction_I
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ a : AdjacentCorrection T₂,
      (2 * correctionAvailableCoefficient e i j a *
          (correctionZI e i a : ℝ) ^ 2 +
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
          correctionZI e i a * correctionWI e i a)) =
      ∑ a : AdjacentCorrection T₂,
        (packageI e i j a +
          2 * (correctionAvailableCoefficient e i j a -
            (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx) *
            (correctionZI e i a : ℝ) ^ 2) := by
  apply PackageLedger.global_package_extraction
    (ConcreteBridgeLedger.reversalEquiv T₂)
    (correctionAvailableCoefficient e i j)
    (fun a =>
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx)
    (fun a =>
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.yy)
    (fun a =>
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy)
    (packageI e i j)
    (fun a => (correctionZI e i a : ℝ))
    (fun a => (correctionWI e i a : ℝ))
  · intro a
    simpa [CompletedSquares.QuadraticCoeff.eval] using
      packageI_eq_eval e i j a
  · intro a
    exact ConcreteBridgeLedger.package_second_eq_reversed_first
      e a i j
  · intro a
    simp only [ConcreteBridgeLedger.reversalEquiv_apply]
    rw [correctionZI_reverse]

theorem global_package_extraction_D
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ a : AdjacentCorrection T₂,
      (2 * correctionAvailableCoefficient e i j a *
          (correctionZD e i a : ℝ) ^ 2 +
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
          correctionZD e i a * correctionWD e i a)) =
      ∑ a : AdjacentCorrection T₂,
        (packageD e i j a +
          2 * (correctionAvailableCoefficient e i j a -
            (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx) *
            (correctionZD e i a : ℝ) ^ 2) := by
  apply PackageLedger.global_package_extraction
    (ConcreteBridgeLedger.reversalEquiv T₂)
    (correctionAvailableCoefficient e i j)
    (fun a =>
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx)
    (fun a =>
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.yy)
    (fun a =>
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy)
    (packageD e i j)
    (fun a => (correctionZD e i a : ℝ))
    (fun a => (correctionWD e i a : ℝ))
  · intro a
    simpa [CompletedSquares.QuadraticCoeff.eval] using
      packageD_eq_eval e i j a
  · intro a
    exact ConcreteBridgeLedger.package_second_eq_reversed_first
      e a i j
  · intro a
    simp only [ConcreteBridgeLedger.reversalEquiv_apply]
    rw [correctionZD_reverse]

end

end ConcretePackageSettlement

end QuartetV060
