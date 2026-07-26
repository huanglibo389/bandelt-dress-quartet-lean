import QuartetV060.ConcreteDeterminantLevels
import QuartetV060.ConcreteBridgeLedger

/-!
# Concrete occurrence settlement and row-boundary cancellation

This file instantiates `(A.29c₀)`--`(A.29c₂)` on the actual taxon blocks of
the two trees.  The column occurrence is held fixed.  Its weight and centered
form are defined directly on taxon blocks, independently of the row
principal edge.  Consequently the row-boundary polynomial is a sum over the
complete type of ordered adjacent row bridges and cancels under the concrete
reversal `(K,H,L) ↦ (L,H,K)`.
-/

namespace QuartetV060

namespace ConcreteOccurrenceSettlement

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

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

variable
    {T₁ T₂ : Tree.PhyloTree X}

/-- Normalized mass of a taxon block in one column atom. -/
def taxonProfile
    (f : RelevantEdge T₂) (A : Finset X) (k : Atom f) : ℚ :=
  normalizedCard (A ∩ block f k)

/-- Normalized mass of a taxon block in the opposite-side column block. -/
def taxonOppositeProfile
    (f : RelevantEdge T₂) (A : Finset X) (k : Atom f) : ℚ :=
  normalizedCard
    (A ∩ aggregateBlock f ((fourSector f).oppositeSideBlock k))

/-- The column atom mass, written without reference to any row chart. -/
def columnAtomMass
    (f : RelevantEdge T₂) (k : Atom f) : ℚ :=
  normalizedCard (block f k)

/-- The full opposite-side mass, also independent of the row chart. -/
def columnOppositeMass
    (f : RelevantEdge T₂) (k : Atom f) : ℚ :=
  normalizedCard
    (aggregateBlock f ((fourSector f).oppositeSideBlock k))

/-- The symmetric coefficient of an arbitrary actual taxon block. -/
def symmetricTaxonWeight
    (f : RelevantEdge T₂) (A : Finset X) (k : Atom f) : ℚ :=
  (1 / 2 : ℚ) *
    (taxonProfile f A k / columnAtomMass f k +
      taxonOppositeProfile f A k / columnOppositeMass f k)

/-- The ordinary-column block weight `w^{τ_f}(A)`. -/
def ordinaryBlockWeight
    (f : RelevantEdge T₂) (A : Finset X) : ℚ :=
  ∑ k, columnAtomMass f k * symmetricTaxonWeight f A k

/-- Centered normalized mass of two actual taxon blocks. -/
def centeredTaxonBlock (A B : Finset X) : ℚ :=
  normalizedCard (A ∩ B) - normalizedCard A * normalizedCard B

/-- The ordinary-column block form, oriented to the representative
`bar k` side chosen in the principal chart. -/
def ordinaryBlockForm
    (f : RelevantEdge T₂) (A : Finset X) : ℚ :=
  centeredTaxonBlock A (columnSplit f).side

/-- The endpoint atom selected by a corrected column occurrence. -/
def selectedColumnAtom
    (b : AdjacentCorrection T₂) : Atom (first b) :=
  endpointAtom (first b) (correctionSlot b)

/-- The corrected-column block weight `w^{C_{f,h}}(A)=r_A^k`. -/
def correctedBlockWeight
    (b : AdjacentCorrection T₂) (A : Finset X) : ℚ :=
  symmetricTaxonWeight (first b) A (selectedColumnAtom b)

/-- The corrected-column block form
`c_k x_{A,bar k}-c_{bar k}x_{A,k}`. -/
def correctedBlockForm
    (b : AdjacentCorrection T₂) (A : Finset X) : ℚ :=
  normalizedCard (correctionK b) *
      centeredTaxonBlock A (correctionL b) -
    normalizedCard (correctionL b) *
      centeredTaxonBlock A (correctionK b)

theorem columnAtomMass_eq_c
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) (k : Atom f) :
    columnAtomMass f k = c e f k := by
  unfold columnAtomMass c J
  rw [jointMass_colMass_eq]
  rfl

theorem columnOppositeMass_eq_cbar
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) (k : Atom f) :
    columnOppositeMass f k = cbar e f k := by
  unfold columnOppositeMass cbar J Fc
  rw [jointMass_colBlockMass_eq]
  rfl

/-- An aggregate row block has exactly the profile obtained by summing its
principal-chart rows. -/
theorem taxonProfile_aggregateBlock
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) (k : Atom f) :
    taxonProfile f (aggregateBlock e V) k =
      rowProfile e f V k := by
  have h :=
    rowProfile_rectangleMass e f V ({k} : Finset (Atom f))
  simpa [taxonProfile, TwoSide.blockSum, rowProfile,
    aggregateBlock] using h.symm

theorem taxonOppositeProfile_aggregateBlock
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) (k : Atom f) :
    taxonOppositeProfile f (aggregateBlock e V) k =
      TwoSide.blockSum (rowProfile e f V)
        ((columnSides f).oppositeBlock k) := by
  have h :=
    rowProfile_rectangleMass e f V
      ((columnSides f).oppositeBlock k)
  rw [columnSides_oppositeBlock] at h
  rw [columnSides_oppositeBlock]
  simpa [taxonOppositeProfile] using h.symm

/-- The taxon-block coefficient agrees with the sum of the concrete
coefficients of its row atoms. -/
theorem symmetricTaxonWeight_aggregateBlock
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) (k : Atom f) :
    symmetricTaxonWeight f (aggregateBlock e V) k =
      ∑ i ∈ V, r e f i k := by
  calc
    symmetricTaxonWeight f (aggregateBlock e V) k =
        (columnSides f).symmetricCoefficient
          (c e f) (rowProfile e f V) k := by
      unfold symmetricTaxonWeight TwoSide.symmetricCoefficient
      rw [taxonProfile_aggregateBlock e f V k]
      rw [taxonOppositeProfile_aggregateBlock e f V k]
      rw [columnAtomMass_eq_c e f k]
      rw [columnOppositeMass_eq_cbar e f k]
      unfold cbar
      rw [columnSides_oppositeBlock]
      rw [c_blockSum]
      simp [J, Fc]
    _ = ∑ i ∈ V, r e f i k :=
      symmetricCoefficient_rowProfile e f V k

theorem ordinaryBlockWeight_aggregateBlock
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) :
    ordinaryBlockWeight f (aggregateBlock e V) =
      ∑ i ∈ V, omega e f i := by
  unfold ordinaryBlockWeight omega alpha
  simp_rw [columnAtomMass_eq_c e f]
  simp_rw [symmetricTaxonWeight_aggregateBlock e f V]
  calc
    (∑ k : Atom f, c e f k * ∑ i ∈ V, r e f i k) =
        ∑ k : Atom f, ∑ i ∈ V, c e f k * r e f i k := by
      apply Fintype.sum_congr
      intro k
      rw [Finset.mul_sum]
    _ = ∑ i ∈ V, ∑ k : Atom f, c e f k * r e f i k := by
      rw [Finset.sum_comm]

theorem centeredTaxonBlock_aggregateBlock
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) (U : Finset (Atom f)) :
    centeredTaxonBlock
        (aggregateBlock e V) (aggregateBlock f U) =
      (jointMass e f).centeredRectangleMass V U := by
  unfold centeredTaxonBlock
  symm
  exact jointMass_centeredRectangleMass_eq e f V U

theorem ordinaryBlockForm_aggregateBlock
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (V : Finset (Atom e)) :
    ordinaryBlockForm f (aggregateBlock e V) =
      (jointMass e f).centeredRectangleMass V (columnSides f).B := by
  unfold ordinaryBlockForm
  rw [← aggregateBlock_columnSides_B f]
  exact centeredTaxonBlock_aggregateBlock e f V (columnSides f).B

theorem ordinaryBlockWeight_selected
    (a : AdjacentCorrection T₁) (f : RelevantEdge T₂) :
    ordinaryBlockWeight f (correctionK a) =
      let i := selectedColumnAtom a
      omega (first a) f i := by
  dsimp [selectedColumnAtom]
  rw [← aggregateBlock_selected_singleton_eq_correctionK a]
  rw [ordinaryBlockWeight_aggregateBlock]
  simp

theorem ordinaryBlockWeight_opposite
    (a : AdjacentCorrection T₁) (f : RelevantEdge T₂) :
    ordinaryBlockWeight f (correctionL a) =
      let i := selectedColumnAtom a
      (Pr (first a)).oppositeWeight (omega (first a) f) i := by
  dsimp [selectedColumnAtom]
  rw [← aggregateBlock_opposite_selected_eq_correctionL a]
  rw [ordinaryBlockWeight_aggregateBlock]
  rfl

theorem ordinaryBlockForm_selected
    (a : AdjacentCorrection T₁) (f : RelevantEdge T₂) :
    ordinaryBlockForm f (correctionK a) =
      let i := selectedColumnAtom a
      ordinaryY (first a) f i := by
  dsimp [selectedColumnAtom]
  rw [← aggregateBlock_selected_singleton_eq_correctionK a]
  rw [ordinaryBlockForm_aggregateBlock]
  simpa using
    (ordinaryY_eq_centeredRectangle
      (first a) f
      (endpointAtom (first a) (correctionSlot a))).symm

theorem ordinaryBlockForm_opposite
    (a : AdjacentCorrection T₁) (f : RelevantEdge T₂) :
    ordinaryBlockForm f (correctionL a) =
      let i := selectedColumnAtom a
      ordinaryX (first a) f i := by
  dsimp [selectedColumnAtom]
  rw [← aggregateBlock_opposite_selected_eq_correctionL a]
  rw [ordinaryBlockForm_aggregateBlock]
  simpa using
    (ordinaryX_eq_centeredRectangle
      (first a) f
      (endpointAtom (first a) (correctionSlot a))).symm

theorem correctedBlockWeight_aggregateBlock
    (e : RelevantEdge T₁) (b : AdjacentCorrection T₂)
    (V : Finset (Atom e)) :
    correctedBlockWeight b (aggregateBlock e V) =
      ∑ i ∈ V, r e (first b) i (selectedColumnAtom b) := by
  exact symmetricTaxonWeight_aggregateBlock
    e (first b) V (selectedColumnAtom b)

theorem correctedBlockForm_aggregateBlock
    (e : RelevantEdge T₁) (b : AdjacentCorrection T₂)
    (V : Finset (Atom e)) :
    correctedBlockForm b (aggregateBlock e V) =
      c e (first b) (selectedColumnAtom b) *
          (jointMass e (first b)).centeredRectangleMass V
            ((fourSector (first b)).oppositeSideBlock
              (selectedColumnAtom b)) -
        cbar e (first b) (selectedColumnAtom b) *
          (jointMass e (first b)).centeredRectangleMass V
            {selectedColumnAtom b} := by
  have hK :
      correctionK b =
        aggregateBlock (first b) {selectedColumnAtom b} := by
    exact (aggregateBlock_selected_singleton_eq_correctionK b).symm
  have hL :
      correctionL b =
        aggregateBlock (first b)
          ((fourSector (first b)).oppositeSideBlock
            (selectedColumnAtom b)) := by
    exact
      (aggregateBlock_opposite_selected_eq_correctionL b).symm
  unfold correctedBlockForm
  rw [hK, hL]
  rw [← centeredTaxonBlock_aggregateBlock e (first b) V]
  rw [← centeredTaxonBlock_aggregateBlock e (first b) V]
  rw [← columnAtomMass_eq_c e (first b) (selectedColumnAtom b)]
  rw [← columnOppositeMass_eq_cbar e (first b)
    (selectedColumnAtom b)]
  unfold columnAtomMass columnOppositeMass
  simp [aggregateBlock]

theorem correctedBlockWeight_selected
    (a : AdjacentCorrection T₁) (b : AdjacentCorrection T₂) :
    correctedBlockWeight b (correctionK a) =
      let i := selectedColumnAtom a
      r (first a) (first b) i (selectedColumnAtom b) := by
  dsimp
  rw [← aggregateBlock_selected_singleton_eq_correctionK a]
  rw [correctedBlockWeight_aggregateBlock]
  simp [selectedColumnAtom]

theorem correctedBlockWeight_opposite
    (a : AdjacentCorrection T₁) (b : AdjacentCorrection T₂) :
    correctedBlockWeight b (correctionL a) =
      let i := selectedColumnAtom a
      (Pr (first a)).oppositeWeight
        (fun j => r (first a) (first b) j (selectedColumnAtom b)) i := by
  dsimp
  rw [← aggregateBlock_opposite_selected_eq_correctionL a]
  rw [correctedBlockWeight_aggregateBlock]
  simp [selectedColumnAtom]
  unfold Pr residualPartition ResidualPartition.oppositeWeight
  rfl

theorem correctedBlockForm_selected
    (a : AdjacentCorrection T₁) (b : AdjacentCorrection T₂) :
    correctedBlockForm b (correctionK a) =
      let i := selectedColumnAtom a
      neighborV (first a) (first b) i (selectedColumnAtom b) := by
  dsimp
  rw [← aggregateBlock_selected_singleton_eq_correctionK a]
  rw [correctedBlockForm_aggregateBlock]
  simp only [selectedColumnAtom]
  unfold neighborV RetainedSquares.neighboringV cbar
  rw [xOpp_eq_rectangle, xSame_eq_rectangle]
  simp [J, Fc]

theorem correctedBlockForm_opposite
    (a : AdjacentCorrection T₁) (b : AdjacentCorrection T₂) :
    correctedBlockForm b (correctionL a) =
      let i := selectedColumnAtom a
      neighborU (first a) (first b) i (selectedColumnAtom b) := by
  dsimp
  rw [← aggregateBlock_opposite_selected_eq_correctionL a]
  rw [correctedBlockForm_aggregateBlock]
  simp only [selectedColumnAtom]
  unfold neighborU RetainedSquares.neighboringU cbar
  unfold xBarOpp xBarSame Fr
  simp [J, Fc]

noncomputable instance correctionsFromFintype
    {T : Tree.PhyloTree X} (e : RelevantEdge T) :
    Fintype (CorrectionsFrom e) :=
  Fintype.subtype
    (Finset.univ.filter fun a : AdjacentCorrection T => first a = e)
    (by intro a; simp)

noncomputable instance endpointAtomIndexFintype
    {T : Tree.PhyloTree X} (e : RelevantEdge T) :
    Fintype (EndpointAtomIndex e) :=
  Fintype.subtype
    (Finset.univ.filter fun i : Atom e =>
      (fourSector e).isEndpoint i)
    (by intro i; simp)

/-- The total type of fixed-first-edge correction fibers is equivalent to
the complete ordered adjacent-correction range. -/
noncomputable def sigmaCorrectionsEquiv
    (T : Tree.PhyloTree X) :
    (Σ e : RelevantEdge T, CorrectionsFrom e) ≃
      AdjacentCorrection T where
  toFun z := z.2.1
  invFun a := ⟨first a, ⟨a, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨e, a, ha⟩
    subst e
    rfl
  right_inv a := rfl

theorem sum_corrections_by_source
    {T : Tree.PhyloTree X}
    (g : AdjacentCorrection T → ℚ) :
    (∑ e : RelevantEdge T, ∑ a : CorrectionsFrom e, g a.1) =
      ∑ a : AdjacentCorrection T, g a := by
  calc
    (∑ e : RelevantEdge T, ∑ a : CorrectionsFrom e, g a.1) =
        ∑ z : Σ e : RelevantEdge T, CorrectionsFrom e, g z.2.1 := by
      symm
      exact Fintype.sum_sigma
        (fun z : Σ e : RelevantEdge T, CorrectionsFrom e => g z.2.1)
    _ = ∑ a : AdjacentCorrection T, g a :=
      (sigmaCorrectionsEquiv T).sum_comp g

/-- One ordinary-column endpoint boundary is literally the concrete bridge
boundary contribution of its selected and opposite taxon blocks. -/
theorem ordinary_boundary_term_eq
    (a : AdjacentCorrection T₁) (f : RelevantEdge T₂) :
    let i := selectedColumnAtom a
    (omega (first a) f i +
        (Pr (first a)).oppositeWeight (omega (first a) f) i) *
      (omega (first a) f i * ordinaryX (first a) f i ^ 2 -
        (Pr (first a)).oppositeWeight (omega (first a) f) i *
          ordinaryY (first a) f i ^ 2) =
      ConcreteBridgeLedger.boundaryContribution
        (ordinaryBlockWeight f) (ordinaryBlockForm f) a := by
  dsimp
  unfold ConcreteBridgeLedger.boundaryContribution
  rw [ordinaryBlockWeight_selected a f]
  rw [ordinaryBlockWeight_opposite a f]
  rw [ordinaryBlockForm_opposite a f]
  rw [ordinaryBlockForm_selected a f]

/-- One corrected-column endpoint boundary is likewise the concrete bridge
boundary contribution for the fixed corrected column occurrence. -/
theorem corrected_boundary_term_eq
    (a : AdjacentCorrection T₁) (b : AdjacentCorrection T₂) :
    let i := selectedColumnAtom a
    let k := selectedColumnAtom b
    (r (first a) (first b) i k +
        (Pr (first a)).oppositeWeight
          (fun j => r (first a) (first b) j k) i) *
      (r (first a) (first b) i k *
          neighborU (first a) (first b) i k ^ 2 -
        (Pr (first a)).oppositeWeight
            (fun j => r (first a) (first b) j k) i *
          neighborV (first a) (first b) i k ^ 2) =
      ConcreteBridgeLedger.boundaryContribution
        (correctedBlockWeight b) (correctedBlockForm b) a := by
  dsimp
  unfold ConcreteBridgeLedger.boundaryContribution
  rw [correctedBlockWeight_selected a b]
  rw [correctedBlockWeight_opposite a b]
  rw [correctedBlockForm_opposite a b]
  rw [correctedBlockForm_selected a b]

/-- Fixed-source version of `ordinary_boundary_term_eq`, with the dependent
atom index transported through the explicit correction/endpoint
equivalence. -/
theorem ordinary_boundary_from_eq
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (a : CorrectionsFrom e) :
    ConcreteBridgeLedger.boundaryContribution
        (ordinaryBlockWeight f) (ordinaryBlockForm f) a.1 =
      let i := (correctionEquivEndpointAtom e a).1
      (omega e f i + (Pr e).oppositeWeight (omega e f) i) *
        (omega e f i * ordinaryX e f i ^ 2 -
          (Pr e).oppositeWeight (omega e f) i *
            ordinaryY e f i ^ 2) := by
  rcases a with ⟨a, ha⟩
  subst e
  symm
  simpa [selectedColumnAtom, correctionEquivEndpointAtom,
      correctionSlot, correctionFromFirst, endpointAtomEquiv] using
    ordinary_boundary_term_eq a f

/-- Fixed-source version of `corrected_boundary_term_eq`. -/
theorem corrected_boundary_from_eq
    (e : RelevantEdge T₁) (b : AdjacentCorrection T₂)
    (a : CorrectionsFrom e) :
    ConcreteBridgeLedger.boundaryContribution
        (correctedBlockWeight b) (correctedBlockForm b) a.1 =
      let i := (correctionEquivEndpointAtom e a).1
      let k := selectedColumnAtom b
      (r e (first b) i k +
          (Pr e).oppositeWeight
            (fun j => r e (first b) j k) i) *
        (r e (first b) i k * neighborU e (first b) i k ^ 2 -
          (Pr e).oppositeWeight
              (fun j => r e (first b) j k) i *
            neighborV e (first b) i k ^ 2) := by
  rcases a with ⟨a, ha⟩
  subst e
  symm
  simpa [selectedColumnAtom, correctionEquivEndpointAtom,
      correctionSlot, correctionFromFirst, endpointAtomEquiv] using
    corrected_boundary_term_eq a b

/-- The ordinary-column row boundary cancels only after all row principal
edges, hence all ordered row bridges, have been summed. -/
theorem sum_ordinary_boundary_eq_zero
    (f : RelevantEdge T₂) :
    (∑ e : RelevantEdge T₁,
      OccurrenceSettlement.boundary
        (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f)) = 0 := by
  calc
    (∑ e : RelevantEdge T₁,
        OccurrenceSettlement.boundary
          (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f)) =
        ∑ e : RelevantEdge T₁, ∑ a : CorrectionsFrom e,
          ConcreteBridgeLedger.boundaryContribution
            (ordinaryBlockWeight f) (ordinaryBlockForm f) a.1 := by
      apply Fintype.sum_congr
      intro e
      unfold OccurrenceSettlement.boundary
      rw [← sum_endpointAtomIndex_eq_endpoint e]
      symm
      exact Fintype.sum_equiv
        (correctionEquivEndpointAtom e)
        (fun a : CorrectionsFrom e =>
          ConcreteBridgeLedger.boundaryContribution
            (ordinaryBlockWeight f) (ordinaryBlockForm f) a.1)
        (fun i : EndpointAtomIndex e =>
          (omega e f i.1 +
              (Pr e).oppositeWeight (omega e f) i.1) *
            (omega e f i.1 * ordinaryX e f i.1 ^ 2 -
              (Pr e).oppositeWeight (omega e f) i.1 *
                ordinaryY e f i.1 ^ 2))
        (fun a => ordinary_boundary_from_eq e f a)
    _ =
        ∑ a : AdjacentCorrection T₁,
          ConcreteBridgeLedger.boundaryContribution
            (ordinaryBlockWeight f) (ordinaryBlockForm f) a := by
      exact sum_corrections_by_source
        (fun a =>
          ConcreteBridgeLedger.boundaryContribution
            (ordinaryBlockWeight f) (ordinaryBlockForm f) a)
    _ = 0 :=
      ConcreteBridgeLedger.sum_boundaryContribution_eq_zero
        (ordinaryBlockWeight f) (ordinaryBlockForm f)

/-- For each fixed corrected column occurrence, its row boundary cancels on
the same complete ordered row-bridge range. -/
theorem sum_corrected_boundary_eq_zero
    (b : AdjacentCorrection T₂) :
    (∑ e : RelevantEdge T₁,
      OccurrenceSettlement.boundary
        (Pr e)
        (fun i => r e (first b) i (selectedColumnAtom b))
        (fun i => neighborU e (first b) i (selectedColumnAtom b))
        (fun i => neighborV e (first b) i (selectedColumnAtom b))) = 0 := by
  calc
    (∑ e : RelevantEdge T₁,
        OccurrenceSettlement.boundary
          (Pr e)
          (fun i => r e (first b) i (selectedColumnAtom b))
          (fun i => neighborU e (first b) i (selectedColumnAtom b))
          (fun i => neighborV e (first b) i (selectedColumnAtom b))) =
        ∑ e : RelevantEdge T₁, ∑ a : CorrectionsFrom e,
          ConcreteBridgeLedger.boundaryContribution
            (correctedBlockWeight b) (correctedBlockForm b) a.1 := by
      apply Fintype.sum_congr
      intro e
      unfold OccurrenceSettlement.boundary
      rw [← sum_endpointAtomIndex_eq_endpoint e]
      symm
      exact Fintype.sum_equiv
        (correctionEquivEndpointAtom e)
        (fun a : CorrectionsFrom e =>
          ConcreteBridgeLedger.boundaryContribution
            (correctedBlockWeight b) (correctedBlockForm b) a.1)
        (fun i : EndpointAtomIndex e =>
          (r e (first b) i.1 (selectedColumnAtom b) +
              (Pr e).oppositeWeight
                (fun j => r e (first b) j (selectedColumnAtom b)) i.1) *
            (r e (first b) i.1 (selectedColumnAtom b) *
                neighborU e (first b) i.1 (selectedColumnAtom b) ^ 2 -
              (Pr e).oppositeWeight
                  (fun j => r e (first b) j (selectedColumnAtom b)) i.1 *
                neighborV e (first b) i.1
                  (selectedColumnAtom b) ^ 2))
        (fun a => corrected_boundary_from_eq e b a)
    _ =
        ∑ a : AdjacentCorrection T₁,
          ConcreteBridgeLedger.boundaryContribution
            (correctedBlockWeight b) (correctedBlockForm b) a := by
      exact sum_corrections_by_source
        (fun a =>
          ConcreteBridgeLedger.boundaryContribution
            (correctedBlockWeight b) (correctedBlockForm b) a)
    _ = 0 :=
      ConcreteBridgeLedger.sum_boundaryContribution_eq_zero
        (correctedBlockWeight b) (correctedBlockForm b)

/-- Concrete `(A.29c₀)` for the ordinary column occurrence. -/
theorem ordinary_twoE_sub_N
    (e : RelevantEdge T₁) (f : RelevantEdge T₂) :
    2 * ordinarySquare e f - ordinaryNeighboring e f =
      2 * OccurrenceSettlement.retainedI
            (Pr e) (omega e f) (ordinaryX e f) +
        OccurrenceSettlement.retainedD
            (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f) +
        OccurrenceSettlement.boundary
            (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f) := by
  exact OccurrenceSettlement.twoE_sub_N
    (Pr e) (omega e f) (ordinaryX e f) (ordinaryY e f)
    (ordinarySquare e f) (sum_omega e f) (ordinaryX_sq e f)

/-- Concrete `(A.29c₀)` for one corrected column occurrence. -/
theorem corrected_twoE_sub_N
    (e : RelevantEdge T₁) (b : AdjacentCorrection T₂) :
    2 * neighborSquare e (first b) (selectedColumnAtom b) -
        OccurrenceSettlement.neighboringN
          (Pr e)
          (fun i => r e (first b) i (selectedColumnAtom b))
          (fun i => neighborU e (first b) i (selectedColumnAtom b))
          (fun i => neighborV e (first b) i (selectedColumnAtom b)) =
      2 * OccurrenceSettlement.retainedI
          (Pr e)
          (fun i => r e (first b) i (selectedColumnAtom b))
          (fun i => neighborU e (first b) i (selectedColumnAtom b)) +
        OccurrenceSettlement.retainedD
          (Pr e)
          (fun i => r e (first b) i (selectedColumnAtom b))
          (fun i => neighborU e (first b) i (selectedColumnAtom b))
          (fun i => neighborV e (first b) i (selectedColumnAtom b)) +
        OccurrenceSettlement.boundary
          (Pr e)
          (fun i => r e (first b) i (selectedColumnAtom b))
          (fun i => neighborU e (first b) i (selectedColumnAtom b))
          (fun i => neighborV e (first b) i (selectedColumnAtom b)) := by
  exact OccurrenceSettlement.twoE_sub_N
    (Pr e)
    (fun i => r e (first b) i (selectedColumnAtom b))
    (fun i => neighborU e (first b) i (selectedColumnAtom b))
    (fun i => neighborV e (first b) i (selectedColumnAtom b))
    (neighborSquare e (first b) (selectedColumnAtom b))
    (sum_r e (first b) (selectedColumnAtom b))
    (fun i => neighborU_sq e (first b) i (selectedColumnAtom b))

end

end ConcreteOccurrenceSettlement

end QuartetV060
