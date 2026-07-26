import QuartetV060.ConcreteRetainedSquares
import QuartetV060.SevenSource

/-!
# Entry from the four determinant levels to principal-chart coordinates

The identities in this file connect the determinants in the definition of
`auxiliaryFunctional` to the centered coordinates used in Appendix A.  This
interface is essential: the residual and bridge ledgers must be identities
for the actual finite-tree determinant sums, not merely identities for an
unrelated local table.
-/

namespace QuartetV060

namespace ConcreteDeterminantLevels

open QuartetDistance
open PhyloOccurrences
open PrincipalBranches
open PrincipalAtoms
open PrincipalChart
open LocalCoordinates
open ConcreteRetainedSquares

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

variable
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)

noncomputable local instance correctionsFromFintype :
    Fintype (CorrectionsFrom e) :=
  Fintype.subtype
    (Finset.univ.filter fun a : AdjacentCorrection T₁ => first a = e)
    (by intro a; simp)

noncomputable local instance endpointAtomIndexFintype :
    Fintype (EndpointAtomIndex e) :=
  Fintype.subtype
    (Finset.univ.filter fun i : Atom e =>
      (fourSector e).isEndpoint i)
    (by intro i; simp)

/-- An ordinary/ordinary determinant is exactly the square of any
principal-chart representative `x_{bar i,bar k}`. -/
theorem ordinaryOrdinary_eq_xBarOpp_sq
    (i : Atom e) (k : Atom f) :
    ordinaryOrdinary
        (correctionSystem T₁) (correctionSystem T₂) e f =
      xBarOpp (jointMass e f) (fourSector e) (fourSector f) i k ^ 2 := by
  change
    splitDetSquare (ordinary T₁ e) (ordinary T₂ f) =
      xBarOpp (jointMass e f) (fourSector e) (fourSector f) i k ^ 2
  rw [splitDetSquare_eq_centeredIntersection_sq]
  unfold xBarOpp
  rw [jointMass_centeredRectangleMass_eq]
  rw [aggregateBlock_opposite_eq, aggregateBlock_opposite_eq]
  cases hi : atomSide e i <;> cases hk : atomSide f k
  · change
      (intersectionMass e.1.cluster f.1.cluster -
          normalizedCard e.1.cluster * normalizedCard f.1.cluster) ^ 2 =
        (normalizedCard (e.1.clusterᶜ ∩ f.1.clusterᶜ) -
          normalizedCard e.1.clusterᶜ *
            normalizedCard f.1.clusterᶜ) ^ 2
    calc
      _ = splitDetSquare (ordinary T₁ e) (ordinary T₂ f) := by
        symm
        exact splitDetSquare_eq_centeredIntersection_sq
          (ordinary T₁ e) (ordinary T₂ f)
      _ = splitDetSquare (ordinary T₁ e).reverse
          (ordinary T₂ f).reverse := by
        rw [splitDetSquare_reverse_left,
          splitDetSquare_reverse_right]
      _ = _ := by
        simpa [intersectionMass, ordinary, OrientedSplit.other] using
          splitDetSquare_eq_centeredIntersection_sq
            (ordinary T₁ e).reverse (ordinary T₂ f).reverse
  · change
      (intersectionMass e.1.cluster f.1.cluster -
          normalizedCard e.1.cluster * normalizedCard f.1.cluster) ^ 2 =
        (normalizedCard (e.1.clusterᶜ ∩ f.1.cluster) -
          normalizedCard e.1.clusterᶜ *
            normalizedCard f.1.cluster) ^ 2
    calc
      _ = splitDetSquare (ordinary T₁ e) (ordinary T₂ f) := by
        symm
        exact splitDetSquare_eq_centeredIntersection_sq
          (ordinary T₁ e) (ordinary T₂ f)
      _ = splitDetSquare (ordinary T₁ e).reverse
          (ordinary T₂ f) := by
        rw [splitDetSquare_reverse_left]
      _ = _ := by
        simpa [intersectionMass, ordinary, OrientedSplit.other] using
          splitDetSquare_eq_centeredIntersection_sq
            (ordinary T₁ e).reverse (ordinary T₂ f)
  · change
      (intersectionMass e.1.cluster f.1.cluster -
          normalizedCard e.1.cluster * normalizedCard f.1.cluster) ^ 2 =
        (normalizedCard (e.1.cluster ∩ f.1.clusterᶜ) -
          normalizedCard e.1.cluster *
            normalizedCard f.1.clusterᶜ) ^ 2
    calc
      _ = splitDetSquare (ordinary T₁ e) (ordinary T₂ f) := by
        symm
        exact splitDetSquare_eq_centeredIntersection_sq
          (ordinary T₁ e) (ordinary T₂ f)
      _ = splitDetSquare (ordinary T₁ e)
          (ordinary T₂ f).reverse := by
        rw [splitDetSquare_reverse_right]
      _ = _ := by
        simpa [intersectionMass, ordinary, OrientedSplit.other] using
          splitDetSquare_eq_centeredIntersection_sq
            (ordinary T₁ e) (ordinary T₂ f).reverse
  · rfl

/-- The ordinary/ordinary chart value is the concrete entry square used in
`(A.15a)`. -/
theorem ordinaryOrdinary_eq_ordinarySquare :
    ordinaryOrdinary
        (correctionSystem T₁) (correctionSystem T₂) e f =
      ordinarySquare e f := by
  exact ordinaryOrdinary_eq_xBarOpp_sq e f
    (anchorRow e) (anchorCol f)

/-- The two complete column sides, named by the anchor column atom. -/
def columnSides : TwoSide (Atom f) where
  S := (fourSector f).sameSideBlock (anchorCol f)

theorem columnSides_B :
    (columnSides f).B =
      (fourSector f).oppositeSideBlock (anchorCol f) := by
  ext k
  simp [columnSides, TwoSide.B, FourSector.sameSideBlock,
    FourSector.oppositeSideBlock]

theorem sameSide_comm
    (u v : Atom f) :
    (fourSector f).sameSide u v ↔
      (fourSector f).sameSide v u := by
  unfold FourSector.sameSide
  constructor <;> exact fun h => h.symm

/-- The two-side opposite block is exactly the four-sector opposite block,
for every atom, not only for the anchor. -/
theorem columnSides_oppositeBlock (k : Atom f) :
    (columnSides f).oppositeBlock k =
      (fourSector f).oppositeSideBlock k := by
  by_cases h :
      (fourSector f).sameSide (anchorCol f) k
  · have hk :
        k ∈ (columnSides f).S := by
      simpa [columnSides] using h
    rw [TwoSide.oppositeBlock_of_mem_S _ hk]
    rw [columnSides_B]
    exact
      FourSector.oppositeSideBlock_eq_of_sameSide
        (fourSector f) h
  · have hk :
        k ∈ (columnSides f).B := by
      rw [columnSides_B]
      rw [FourSector.mem_oppositeSideBlock_iff]
      intro hka
      exact h hka
    rw [TwoSide.oppositeBlock_of_mem_B _ hk]
    unfold columnSides
    exact
      (FourSector.oppositeSideBlock_eq_sameSideBlock_of_not_sameSide
        (fourSector f) (u := k) (v := anchorCol f)
        (fun hka => h ((sameSide_comm f k (anchorCol f)).1 hka))).symm

/-- The column profile of an aggregate row block. -/
def rowProfile (V : Finset (Atom e)) (k : Atom f) : ℚ :=
  ∑ i ∈ V, (jointMass e f).a i k

theorem rowProfile_blockSum
    (V : Finset (Atom e)) (U : Finset (Atom f)) :
    TwoSide.blockSum (rowProfile e f V) U =
      ∑ i ∈ V, (jointMass e f).mixedBlockMass i U := by
  unfold TwoSide.blockSum rowProfile JointMass.mixedBlockMass
  rw [Finset.sum_comm]

theorem rowProfile_total
    (V : Finset (Atom e)) :
    TwoSide.total (rowProfile e f V) =
      ∑ i ∈ V, (jointMass e f).rowMass i := by
  unfold TwoSide.total rowProfile JointMass.rowMass
  rw [Finset.sum_comm]

theorem c_blockSum
    (U : Finset (Atom f)) :
    TwoSide.blockSum (c e f) U =
      (jointMass e f).colBlockMass U := by
  rfl

theorem rowProfile_apply
    (V : Finset (Atom e)) (k : Atom f) :
    rowProfile e f V k =
      ∑ i ∈ V, (jointMass e f).a i k := by
  rfl

/-- Aggregating row atoms before taking the symmetric column coefficient is
the same as summing their concrete coefficients `r_i^k`. -/
theorem symmetricCoefficient_rowProfile
    (V : Finset (Atom e)) (k : Atom f) :
    (columnSides f).symmetricCoefficient
        (c e f) (rowProfile e f V) k =
      ∑ i ∈ V, r e f i k := by
  unfold TwoSide.symmetricCoefficient r
  rw [columnSides_oppositeBlock]
  rw [rowProfile_apply]
  rw [rowProfile_blockSum]
  rw [c_blockSum]
  unfold JointMass.symmetricRowCoefficient J Fc c
  rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_div]
  rw [← Finset.sum_div]
  rfl

/-- The weighted coefficient of a row block is the sum of its concrete
ordinary-column weights. -/
theorem weightedAverage_rowProfile
    (V : Finset (Atom e)) :
    (columnSides f).weightedAverage
        (c e f) (rowProfile e f V) =
      ∑ i ∈ V, omega e f i := by
  unfold TwoSide.weightedAverage omega alpha
  simp_rw [symmetricCoefficient_rowProfile]
  calc
    (∑ k : Atom f, c e f k * ∑ i ∈ V, r e f i k) =
        ∑ k : Atom f, ∑ i ∈ V,
          c e f k * r e f i k := by
            apply Fintype.sum_congr
            intro k
            rw [Finset.mul_sum]
    _ = ∑ i ∈ V, ∑ k : Atom f,
          c e f k * r e f i k := by
            rw [Finset.sum_comm]

/-- The centered column-side mass of a row block is the corresponding
centered rectangle of the concrete joint table. -/
theorem centeredBlock_rowProfile
    (V : Finset (Atom e)) (U : Finset (Atom f)) :
    (columnSides f).centeredBlock
        (c e f) (rowProfile e f V) U =
      (jointMass e f).centeredRectangleMass V U := by
  unfold TwoSide.centeredBlock JointMass.centeredRectangleMass
    JointMass.centered
  rw [rowProfile_blockSum]
  rw [rowProfile_total]
  rw [c_blockSum]
  simp only [Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · rfl
  · unfold JointMass.colBlockMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]

theorem c_ne (k : Atom f) :
    c e f k ≠ 0 :=
  (c_pos e f k).ne'

theorem c_blockSum_S_pos :
    0 <
      TwoSide.blockSum (c e f) (columnSides f).S := by
  unfold TwoSide.blockSum
  apply Finset.sum_pos'
  · intro k hk
    exact (c_pos e f k).le
  · refine ⟨anchorCol f, ?_, c_pos e f (anchorCol f)⟩
    simp [columnSides, FourSector.mem_sameSideBlock_iff,
      FourSector.sameSide]

theorem c_blockSum_B_pos :
    0 <
      TwoSide.blockSum (c e f) (columnSides f).B := by
  rw [c_blockSum]
  rw [columnSides_B]
  exact cbar_pos e f (anchorCol f)

theorem c_total :
    TwoSide.total (c e f) = 1 := by
  exact (jointMass e f).sum_colMass

/-- Concrete form of the weighted determinant cancellation.  It applies to
arbitrary aggregate row blocks, so no endpoint multiplicity or bridge
reindexing is hidden in the identity. -/
theorem aggregate_weighted_cancellation
    (V W : Finset (Atom e)) :
    ((∑ i ∈ V, omega e f i) *
          (jointMass e f).centeredRectangleMass
            W (columnSides f).B -
        (∑ i ∈ W, omega e f i) *
          (jointMass e f).centeredRectangleMass
            V (columnSides f).B) ^ 2 =
      ((∑ i ∈ V, (jointMass e f).rowMass i) *
            (jointMass e f).centeredRectangleMass
              W (columnSides f).B -
          (∑ i ∈ W, (jointMass e f).rowMass i) *
            (jointMass e f).centeredRectangleMass
              V (columnSides f).B) ^ 2 := by
  simpa [weightedAverage_rowProfile, centeredBlock_rowProfile,
      rowProfile_total] using
    (TwoSide.weighted_determinant_square_cancellation
      (columnSides f) (c e f)
      (rowProfile e f V) (rowProfile e f W)
      (c_ne e f)
      (c_blockSum_S_pos e f).ne'
      (c_blockSum_B_pos e f).ne'
      (c_total e f))

/-- The ordinary column split, oriented so that its chosen side is the
aggregate block called `bar k` by the principal chart. -/
noncomputable def columnSplit : OrientedSplit X :=
  match atomSide f (anchorCol f) with
  | .child => (ordinary T₂ f).reverse
  | .parent => ordinary T₂ f

theorem columnSplit_side :
    (columnSplit f).side =
      aggregateBlock f
        ((fourSector f).oppositeSideBlock (anchorCol f)) := by
  rw [aggregateBlock_opposite_eq]
  cases h : atomSide f (anchorCol f) <;>
    simp [columnSplit, h, ordinary, OrientedSplit.other]

theorem aggregateBlock_columnSides_B :
    aggregateBlock f (columnSides f).B =
      (columnSplit f).side := by
  rw [columnSides_B]
  exact (columnSplit_side f).symm

/-- Reorienting the ordinary column split to the chart's `bar k` side does
not change a squared side-pair determinant. -/
theorem sidePairSplitDetSquare_columnSplit
    (p : SidePair X) :
    sidePairSplitDetSquare p (columnSplit f) =
      sidePairSplitDetSquare p (ordinary T₂ f) := by
  cases h : atomSide f (anchorCol f) with
  | child =>
      simp [columnSplit, h]
  | parent =>
      simp [columnSplit, h]

theorem centeredRectangle_columnSides_B
    (V : Finset (Atom e)) :
    (jointMass e f).centeredRectangleMass V (columnSides f).B =
      intersectionMass (aggregateBlock e V) (columnSplit f).side -
        normalizedCard (aggregateBlock e V) *
          normalizedCard (columnSplit f).side := by
  rw [jointMass_centeredRectangleMass_eq]
  rw [aggregateBlock_columnSides_B]
  rfl

theorem ordinaryX_eq_centeredRectangle
    (i : Atom e) :
    ordinaryX e f i =
      (jointMass e f).centeredRectangleMass
        ((fourSector e).oppositeSideBlock i)
        (columnSides f).B := by
  unfold ordinaryX xBarOpp J Fr Fc
  rw [columnSides_B]

theorem ordinaryY_eq_centeredRectangle
    (i : Atom e) :
    ordinaryY e f i =
      (jointMass e f).centeredRectangleMass
        {i} (columnSides f).B := by
  unfold ordinaryY J Fc
  rw [xOpp_eq_rectangle]
  rw [columnSides_B]

theorem endpoint_weighted_cancellation
    (i : Atom e) :
    (omega e f i * ordinaryX e f i -
        (Pr e).oppositeWeight (omega e f) i *
          ordinaryY e f i) ^ 2 =
      ((jointMass e f).rowMass i *
            (jointMass e f).centeredRectangleMass
              ((fourSector e).oppositeSideBlock i)
              (columnSides f).B -
          (∑ j ∈ (fourSector e).oppositeSideBlock i,
              (jointMass e f).rowMass j) *
            (jointMass e f).centeredRectangleMass
              {i} (columnSides f).B) ^ 2 := by
  have h :=
    aggregate_weighted_cancellation e f
      ({i} : Finset (Atom e))
      ((fourSector e).oppositeSideBlock i)
  simpa [ordinaryX_eq_centeredRectangle,
      ordinaryY_eq_centeredRectangle, Pr,
      residualPartition, ResidualPartition.oppositeWeight] using h

theorem aggregateBlock_selected_singleton_eq_correctionK
    (a : AdjacentCorrection T₁) :
    aggregateBlock (first a)
        {endpointAtom (first a) (correctionSlot a)} =
      correctionK a := by
  rw [correctionK_eq_selectedAtomBlock a]
  simp [aggregateBlock]

/-- The mass-level contrast on a selected endpoint is exactly the neighboring
contrast of the actual ordered adjacent side-pair against the reoriented
ordinary column split. -/
theorem endpoint_mass_contrast_eq_neighboring
    (a : AdjacentCorrection T₁) (f : RelevantEdge T₂) :
    let i := endpointAtom (first a) (correctionSlot a)
    (jointMass (first a) f).rowMass i *
          (jointMass (first a) f).centeredRectangleMass
            ((fourSector (first a)).oppositeSideBlock i)
            (columnSides f).B -
        (∑ j ∈ (fourSector (first a)).oppositeSideBlock i,
            (jointMass (first a) f).rowMass j) *
          (jointMass (first a) f).centeredRectangleMass
            {i} (columnSides f).B =
      SidePairData.neighboringContrast
        (sidePairAgainstSplitData (corrected a) (columnSplit f)) := by
  dsimp
  let i := endpointAtom (first a) (correctionSlot a)
  have hmassK :=
    jointMass_rowBlockMass_eq (first a) f
      ({i} : Finset (Atom (first a)))
  have hmassL :=
    jointMass_rowBlockMass_eq (first a) f
      ((fourSector (first a)).oppositeSideBlock i)
  have hcenterK :=
    centeredRectangle_columnSides_B (first a) f
      ({i} : Finset (Atom (first a)))
  have hcenterL :=
    centeredRectangle_columnSides_B (first a) f
      ((fourSector (first a)).oppositeSideBlock i)
  have hK :
      aggregateBlock (first a) {i} = correctionK a := by
    exact aggregateBlock_selected_singleton_eq_correctionK a
  have hL :
      aggregateBlock (first a)
          ((fourSector (first a)).oppositeSideBlock i) =
        correctionL a := by
    exact aggregateBlock_opposite_selected_eq_correctionL a
  simp only [Finset.sum_singleton] at hmassK
  rw [hK] at hmassK hcenterK
  rw [hL] at hmassL hcenterL
  rw [hmassK, hmassL, hcenterK, hcenterL]
  unfold SidePairData.neighboringContrast
    SidePairData.centeredLeft SidePairData.centeredRight
    sidePairAgainstSplitData corrected
  rfl

/-- One endpoint term in `(A.15a)` is the actual corrected/ordinary
determinant indexed by the corresponding ordered adjacent edge. -/
theorem endpoint_neighboring_eq_correctedOrdinary_term
    (a : AdjacentCorrection T₁) (f : RelevantEdge T₂) :
    let i := endpointAtom (first a) (correctionSlot a)
    (omega (first a) f i * ordinaryX (first a) f i -
        (Pr (first a)).oppositeWeight (omega (first a) f) i *
          ordinaryY (first a) f i) ^ 2 =
      sidePairSplitDetSquare (corrected a) (ordinary T₂ f) := by
  dsimp
  let i := endpointAtom (first a) (correctionSlot a)
  calc
    (omega (first a) f i * ordinaryX (first a) f i -
        (Pr (first a)).oppositeWeight (omega (first a) f) i *
          ordinaryY (first a) f i) ^ 2 =
        ((jointMass (first a) f).rowMass i *
              (jointMass (first a) f).centeredRectangleMass
                ((fourSector (first a)).oppositeSideBlock i)
                (columnSides f).B -
            (∑ j ∈ (fourSector (first a)).oppositeSideBlock i,
                (jointMass (first a) f).rowMass j) *
              (jointMass (first a) f).centeredRectangleMass
                {i} (columnSides f).B) ^ 2 :=
      endpoint_weighted_cancellation (first a) f i
    _ =
        SidePairData.neighboringContrast
          (sidePairAgainstSplitData
            (corrected a) (columnSplit f)) ^ 2 := by
      rw [endpoint_mass_contrast_eq_neighboring a f]
    _ =
        sidePairSplitDetSquare (corrected a) (columnSplit f) := by
      symm
      exact
        sidePair_split_det_eq_neighboringContrast_sq
          (corrected a) (columnSplit f)
    _ =
        sidePairSplitDetSquare (corrected a) (ordinary T₂ f) :=
      sidePairSplitDetSquare_columnSplit f (corrected a)

/-- The multiplicity-one composite from fixed-first-edge corrections to
endpoint atoms.  This is the formal `h ↦ k(e,h)` crosswalk used when
settling the complete corrected/ordinary sum. -/
noncomputable def correctionEquivEndpointAtom :
    CorrectionsFrom e ≃ EndpointAtomIndex e :=
  (endpointSlotEquivCorrectionsFrom e).symm.trans
    (endpointAtomEquiv e)

theorem sum_fiber_eq_sum_correctionsFrom
    (g : AdjacentCorrection T₁ → ℚ) :
    (∑ a ∈ (correctionSystem T₁).fiber e, g a) =
      ∑ a : CorrectionsFrom e, g a.1 := by
  classical
  unfold CorrectionSystem.fiber correctionSystem
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp [CorrectionsFrom]

theorem sum_endpointAtomIndex_eq_endpoint
    (g : Atom e → ℚ) :
    (∑ i : EndpointAtomIndex e, g i.1) =
      ∑ i ∈ (Pr e).endpoint, g i := by
  classical
  change
    (∑ i : {i : Atom e // (fourSector e).isEndpoint i}, g i.1) =
      ∑ i ∈ (Pr e).endpoint, g i
  unfold Pr residualPartition
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp

theorem correction_term_eq_endpointAtom_term
    (a : CorrectionsFrom e) :
    sidePairSplitDetSquare (corrected a.1) (ordinary T₂ f) =
      let i := (correctionEquivEndpointAtom e a).1
      (omega e f i * ordinaryX e f i -
          (Pr e).oppositeWeight (omega e f) i *
            ordinaryY e f i) ^ 2 := by
  rcases a with ⟨a, ha⟩
  subst e
  symm
  simpa [correctionEquivEndpointAtom, correctionSlot,
      correctionFromFirst, endpointAtomEquiv] using
    endpoint_neighboring_eq_correctedOrdinary_term a f

/-- The full corrected/ordinary determinant sum is exactly the neighboring
sum in concrete `(A.15a)`.  The equality uses the explicit
correction-to-endpoint bijection, so every ordered adjacent correction occurs
once and only once. -/
theorem correctedOrdinary_eq_ordinaryNeighboring :
    correctedOrdinary
        (correctionSystem T₁) (correctionSystem T₂) e f =
      ordinaryNeighboring e f := by
  unfold correctedOrdinary ordinaryNeighboring
    OccurrenceSettlement.neighboringN
  change
    (∑ a ∈ (correctionSystem T₁).fiber e,
        sidePairSplitDetSquare (corrected a) (ordinary T₂ f)) =
      ∑ i ∈ (Pr e).endpoint,
        (omega e f i * ordinaryX e f i -
            (Pr e).oppositeWeight (omega e f) i *
              ordinaryY e f i) ^ 2
  rw [sum_fiber_eq_sum_correctionsFrom e
    (fun a =>
      sidePairSplitDetSquare (corrected a) (ordinary T₂ f))]
  calc
    (∑ a : CorrectionsFrom e,
        sidePairSplitDetSquare (corrected a.1) (ordinary T₂ f)) =
        ∑ i : EndpointAtomIndex e,
          (omega e f i.1 * ordinaryX e f i.1 -
              (Pr e).oppositeWeight (omega e f) i.1 *
                ordinaryY e f i.1) ^ 2 := by
      exact Fintype.sum_equiv
        (correctionEquivEndpointAtom e)
        (fun a : CorrectionsFrom e =>
          sidePairSplitDetSquare (corrected a.1) (ordinary T₂ f))
        (fun i : EndpointAtomIndex e =>
          (omega e f i.1 * ordinaryX e f i.1 -
              (Pr e).oppositeWeight (omega e f) i.1 *
                ordinaryY e f i.1) ^ 2)
        (correction_term_eq_endpointAtom_term e f)
    _ = ∑ i ∈ (Pr e).endpoint,
          (omega e f i * ordinaryX e f i -
              (Pr e).oppositeWeight (omega e f) i *
                ordinaryY e f i) ^ 2 := by
      exact sum_endpointAtomIndex_eq_endpoint e
        (fun i =>
          (omega e f i * ordinaryX e f i -
              (Pr e).oppositeWeight (omega e f) i *
                ordinaryY e f i) ^ 2)

/-- For a selected column correction, the concrete first neighboring form
`U_i(k)` is the neighboring contrast of the actual column side-pair against
the row split oriented by `bar i`. -/
theorem neighborU_selected_eq_neighboring
    (e : RelevantEdge T₁) (b : AdjacentCorrection T₂) :
    let k := endpointAtom (first b) (correctionSlot b)
    neighborU e (first b) (anchorRow e) k =
      SidePairData.neighboringContrast
        (sidePairAgainstSplitData (corrected b) (columnSplit e)) := by
  dsimp
  let k := endpointAtom (first b) (correctionSlot b)
  have hK :
      aggregateBlock (first b) {k} = correctionK b := by
    exact aggregateBlock_selected_singleton_eq_correctionK b
  have hKblock :
      block (first b) k = correctionK b := by
    exact (correctionK_eq_selectedAtomBlock b).symm
  have hL :
      aggregateBlock (first b)
          ((fourSector (first b)).oppositeSideBlock k) =
        correctionL b := by
    exact aggregateBlock_opposite_selected_eq_correctionL b
  have hrow :
      aggregateBlock e
          ((fourSector e).oppositeSideBlock (anchorRow e)) =
        (columnSplit e).side := by
    exact (columnSplit_side e).symm
  have hc :=
    jointMass_colMass_eq e (first b) k
  have hcbar :=
    jointMass_colBlockMass_eq e (first b)
      ((fourSector (first b)).oppositeSideBlock k)
  have hxBarOpp :=
    jointMass_centeredRectangleMass_eq e (first b)
      ((fourSector e).oppositeSideBlock (anchorRow e))
      ((fourSector (first b)).oppositeSideBlock k)
  have hxBarSame :=
    jointMass_centeredRectangleMass_eq e (first b)
      ((fourSector e).oppositeSideBlock (anchorRow e))
      ({k} : Finset (Atom (first b)))
  rw [hKblock] at hc
  rw [hK] at hxBarSame
  rw [hL] at hcbar hxBarOpp
  rw [hrow] at hxBarOpp hxBarSame
  unfold neighborU RetainedSquares.neighboringU
    c cbar xBarOpp xBarSame J Fr Fc
  rw [hc, hcbar, hxBarOpp, hxBarSame]
  unfold SidePairData.neighboringContrast
    SidePairData.centeredLeft SidePairData.centeredRight
    sidePairAgainstSplitData corrected intersectionMass
  rw [Finset.inter_comm (columnSplit e).side (correctionL b)]
  rw [Finset.inter_comm (columnSplit e).side (correctionK b)]
  simp [normalizedCard]
  ring

theorem neighborSquare_selected_eq_ordinaryCorrected_term
    (e : RelevantEdge T₁) (b : AdjacentCorrection T₂) :
    let k := endpointAtom (first b) (correctionSlot b)
    neighborSquare e (first b) k =
      splitSidePairDetSquare (ordinary T₁ e) (corrected b) := by
  dsimp
  let k := endpointAtom (first b) (correctionSlot b)
  calc
    neighborSquare e (first b) k =
        neighborU e (first b) (anchorRow e) k ^ 2 := rfl
    _ =
        SidePairData.neighboringContrast
          (sidePairAgainstSplitData
            (corrected b) (columnSplit e)) ^ 2 := by
      rw [neighborU_selected_eq_neighboring e b]
    _ =
        sidePairSplitDetSquare (corrected b) (columnSplit e) := by
      symm
      exact
        sidePair_split_det_eq_neighboringContrast_sq
          (corrected b) (columnSplit e)
    _ =
        sidePairSplitDetSquare (corrected b) (ordinary T₁ e) :=
      sidePairSplitDetSquare_columnSplit e (corrected b)
    _ =
        splitSidePairDetSquare (ordinary T₁ e) (corrected b) := by
      symm
      exact
        splitSidePairDetSquare_eq_sidePairSplitDetSquare
          (ordinary T₁ e) (corrected b)

theorem ordinaryCorrected_term_eq_endpointAtom_term
    (b : CorrectionsFrom f) :
    splitSidePairDetSquare (ordinary T₁ e) (corrected b.1) =
      neighborSquare e f (correctionEquivEndpointAtom f b).1 := by
  rcases b with ⟨b, hb⟩
  subst f
  symm
  simpa [correctionEquivEndpointAtom, correctionSlot,
      correctionFromFirst, endpointAtomEquiv] using
    neighborSquare_selected_eq_ordinaryCorrected_term e b

/-- The complete ordinary/corrected determinant level is the exact sum of
the concrete endpoint squares that starts `(A.15b)`. -/
theorem ordinaryCorrected_eq_sum_neighborSquare :
    ordinaryCorrected
        (correctionSystem T₁) (correctionSystem T₂) e f =
      ∑ k ∈ (Pc f).endpoint, neighborSquare e f k := by
  unfold ordinaryCorrected
  change
    (∑ b ∈ (correctionSystem T₂).fiber f,
        splitSidePairDetSquare (ordinary T₁ e) (corrected b)) =
      ∑ k ∈ (Pc f).endpoint, neighborSquare e f k
  rw [sum_fiber_eq_sum_correctionsFrom f
    (fun b =>
      splitSidePairDetSquare (ordinary T₁ e) (corrected b))]
  calc
    (∑ b : CorrectionsFrom f,
        splitSidePairDetSquare (ordinary T₁ e) (corrected b.1)) =
        ∑ k : EndpointAtomIndex f,
          neighborSquare e f k.1 := by
      exact Fintype.sum_equiv
        (correctionEquivEndpointAtom f)
        (fun b : CorrectionsFrom f =>
          splitSidePairDetSquare (ordinary T₁ e) (corrected b.1))
        (fun k : EndpointAtomIndex f =>
          neighborSquare e f k.1)
        (ordinaryCorrected_term_eq_endpointAtom_term e f)
    _ = ∑ k ∈ (Pc f).endpoint, neighborSquare e f k := by
      exact sum_endpointAtomIndex_eq_endpoint f
        (fun k => neighborSquare e f k)

theorem rowProfile_rectangleMass
    (V : Finset (Atom e)) (U : Finset (Atom f)) :
    TwoSide.blockSum (rowProfile e f V) U =
      normalizedCard
        (aggregateBlock e V ∩ aggregateBlock f U) := by
  rw [rowProfile_blockSum]
  exact jointMass_rectangleMass_eq e f V U

theorem r_eq_symmetricCoefficient_singleton
    (i : Atom e) (k : Atom f) :
    r e f i k =
      (columnSides f).symmetricCoefficient
        (c e f) (rowProfile e f {i}) k := by
  symm
  simpa using
    symmetricCoefficient_rowProfile e f
      ({i} : Finset (Atom e)) k

theorem oppositeWeight_r_eq_symmetricCoefficient
    (i : Atom e) (k : Atom f) :
    (Pr e).oppositeWeight (fun j => r e f j k) i =
      (columnSides f).symmetricCoefficient
        (c e f)
        (rowProfile e f ((fourSector e).oppositeSideBlock i)) k := by
  unfold Pr residualPartition ResidualPartition.oppositeWeight
  symm
  exact
    symmetricCoefficient_rowProfile e f
      ((fourSector e).oppositeSideBlock i) k

theorem neighborU_eq_centeredProfiles
    (i : Atom e) (k : Atom f) :
    neighborU e f i k =
      c e f k *
          (columnSides f).centeredBlock
            (c e f)
            (rowProfile e f
              ((fourSector e).oppositeSideBlock i))
            ((columnSides f).oppositeBlock k) -
        TwoSide.blockSum (c e f)
            ((columnSides f).oppositeBlock k) *
          (columnSides f).centeredBlock
            (c e f)
            (rowProfile e f
              ((fourSector e).oppositeSideBlock i))
            {k} := by
  unfold neighborU RetainedSquares.neighboringU
    xBarOpp xBarSame J Fr Fc cbar
  rw [centeredBlock_rowProfile]
  rw [centeredBlock_rowProfile]
  rw [columnSides_oppositeBlock]
  rw [c_blockSum]
  rfl

theorem neighborV_eq_centeredProfiles
    (i : Atom e) (k : Atom f) :
    neighborV e f i k =
      c e f k *
          (columnSides f).centeredBlock
            (c e f) (rowProfile e f {i})
            ((columnSides f).oppositeBlock k) -
        TwoSide.blockSum (c e f)
            ((columnSides f).oppositeBlock k) *
          (columnSides f).centeredBlock
            (c e f) (rowProfile e f {i}) {k} := by
  unfold neighborV RetainedSquares.neighboringV cbar
  rw [xOpp_eq_rectangle]
  rw [xSame_eq_rectangle]
  rw [centeredBlock_rowProfile]
  rw [centeredBlock_rowProfile]
  rw [columnSides_oppositeBlock]
  rw [c_blockSum]
  rfl

/-- The concrete corrected/corrected neighboring contrast collapses to the
raw determinant of the selected and opposite row blocks. -/
theorem corrected_contrast_cancellation
    (i : Atom e) (k : Atom f) :
    r e f i k * neighborU e f i k -
        (Pr e).oppositeWeight (fun j => r e f j k) i *
          neighborV e f i k =
      rowProfile e f {i} k *
          TwoSide.blockSum
            (rowProfile e f
              ((fourSector e).oppositeSideBlock i))
            ((columnSides f).oppositeBlock k) -
        TwoSide.blockSum (rowProfile e f {i})
            ((columnSides f).oppositeBlock k) *
          rowProfile e f
            ((fourSector e).oppositeSideBlock i) k := by
  have hcbar :
      TwoSide.blockSum (c e f)
          ((columnSides f).oppositeBlock k) ≠ 0 := by
    rw [columnSides_oppositeBlock]
    rw [c_blockSum]
    exact (cbar_pos e f k).ne'
  have h :=
    TwoSide.symmetric_neighboring_determinant_cancellation
      (columnSides f) (c e f)
      (rowProfile e f {i})
      (rowProfile e f ((fourSector e).oppositeSideBlock i))
      k (c_ne e f k) hcbar
  rw [← r_eq_symmetricCoefficient_singleton e f i k] at h
  rw [← oppositeWeight_r_eq_symmetricCoefficient e f i k] at h
  rw [← neighborU_eq_centeredProfiles e f i k] at h
  rw [← neighborV_eq_centeredProfiles e f i k] at h
  exact h

/-- One pair of selected row/column endpoint atoms gives exactly the actual
corrected/corrected side-pair determinant. -/
theorem corrected_contrast_sq_eq_sidePairDetSquare
    (a : AdjacentCorrection T₁) (b : AdjacentCorrection T₂) :
    let i := endpointAtom (first a) (correctionSlot a)
    let k := endpointAtom (first b) (correctionSlot b)
    (r (first a) (first b) i k *
          neighborU (first a) (first b) i k -
        (Pr (first a)).oppositeWeight
            (fun j => r (first a) (first b) j k) i *
          neighborV (first a) (first b) i k) ^ 2 =
      sidePairDetSquare (corrected a) (corrected b) := by
  dsimp
  let i := endpointAtom (first a) (correctionSlot a)
  let k := endpointAtom (first b) (correctionSlot b)
  let Wi := (fourSector (first a)).oppositeSideBlock i
  let Wk := (fourSector (first b)).oppositeSideBlock k
  have hKr :
      aggregateBlock (first a) {i} = correctionK a :=
    aggregateBlock_selected_singleton_eq_correctionK a
  have hLr :
      aggregateBlock (first a) Wi = correctionL a := by
    exact aggregateBlock_opposite_selected_eq_correctionL a
  have hKc :
      aggregateBlock (first b) {k} = correctionK b :=
    aggregateBlock_selected_singleton_eq_correctionK b
  have hLc :
      aggregateBlock (first b) Wk = correctionL b := by
    exact aggregateBlock_opposite_selected_eq_correctionL b
  have hA :=
    rowProfile_rectangleMass (first a) (first b)
      ({i} : Finset (Atom (first a)))
      ({k} : Finset (Atom (first b)))
  have hB :=
    rowProfile_rectangleMass (first a) (first b)
      ({i} : Finset (Atom (first a))) Wk
  have hC :=
    rowProfile_rectangleMass (first a) (first b)
      Wi ({k} : Finset (Atom (first b)))
  have hD :=
    rowProfile_rectangleMass (first a) (first b) Wi Wk
  simp only [TwoSide.blockSum, Finset.sum_singleton] at hA hC
  rw [hKr, hKc] at hA
  rw [hKr, hLc] at hB
  rw [hLr, hKc] at hC
  rw [hLr, hLc] at hD
  have hcancel :=
    corrected_contrast_cancellation
      (first a) (first b) i k
  rw [columnSides_oppositeBlock] at hcancel
  calc
    (r (first a) (first b) i k *
          neighborU (first a) (first b) i k -
        (Pr (first a)).oppositeWeight
            (fun j => r (first a) (first b) j k) i *
          neighborV (first a) (first b) i k) ^ 2 =
        (rowProfile (first a) (first b) {i} k *
              TwoSide.blockSum
                (rowProfile (first a) (first b) Wi) Wk -
            TwoSide.blockSum
                (rowProfile (first a) (first b) {i}) Wk *
              rowProfile (first a) (first b) Wi k) ^ 2 := by
      rw [hcancel]
    _ =
        (normalizedCard (correctionK a ∩ correctionK b) *
              normalizedCard (correctionL a ∩ correctionL b) -
            normalizedCard (correctionK a ∩ correctionL b) *
              normalizedCard (correctionL a ∩ correctionK b)) ^ 2 := by
      rw [hA, hB, hC, hD]
    _ = sidePairDetSquare (corrected a) (corrected b) := by
      rfl

def correctedContrastTerm
    (i : Atom e) (k : Atom f) : ℚ :=
  (r e f i k * neighborU e f i k -
      (Pr e).oppositeWeight (fun j => r e f j k) i *
        neighborV e f i k) ^ 2

theorem correctedCorrected_term_eq_endpointAtom_term
    (a : CorrectionsFrom e) (b : CorrectionsFrom f) :
    sidePairDetSquare (corrected a.1) (corrected b.1) =
      correctedContrastTerm e f
        (correctionEquivEndpointAtom e a).1
        (correctionEquivEndpointAtom f b).1 := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  subst e
  subst f
  symm
  simpa [correctedContrastTerm, correctionEquivEndpointAtom,
      correctionSlot, correctionFromFirst, endpointAtomEquiv] using
    corrected_contrast_sq_eq_sidePairDetSquare a b

/-- The complete corrected/corrected determinant level is exactly the
double endpoint neighboring sum used in concrete `(A.15b)`. -/
theorem correctedCorrected_eq_correctedNeighboring :
    correctedCorrected
        (correctionSystem T₁) (correctionSystem T₂) e f =
      correctedNeighboring e f := by
  unfold correctedCorrected correctedNeighboring
    OccurrenceSettlement.neighboringN
  change
    (∑ a ∈ (correctionSystem T₁).fiber e,
        ∑ b ∈ (correctionSystem T₂).fiber f,
          sidePairDetSquare (corrected a) (corrected b)) =
      ∑ k ∈ (Pc f).endpoint,
        ∑ i ∈ (Pr e).endpoint, correctedContrastTerm e f i k
  rw [sum_fiber_eq_sum_correctionsFrom e
    (fun a =>
      ∑ b ∈ (correctionSystem T₂).fiber f,
        sidePairDetSquare (corrected a) (corrected b))]
  have hinner :
      ∀ a : CorrectionsFrom e,
        (∑ b ∈ (correctionSystem T₂).fiber f,
            sidePairDetSquare (corrected a.1) (corrected b)) =
          ∑ b : CorrectionsFrom f,
            sidePairDetSquare (corrected a.1) (corrected b.1) := by
    intro a
    exact sum_fiber_eq_sum_correctionsFrom f
      (fun b => sidePairDetSquare (corrected a.1) (corrected b))
  simp_rw [hinner]
  calc
    (∑ a : CorrectionsFrom e, ∑ b : CorrectionsFrom f,
        sidePairDetSquare (corrected a.1) (corrected b.1)) =
        ∑ i : EndpointAtomIndex e,
          ∑ k : EndpointAtomIndex f,
            correctedContrastTerm e f i.1 k.1 := by
      apply Fintype.sum_equiv
        (correctionEquivEndpointAtom e)
        (fun a : CorrectionsFrom e =>
          ∑ b : CorrectionsFrom f,
            sidePairDetSquare (corrected a.1) (corrected b.1))
        (fun i : EndpointAtomIndex e =>
          ∑ k : EndpointAtomIndex f,
            correctedContrastTerm e f i.1 k.1)
      intro a
      exact Fintype.sum_equiv
        (correctionEquivEndpointAtom f)
        (fun b : CorrectionsFrom f =>
          sidePairDetSquare (corrected a.1) (corrected b.1))
        (fun k : EndpointAtomIndex f =>
          correctedContrastTerm e f
            (correctionEquivEndpointAtom e a).1 k.1)
        (fun b =>
          correctedCorrected_term_eq_endpointAtom_term e f a b)
    _ =
        ∑ i ∈ (Pr e).endpoint,
          ∑ k ∈ (Pc f).endpoint,
            correctedContrastTerm e f i k := by
      calc
        (∑ i : EndpointAtomIndex e,
            ∑ k : EndpointAtomIndex f,
              correctedContrastTerm e f i.1 k.1) =
            ∑ i : EndpointAtomIndex e,
              ∑ k ∈ (Pc f).endpoint,
                correctedContrastTerm e f i.1 k := by
          apply Fintype.sum_congr
          intro i
          exact sum_endpointAtomIndex_eq_endpoint f
            (fun k => correctedContrastTerm e f i.1 k)
        _ =
            ∑ i ∈ (Pr e).endpoint,
              ∑ k ∈ (Pc f).endpoint,
                correctedContrastTerm e f i k := by
          exact sum_endpointAtomIndex_eq_endpoint e
            (fun i =>
              ∑ k ∈ (Pc f).endpoint,
                correctedContrastTerm e f i k)
    _ =
        ∑ k ∈ (Pc f).endpoint,
          ∑ i ∈ (Pr e).endpoint,
            correctedContrastTerm e f i k := by
      rw [Finset.sum_comm]

theorem ordinarySquare_comm :
    ordinarySquare e f = ordinarySquare f e := by
  calc
    ordinarySquare e f =
        ordinaryOrdinary
          (correctionSystem T₁) (correctionSystem T₂) e f := by
      symm
      exact ordinaryOrdinary_eq_ordinarySquare e f
    _ = splitDetSquare (ordinary T₁ e) (ordinary T₂ f) := rfl
    _ = splitDetSquare (ordinary T₂ f) (ordinary T₁ e) :=
      splitDetSquare_comm (ordinary T₁ e) (ordinary T₂ f)
    _ =
        ordinaryOrdinary
          (correctionSystem T₂) (correctionSystem T₁) f e := rfl
    _ = ordinarySquare f e :=
      ordinaryOrdinary_eq_ordinarySquare f e

theorem ordinaryCorrected_eq_transposed_correctedOrdinary :
    ordinaryCorrected
        (correctionSystem T₁) (correctionSystem T₂) e f =
      correctedOrdinary
        (correctionSystem T₂) (correctionSystem T₁) f e := by
  unfold ordinaryCorrected correctedOrdinary
  change
    (∑ b ∈ (correctionSystem T₂).fiber f,
        splitSidePairDetSquare (ordinary T₁ e) (corrected b)) =
      ∑ b ∈ (correctionSystem T₂).fiber f,
        sidePairSplitDetSquare (corrected b) (ordinary T₁ e)
  apply Finset.sum_congr rfl
  intro b hb
  exact
    splitSidePairDetSquare_eq_sidePairSplitDetSquare
      (ordinary T₁ e) (corrected b)

theorem actual_rowResidual :
    correctedOrdinary
        (correctionSystem T₁) (correctionSystem T₂) e f =
      ordinaryOrdinary
          (correctionSystem T₁) (correctionSystem T₂) e f -
        R1Abstract e f + Q1 e f := by
  rw [correctedOrdinary_eq_ordinaryNeighboring]
  rw [ordinaryOrdinary_eq_ordinarySquare]
  linarith [A15a e f]

theorem actual_colResidual :
    ordinaryCorrected
        (correctionSystem T₁) (correctionSystem T₂) e f =
      ordinaryOrdinary
          (correctionSystem T₁) (correctionSystem T₂) e f -
        R1Abstract f e + Q1 f e := by
  rw [ordinaryCorrected_eq_transposed_correctedOrdinary]
  rw [correctedOrdinary_eq_ordinaryNeighboring]
  rw [ordinaryOrdinary_eq_ordinarySquare]
  rw [ordinarySquare_comm]
  linarith [A15a f e]

theorem actual_neighborResidual :
    correctedCorrected
        (correctionSystem T₁) (correctionSystem T₂) e f =
      ordinaryCorrected
          (correctionSystem T₁) (correctionSystem T₂) e f -
        R2Retained e f + Q2 e f := by
  rw [correctedCorrected_eq_correctedNeighboring]
  rw [ordinaryCorrected_eq_sum_neighborSquare]
  linarith [A15b e f]

/-- The exact seven-source data of one actual principal chart.  No local
symbol in this structure is free-standing: every one has already been
identified with its corresponding finite-tree determinant level. -/
noncomputable def concreteSevenSourceData : SevenSourceData where
  U :=
    ordinaryOrdinary
      (correctionSystem T₁) (correctionSystem T₂) e f
  R :=
    correctedOrdinary
      (correctionSystem T₁) (correctionSystem T₂) e f
  C :=
    ordinaryCorrected
      (correctionSystem T₁) (correctionSystem T₂) e f
  B :=
    correctedCorrected
      (correctionSystem T₁) (correctionSystem T₂) e f
  R1 := R1Abstract e f
  Q1 := Q1 e f
  R1transpose := R1Abstract f e
  Q1transpose := Q1 f e
  R2 := R2Retained e f
  Q2 := Q2 e f
  rowResidual := actual_rowResidual e f
  colResidual := actual_colResidual e f
  neighborResidual := actual_neighborResidual e f

theorem concrete_fourLevel_eq_sevenSource :
    (concreteSevenSourceData e f).fourLevelNumerator =
      (concreteSevenSourceData e f).sevenSourceNumerator :=
  SevenSourceData.fourLevel_eq_sevenSource
    (concreteSevenSourceData e f)

end

end ConcreteDeterminantLevels

end QuartetV060
