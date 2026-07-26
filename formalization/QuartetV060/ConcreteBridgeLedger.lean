import QuartetV060.PrincipalChart
import QuartetV060.PackageLedger

/-!
# Concrete coefficient transport along bridge reversal

The completed-square data are constructed from actual taxon blocks.  Reversal
of an ordered adjacent edge swaps the selected and opposite blocks, so the
second-square coefficient of a package is definitionally transported to the
first-square coefficient of the reversed package.
-/

namespace QuartetV060

namespace ConcreteBridgeLedger

open scoped BigOperators

open QuartetDistance
open PhyloOccurrences
open PhyloBridgeReversal
open PrincipalAtoms
open PrincipalChart

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

/-- Uniform normalized mass of an actual taxon block. -/
def mass (A : Finset X) : ℝ :=
  (A.card : ℝ) / (Fintype.card X : ℝ)

theorem card_X_real_pos : (0 : ℝ) < Fintype.card X := by
  exact_mod_cast (Fintype.card_pos_iff.mpr
    (inferInstance : Nonempty X))

theorem mass_nonneg (A : Finset X) :
    0 ≤ mass A := by
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt card_X_real_pos)

theorem mass_pos {A : Finset X} (hA : A.Nonempty) :
    0 < mass A := by
  exact div_pos
    (by exact_mod_cast (Finset.card_pos.mpr hA))
    card_X_real_pos

theorem mass_compl (A : Finset X) :
    mass Aᶜ = 1 - mass A := by
  unfold mass
  rw [Finset.card_compl]
  rw [Nat.cast_sub (Finset.card_le_univ A)]
  have hN : (Fintype.card X : ℝ) ≠ 0 :=
    ne_of_gt card_X_real_pos
  field_simp [hN]

/-- The real-valued block mass is the cast of the rational normalization used
by the concrete joint-mass table. -/
theorem mass_eq_ratCast (A : Finset X) :
    mass A =
      (((A.card : ℚ) / (Fintype.card X : ℚ)) : ℝ) := by
  unfold mass
  norm_cast

theorem correctionK_union_middle_eq_correctionL_compl
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    correctionK a ∪ (bridgeBlocks a).H =
      (correctionL a)ᶜ := by
  ext x
  have hdisj := correctionK_disjoint_correctionL a
  rw [Finset.disjoint_left] at hdisj
  simp only [bridgeBlocks_H, Finset.mem_union, Finset.mem_compl]
  constructor
  · intro hx
    rcases hx with hxK | hnot
    · exact fun hxL => hdisj hxK hxL
    · exact fun hxL => hnot (Or.inr hxL)
  · intro hxL
    by_cases hxK : x ∈ correctionK a
    · exact Or.inl hxK
    · exact Or.inr (by
        intro hx
        rcases hx with hxK' | hxL'
        · exact hxK hxK'
        · exact hxL hxL')

/-- The actual masses and row intersections used by one package.  The
`cKplus` field is the mass of `K ∪ H`, written as `Lᶜ` using the concrete
three-block partition. -/
def endpointData
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    CompletedSquares.EndpointData where
  cK := mass (correctionK a)
  cB := mass (correctionL a)
  cKplus := mass (correctionL a)ᶜ
  aiK := mass (PrincipalAtoms.block e i ∩ correctionK a)
  ajK := mass (PrincipalAtoms.block e j ∩ correctionK a)
  aiB := mass (PrincipalAtoms.block e i ∩ correctionL a)
  ajB := mass (PrincipalAtoms.block e j ∩ correctionL a)

/-- The same seven coefficients, now written entirely in the actual
principal-chart joint mass table. -/
def chartEndpointData
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    CompletedSquares.EndpointData :=
  let f := first a
  let k :=
    endpointAtom f (correctionSlot a)
  let J := jointMass e f
  let B := (fourSector f).oppositeSideBlock k
  {
    cK := (J.colMass k : ℝ)
    cB := (J.colBlockMass B : ℝ)
    cKplus := 1 - (J.colBlockMass B : ℝ)
    aiK := (J.a i k : ℝ)
    ajK := (J.a j k : ℝ)
    aiB := (J.mixedBlockMass i B : ℝ)
    ajB := (J.mixedBlockMass j B : ℝ)
  }

/-- The concrete bridge data are literally the masses of the selected
endpoint atom and its full opposite-side block in the source chart.  This is
the exact interface from the geometric `(K,H,L)` bridge to the coefficients
used in `(A.21a)`--`(A.25)`. -/
theorem endpointData_eq_chartEndpointData
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    endpointData e a i j =
      chartEndpointData e a i j := by
  let f := first a
  let k := endpointAtom f (correctionSlot a)
  let B := (fourSector f).oppositeSideBlock k
  have hK :
      correctionK a = block f k := by
    simpa [f, k] using correctionK_eq_selectedAtomBlock a
  have hB :
      correctionL a = aggregateBlock f B := by
    simpa [f, k, B] using
      (aggregateBlock_opposite_selected_eq_correctionL a).symm
  apply CompletedSquares.EndpointData.ext
  · unfold endpointData chartEndpointData
    dsimp [f, k, B]
    rw [hK, jointMass_colMass_eq, mass_eq_ratCast]
    norm_cast
  · unfold endpointData chartEndpointData
    dsimp [f, k, B]
    rw [hB, jointMass_colBlockMass_eq, mass_eq_ratCast]
    norm_cast
  · unfold endpointData chartEndpointData
    dsimp [f, k, B]
    rw [mass_compl, hB, jointMass_colBlockMass_eq,
      mass_eq_ratCast]
    norm_cast
  · unfold endpointData chartEndpointData
    dsimp [f, k, B]
    rw [hK, jointMass_a, mass_eq_ratCast]
    norm_cast
  · unfold endpointData chartEndpointData
    dsimp [f, k, B]
    rw [hK, jointMass_a, mass_eq_ratCast]
    norm_cast
  · unfold endpointData chartEndpointData
    dsimp [f, k, B]
    rw [hB, jointMass_mixedBlockMass_eq, mass_eq_ratCast]
    norm_cast
  · unfold endpointData chartEndpointData
    dsimp [f, k, B]
    rw [hB, jointMass_mixedBlockMass_eq, mass_eq_ratCast]
    norm_cast

theorem endpointData_cKplus_eq_sameSide
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    (endpointData e a i j).cKplus =
      mass (correctionK a ∪ (bridgeBlocks a).H) := by
  unfold endpointData
  rw [correctionK_union_middle_eq_correctionL_compl]

theorem endpointData_nonnegative
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    (endpointData e a i j).Nonnegative := by
  repeat' apply And.intro
  all_goals exact mass_nonneg _

theorem endpointData_cK_pos
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    0 < (endpointData e a i j).cK := by
  exact mass_pos (correctionK_nonempty a)

theorem endpointData_cB_pos
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    0 < (endpointData e a i j).cB := by
  exact mass_pos (correctionL_nonempty a)

theorem endpointData_cKplus_pos
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    0 < (endpointData e a i j).cKplus := by
  apply mass_pos
  obtain ⟨x, hx⟩ := correctionK_nonempty a
  refine ⟨x, Finset.mem_compl.mpr ?_⟩
  exact fun hxL =>
    Finset.disjoint_left.mp
      (correctionK_disjoint_correctionL a) hx hxL

theorem endpointData_cK_lt_one
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    (endpointData e a i j).cK < 1 := by
  unfold endpointData mass
  apply (div_lt_one card_X_real_pos).2
  have hcardUnion :
      (correctionK a ∪ correctionL a).card =
        (correctionK a).card + (correctionL a).card :=
    Finset.card_union_of_disjoint
      (correctionK_disjoint_correctionL a)
  have hle :
      (correctionK a ∪ correctionL a).card ≤
        Fintype.card X := by
    simpa using Finset.card_le_card
      (Finset.subset_univ
        (correctionK a ∪ correctionL a))
  have hLpos : 0 < (correctionL a).card :=
    Finset.card_pos.mpr (correctionL_nonempty a)
  have hKcard :
      (correctionK a).card < Fintype.card X := by
    omega
  exact_mod_cast hKcard

theorem endpointData_cKplus_eq_one_sub_cB
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    (endpointData e a i j).cKplus =
      1 - (endpointData e a i j).cB := by
  exact mass_compl (correctionL a)

/-- Concrete coefficient data are reversed exactly by
`(K,H,L) ↦ (L,H,K)`. -/
theorem endpointData_reverse
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    endpointData e (reverseCorrection a) i j =
      (endpointData e a i j).reverse := by
  apply CompletedSquares.EndpointData.ext
  · simp [endpointData]
  · simp [endpointData]
  · simp [endpointData, mass_compl]
  · simp [endpointData]
  · simp [endpointData]
  · simp [endpointData]
  · simp [endpointData]

/-- The total second-square coefficient in one source package is the total
first-square coefficient in the reversed principal chart. -/
theorem package_second_eq_reversed_first
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (a : AdjacentCorrection T₂)
    (i j : PrincipalAtoms.Atom e) :
    (endpointData e a i j).packageCoeff.yy =
      (endpointData e (reverseCorrection a) i j).packageCoeff.xx := by
  rw [endpointData_reverse]
  exact
    (endpointData e a i j).packageCoeff_yy_eq_reverse_xx
      (endpointData_cKplus_eq_one_sub_cB e a i j)

/-- Reversal as an equivalence on the complete ordered adjacent-edge range. -/
noncomputable def reversalEquiv
    (T : Tree.PhyloTree X) :
    AdjacentCorrection T ≃ AdjacentCorrection T where
  toFun := reverseCorrection
  invFun := reverseCorrection
  left_inv := reverseCorrection_reverseCorrection
  right_inv := reverseCorrection_reverseCorrection

@[simp] theorem reversalEquiv_apply
    {T : Tree.PhyloTree X}
    (a : AdjacentCorrection T) :
    reversalEquiv T a = reverseCorrection a :=
  rfl

/-- The coefficient-preserving omitted-face/target-face identity on the
complete column bridge range. -/
theorem sum_package_second_eq_first
    {T₁ T₂ : Tree.PhyloTree X}
    (e : RelevantEdge T₁)
    (i j : PrincipalAtoms.Atom e)
    (Z W : AdjacentCorrection T₂ → ℝ)
    (hW : ∀ a,
      W a ^ 2 = Z (reverseCorrection a) ^ 2) :
    (∑ a : AdjacentCorrection T₂,
        (endpointData e a i j).packageCoeff.yy * W a ^ 2) =
      ∑ a : AdjacentCorrection T₂,
        (endpointData e a i j).packageCoeff.xx * Z a ^ 2 := by
  apply PackageLedger.sum_package_second_eq_first
    (reversalEquiv T₂)
    (fun a => (endpointData e a i j).packageCoeff.xx)
    (fun a => (endpointData e a i j).packageCoeff.yy)
    Z W
  · intro a
    exact package_second_eq_reversed_first e a i j
  · exact hW

/-- One concrete row-boundary summand for a block-additive weight `w` and
a chart-independent block form `z`.  In the source chart the representative
forms are evaluated on the opposite and selected outer blocks, respectively. -/
def boundaryContribution
    {T : Tree.PhyloTree X}
    (w z : Finset X → ℚ)
    (a : AdjacentCorrection T) : ℚ :=
  (w (correctionK a) + w (correctionL a)) *
    (w (correctionK a) * z (correctionL a) ^ 2 -
      w (correctionL a) * z (correctionK a) ^ 2)

/-- Concrete bridge reversal negates the complete boundary summand. -/
theorem boundaryContribution_reverse
    {T : Tree.PhyloTree X}
    (w z : Finset X → ℚ)
    (a : AdjacentCorrection T) :
    boundaryContribution w z (reverseCorrection a) =
      -boundaryContribution w z a := by
  unfold boundaryContribution
  simp only [correctionK_reverseCorrection,
    correctionL_reverseCorrection]
  ring

/-- The row-boundary polynomial cancels on the complete ordered bridge
range.  This is the concrete tree-level form of `(A.29c₁)`. -/
theorem sum_boundaryContribution_eq_zero
    {T : Tree.PhyloTree X}
    (w z : Finset X → ℚ) :
    (∑ a : AdjacentCorrection T,
      boundaryContribution w z a) = 0 := by
  exact
    BridgeSystem.sum_eq_zero_of_antiInvariant
      (bridgeSystem T)
      (boundaryContribution w z)
      (boundaryContribution_reverse w z)

end

end ConcreteBridgeLedger

end QuartetV060
