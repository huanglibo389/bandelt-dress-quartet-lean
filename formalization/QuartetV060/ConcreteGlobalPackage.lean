import QuartetV060.ConcretePackageSettlement

/-!
# Global endpoint-face cancellation and package extraction

This file completes the passage `(A.29d)`--`(A.29f)` for the concrete
principal charts.  The positive ordered column pool is first partitioned
into `I ∪ D` and the endpoint diagonal.  The endpoint diagonal is then
combined with the expanded neighboring square.  Only after summing the
complete ordered column-bridge range is the first/second-face cancellation
performed.
-/

namespace QuartetV060

namespace ConcreteGlobalPackage

open scoped BigOperators

open QuartetDistance
open PhyloOccurrences
open PrincipalBranches
open PrincipalAtoms
open PrincipalChart
open ConcreteRetainedSquares
open ConcreteDeterminantLevels
open ConcreteOccurrenceSettlement
open ConcreteRowSettlement
open ConcretePackageSettlement

noncomputable section

variable {X : Type}
    [Fintype X] [Nonempty X] [DecidableEq X]

variable
    {T₁ T₂ : Tree.PhyloTree X}

/-! ## Finite reindexing lemmas -/

theorem sum_endpointAtomIndex_eq_endpoint_real
    (f : RelevantEdge T₂) (g : Atom f → ℝ) :
    (∑ k : EndpointAtomIndex f, g k.1) =
      ∑ k ∈ (Pc f).endpoint, g k := by
  change
    (∑ k : {k : Atom f // (fourSector f).isEndpoint k}, g k.1) =
      ∑ k ∈ (Pc f).endpoint, g k
  unfold Pc residualPartition
  rw [← Finset.sum_subtype_eq_sum_filter]
  simp

theorem sum_corrections_by_source_real
    (g : AdjacentCorrection T₂ → ℝ) :
    (∑ f : RelevantEdge T₂, ∑ a : CorrectionsFrom f, g a.1) =
      ∑ a : AdjacentCorrection T₂, g a := by
  calc
    (∑ f : RelevantEdge T₂, ∑ a : CorrectionsFrom f, g a.1) =
        ∑ z : Σ f : RelevantEdge T₂, CorrectionsFrom f, g z.2.1 := by
      symm
      exact Fintype.sum_sigma
        (fun z : Σ f : RelevantEdge T₂, CorrectionsFrom f => g z.2.1)
    _ = ∑ a : AdjacentCorrection T₂, g a :=
      (sigmaCorrectionsEquiv T₂).sum_comp g

theorem sum_pair_slices
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset (C × C)) (F : C × C → ℝ) :
    (∑ u : C, ∑ z ∈ S, if z.1 = u then F z else 0) =
      ∑ z ∈ S, F z := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp

theorem rearrange_package_sum
    {ι : Type*} [Fintype ι]
    (A D Z M P : ι → ℝ)
    (h :
      (∑ x : ι, (2 * A x * Z x ^ 2 + M x)) =
        ∑ x : ι, (P x + 2 * (A x - D x) * Z x ^ 2)) :
    (∑ x : ι, M x) =
      (∑ x : ι, P x) -
        2 * ∑ x : ι, D x * Z x ^ 2 := by
  have hleft :
      (∑ x : ι, (2 * A x * Z x ^ 2 + M x)) =
        2 * (∑ x : ι, A x * Z x ^ 2) +
          ∑ x : ι, M x := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Fintype.sum_congr
    intro x
    ring
  have hright :
      (∑ x : ι, (P x + 2 * (A x - D x) * Z x ^ 2)) =
        (∑ x : ι, P x) +
          2 * ((∑ x : ι, A x * Z x ^ 2) -
            ∑ x : ι, D x * Z x ^ 2) := by
    rw [Finset.sum_add_distrib]
    congr 1
    calc
      (∑ x : ι, 2 * (A x - D x) * Z x ^ 2) =
          ∑ x : ι,
            2 * (A x * Z x ^ 2 - D x * Z x ^ 2) := by
        apply Fintype.sum_congr
        intro x
        ring
      _ =
          2 * ∑ x : ι,
            (A x * Z x ^ 2 - D x * Z x ^ 2) := by
        rw [Finset.mul_sum]
      _ =
          2 * ((∑ x : ι, A x * Z x ^ 2) -
            ∑ x : ι, D x * Z x ^ 2) := by
        rw [Finset.sum_sub_distrib]
  rw [hleft, hright] at h
  linarith

/-! ## The positive ordered pool -/

def positivePool
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (Z : Atom f → ℚ) : ℚ :=
  ∑ u : Atom f, ∑ l : Atom f,
    alpha e f i u * alpha e f j l * Z u ^ 2

def availablePool
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (Z : Atom f → ℚ) : ℚ :=
  ∑ z ∈ (Pc f).I ∪ (Pc f).D,
    alpha e f i z.1 * alpha e f j z.2 * Z z.1 ^ 2

def endpointDiagonalPool
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (Z : Atom f → ℚ) : ℚ :=
  ∑ k ∈ (Pc f).endpoint,
    c e f k ^ 2 * r e f i k * r e f j k * Z k ^ 2

theorem positivePool_partition
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (Z : Atom f → ℚ) :
    positivePool e f i j Z =
      availablePool e f i j Z +
        endpointDiagonalPool e f i j Z := by
  let F : Atom f × Atom f → ℚ :=
    fun z =>
      alpha e f i z.1 * alpha e f j z.2 * Z z.1 ^ 2
  have hpart := (Pc f).sum_partition F
  have hID :
      (∑ z ∈ (Pc f).I ∪ (Pc f).D, F z) =
        (∑ z ∈ (Pc f).I, F z) +
          ∑ z ∈ (Pc f).D, F z := by
    rw [Finset.sum_union]
    exact
      (Pc f).disjoint_I_rest.mono_right
        (Finset.subset_union_left)
  have hdiag :
      (∑ z ∈ (Pc f).deltaE, F z) =
        endpointDiagonalPool e f i j Z := by
    rw [(Pc f).sum_deltaE F]
    unfold endpointDiagonalPool F alpha
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hall :
      positivePool e f i j Z =
        ∑ z ∈ (Pc f).allPairs, F z := by
    unfold positivePool
    rw [Finset.sum_finset_product
      (Pc f).allPairs Finset.univ (fun _ : Atom f => Finset.univ)]
    intro z
    simp [ResidualPartition.allPairs]
  rw [hall]
  change
    (∑ z ∈ (Pc f).allPairs, F z) =
      availablePool e f i j Z +
        endpointDiagonalPool e f i j Z
  unfold availablePool
  change
    (∑ z ∈ (Pc f).allPairs, F z) =
      (∑ z ∈ (Pc f).I ∪ (Pc f).D, F z) +
        endpointDiagonalPool e f i j Z
  rw [hID]
  calc
    (∑ z ∈ (Pc f).allPairs, F z) =
        (∑ z ∈ (Pc f).I, F z) +
          (∑ z ∈ (Pc f).D, F z) +
            ∑ z ∈ (Pc f).deltaE, F z := hpart
    _ =
        (∑ z ∈ (Pc f).I, F z) +
          (∑ z ∈ (Pc f).D, F z) +
            endpointDiagonalPool e f i j Z := by
      rw [hdiag]

theorem availableCoefficient_sum
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (Z : Atom f → ℚ) :
    (∑ u : Atom f,
      availableCoefficient e f i j u * (Z u : ℝ) ^ 2) =
      (availablePool e f i j Z : ℝ) := by
  let F : Atom f × Atom f → ℚ :=
    fun z =>
      c e f z.1 * c e f z.2 *
        r e f i z.1 * r e f j z.2
  have hslice :
      (∑ u : Atom f,
        ∑ z ∈ (Pc f).I ∪ (Pc f).D,
          if z.1 = u then F z * Z u ^ 2 else 0) =
        ∑ z ∈ (Pc f).I ∪ (Pc f).D,
          F z * Z z.1 ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    simp
  calc
    (∑ u : Atom f,
        availableCoefficient e f i j u * (Z u : ℝ) ^ 2) =
        ((∑ u : Atom f,
          ∑ z ∈ (Pc f).I ∪ (Pc f).D,
            if z.1 = u then F z * Z u ^ 2 else 0 : ℚ) : ℝ) := by
      unfold availableCoefficient F
      push_cast
      apply Fintype.sum_congr
      intro u
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      split <;> push_cast <;> ring
    _ =
        ((∑ z ∈ (Pc f).I ∪ (Pc f).D,
          F z * Z z.1 ^ 2 : ℚ) : ℝ) := by
      rw [hslice]
    _ = (availablePool e f i j Z : ℝ) := by
      congr 1
      unfold availablePool alpha F
      apply Finset.sum_congr rfl
      intro z hz
      ring

/-! ## Expansion of one direct row polynomial -/

def endpointRemainder
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (Z W : Atom f → ℚ) : ℝ :=
  ∑ k ∈ (Pc f).endpoint,
    (((c e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
          (Z k : ℝ) ^ 2 +
        ((2 * c e f k * cbar e f k *
            r e f i k * r e f j k : ℚ) : ℝ) *
          Z k * W k -
        ((cbar e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
          (W k : ℝ) ^ 2)

def endpointRemainderI
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) : ℝ :=
  endpointRemainder e f i j (ZI e f i) (WI e f i)

def endpointRemainderD
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) : ℝ :=
  endpointRemainder e f i j (ZD e f i) (WD e f i)

theorem endpoint_expansion
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (Z W : Atom f → ℚ) :
    2 * (endpointDiagonalPool e f i j Z : ℝ) -
        (∑ k ∈ (Pc f).endpoint,
          (r e f i k : ℝ) * r e f j k *
            ((c e f k : ℝ) * Z k -
              (cbar e f k : ℝ) * W k) ^ 2) =
      endpointRemainder e f i j Z W := by
  unfold endpointDiagonalPool endpointRemainder
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem directRowI_expanded
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) :
    (directRowI e f (i, j) : ℝ) =
      2 * ∑ u : Atom f,
        availableCoefficient e f i j u *
          (ZI e f i u : ℝ) ^ 2 +
        endpointRemainderI e f i j := by
  unfold directRowI
  simp only [Prod.fst, Prod.snd]
  rw [show
    (∑ u : Atom f, ∑ l : Atom f,
      alpha e f i u * alpha e f j l * ZI e f i u ^ 2) =
        positivePool e f i j (ZI e f i) by rfl]
  rw [positivePool_partition e f i j (ZI e f i)]
  push_cast
  rw [availableCoefficient_sum e f i j (ZI e f i)]
  unfold endpointRemainderI
  have hendpoint :=
    endpoint_expansion e f i j (ZI e f i) (WI e f i)
  linarith

theorem directRowD_expanded
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) :
    (directRowD e f (i, j) : ℝ) =
      2 * ∑ u : Atom f,
        availableCoefficient e f i j u *
          (ZD e f i u : ℝ) ^ 2 +
        endpointRemainderD e f i j := by
  unfold directRowD
  simp only [Prod.fst, Prod.snd]
  rw [show
    (∑ u : Atom f, ∑ l : Atom f,
      alpha e f i u * alpha e f j l * ZD e f i u ^ 2) =
        positivePool e f i j (ZD e f i) by rfl]
  rw [positivePool_partition e f i j (ZD e f i)]
  push_cast
  rw [availableCoefficient_sum e f i j (ZD e f i)]
  unfold endpointRemainderD
  have hendpoint :=
    endpoint_expansion e f i j (ZD e f i) (WD e f i)
  linarith

/-! ## Reindexing endpoint atoms by ordered adjacent corrections -/

def correctionEndpointTermI
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) : ℝ :=
  firstFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) *
      (correctionZI e i a : ℝ) ^ 2 +
    mixedFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) *
      correctionZI e i a * correctionWI e i a -
    secondFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) *
      (correctionWI e i a : ℝ) ^ 2

def correctionEndpointTermD
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) : ℝ :=
  firstFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) *
      (correctionZD e i a : ℝ) ^ 2 +
    mixedFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) *
      correctionZD e i a * correctionWD e i a -
    secondFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) *
      (correctionWD e i a : ℝ) ^ 2

def correctionMixedI
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) : ℝ :=
  mixedFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) *
    correctionZI e i a * correctionWI e i a

def correctionMixedD
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) : ℝ :=
  mixedFaceCoeff (ConcreteBridgeLedger.endpointData e a i j) *
    correctionZD e i a * correctionWD e i a

theorem correctionMixedI_eq_packageMixed
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionMixedI e i j a =
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
        correctionZI e i a * correctionWI e i a := by
  unfold correctionMixedI
  rw [packageCoeff_xy_eq_mixedFaceCoeff
    (ConcreteBridgeLedger.endpointData e a i j)
    (ne_of_gt
      (ConcreteBridgeLedger.endpointData_cK_pos e a i j))
    (ne_of_gt
      (ConcreteBridgeLedger.endpointData_cB_pos e a i j))]

theorem correctionMixedD_eq_packageMixed
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) :
    correctionMixedD e i j a =
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
        correctionZD e i a * correctionWD e i a := by
  unfold correctionMixedD
  rw [packageCoeff_xy_eq_mixedFaceCoeff
    (ConcreteBridgeLedger.endpointData e a i j)
    (ne_of_gt
      (ConcreteBridgeLedger.endpointData_cK_pos e a i j))
    (ne_of_gt
      (ConcreteBridgeLedger.endpointData_cB_pos e a i j))]

theorem correctionEndpointTermI_eq_chart
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (a : CorrectionsFrom f) :
    correctionEndpointTermI e i j a.1 =
      let k := (correctionEquivEndpointAtom f a).1
      (((c e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
          (ZI e f i k : ℝ) ^ 2 +
        ((2 * c e f k * cbar e f k *
            r e f i k * r e f j k : ℚ) : ℝ) *
          ZI e f i k * WI e f i k -
        ((cbar e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
          (WI e f i k : ℝ) ^ 2) := by
  rcases a with ⟨a, ha⟩
  subst f
  simp only [correctionEndpointTermI]
  rw [firstFaceCoeff_eq_chart, mixedFaceCoeff_eq_chart,
    secondFaceCoeff_eq_chart, correctionZI_eq_chart,
    correctionWI_eq_chart]
  simp [correctionEquivEndpointAtom, correctionSlot,
    correctionFromFirst, endpointAtomEquiv, selectedColumnAtom]

theorem correctionEndpointTermD_eq_chart
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (a : CorrectionsFrom f) :
    correctionEndpointTermD e i j a.1 =
      let k := (correctionEquivEndpointAtom f a).1
      (((c e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
          (ZD e f i k : ℝ) ^ 2 +
        ((2 * c e f k * cbar e f k *
            r e f i k * r e f j k : ℚ) : ℝ) *
          ZD e f i k * WD e f i k -
        ((cbar e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
          (WD e f i k : ℝ) ^ 2) := by
  rcases a with ⟨a, ha⟩
  subst f
  simp only [correctionEndpointTermD]
  rw [firstFaceCoeff_eq_chart, mixedFaceCoeff_eq_chart,
    secondFaceCoeff_eq_chart, correctionZD_eq_chart,
    correctionWD_eq_chart]
  simp [correctionEquivEndpointAtom, correctionSlot,
    correctionFromFirst, endpointAtomEquiv, selectedColumnAtom]

theorem endpointRemainderI_reindex
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂, endpointRemainderI e f i j) =
      ∑ a : AdjacentCorrection T₂,
        correctionEndpointTermI e i j a := by
  calc
    (∑ f : RelevantEdge T₂, endpointRemainderI e f i j) =
        ∑ f : RelevantEdge T₂, ∑ k ∈ (Pc f).endpoint,
          (((c e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
              (ZI e f i k : ℝ) ^ 2 +
            ((2 * c e f k * cbar e f k *
                r e f i k * r e f j k : ℚ) : ℝ) *
              ZI e f i k * WI e f i k -
            ((cbar e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
              (WI e f i k : ℝ) ^ 2) := by rfl
    _ =
        ∑ f : RelevantEdge T₂, ∑ a : CorrectionsFrom f,
          correctionEndpointTermI e i j a.1 := by
      apply Fintype.sum_congr
      intro f
      calc
        (∑ k ∈ (Pc f).endpoint,
            (((c e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
                (ZI e f i k : ℝ) ^ 2 +
              ((2 * c e f k * cbar e f k *
                  r e f i k * r e f j k : ℚ) : ℝ) *
                ZI e f i k * WI e f i k -
              ((cbar e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
                (WI e f i k : ℝ) ^ 2)) =
            ∑ k : EndpointAtomIndex f,
              (((c e f k.1 ^ 2 * r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                  (ZI e f i k.1 : ℝ) ^ 2 +
                ((2 * c e f k.1 * cbar e f k.1 *
                    r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                  ZI e f i k.1 * WI e f i k.1 -
                ((cbar e f k.1 ^ 2 *
                    r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                  (WI e f i k.1 : ℝ) ^ 2) := by
          symm
          convert
            (sum_endpointAtomIndex_eq_endpoint_real f
              (fun k =>
                (c e f k : ℝ) ^ 2 *
                      (r e f i k : ℝ) * (r e f j k : ℝ) *
                      (ZI e f i k : ℝ) ^ 2 +
                  2 * (c e f k : ℝ) * (cbar e f k : ℝ) *
                      (r e f i k : ℝ) * (r e f j k : ℝ) *
                      (ZI e f i k : ℝ) * (WI e f i k : ℝ) -
                  (cbar e f k : ℝ) ^ 2 *
                      (r e f i k : ℝ) * (r e f j k : ℝ) *
                      (WI e f i k : ℝ) ^ 2)) using 1 <;>
            push_cast <;> ring
        _ =
            ∑ a : CorrectionsFrom f,
              correctionEndpointTermI e i j a.1 := by
          symm
          exact Fintype.sum_equiv
            (correctionEquivEndpointAtom f)
            (fun a : CorrectionsFrom f =>
              correctionEndpointTermI e i j a.1)
            (fun k : EndpointAtomIndex f =>
              (((c e f k.1 ^ 2 *
                  r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                    (ZI e f i k.1 : ℝ) ^ 2 +
                ((2 * c e f k.1 * cbar e f k.1 *
                    r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                    ZI e f i k.1 * WI e f i k.1 -
                ((cbar e f k.1 ^ 2 *
                    r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                    (WI e f i k.1 : ℝ) ^ 2))
            (correctionEndpointTermI_eq_chart e f i j)
    _ = ∑ a : AdjacentCorrection T₂,
          correctionEndpointTermI e i j a :=
      sum_corrections_by_source_real _

theorem endpointRemainderD_reindex
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂, endpointRemainderD e f i j) =
      ∑ a : AdjacentCorrection T₂,
        correctionEndpointTermD e i j a := by
  calc
    (∑ f : RelevantEdge T₂, endpointRemainderD e f i j) =
        ∑ f : RelevantEdge T₂, ∑ k ∈ (Pc f).endpoint,
          (((c e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
              (ZD e f i k : ℝ) ^ 2 +
            ((2 * c e f k * cbar e f k *
                r e f i k * r e f j k : ℚ) : ℝ) *
              ZD e f i k * WD e f i k -
            ((cbar e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
              (WD e f i k : ℝ) ^ 2) := by rfl
    _ =
        ∑ f : RelevantEdge T₂, ∑ a : CorrectionsFrom f,
          correctionEndpointTermD e i j a.1 := by
      apply Fintype.sum_congr
      intro f
      calc
        (∑ k ∈ (Pc f).endpoint,
            (((c e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
                (ZD e f i k : ℝ) ^ 2 +
              ((2 * c e f k * cbar e f k *
                  r e f i k * r e f j k : ℚ) : ℝ) *
                ZD e f i k * WD e f i k -
              ((cbar e f k ^ 2 * r e f i k * r e f j k : ℚ) : ℝ) *
                (WD e f i k : ℝ) ^ 2)) =
            ∑ k : EndpointAtomIndex f,
              (((c e f k.1 ^ 2 * r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                  (ZD e f i k.1 : ℝ) ^ 2 +
                ((2 * c e f k.1 * cbar e f k.1 *
                    r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                  ZD e f i k.1 * WD e f i k.1 -
                ((cbar e f k.1 ^ 2 *
                    r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                  (WD e f i k.1 : ℝ) ^ 2) := by
          symm
          convert
            (sum_endpointAtomIndex_eq_endpoint_real f
              (fun k =>
                (c e f k : ℝ) ^ 2 *
                      (r e f i k : ℝ) * (r e f j k : ℝ) *
                      (ZD e f i k : ℝ) ^ 2 +
                  2 * (c e f k : ℝ) * (cbar e f k : ℝ) *
                      (r e f i k : ℝ) * (r e f j k : ℝ) *
                      (ZD e f i k : ℝ) * (WD e f i k : ℝ) -
                  (cbar e f k : ℝ) ^ 2 *
                      (r e f i k : ℝ) * (r e f j k : ℝ) *
                      (WD e f i k : ℝ) ^ 2)) using 1 <;>
            push_cast <;> ring
        _ =
            ∑ a : CorrectionsFrom f,
              correctionEndpointTermD e i j a.1 := by
          symm
          exact Fintype.sum_equiv
            (correctionEquivEndpointAtom f)
            (fun a : CorrectionsFrom f =>
              correctionEndpointTermD e i j a.1)
            (fun k : EndpointAtomIndex f =>
              (((c e f k.1 ^ 2 *
                  r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                    (ZD e f i k.1 : ℝ) ^ 2 +
                ((2 * c e f k.1 * cbar e f k.1 *
                    r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                    ZD e f i k.1 * WD e f i k.1 -
                ((cbar e f k.1 ^ 2 *
                    r e f i k.1 * r e f j k.1 : ℚ) : ℝ) *
                    (WD e f i k.1 : ℝ) ^ 2))
            (correctionEndpointTermD_eq_chart e f i j)
    _ = ∑ a : AdjacentCorrection T₂,
          correctionEndpointTermD e i j a :=
      sum_corrections_by_source_real _

theorem sum_correctionEndpointTermI_eq_mixed
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ a : AdjacentCorrection T₂,
      correctionEndpointTermI e i j a) =
      ∑ a : AdjacentCorrection T₂, correctionMixedI e i j a := by
  have hcancel := endpoint_faces_I_eq_zero (T₂ := T₂) e i j
  unfold correctionEndpointTermI correctionMixedI
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib] at hcancel
  linarith

theorem sum_correctionEndpointTermD_eq_mixed
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ a : AdjacentCorrection T₂,
      correctionEndpointTermD e i j a) =
      ∑ a : AdjacentCorrection T₂, correctionMixedD e i j a := by
  have hcancel := endpoint_faces_D_eq_zero (T₂ := T₂) e i j
  unfold correctionEndpointTermD correctionMixedD
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib] at hcancel
  linarith

theorem global_endpoint_face_cancellation_I
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂, endpointRemainderI e f i j) =
      ∑ a : AdjacentCorrection T₂, correctionMixedI e i j a := by
  rw [endpointRemainderI_reindex]
  exact sum_correctionEndpointTermI_eq_mixed e i j

theorem global_endpoint_face_cancellation_D
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂, endpointRemainderD e f i j) =
      ∑ a : AdjacentCorrection T₂, correctionMixedD e i j a := by
  rw [endpointRemainderD_reindex]
  exact sum_correctionEndpointTermD_eq_mixed e i j

/-! ## The chart-indexed first-face demand -/

def localEndpointData
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) :
    CompletedSquares.EndpointData :=
  {
    cK := (c e f u : ℝ)
    cB := (cbar e f u : ℝ)
    cKplus := 1 - (cbar e f u : ℝ)
    aiK := ((J e f).a i u : ℝ)
    ajK := ((J e f).a j u : ℝ)
    aiB :=
      ((J e f).mixedBlockMass i ((Fc f).oppositeSideBlock u) : ℝ)
    ajB :=
      ((J e f).mixedBlockMass j ((Fc f).oppositeSideBlock u) : ℝ)
  }

def demandCoefficient
    (e : RelevantEdge T₁) (f : RelevantEdge T₂)
    (i j : Atom e) (u : Atom f) : ℝ :=
  if u ∈ (Pc f).endpoint
  then (localEndpointData e f i j u).packageCoeff.xx
  else 0

theorem endpointData_eq_localEndpointData
    (e : RelevantEdge T₁) (a : AdjacentCorrection T₂)
    (i j : Atom e) :
    ConcreteBridgeLedger.endpointData e a i j =
      localEndpointData e (first a) i j (selectedColumnAtom a) := by
  rw [ConcreteBridgeLedger.endpointData_eq_chartEndpointData]
  rfl

theorem demandCoefficient_selected
    (e : RelevantEdge T₁) (i j : Atom e)
    (a : AdjacentCorrection T₂) :
    demandCoefficient e (first a) i j (selectedColumnAtom a) =
      (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx := by
  unfold demandCoefficient
  have hk :
      selectedColumnAtom a ∈ (Pc (first a)).endpoint := by
    change
      selectedColumnAtom a ∈
        (residualPartition (first a)).endpoint
    rw [mem_residualPartition_endpoint]
    exact endpointAtom_isEndpoint
      (first a) (correctionSlot a)
  rw [if_pos hk]
  rw [← endpointData_eq_localEndpointData]

set_option maxHeartbeats 800000 in
theorem demand_sum_I
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂, ∑ u : Atom f,
      demandCoefficient e f i j u * (ZI e f i u : ℝ) ^ 2) =
      ∑ a : AdjacentCorrection T₂,
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx *
          (correctionZI e i a : ℝ) ^ 2 := by
  calc
    (∑ f : RelevantEdge T₂, ∑ u : Atom f,
        demandCoefficient e f i j u * (ZI e f i u : ℝ) ^ 2) =
        ∑ f : RelevantEdge T₂, ∑ u ∈ (Pc f).endpoint,
          (localEndpointData e f i j u).packageCoeff.xx *
            (ZI e f i u : ℝ) ^ 2 := by
      apply Fintype.sum_congr
      intro f
      simp [demandCoefficient]
    _ =
        ∑ f : RelevantEdge T₂, ∑ a : CorrectionsFrom f,
          (ConcreteBridgeLedger.endpointData e a.1 i j).packageCoeff.xx *
            (correctionZI e i a.1 : ℝ) ^ 2 := by
      apply Fintype.sum_congr
      intro f
      calc
        (∑ u ∈ (Pc f).endpoint,
            (localEndpointData e f i j u).packageCoeff.xx *
              (ZI e f i u : ℝ) ^ 2) =
            ∑ u : EndpointAtomIndex f,
              (localEndpointData e f i j u.1).packageCoeff.xx *
                (ZI e f i u.1 : ℝ) ^ 2 := by
          symm
          simpa only using
            (sum_endpointAtomIndex_eq_endpoint_real f
              (fun u =>
                (localEndpointData e f i j u).packageCoeff.xx *
                  (ZI e f i u : ℝ) ^ 2))
        _ =
            ∑ a : CorrectionsFrom f,
              (ConcreteBridgeLedger.endpointData e a.1 i j).packageCoeff.xx *
                (correctionZI e i a.1 : ℝ) ^ 2 := by
          symm
          exact Fintype.sum_equiv
            (correctionEquivEndpointAtom f)
            (fun a : CorrectionsFrom f =>
              (ConcreteBridgeLedger.endpointData e a.1 i j).packageCoeff.xx *
                (correctionZI e i a.1 : ℝ) ^ 2)
            (fun u : EndpointAtomIndex f =>
              (localEndpointData e f i j u.1).packageCoeff.xx *
                (ZI e f i u.1 : ℝ) ^ 2)
            (by
              intro a
              rcases a with ⟨a, ha⟩
              subst f
              rw [endpointData_eq_localEndpointData]
              rw [correctionZI_eq_chart]
              simp [correctionEquivEndpointAtom, correctionSlot,
                correctionFromFirst, endpointAtomEquiv,
                selectedColumnAtom])
    _ =
        ∑ a : AdjacentCorrection T₂,
          (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx *
            (correctionZI e i a : ℝ) ^ 2 :=
      sum_corrections_by_source_real
        (fun a : AdjacentCorrection T₂ =>
          (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx *
            (correctionZI e i a : ℝ) ^ 2)

set_option maxHeartbeats 800000 in
theorem demand_sum_D
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂, ∑ u : Atom f,
      demandCoefficient e f i j u * (ZD e f i u : ℝ) ^ 2) =
      ∑ a : AdjacentCorrection T₂,
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx *
          (correctionZD e i a : ℝ) ^ 2 := by
  calc
    (∑ f : RelevantEdge T₂, ∑ u : Atom f,
        demandCoefficient e f i j u * (ZD e f i u : ℝ) ^ 2) =
        ∑ f : RelevantEdge T₂, ∑ u ∈ (Pc f).endpoint,
          (localEndpointData e f i j u).packageCoeff.xx *
            (ZD e f i u : ℝ) ^ 2 := by
      apply Fintype.sum_congr
      intro f
      simp [demandCoefficient]
    _ =
        ∑ f : RelevantEdge T₂, ∑ a : CorrectionsFrom f,
          (ConcreteBridgeLedger.endpointData e a.1 i j).packageCoeff.xx *
            (correctionZD e i a.1 : ℝ) ^ 2 := by
      apply Fintype.sum_congr
      intro f
      calc
        (∑ u ∈ (Pc f).endpoint,
            (localEndpointData e f i j u).packageCoeff.xx *
              (ZD e f i u : ℝ) ^ 2) =
            ∑ u : EndpointAtomIndex f,
              (localEndpointData e f i j u.1).packageCoeff.xx *
                (ZD e f i u.1 : ℝ) ^ 2 := by
          symm
          simpa only using
            (sum_endpointAtomIndex_eq_endpoint_real f
              (fun u =>
                (localEndpointData e f i j u).packageCoeff.xx *
                  (ZD e f i u : ℝ) ^ 2))
        _ =
            ∑ a : CorrectionsFrom f,
              (ConcreteBridgeLedger.endpointData e a.1 i j).packageCoeff.xx *
                (correctionZD e i a.1 : ℝ) ^ 2 := by
          symm
          exact Fintype.sum_equiv
            (correctionEquivEndpointAtom f)
            (fun a : CorrectionsFrom f =>
              (ConcreteBridgeLedger.endpointData e a.1 i j).packageCoeff.xx *
                (correctionZD e i a.1 : ℝ) ^ 2)
            (fun u : EndpointAtomIndex f =>
              (localEndpointData e f i j u.1).packageCoeff.xx *
                (ZD e f i u.1 : ℝ) ^ 2)
            (by
              intro a
              rcases a with ⟨a, ha⟩
              subst f
              rw [endpointData_eq_localEndpointData]
              rw [correctionZD_eq_chart]
              simp [correctionEquivEndpointAtom, correctionSlot,
                correctionFromFirst, endpointAtomEquiv,
                selectedColumnAtom])
    _ =
        ∑ a : AdjacentCorrection T₂,
          (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx *
            (correctionZD e i a : ℝ) ^ 2 :=
      sum_corrections_by_source_real
        (fun a : AdjacentCorrection T₂ =>
          (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx *
            (correctionZD e i a : ℝ) ^ 2)

/-! ## Concrete global package ledger `(A.29f)` -/

theorem global_package_ledger_I
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂, (directRowI e f (i, j) : ℝ)) =
      (∑ a : AdjacentCorrection T₂, packageI e i j a) +
        2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
          (availableCoefficient e f i j u -
            demandCoefficient e f i j u) *
              (ZI e f i u : ℝ) ^ 2 := by
  have hdirect :
      (∑ f : RelevantEdge T₂, (directRowI e f (i, j) : ℝ)) =
        2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
          availableCoefficient e f i j u *
            (ZI e f i u : ℝ) ^ 2 +
          ∑ a : AdjacentCorrection T₂,
            correctionMixedI e i j a := by
    calc
      (∑ f : RelevantEdge T₂, (directRowI e f (i, j) : ℝ)) =
          ∑ f : RelevantEdge T₂,
            (2 * ∑ u : Atom f,
              availableCoefficient e f i j u *
                (ZI e f i u : ℝ) ^ 2 +
              endpointRemainderI e f i j) := by
        apply Fintype.sum_congr
        intro f
        exact directRowI_expanded e f i j
      _ =
          2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            availableCoefficient e f i j u *
              (ZI e f i u : ℝ) ^ 2 +
            ∑ f : RelevantEdge T₂,
              endpointRemainderI e f i j := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ =
          2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            availableCoefficient e f i j u *
              (ZI e f i u : ℝ) ^ 2 +
            ∑ a : AdjacentCorrection T₂,
              correctionMixedI e i j a := by
        rw [global_endpoint_face_cancellation_I]
  have hpkg := global_package_extraction_I (T₂ := T₂) e i j
  have hdemand := demand_sum_I (T₂ := T₂) e i j
  have hpkgRearranged :
      (∑ a : AdjacentCorrection T₂,
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
          correctionZI e i a * correctionWI e i a) =
        (∑ a : AdjacentCorrection T₂, packageI e i j a) -
          2 * ∑ a : AdjacentCorrection T₂,
            (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx *
              (correctionZI e i a : ℝ) ^ 2 :=
    rearrange_package_sum
      (correctionAvailableCoefficient e i j)
      (fun a =>
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx)
      (fun a => (correctionZI e i a : ℝ))
      (fun a =>
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
          correctionZI e i a * correctionWI e i a)
      (packageI e i j)
      hpkg
  have hmixed :
      (∑ a : AdjacentCorrection T₂, correctionMixedI e i j a) =
        ∑ a : AdjacentCorrection T₂,
          (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
            correctionZI e i a * correctionWI e i a := by
    apply Fintype.sum_congr
    intro a
    exact correctionMixedI_eq_packageMixed e i j a
  have hresidual :
      (∑ f : RelevantEdge T₂, ∑ u : Atom f,
        (availableCoefficient e f i j u -
          demandCoefficient e f i j u) *
            (ZI e f i u : ℝ) ^ 2) =
        (∑ f : RelevantEdge T₂, ∑ u : Atom f,
          availableCoefficient e f i j u *
            (ZI e f i u : ℝ) ^ 2) -
          ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            demandCoefficient e f i j u *
              (ZI e f i u : ℝ) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    apply Fintype.sum_congr
    intro f
    rw [← Finset.sum_sub_distrib]
    apply Fintype.sum_congr
    intro u
    ring
  rw [hdirect, hmixed, hpkgRearranged, hresidual, hdemand]
  ring

theorem global_package_ledger_D
    (e : RelevantEdge T₁) (i j : Atom e) :
    (∑ f : RelevantEdge T₂, (directRowD e f (i, j) : ℝ)) =
      (∑ a : AdjacentCorrection T₂, packageD e i j a) +
        2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
          (availableCoefficient e f i j u -
            demandCoefficient e f i j u) *
              (ZD e f i u : ℝ) ^ 2 := by
  have hdirect :
      (∑ f : RelevantEdge T₂, (directRowD e f (i, j) : ℝ)) =
        2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
          availableCoefficient e f i j u *
            (ZD e f i u : ℝ) ^ 2 +
          ∑ a : AdjacentCorrection T₂,
            correctionMixedD e i j a := by
    calc
      (∑ f : RelevantEdge T₂, (directRowD e f (i, j) : ℝ)) =
          ∑ f : RelevantEdge T₂,
            (2 * ∑ u : Atom f,
              availableCoefficient e f i j u *
                (ZD e f i u : ℝ) ^ 2 +
              endpointRemainderD e f i j) := by
        apply Fintype.sum_congr
        intro f
        exact directRowD_expanded e f i j
      _ =
          2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            availableCoefficient e f i j u *
              (ZD e f i u : ℝ) ^ 2 +
            ∑ f : RelevantEdge T₂,
              endpointRemainderD e f i j := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ =
          2 * ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            availableCoefficient e f i j u *
              (ZD e f i u : ℝ) ^ 2 +
            ∑ a : AdjacentCorrection T₂,
              correctionMixedD e i j a := by
        rw [global_endpoint_face_cancellation_D]
  have hpkg := global_package_extraction_D (T₂ := T₂) e i j
  have hdemand := demand_sum_D (T₂ := T₂) e i j
  have hpkgRearranged :
      (∑ a : AdjacentCorrection T₂,
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
          correctionZD e i a * correctionWD e i a) =
        (∑ a : AdjacentCorrection T₂, packageD e i j a) -
          2 * ∑ a : AdjacentCorrection T₂,
            (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx *
              (correctionZD e i a : ℝ) ^ 2 :=
    rearrange_package_sum
      (correctionAvailableCoefficient e i j)
      (fun a =>
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xx)
      (fun a => (correctionZD e i a : ℝ))
      (fun a =>
        (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
          correctionZD e i a * correctionWD e i a)
      (packageD e i j)
      hpkg
  have hmixed :
      (∑ a : AdjacentCorrection T₂, correctionMixedD e i j a) =
        ∑ a : AdjacentCorrection T₂,
          (ConcreteBridgeLedger.endpointData e a i j).packageCoeff.xy *
            correctionZD e i a * correctionWD e i a := by
    apply Fintype.sum_congr
    intro a
    exact correctionMixedD_eq_packageMixed e i j a
  have hresidual :
      (∑ f : RelevantEdge T₂, ∑ u : Atom f,
        (availableCoefficient e f i j u -
          demandCoefficient e f i j u) *
            (ZD e f i u : ℝ) ^ 2) =
        (∑ f : RelevantEdge T₂, ∑ u : Atom f,
          availableCoefficient e f i j u *
            (ZD e f i u : ℝ) ^ 2) -
          ∑ f : RelevantEdge T₂, ∑ u : Atom f,
            demandCoefficient e f i j u *
              (ZD e f i u : ℝ) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    apply Fintype.sum_congr
    intro f
    rw [← Finset.sum_sub_distrib]
    apply Fintype.sum_congr
    intro u
    ring
  rw [hdirect, hmixed, hpkgRearranged, hresidual, hdemand]
  ring

end

end ConcreteGlobalPackage

end QuartetV060
