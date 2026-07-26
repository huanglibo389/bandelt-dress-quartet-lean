import QuartetV060.QuartetTopologyCounting
import QuartetV060.KernelRange

/-!
# Distinct and repeated ordered-quadruple contributions

The kernel sum over `(Fin n)⁴` is partitioned into injective and
noninjective maps from `Fin 4`.  The injective part is evaluated exactly by
the 24-ordering table.  The noninjective part is retained as an explicit
remainder and bounded by its exact cardinality using the full-domain kernel
range.
-/

namespace QuartetV060

namespace DistinctTupleCounting

open QuartetDistance QuartetTopologyCounting KernelRange

noncomputable section

/-- The four nested sums and the sum over functions `Fin 4 → X` have exactly
the same indices. -/
def tuple4Equiv (X : Type) :
    (Fin 4 → X) ≃ X × (X × (X × X)) where
  toFun f := (f 0, (f 1, (f 2, f 3)))
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨a, b, c, d⟩
    rfl

theorem nested_sum_eq_tuple_sum
    {X : Type} [Fintype X] (g : (Fin 4 → X) → ℚ) :
    (∑ a : X, ∑ b : X, ∑ c : X, ∑ d : X, g ![a, b, c, d]) =
      ∑ f : Fin 4 → X, g f := by
  rw [Fintype.sum_equiv (tuple4Equiv X)
    g (fun p => g ((tuple4Equiv X).symm p)) (by simp)]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Regard the reference library's four-subset type as an `Upper.Quartet`. -/
def fourSubsetAsQuartet {n : ℕ}
    (q : Circular.FourSubset n) : Upper.Quartet n :=
  ⟨q.1, Circular.fourSubset_card q⟩

/-- The resolved topology displayed by a tree on one four-subset. -/
def topologyOnFourSubset {n : ℕ}
    (T : Tree.PhyloTree (Fin n)) (q : Circular.FourSubset n) : Fin 3 :=
  Upper.displayedTopology T (fourSubsetAsQuartet q)

/-- Pointwise product of the two concrete tree kernels. -/
def tupleKernelProduct {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) (f : Fin 4 → Fin n) : ℚ :=
  TreeKernel.kernel T₁ (f 0) (f 1) (f 2) (f 3) *
    TreeKernel.kernel T₂ (f 0) (f 1) (f 2) (f 3)

theorem injectiveStripSampleDataEquiv_symm_apply
    {n : ℕ} (q : Circular.FourSubset n) (σ : Circular.Perm4) :
    ((Circular.injectiveStripSampleDataEquiv n).symm (q, σ)).1 =
      enumeration (fourSubsetAsQuartet q) σ.symm := by
  rfl

/-- Contribution from ordered four-tuples with four distinct labels. -/
def distinctKernelSum {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) : ℚ :=
  ∑ f : {f : Fin 4 → Fin n // Function.Injective f},
    tupleKernelProduct T₁ T₂ f.1

/-- Contribution from ordered four-tuples containing a repeated label. -/
def repeatedKernelSum {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) : ℚ :=
  ∑ f : {f : Fin 4 → Fin n // ¬ Function.Injective f},
    tupleKernelProduct T₁ T₂ f.1

/-- Number of four-subsets on which the two trees display the same topology. -/
def sameCount {n : ℕ}
    (T₁ T₂ : Tree.PhyloTree (Fin n)) : ℕ :=
  Counting.truthAgreementCount
    (topologyOnFourSubset T₁) (topologyOnFourSubset T₂)

/-- Quartet distance: number of four-subsets on which the displayed
topologies differ. -/
def diffCount {n : ℕ}
    (T₁ T₂ : Tree.PhyloTree (Fin n)) : ℕ :=
  Counting.truthDistance
    (topologyOnFourSubset T₁) (topologyOnFourSubset T₂)

/-- Exact injective contribution before multiplication by the global factor
`1/4`: `16` for every agreeing four-subset and `-8` for every differing
four-subset. -/
theorem distinctKernelSum_eq
    {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    distinctKernelSum T₁ T₂ =
      16 * sameCount T₁ T₂ - 8 * diffCount T₁ T₂ := by
  classical
  unfold distinctKernelSum
  rw [Fintype.sum_equiv
    (Circular.injectiveStripSampleDataEquiv n)
    (fun f => tupleKernelProduct T₁ T₂ f.1)
    (fun z =>
      tupleKernelProduct T₁ T₂
        ((Circular.injectiveStripSampleDataEquiv n).symm z).1)
    (by simp)]
  simp only [Fintype.sum_prod_type]
  simp_rw [injectiveStripSampleDataEquiv_symm_apply]
  simp_rw [tupleKernelProduct, kernel_enumeration_eq_localKernel]
  have hpoint :
      ∀ q : Circular.FourSubset n,
        (∑ σ : Circular.Perm4,
          localKernel
              (Upper.displayedTopology T₁ (fourSubsetAsQuartet q)) σ.symm *
            localKernel
              (Upper.displayedTopology T₂ (fourSubsetAsQuartet q)) σ.symm) =
          if Upper.displayedTopology T₁ (fourSubsetAsQuartet q) =
              Upper.displayedTopology T₂ (fourSubsetAsQuartet q)
            then 16 else -8 := by
    intro q
    by_cases h :
        Upper.displayedTopology T₁ (fourSubsetAsQuartet q) =
          Upper.displayedTopology T₂ (fourSubsetAsQuartet q)
    · rw [if_pos h, h, localKernel_same_sum_symm]
    · rw [if_neg h, localKernel_diff_sum_symm _ _ h]
  simp_rw [hpoint]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul,
    Counting.truthAgreementCount, Counting.truthDistance,
    sameCount, diffCount, topologyOnFourSubset]
  push_cast
  ring

/-- Partition the full ordered-quadruple sum into distinct and repeated
tuples, retaining every occurrence exactly once. -/
theorem allKernelSum_eq_distinct_add_repeated
    {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    (∑ f : Fin 4 → Fin n, tupleKernelProduct T₁ T₂ f) =
      distinctKernelSum T₁ T₂ + repeatedKernelSum T₁ T₂ := by
  classical
  exact
    (Fintype.sum_subtype_add_sum_subtype
      (fun f : Fin 4 → Fin n => Function.Injective f)
      (tupleKernelProduct T₁ T₂)).symm

/-- The exact number of ordered four-tuples containing a repeated label. -/
theorem card_noninjective_tuple (n : ℕ) :
    Fintype.card {f : Fin 4 → Fin n // ¬ Function.Injective f} =
      n ^ 4 - Circular.fallingFour n := by
  classical
  rw [Fintype.card_subtype_compl,
    Circular.card_injectiveStripSample]
  simp

/-- Polynomial form of the collision count, valid on the manuscript's
domain `n ≥ 4`. -/
theorem collision_count_polynomial (n : ℕ) (hn : 4 ≤ n) :
    n ^ 4 - Circular.fallingFour n =
      6 * n ^ 3 - 11 * n ^ 2 + 6 * n := by
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have hfall : Circular.fallingFour n ≤ n ^ 4 := by
    unfold Circular.fallingFour
    calc
      n * (n - 1) * (n - 2) * (n - 3) ≤
          n * n * n * n := by
            gcongr <;> exact Nat.sub_le _ _
      _ = n ^ 4 := by ring
  have hrhs : 11 * n ^ 2 ≤ 6 * n ^ 3 := by
    nlinarith
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hfall, Nat.cast_sub hrhs,
    Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
  unfold Circular.fallingFour
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
  ring

/-- Triangle bound for the repeated-label sum from an arbitrary pointwise
bound. -/
theorem repeatedKernelSum_abs_le_card
    {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n))
    (hbound :
      ∀ f : Fin 4 → Fin n,
        |tupleKernelProduct T₁ T₂ f| ≤ 1) :
    |repeatedKernelSum T₁ T₂| ≤
      Fintype.card {f : Fin 4 → Fin n // ¬ Function.Injective f} := by
  classical
  unfold repeatedKernelSum
  calc
    |∑ f : {f : Fin 4 → Fin n // ¬ Function.Injective f},
        tupleKernelProduct T₁ T₂ f.1| ≤
        ∑ f : {f : Fin 4 → Fin n // ¬ Function.Injective f},
          |tupleKernelProduct T₁ T₂ f.1| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _f : {f : Fin 4 → Fin n // ¬ Function.Injective f}, (1 : ℚ) := by
          exact Finset.sum_le_sum fun i _ => hbound i.1
    _ = Fintype.card {f : Fin 4 → Fin n // ¬ Function.Injective f} := by
          simp

/-- Concrete repeated-label bound using the full-domain kernel range. -/
theorem repeatedKernelSum_abs_le_collision_count
    {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    |repeatedKernelSum T₁ T₂| ≤
      Fintype.card {f : Fin 4 → Fin n // ¬ Function.Injective f} := by
  apply repeatedKernelSum_abs_le_card
  intro f
  exact abs_kernel_mul_kernel_le_one T₁ T₂ (f 0) (f 1) (f 2) (f 3)

/-- The manuscript's repeated-label remainder, including the global factor
`1/4` from the ordered-quadruple kernel identity. -/
def repeatedRemainder {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) : ℚ :=
  (1 / 4 : ℚ) * repeatedKernelSum T₁ T₂

/-- Explicit polynomial bound for the repeated-label remainder. -/
theorem abs_repeatedRemainder_le
    {n : ℕ} [Nonempty (Fin n)] (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    |repeatedRemainder T₁ T₂| ≤
      (1 / 4 : ℚ) * (6 * n ^ 3 - 11 * n ^ 2 + 6 * n) := by
  have h :=
    repeatedKernelSum_abs_le_collision_count T₁ T₂
  rw [card_noninjective_tuple,
    collision_count_polynomial n hn] at h
  have hrhs : 11 * n ^ 2 ≤ 6 * n ^ 3 := by
    nlinarith
  have hcast :
      ((6 * n ^ 3 - 11 * n ^ 2 + 6 * n : ℕ) : ℚ) =
        6 * (n : ℚ) ^ 3 - 11 * (n : ℚ) ^ 2 + 6 * (n : ℚ) := by
    rw [Nat.cast_add, Nat.cast_sub hrhs]
    push_cast
    ring
  rw [hcast] at h
  unfold repeatedRemainder
  rw [abs_mul]
  norm_num
  linarith

/-- Full kernel sum after the distinct/repeated partition. -/
theorem allKernelSum_eq_counts_add_remainder
    {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    (1 / 4 : ℚ) *
        (∑ f : Fin 4 → Fin n, tupleKernelProduct T₁ T₂ f) =
      4 * sameCount T₁ T₂ - 2 * diffCount T₁ T₂ +
        repeatedRemainder T₁ T₂ := by
  rw [allKernelSum_eq_distinct_add_repeated,
    distinctKernelSum_eq]
  unfold repeatedRemainder
  ring

/-- Exact identification of the auxiliary functional with the complete
ordered-quadruple kernel sum. -/
theorem auxiliaryFunctional_eq_allKernelSum
    {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    (n : ℚ) ^ 4 *
        auxiliaryFunctional
          (PhyloOccurrences.correctionSystem T₁)
          (PhyloOccurrences.correctionSystem T₂) =
      (1 / 4 : ℚ) *
        ∑ f : Fin 4 → Fin n, tupleKernelProduct T₁ T₂ f := by
  have h :=
    auxiliaryFunctional_kernel_identity
      (S₁ := PhyloOccurrences.correctionSystem T₁)
      (S₂ := PhyloOccurrences.correctionSystem T₂)
  simp only [Fintype.card_fin] at h
  let g : (Fin 4 → Fin n) → ℚ := fun f =>
    ((PhyloOccurrences.correctionSystem T₁).occurrenceFamily).kernel
        (f 0) (f 1) (f 2) (f 3) *
      ((PhyloOccurrences.correctionSystem T₂).occurrenceFamily).kernel
        (f 0) (f 1) (f 2) (f 3)
  have hsum := nested_sum_eq_tuple_sum g
  have hsum' :
      (∑ q₁ : Fin n, ∑ q₂ : Fin n, ∑ q₃ : Fin n, ∑ q₄ : Fin n,
        ((PhyloOccurrences.correctionSystem T₁).occurrenceFamily).kernel
            q₁ q₂ q₃ q₄ *
          ((PhyloOccurrences.correctionSystem T₂).occurrenceFamily).kernel
            q₁ q₂ q₃ q₄) =
        ∑ f : Fin 4 → Fin n, tupleKernelProduct T₁ T₂ f := by
    simpa [g, tupleKernelProduct, TreeKernel.kernel] using hsum
  rw [hsum'] at h
  exact h

/-- The manuscript's exact counting identity:
`n⁴ f₁ = 4 Same - 2 Diff + Rₙ`. -/
theorem auxiliaryFunctional_counting_identity
    {n : ℕ} [Nonempty (Fin n)]
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    (n : ℚ) ^ 4 *
        auxiliaryFunctional
          (PhyloOccurrences.correctionSystem T₁)
          (PhyloOccurrences.correctionSystem T₂) =
      4 * sameCount T₁ T₂ - 2 * diffCount T₁ T₂ +
        repeatedRemainder T₁ T₂ := by
  rw [auxiliaryFunctional_eq_allKernelSum,
    allKernelSum_eq_counts_add_remainder]

end

end DistinctTupleCounting

end QuartetV060
