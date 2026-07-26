import QuartetV060.MainTheorem
import QuartetDistance.Lower
import QuartetDistance.Maximum

/-!
# The random-relabeling lower bound and the sharp finite sandwich

Appendix A supplies the upper bound.  The lower bound used in the manuscript
is independent: relabel one fixed tree uniformly and count the three quartet
topologies.  We reuse the fully formalized random-relabeling theorem from the
reference infrastructure, after proving that its quartet-distance definition
is exactly the `diffCount` used by the v0.60 counting argument.
-/

namespace QuartetV060

namespace Sharpness

open QuartetDistance
open DistinctTupleCounting

noncomputable section

/-- The powerset representation of four-subsets and the cardinality-subtype
representation used by `Upper` define the same quartet distance. -/
theorem diffCount_eq_upper_quartetDistance
    {n : ℕ} (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    diffCount T₁ T₂ = Upper.quartetDistance T₁ T₂ := by
  classical
  unfold diffCount Counting.truthDistance Upper.quartetDistance
  apply Finset.card_bij
    (fun q _ => fourSubsetAsQuartet q)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    simpa [topologyOnFourSubset] using hq
  · intro q₁ hq₁ q₂ hq₂ h
    exact Subtype.ext
      (congrArg (fun q : Upper.Quartet n => q.1) h)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    let s : Circular.FourSubset n :=
      ⟨q.1, by
        simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
        exact q.2⟩
    refine ⟨s, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [topologyOnFourSubset, fourSubsetAsQuartet, s] using hq
    · exact Subtype.ext rfl

theorem diffCount_le_choose
    {n : ℕ} (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    diffCount T₁ T₂ ≤ Nat.choose n 4 := by
  have h := MainCounting.sameCount_add_diffCount T₁ T₂
  omega

/-- Maximum v0.60 quartet distance on `Fin n`. -/
def maximumDistance (n : ℕ) : ℕ :=
  maxPairValue (@diffCount n)

theorem diffCount_le_maximumDistance
    {n : ℕ} (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    diffCount T₁ T₂ ≤ maximumDistance n := by
  exact value_le_maxPairValue (@diffCount n)
    diffCount_le_choose T₁ T₂

/-- Exact denominator-cleared random-relabeling lower bound. -/
theorem maximumDistance_lower_bound
    (n : ℕ) (hn : 4 ≤ n) :
    2 * Nat.choose n 4 ≤ 3 * maximumDistance n := by
  obtain ⟨T⟩ := Lower.nonempty_phyloTree_fin n hn
  obtain ⟨π, hπ⟩ := Lower.exists_relabeling_two_thirds T T
  rw [← diffCount_eq_upper_quartetDistance] at hπ
  exact hπ.trans
    (Nat.mul_le_mul_left 3
      (diffCount_le_maximumDistance T (Lower.relabel π T)))

theorem maximumDistance_pos
    (n : ℕ) (hn : 4 ≤ n) :
    0 < maximumDistance n := by
  have hchoose : 0 < Nat.choose n 4 := Nat.choose_pos hn
  have hlow := maximumDistance_lower_bound n hn
  omega

theorem exists_maximizing_trees
    (n : ℕ) (hn : 4 ≤ n) :
    ∃ T₁ T₂ : Tree.PhyloTree (Fin n),
      maximumDistance n = diffCount T₁ T₂ := by
  rcases maxPairValue_eq_zero_or_exists (@diffCount n)
      diffCount_le_choose with hzero | htrees
  · exact False.elim ((maximumDistance_pos n hn).ne' hzero)
  · exact htrees

/-- The v0.60 upper bound applied to the actual maximum. -/
theorem maximumDistance_upper_bound
    (n : ℕ) (hn : 4 ≤ n) :
    (maximumDistance n : ℚ) ≤
      (2 / 3 : ℚ) * Nat.choose n 4 +
        (6 * (n : ℚ) ^ 3 - 11 * (n : ℚ) ^ 2 + 6 * n) / 24 := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨T₁, T₂, hmax⟩ := exists_maximizing_trees n hn
  rw [hmax]
  exact MainTheorem.diffCount_upper_bound hn T₁ T₂

/-- Exact normalized sandwich behind the sharp asymptotic corollary. -/
theorem maximumDistance_normalized_bounds
    (n : ℕ) (hn : 4 ≤ n) :
    (2 / 3 : ℚ) ≤
        (maximumDistance n : ℚ) / Nat.choose n 4 ∧
      (maximumDistance n : ℚ) / Nat.choose n 4 ≤
        (2 / 3 : ℚ) + MainTheorem.epsilon n := by
  have hchoose := MainTheorem.choose_four_pos hn
  constructor
  · rw [le_div_iff₀ hchoose]
    have hlow := maximumDistance_lower_bound n hn
    have hlowQ :
        (2 : ℚ) * Nat.choose n 4 ≤
          3 * maximumDistance n := by
      exact_mod_cast hlow
    nlinarith
  · rw [div_le_iff₀ hchoose]
    have hupp := maximumDistance_upper_bound n hn
    unfold MainTheorem.epsilon
    field_simp
    nlinarith

/-- The degree-two-over-degree-three form of the normalized error, written in
the inverse variable `x = 1/n`. -/
def asymptoticErrorExpression (x : ℝ) : ℝ :=
  (6 * x - 11 * x ^ 2 + 6 * x ^ 3) /
    ((1 - x) * (1 - 2 * x) * (1 - 3 * x))

theorem epsilon_cast_eq_asymptoticErrorExpression
    (n : ℕ) (hn : 4 ≤ n) :
    (MainTheorem.epsilon n : ℝ) =
      asymptoticErrorExpression ((n : ℝ)⁻¹) := by
  have hfallNat := twentyFour_mul_quartetCount n
  have hfall :
      (24 : ℝ) * (Nat.choose n 4 : ℝ) =
        (n : ℝ) * ((n : ℝ) - 1) *
          ((n : ℝ) - 2) * ((n : ℝ) - 3) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hfallNat
    simp only [quartetCount, Nat.cast_mul] at h
    rw [Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_sub (by omega : 2 ≤ n),
      Nat.cast_sub (by omega : 3 ≤ n)] at h
    norm_num at h ⊢
    exact h
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hn3 : (n : ℝ) - 3 ≠ 0 := by linarith
  unfold MainTheorem.epsilon asymptoticErrorExpression
  push_cast
  rw [show
    (24 : ℝ) * (Nat.choose n 4 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) *
        ((n : ℝ) - 2) * ((n : ℝ) - 3) from hfall]
  field_simp [hn0, hn1, hn2, hn3]

/-- Formal `o(1)` content of the manuscript's explicit error term. -/
theorem epsilon_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => (MainTheorem.epsilon n : ℝ))
      Filter.atTop (nhds 0) := by
  let g : ℝ → ℝ := asymptoticErrorExpression
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹))
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hg : ContinuousAt g 0 := by
    dsimp only [g, asymptoticErrorExpression]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hcomp :
      Filter.Tendsto (fun n : ℕ => g ((n : ℝ)⁻¹))
        Filter.atTop (nhds (g 0)) :=
    hg.tendsto.comp hinv
  have hg0 : g 0 = 0 := by
    norm_num [g, asymptoticErrorExpression]
  rw [hg0] at hcomp
  apply hcomp.congr'
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  exact (epsilon_cast_eq_asymptoticErrorExpression n hn).symm

/-- Normalized maximum quartet distance. -/
def normalizedMaximum (n : ℕ) : ℝ :=
  (maximumDistance n : ℝ) / (Nat.choose n 4 : ℝ)

/-- Formal sharp asymptotic value:
`maximumDistance n / choose n 4 → 2/3`. -/
theorem normalizedMaximum_tendsto_two_thirds :
    Filter.Tendsto normalizedMaximum Filter.atTop
      (nhds ((2 : ℝ) / 3)) := by
  have hlower :
      Filter.Tendsto (fun _ : ℕ => (2 : ℝ) / 3)
        Filter.atTop (nhds ((2 : ℝ) / 3)) :=
    tendsto_const_nhds
  have hupper :
      Filter.Tendsto
        (fun n : ℕ =>
          (2 : ℝ) / 3 + (MainTheorem.epsilon n : ℝ))
        Filter.atTop (nhds ((2 : ℝ) / 3)) := by
    simpa using tendsto_const_nhds.add epsilon_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hupper
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    have h := (maximumDistance_normalized_bounds n hn).1
    unfold normalizedMaximum
    have hR :
        (((2 / 3 : ℚ) : ℝ)) ≤
          ((((maximumDistance n : ℚ) /
            Nat.choose n 4) : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).2 h
    norm_num at hR ⊢
    exact hR
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    have h := (maximumDistance_normalized_bounds n hn).2
    unfold normalizedMaximum
    have hR :
        (((((maximumDistance n : ℚ) /
            Nat.choose n 4) : ℚ) : ℝ)) ≤
          ((((2 / 3 : ℚ) + MainTheorem.epsilon n : ℚ)) : ℝ) :=
      (Rat.cast_le (K := ℝ)).2 h
    norm_num at hR ⊢
    exact hR

end

end Sharpness

end QuartetV060
