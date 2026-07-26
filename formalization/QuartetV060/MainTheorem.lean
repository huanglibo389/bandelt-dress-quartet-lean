import QuartetV060.ConcreteFourFamilies
import QuartetV060.MainCounting

/-!
# The concrete v0.60 quartet-distance theorem

The only nonnegativity input in this file is the concrete bridge-ledger
identity proved in `ConcreteFourFamilies`.  Thus the final counting bound is
connected to the manuscript's Appendix A rather than to the alternative
permuton proof.
-/

namespace QuartetV060

namespace MainTheorem

open QuartetDistance
open DistinctTupleCounting

noncomputable section

/-- The exact finite lower bound for the number of agreeing quartets. -/
theorem sameCount_lower_bound
    {n : ℕ} [Nonempty (Fin n)] (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    (Nat.choose n 4 : ℚ) / 3 -
        (6 * (n : ℚ) ^ 3 - 11 * (n : ℚ) ^ 2 + 6 * n) / 24 ≤
      sameCount T₁ T₂ := by
  exact MainCounting.sameCount_lower_bound hn T₁ T₂
    (ConcreteFourFamilies.auxiliaryFunctional_nonnegative
      (T₁ := T₁) (T₂ := T₂))

/-- The exact finite upper bound for quartet distance. -/
theorem diffCount_upper_bound
    {n : ℕ} [Nonempty (Fin n)] (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    diffCount T₁ T₂ ≤
      (2 / 3 : ℚ) * Nat.choose n 4 +
        (6 * (n : ℚ) ^ 3 - 11 * (n : ℚ) ^ 2 + 6 * n) / 24 := by
  exact MainCounting.diffCount_upper_bound hn T₁ T₂
    (ConcreteFourFamilies.auxiliaryFunctional_nonnegative
      (T₁ := T₁) (T₂ := T₂))

/-- The explicit error term in the normalized statement of the manuscript. -/
def epsilon (n : ℕ) : ℚ :=
  (6 * (n : ℚ) ^ 3 - 11 * (n : ℚ) ^ 2 + 6 * n) /
    (24 * Nat.choose n 4)

theorem choose_four_pos
    {n : ℕ} (hn : 4 ≤ n) :
    (0 : ℚ) < Nat.choose n 4 := by
  exact_mod_cast Nat.choose_pos hn

/-- The normalized lower and upper bounds displayed in the main theorem. -/
theorem normalized_bounds
    {n : ℕ} [Nonempty (Fin n)] (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    (1 / 3 : ℚ) - epsilon n ≤
        (sameCount T₁ T₂ : ℚ) / Nat.choose n 4 ∧
      (diffCount T₁ T₂ : ℚ) / Nat.choose n 4 ≤
        (2 / 3 : ℚ) + epsilon n := by
  have hchoose := choose_four_pos hn
  constructor
  · rw [le_div_iff₀ hchoose]
    have h := sameCount_lower_bound hn T₁ T₂
    unfold epsilon
    field_simp
    nlinarith
  · rw [div_le_iff₀ hchoose]
    have h := diffCount_upper_bound hn T₁ T₂
    unfold epsilon
    field_simp
    nlinarith

end

end MainTheorem

end QuartetV060
