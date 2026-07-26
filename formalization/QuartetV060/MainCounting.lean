import QuartetV060.DistinctTupleCounting

/-!
# The finite quartet bounds from the counting identity

The counting identity already contains the exact repeated-label remainder.
This file isolates the final implication used in the main theorem: once the
concrete auxiliary functional is known to be nonnegative, the explicit
finite `Same` and `Diff` bounds follow.  No asymptotic notation is used in
the formal statements.
-/

namespace QuartetV060

namespace MainCounting

open QuartetDistance DistinctTupleCounting

noncomputable section

/-- The agreeing and differing four-subsets partition the complete set of
four-subsets. -/
theorem sameCount_add_diffCount
    {n : ℕ}
    (T₁ T₂ : Tree.PhyloTree (Fin n)) :
    sameCount T₁ T₂ + diffCount T₁ T₂ = Nat.choose n 4 := by
  have h :=
    Counting.truthAgreementCount_add_truthDistance
      (topologyOnFourSubset T₁) (topologyOnFourSubset T₂)
  simpa [sameCount, diffCount, Circular.FourSubset] using h

/-- The manuscript's explicit lower bound for the number of agreeing
quartets, conditional only on the concrete nonnegativity theorem for the
auxiliary functional. -/
theorem sameCount_lower_bound
    {n : ℕ} [Nonempty (Fin n)] (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n))
    (hnonneg :
      0 ≤ auxiliaryFunctional
        (PhyloOccurrences.correctionSystem T₁)
        (PhyloOccurrences.correctionSystem T₂)) :
    (Nat.choose n 4 : ℚ) / 3 -
        (6 * (n : ℚ) ^ 3 - 11 * (n : ℚ) ^ 2 + 6 * n) / 24 ≤
      sameCount T₁ T₂ := by
  have hcount := auxiliaryFunctional_counting_identity T₁ T₂
  have hrem := abs_repeatedRemainder_le hn T₁ T₂
  have hpartNat := sameCount_add_diffCount T₁ T₂
  have hpart :
      (sameCount T₁ T₂ : ℚ) + diffCount T₁ T₂ =
        Nat.choose n 4 := by
    exact_mod_cast hpartNat
  have hn4 : 0 ≤ (n : ℚ) ^ 4 := by positivity
  have hlhs :
      0 ≤ (n : ℚ) ^ 4 *
        auxiliaryFunctional
          (PhyloOccurrences.correctionSystem T₁)
          (PhyloOccurrences.correctionSystem T₂) :=
    mul_nonneg hn4 hnonneg
  have hremUpper :
      repeatedRemainder T₁ T₂ ≤
        (1 / 4 : ℚ) *
          (6 * (n : ℚ) ^ 3 - 11 * (n : ℚ) ^ 2 + 6 * n) :=
    le_trans (le_abs_self _) hrem
  rw [hcount] at hlhs
  linarith

/-- The equivalent explicit upper bound for quartet distance. -/
theorem diffCount_upper_bound
    {n : ℕ} [Nonempty (Fin n)] (hn : 4 ≤ n)
    (T₁ T₂ : Tree.PhyloTree (Fin n))
    (hnonneg :
      0 ≤ auxiliaryFunctional
        (PhyloOccurrences.correctionSystem T₁)
        (PhyloOccurrences.correctionSystem T₂)) :
    diffCount T₁ T₂ ≤
      (2 / 3 : ℚ) * Nat.choose n 4 +
        (6 * (n : ℚ) ^ 3 - 11 * (n : ℚ) ^ 2 + 6 * n) / 24 := by
  have hsame := sameCount_lower_bound hn T₁ T₂ hnonneg
  have hpartNat := sameCount_add_diffCount T₁ T₂
  have hpart :
      (sameCount T₁ T₂ : ℚ) + diffCount T₁ T₂ =
        Nat.choose n 4 := by
    exact_mod_cast hpartNat
  linarith

end

end MainCounting

end QuartetV060
