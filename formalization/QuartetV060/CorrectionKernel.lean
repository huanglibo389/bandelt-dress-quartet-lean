import QuartetV060.Kernel

/-!
# The manuscript correction system as a signed occurrence kernel

This file connects the four-term definition of the auxiliary functional to
the occurrence kernel.  The occurrence type is the disjoint sum of ordinary
edge occurrences and ordered-adjacent correction occurrences; in particular,
two correction indices are never identified merely because they determine the
same underlying side-pair.
-/

namespace QuartetV060

open scoped BigOperators

noncomputable section

variable
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    {E A : Type*} [Fintype E] [DecidableEq E]
      [Fintype A] [DecidableEq A]

namespace CorrectionSystem

/-- The signed occurrence family attached to one coordinate of the
manuscript's correction system.  Ordinary occurrences have weight `1`;
ordered-adjacent corrections have weight `-1/2`. -/
def occurrenceFamily (S : CorrectionSystem X E A) :
    Kernel.OccurrenceFamily (X := X) (E ⊕ A) where
  sidePair
    | Sum.inl e => (S.ordinary e).toSidePair
    | Sum.inr α => S.corrected α
  weight
    | Sum.inl _ => 1
    | Sum.inr _ => -(1 / 2 : ℚ)

/-- The source fibers partition the correction occurrences with
multiplicity one. -/
theorem sum_fiber (S : CorrectionSystem X E A) (g : A → ℚ) :
    (∑ e : E, ∑ α ∈ S.fiber e, g α) = ∑ α : A, g α := by
  classical
  simp_rw [fiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α hα
  simp

end CorrectionSystem

section Functional

variable
    {E₁ A₁ E₂ A₂ : Type*}
    [Fintype E₁] [DecidableEq E₁]
    [Fintype A₁] [DecidableEq A₁]
    [Fintype E₂] [DecidableEq E₂]
    [Fintype A₂] [DecidableEq A₂]
    (S₁ : CorrectionSystem X E₁ A₁)
    (S₂ : CorrectionSystem X E₂ A₂)

private theorem total_correctedOrdinary :
    (∑ e : E₁, ∑ f : E₂, correctedOrdinary S₁ S₂ e f) =
      ∑ α : A₁, ∑ f : E₂,
        sidePairSplitDetSquare (S₁.corrected α) (S₂.ordinary f) := by
  unfold correctedOrdinary
  calc
    (∑ e : E₁, ∑ f : E₂, ∑ α ∈ S₁.fiber e,
        sidePairSplitDetSquare (S₁.corrected α) (S₂.ordinary f)) =
        ∑ f : E₂, ∑ e : E₁, ∑ α ∈ S₁.fiber e,
          sidePairSplitDetSquare (S₁.corrected α)
            (S₂.ordinary f) := by
              rw [Finset.sum_comm]
    _ = ∑ f : E₂, ∑ α : A₁,
        sidePairSplitDetSquare (S₁.corrected α)
          (S₂.ordinary f) := by
            apply Finset.sum_congr rfl
            intro f hf
            exact CorrectionSystem.sum_fiber S₁ _
    _ = ∑ α : A₁, ∑ f : E₂,
        sidePairSplitDetSquare (S₁.corrected α)
          (S₂.ordinary f) := by
            rw [Finset.sum_comm]

private theorem total_ordinaryCorrected :
    (∑ e : E₁, ∑ f : E₂, ordinaryCorrected S₁ S₂ e f) =
      ∑ e : E₁, ∑ β : A₂,
        splitSidePairDetSquare (S₁.ordinary e) (S₂.corrected β) := by
  unfold ordinaryCorrected
  apply Finset.sum_congr rfl
  intro e he
  exact CorrectionSystem.sum_fiber S₂ _

private theorem total_correctedCorrected :
    (∑ e : E₁, ∑ f : E₂, correctedCorrected S₁ S₂ e f) =
      ∑ α : A₁, ∑ β : A₂,
        sidePairDetSquare (S₁.corrected α) (S₂.corrected β) := by
  unfold correctedCorrected
  calc
    (∑ e : E₁, ∑ f : E₂,
        ∑ α ∈ S₁.fiber e, ∑ β ∈ S₂.fiber f,
          sidePairDetSquare (S₁.corrected α) (S₂.corrected β)) =
        ∑ e : E₁, ∑ α ∈ S₁.fiber e,
          ∑ f : E₂, ∑ β ∈ S₂.fiber f,
            sidePairDetSquare (S₁.corrected α)
              (S₂.corrected β) := by
                apply Finset.sum_congr rfl
                intro e he
                rw [Finset.sum_comm]
    _ = ∑ e : E₁, ∑ α ∈ S₁.fiber e,
        ∑ β : A₂,
          sidePairDetSquare (S₁.corrected α)
            (S₂.corrected β) := by
              apply Finset.sum_congr rfl
              intro e he
              apply Finset.sum_congr rfl
              intro α hα
              exact CorrectionSystem.sum_fiber S₂ _
    _ = ∑ α : A₁, ∑ β : A₂,
        sidePairDetSquare (S₁.corrected α)
          (S₂.corrected β) := by
            exact CorrectionSystem.sum_fiber S₁ _

private theorem sum_two_mul_const
    {U V : Type*} [Fintype U] [Fintype V]
    (f : U → V → ℚ) (c : ℚ) :
    (∑ u : U, ∑ v : V, f u v * c) =
      c * ∑ u : U, ∑ v : V, f u v := by
  calc
    (∑ u : U, ∑ v : V, f u v * c) =
        ∑ u : U, ∑ v : V, c * f u v := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          ring
    _ = c * ∑ u : U, ∑ v : V, f u v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]

private theorem sum_two_const_mul
    {U V : Type*} [Fintype U] [Fintype V]
    (c : ℚ) (f : U → V → ℚ) :
    (∑ u : U, ∑ v : V, c * f u v) =
      c * ∑ u : U, ∑ v : V, f u v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]

/-- Expanding the two disjoint-sum occurrence indices gives the four global
ordinary/corrected quadrants with coefficients `1,-1/2,-1/2,1/4`. -/
theorem occurrenceFunctional_eq_globalQuadrants :
    (S₁.occurrenceFamily).functional S₂.occurrenceFamily =
      (∑ e : E₁, ∑ f : E₂, ordinaryOrdinary S₁ S₂ e f)
      - (1 / 2 : ℚ) *
          (∑ α : A₁, ∑ f : E₂,
            sidePairSplitDetSquare (S₁.corrected α) (S₂.ordinary f))
      - (1 / 2 : ℚ) *
          (∑ e : E₁, ∑ β : A₂,
            splitSidePairDetSquare (S₁.ordinary e) (S₂.corrected β))
      + (1 / 4 : ℚ) *
          (∑ α : A₁, ∑ β : A₂,
            sidePairDetSquare (S₁.corrected α) (S₂.corrected β)) := by
  unfold Kernel.OccurrenceFamily.functional
    CorrectionSystem.occurrenceFamily ordinaryOrdinary
  simp only [Fintype.sum_sum_type]
  simp only [Finset.sum_add_distrib,
    sidePairDetSquare_toSidePair_toSidePair,
    sidePairDetSquare_toSidePair_left,
    sidePairDetSquare_toSidePair_right,
    sidePairSplitDetSquare_toSidePair]
  simp_rw [sum_two_const_mul]
  ring

/-- The edge-indexed definition of `auxiliaryFunctional` has the same four
global quadrants because each correction has exactly one source edge. -/
theorem auxiliaryFunctional_eq_globalQuadrants :
    auxiliaryFunctional S₁ S₂ =
      (∑ e : E₁, ∑ f : E₂, ordinaryOrdinary S₁ S₂ e f)
      - (1 / 2 : ℚ) *
          (∑ α : A₁, ∑ f : E₂,
            sidePairSplitDetSquare (S₁.corrected α) (S₂.ordinary f))
      - (1 / 2 : ℚ) *
          (∑ e : E₁, ∑ β : A₂,
            splitSidePairDetSquare (S₁.ordinary e) (S₂.corrected β))
      + (1 / 4 : ℚ) *
          (∑ α : A₁, ∑ β : A₂,
            sidePairDetSquare (S₁.corrected α) (S₂.corrected β)) := by
  unfold auxiliaryFunctional
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [sum_two_const_mul]
  rw [total_correctedOrdinary S₁ S₂]
  rw [total_ordinaryCorrected S₁ S₂]
  rw [total_correctedCorrected S₁ S₂]

/-- Exact identification of the manuscript's original four-term functional
with the signed occurrence functional used by the kernel proof. -/
theorem occurrenceFunctional_eq_auxiliary :
    (S₁.occurrenceFamily).functional S₂.occurrenceFamily =
      auxiliaryFunctional S₁ S₂ :=
  (occurrenceFunctional_eq_globalQuadrants S₁ S₂).trans
    (auxiliaryFunctional_eq_globalQuadrants S₁ S₂).symm

/-- The ordered-quadruple kernel formula, now stated directly for the
manuscript's auxiliary functional rather than for an abstract occurrence
family. -/
theorem auxiliaryFunctional_kernel_identity :
    (Fintype.card X : ℚ) ^ 4 * auxiliaryFunctional S₁ S₂ =
      (1 / 4 : ℚ) *
        ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
          (S₁.occurrenceFamily).kernel q₁ q₂ q₃ q₄ *
            (S₂.occurrenceFamily).kernel q₁ q₂ q₃ q₄ := by
  rw [← occurrenceFunctional_eq_auxiliary S₁ S₂]
  exact Kernel.OccurrenceFamily.ordered_quadruple_kernel_identity
    S₁.occurrenceFamily S₂.occurrenceFamily

end Functional

end

end QuartetV060
