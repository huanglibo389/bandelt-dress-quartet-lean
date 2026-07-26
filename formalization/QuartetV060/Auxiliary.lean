import QuartetV060.SplitSidePair

/-!
# The four ordinary/corrected choices and the auxiliary functional

This file is the exact finite-sum counterpart of the paper's definition of
`f₁`.  A correction occurrence retains its source edge explicitly, so an
ordered adjacent pair is never silently replaced by an unindexed sum.
-/

namespace QuartetV060

open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]

/-- Abstract data supplied by one tree coordinate to the definition of
`f₁`.  The tree realization will later instantiate `Edge`, `Correction`,
`ordinary`, `source`, and `corrected`. -/
structure CorrectionSystem
    (X Edge Correction : Type*)
    [Fintype X] [DecidableEq X] where
  ordinary : Edge → OrientedSplit X
  source : Correction → Edge
  corrected : Correction → SidePair X

namespace CorrectionSystem

variable {E A : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A]

/-- The ordered correction occurrences whose first edge is `e`. -/
def fiber (S : CorrectionSystem X E A) (e : E) : Finset A :=
  Finset.univ.filter fun α => S.source α = e

theorem mem_fiber_iff (S : CorrectionSystem X E A) (e : E) (α : A) :
    α ∈ S.fiber e ↔ S.source α = e := by
  simp [fiber]

end CorrectionSystem

section Auxiliary

variable {E₁ A₁ E₂ A₂ : Type*}
  [Fintype E₁] [DecidableEq E₁]
  [Fintype A₁] [DecidableEq A₁]
  [Fintype E₂] [DecidableEq E₂]
  [Fintype A₂] [DecidableEq A₂]

variable (S₁ : CorrectionSystem X E₁ A₁)
  (S₂ : CorrectionSystem X E₂ A₂)

/-- The ordinary/ordinary determinant for a fixed edge pair. -/
noncomputable def ordinaryOrdinary (e : E₁) (f : E₂) : ℚ :=
  splitDetSquare (S₁.ordinary e) (S₂.ordinary f)

/-- The sum denoted `T[σ_e⁺, τ_f]` in the paper. -/
noncomputable def correctedOrdinary (e : E₁) (f : E₂) : ℚ :=
  ∑ α ∈ S₁.fiber e,
    sidePairSplitDetSquare (S₁.corrected α) (S₂.ordinary f)

/-- The sum denoted `T[σ_e, τ_f⁺]` in the paper. -/
noncomputable def ordinaryCorrected (e : E₁) (f : E₂) : ℚ :=
  ∑ β ∈ S₂.fiber f,
    splitSidePairDetSquare (S₁.ordinary e) (S₂.corrected β)

/-- The sum denoted `T[σ_e⁺, τ_f⁺]` in the paper. -/
noncomputable def correctedCorrected (e : E₁) (f : E₂) : ℚ :=
  ∑ α ∈ S₁.fiber e, ∑ β ∈ S₂.fiber f,
    sidePairDetSquare (S₁.corrected α) (S₂.corrected β)

/-- The exact auxiliary functional from the v0.60 paper.  Each determinant
is squared before correction occurrences are summed. -/
noncomputable def auxiliaryFunctional : ℚ :=
  ∑ e, ∑ f,
    (ordinaryOrdinary S₁ S₂ e f
      - (1 / 2 : ℚ) * correctedOrdinary S₁ S₂ e f
      - (1 / 2 : ℚ) * ordinaryCorrected S₁ S₂ e f
      + (1 / 4 : ℚ) * correctedCorrected S₁ S₂ e f)

theorem ordinaryOrdinary_nonneg (e : E₁) (f : E₂) :
    0 ≤ ordinaryOrdinary S₁ S₂ e f := by
  exact splitDetSquare_nonneg _ _

theorem correctedOrdinary_nonneg (e : E₁) (f : E₂) :
    0 ≤ correctedOrdinary S₁ S₂ e f := by
  unfold correctedOrdinary
  apply Finset.sum_nonneg
  intro α hα
  exact sidePairSplitDetSquare_nonneg _ _

theorem ordinaryCorrected_nonneg (e : E₁) (f : E₂) :
    0 ≤ ordinaryCorrected S₁ S₂ e f := by
  unfold ordinaryCorrected
  apply Finset.sum_nonneg
  intro β hβ
  rw [splitSidePairDetSquare_eq_sidePairSplitDetSquare]
  exact sidePairSplitDetSquare_nonneg _ _

theorem correctedCorrected_nonneg (e : E₁) (f : E₂) :
    0 ≤ correctedCorrected S₁ S₂ e f := by
  unfold correctedCorrected
  apply Finset.sum_nonneg
  intro α hα
  apply Finset.sum_nonneg
  intro β hβ
  exact sidePairDetSquare_nonneg _ _

end Auxiliary

end QuartetV060
