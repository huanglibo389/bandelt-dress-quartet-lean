import QuartetV060.ActivePathGeometry

/-!
# The concrete tree kernel as a signed quartet-topology indicator

This file closes the geometric interpretation of the manuscript kernel.
For labels distinct within the two tested pairings, each positional path
weight is the truth indicator of an actual delete-edge separation.  The tree
kernel is therefore the difference of the `13|24` and `14|23` displayed-pair
indicators.
-/

namespace QuartetV060

namespace QuartetKernelGeometry

open QuartetDistance
open TreeKernel
open ActivePathGeometry

noncomputable section

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

/-- The rational `{0,1}` indicator of a directly displayed ordered pairing. -/
noncomputable def displaysPairIndicator
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) : ℚ := by
  classical
  exact if DisplaysPair T q₁ q₂ q₃ q₄ then 1 else 0

/-- Path weight is exactly the indicator of delete-edge separation. -/
theorem pathWeight_eq_displaysPairIndicator
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (hq12 : q₁ ≠ q₂) (hq34 : q₃ ≠ q₄) :
    pathWeight T q₁ q₂ q₃ q₄ =
      displaysPairIndicator T q₁ q₂ q₃ q₄ := by
  classical
  by_cases hdisplay : DisplaysPair T q₁ q₂ q₃ q₄
  · have hone :=
      (pathWeight_eq_one_iff_displaysPair
        T q₁ q₂ q₃ q₄ hq12 hq34).2 hdisplay
    simp [displaysPairIndicator, hdisplay, hone]
  · have hnotone :
        pathWeight T q₁ q₂ q₃ q₄ ≠ 1 :=
      fun hone =>
        hdisplay
          ((pathWeight_eq_one_iff_displaysPair
            T q₁ q₂ q₃ q₄ hq12 hq34).1 hone)
    rcases pathWeight_eq_zero_or_one
      T q₁ q₂ q₃ q₄ hq12 hq34 with hzero | hone
    · simp [displaysPairIndicator, hdisplay, hzero]
    · exact False.elim (hnotone hone)

/-- Exact pointwise quartet interpretation of the concrete occurrence kernel.
The four inequalities are precisely those required by the two displayed
pairings on the right. -/
theorem kernel_eq_pairingIndicator_sub_pairingIndicator
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X)
    (h13 : q₁ ≠ q₃) (h24 : q₂ ≠ q₄)
    (h14 : q₁ ≠ q₄) (h23 : q₂ ≠ q₃) :
    kernel T q₁ q₂ q₃ q₄ =
      displaysPairIndicator T q₁ q₃ q₂ q₄ -
        displaysPairIndicator T q₁ q₄ q₂ q₃ := by
  rw [kernel_eq_pathWeight_sub_pathWeight,
    pathWeight_eq_displaysPairIndicator
      T q₁ q₃ q₂ q₄ h13 h24,
    pathWeight_eq_displaysPairIndicator
      T q₁ q₄ q₂ q₃ h14 h23]

end

end QuartetKernelGeometry

end QuartetV060
