import QuartetV060.RepeatedPathGeometry

/-!
# Full-domain range of the concrete tree kernel

Every positional path weight is zero or one, including tuples with repeated
labels.  The concrete signed quartet kernel is the difference of two such
weights and therefore takes only the values `-1`, `0`, and `1`.
-/

namespace QuartetV060

namespace KernelRange

open QuartetDistance TreeKernel
open RepeatedPathGeometry

noncomputable section

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

/-- The exact full-domain range of the concrete tree kernel. -/
theorem kernel_eq_neg_one_or_zero_or_one
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    kernel T q₁ q₂ q₃ q₄ = -1 ∨
      kernel T q₁ q₂ q₃ q₄ = 0 ∨
      kernel T q₁ q₂ q₃ q₄ = 1 := by
  rw [kernel_eq_pathWeight_sub_pathWeight]
  rcases pathWeight_eq_zero_or_one_full T q₁ q₃ q₂ q₄ with h₁ | h₁ <;>
    rcases pathWeight_eq_zero_or_one_full T q₁ q₄ q₂ q₃ with h₂ | h₂ <;>
    rw [h₁, h₂] <;> norm_num

/-- Uniform pointwise bound for the concrete tree kernel. -/
theorem abs_kernel_le_one
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    |kernel T q₁ q₂ q₃ q₄| ≤ 1 := by
  rcases kernel_eq_neg_one_or_zero_or_one T q₁ q₂ q₃ q₄ with h | h | h <;>
    rw [h] <;> norm_num

/-- Uniform pointwise bound for the product of two tree kernels. -/
theorem abs_kernel_mul_kernel_le_one
    (T₁ T₂ : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    |kernel T₁ q₁ q₂ q₃ q₄ * kernel T₂ q₁ q₂ q₃ q₄| ≤ 1 := by
  rw [abs_mul]
  nlinarith [abs_kernel_le_one T₁ q₁ q₂ q₃ q₄,
    abs_kernel_le_one T₂ q₁ q₂ q₃ q₄,
    abs_nonneg (kernel T₁ q₁ q₂ q₃ q₄),
    abs_nonneg (kernel T₂ q₁ q₂ q₃ q₄)]

end

end KernelRange

end QuartetV060
