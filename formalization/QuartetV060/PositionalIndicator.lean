import QuartetV060.CorrectionKernel

/-!
# Positional side-pair indicators

This file formalizes the full-domain indicator calculation from Section 5.
No distinctness assumption is made on the four taxa.  In particular, the
adjacent-correction identity below applies unchanged to tuples with repeated
entries.
-/

namespace QuartetV060

namespace Positional

noncomputable section

variable
    {X : Type*}
    [Fintype X] [Nonempty X] [DecidableEq X]

/-- The two ordered pairs of positions are separated by the ordered
side-pair `(A,B)`, in either orientation. -/
def Separates (A B : Finset X) (q₁ q₂ q₃ q₄ : X) : Prop :=
  (q₁ ∈ A ∧ q₂ ∈ A ∧ q₃ ∈ B ∧ q₄ ∈ B) ∨
    (q₁ ∈ B ∧ q₂ ∈ B ∧ q₃ ∈ A ∧ q₄ ∈ A)

/-- The `{0,1}`-valued positional side-pair indicator. -/
noncomputable def indicator (A B : Finset X) (q₁ q₂ q₃ q₄ : X) : ℚ := by
  classical
  exact if Separates A B q₁ q₂ q₃ q₄ then 1 else 0

/-- The same indicator attached to a bundled side-pair. -/
def sidePairIndicator (o : SidePair X) (q₁ q₂ q₃ q₄ : X) : ℚ :=
  indicator o.left o.right q₁ q₂ q₃ q₄

theorem indicator_eq_membership_formula
    (A B : Finset X) (hAB : Disjoint A B) (q₁ q₂ q₃ q₄ : X) :
    indicator A B q₁ q₂ q₃ q₄ =
      Kernel.indicator A q₁ * Kernel.indicator A q₂ *
          Kernel.indicator B q₃ * Kernel.indicator B q₄
        + Kernel.indicator B q₁ * Kernel.indicator B q₂ *
          Kernel.indicator A q₃ * Kernel.indicator A q₄ := by
  have hAB' := Finset.disjoint_left.mp hAB
  by_cases hA₁ : q₁ ∈ A <;>
    by_cases hA₂ : q₂ ∈ A <;>
    by_cases hA₃ : q₃ ∈ A <;>
    by_cases hA₄ : q₄ ∈ A <;>
    by_cases hB₁ : q₁ ∈ B <;>
    by_cases hB₂ : q₂ ∈ B <;>
    by_cases hB₃ : q₃ ∈ B <;>
    by_cases hB₄ : q₄ ∈ B <;>
    simp_all [indicator, Separates, Kernel.indicator]

theorem indicator_reverse
    (A B : Finset X) (q₁ q₂ q₃ q₄ : X) :
    indicator B A q₁ q₂ q₃ q₄ =
      indicator A B q₁ q₂ q₃ q₄ := by
  classical
  unfold indicator
  congr 1
  unfold Separates
  aesop

@[simp] theorem sidePairIndicator_reverse
    (o : SidePair X) (q₁ q₂ q₃ q₄ : X) :
    sidePairIndicator o.reverse q₁ q₂ q₃ q₄ =
      sidePairIndicator o q₁ q₂ q₃ q₄ := by
  exact indicator_reverse _ _ _ _ _ _

/-- Equation (the positional expansion following the kernel definition):
the product of two antisymmetric factors is the difference of the `13|24`
and `14|23` indicators. -/
theorem phi_product_eq_indicator_sub_indicator
    (o : SidePair X) (q₁ q₂ q₃ q₄ : X) :
    Kernel.phi o q₁ q₂ * Kernel.phi o q₃ q₄ =
      sidePairIndicator o q₁ q₃ q₂ q₄ -
        sidePairIndicator o q₁ q₄ q₂ q₃ := by
  unfold sidePairIndicator
  rw [indicator_eq_membership_formula o.left o.right o.disjoint,
    indicator_eq_membership_formula o.left o.right o.disjoint]
  unfold Kernel.phi
  ring

/-- The logical core of the adjacent-correction identity.  The three blocks
`K,H,L` are pairwise disjoint.  An ordered pair of position-groups is
separated by `K|L` exactly when it is separated by both edge cuts
`L|(K∪H)` and `K|(H∪L)`. -/
theorem separates_adjacent_iff
    (K H L : Finset X)
    (hKH : Disjoint K H) (hKL : Disjoint K L) (hHL : Disjoint H L)
    (q₁ q₂ q₃ q₄ : X) :
    Separates K L q₁ q₂ q₃ q₄ ↔
      Separates L (K ∪ H) q₁ q₂ q₃ q₄ ∧
        Separates K (H ∪ L) q₁ q₂ q₃ q₄ := by
  have hKH' := Finset.disjoint_left.mp hKH
  have hKL' := Finset.disjoint_left.mp hKL
  have hHL' := Finset.disjoint_left.mp hHL
  simp only [Separates, Finset.mem_union]
  aesop

/-- Full-domain adjacent correction identity.  It includes every repeated
label pattern because the statement quantifies over all four-tuples. -/
theorem adjacent_indicator
    (K H L : Finset X)
    (hKH : Disjoint K H) (hKL : Disjoint K L) (hHL : Disjoint H L)
    (q₁ q₂ q₃ q₄ : X) :
    indicator K L q₁ q₂ q₃ q₄ =
      indicator L (K ∪ H) q₁ q₂ q₃ q₄ *
        indicator K (H ∪ L) q₁ q₂ q₃ q₄ := by
  classical
  have hiff :=
    separates_adjacent_iff K H L hKH hKL hHL q₁ q₂ q₃ q₄
  by_cases h : Separates K L q₁ q₂ q₃ q₄
  · have hboth := hiff.mp h
    simp [indicator, h, hboth.1, hboth.2]
  · have hnotboth :
        ¬(Separates L (K ∪ H) q₁ q₂ q₃ q₄ ∧
          Separates K (H ∪ L) q₁ q₂ q₃ q₄) := by
      exact fun hboth => h (hiff.mpr hboth)
    by_cases hleft : Separates L (K ∪ H) q₁ q₂ q₃ q₄
    · have hright : ¬Separates K (H ∪ L) q₁ q₂ q₃ q₄ := by
        exact fun hr => hnotboth ⟨hleft, hr⟩
      simp [indicator, h, hleft, hright]
    · simp [indicator, h, hleft]

/-- Equivalent complement form used by the concrete tree occurrence
construction. -/
theorem adjacent_indicator_complements
    (K L : Finset X) (hKL : Disjoint K L)
    (q₁ q₂ q₃ q₄ : X) :
    indicator K L q₁ q₂ q₃ q₄ =
      indicator L Lᶜ q₁ q₂ q₃ q₄ *
        indicator K Kᶜ q₁ q₂ q₃ q₄ := by
  let H := (K ∪ L)ᶜ
  have hKH : Disjoint K H := by
    exact Finset.disjoint_left.mpr (by
      intro x hxK hxH
      exact (Finset.mem_compl.mp hxH)
        (Finset.mem_union_left L hxK))
  have hHL : Disjoint H L := by
    exact Finset.disjoint_left.mpr (by
      intro x hxH hxL
      exact (Finset.mem_compl.mp hxH)
        (Finset.mem_union_right K hxL))
  have hbase :=
    adjacent_indicator K H L hKH hKL hHL q₁ q₂ q₃ q₄
  have hL : K ∪ H = Lᶜ := by
    ext x
    simp only [H, Finset.mem_union, Finset.mem_compl]
    constructor
    · rintro (hxK | hxH)
      · exact fun hxL => Finset.disjoint_left.mp hKL hxK hxL
      · exact fun hxL => hxH (Or.inr hxL)
    · intro hxL
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr (by
          intro hxUnion
          exact hxUnion.elim hxK hxL)
  have hK : H ∪ L = Kᶜ := by
    ext x
    simp only [H, Finset.mem_union, Finset.mem_compl]
    constructor
    · rintro (hxH | hxL)
      · exact fun hxK => hxH (Or.inl hxK)
      · exact fun hxK => Finset.disjoint_left.mp hKL hxK hxL
    · intro hxK
      by_cases hxL : x ∈ L
      · exact Or.inr hxL
      · exact Or.inl (by
          intro hxUnion
          exact hxUnion.elim hxK hxL)
  simpa [hL, hK] using hbase

end

end Positional

end QuartetV060
