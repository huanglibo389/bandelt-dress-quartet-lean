import QuartetV060.FourFamilyLedger

/-!
# The occurrence kernel and the ordered-quadruple identity

This file formalizes the counting interface in Section 5 of v0.60.  Ordinary
edge occurrences and ordered-adjacent correction occurrences are both
represented by an ordered side-pair and a rational weight.  The kernel is
then a finite sum over those indexed occurrences.
-/

namespace QuartetV060

open scoped BigOperators

namespace Kernel

noncomputable section

variable
    {X : Type*}
    [Fintype X] [Nonempty X] [DecidableEq X]

/-- Rational truth indicator of membership in a finite side. -/
def indicator (A : Finset X) (x : X) : ℚ :=
  if x ∈ A then 1 else 0

/-- The antisymmetric function `phi_o` associated with an ordered
side-pair. -/
def phi (o : SidePair X) (x y : X) : ℚ :=
  indicator o.left x * indicator o.right y -
    indicator o.right x * indicator o.left y

@[simp] theorem phi_reverse (o : SidePair X) (x y : X) :
    phi o.reverse x y = -phi o x y := by
  unfold phi SidePair.reverse
  ring

/-- Unnormalized intersection cardinality, written as an indicator sum. -/
def rawIntersection (A B : Finset X) : ℚ :=
  ∑ x : X, indicator A x * indicator B x

theorem rawIntersection_eq_card (A B : Finset X) :
    rawIntersection A B = ((A ∩ B).card : ℚ) := by
  classical
  unfold rawIntersection indicator
  calc
    (∑ x : X,
        (if x ∈ A then (1 : ℚ) else 0) *
          (if x ∈ B then (1 : ℚ) else 0)) =
        ∑ x : X, if x ∈ A ∩ B then (1 : ℚ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hA : x ∈ A <;>
            by_cases hB : x ∈ B <;>
            simp [hA, hB]
    _ = ((A ∩ B).card : ℚ) := by
      have h := Finset.sum_boole
        (R := ℚ) (fun x : X => x ∈ A ∩ B) (Finset.univ : Finset X)
      have hfilter :
          (Finset.univ.filter fun x : X => x ∈ A ∩ B) = A ∩ B := by
        ext x
        simp
      rw [hfilter] at h
      simpa using h

/-- The unnormalized determinant `Delta(o,p)` from the manuscript. -/
def rawDelta (o p : SidePair X) : ℚ :=
  rawIntersection o.left p.left * rawIntersection o.right p.right -
    rawIntersection o.left p.right * rawIntersection o.right p.left

private theorem sum_separable (f g : X → ℚ) :
    (∑ x : X, ∑ y : X, f x * g y) =
      (∑ x : X, f x) * ∑ y : X, g y := by
  symm
  exact Fintype.sum_mul_sum f g

/-- Direct finite expansion:
`sum_(x,y) phi_o(x,y) phi_p(x,y) = 2 Delta(o,p)`. -/
theorem sum_phi_mul_phi (o p : SidePair X) :
    (∑ x : X, ∑ y : X, phi o x y * phi p x y) =
      2 * rawDelta o p := by
  let oL := fun x : X => indicator o.left x
  let oR := fun x : X => indicator o.right x
  let pL := fun x : X => indicator p.left x
  let pR := fun x : X => indicator p.right x
  have hLLRR :
      (∑ x : X, ∑ y : X,
        (oL x * oR y) * (pL x * pR y)) =
        rawIntersection o.left p.left *
          rawIntersection o.right p.right := by
    calc
      (∑ x : X, ∑ y : X,
          (oL x * oR y) * (pL x * pR y)) =
          ∑ x : X, ∑ y : X,
            (oL x * pL x) * (oR y * pR y) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ x : X, oL x * pL x) *
          ∑ y : X, oR y * pR y :=
        sum_separable _ _
      _ = rawIntersection o.left p.left *
          rawIntersection o.right p.right := rfl
  have hLRRL :
      (∑ x : X, ∑ y : X,
        (oL x * oR y) * (pR x * pL y)) =
        rawIntersection o.left p.right *
          rawIntersection o.right p.left := by
    calc
      (∑ x : X, ∑ y : X,
          (oL x * oR y) * (pR x * pL y)) =
          ∑ x : X, ∑ y : X,
            (oL x * pR x) * (oR y * pL y) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ x : X, oL x * pR x) *
          ∑ y : X, oR y * pL y :=
        sum_separable _ _
      _ = rawIntersection o.left p.right *
          rawIntersection o.right p.left := rfl
  have hRLLR :
      (∑ x : X, ∑ y : X,
        (oR x * oL y) * (pL x * pR y)) =
        rawIntersection o.left p.right *
          rawIntersection o.right p.left := by
    calc
      (∑ x : X, ∑ y : X,
          (oR x * oL y) * (pL x * pR y)) =
          ∑ x : X, ∑ y : X,
            (oR x * pL x) * (oL y * pR y) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ x : X, oR x * pL x) *
          ∑ y : X, oL y * pR y :=
        sum_separable _ _
      _ = rawIntersection o.left p.right *
          rawIntersection o.right p.left := by
            unfold rawIntersection oL oR pL pR
            ring
  have hRRLL :
      (∑ x : X, ∑ y : X,
        (oR x * oL y) * (pR x * pL y)) =
        rawIntersection o.left p.left *
          rawIntersection o.right p.right := by
    calc
      (∑ x : X, ∑ y : X,
          (oR x * oL y) * (pR x * pL y)) =
          ∑ x : X, ∑ y : X,
            (oR x * pR x) * (oL y * pL y) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ x : X, oR x * pR x) *
          ∑ y : X, oL y * pL y :=
        sum_separable _ _
      _ = rawIntersection o.left p.left *
          rawIntersection o.right p.right := by
            unfold rawIntersection oL oR pL pR
            ring
  unfold phi rawDelta
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hLLRR, hLRRL, hRLLR, hRRLL]
  ring

/-- The normalized side-pair determinant is `Delta²/N⁴`. -/
theorem sidePairDetSquare_eq_rawDelta
    (o p : SidePair X) :
    sidePairDetSquare o p =
      rawDelta o p ^ 2 / (Fintype.card X : ℚ) ^ 4 := by
  have hN : (Fintype.card X : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [sidePairDetSquare, sidePairTable, Table2.detSquare,
    Table2.det, intersectionMass, normalizedCard, rawDelta,
    rawIntersection_eq_card]
  field_simp [hN]

/-- A finite signed occurrence family.  Distinct indices remain distinct even
when their underlying side-pairs happen to coincide. -/
structure OccurrenceFamily (Occ : Type*) where
  sidePair : Occ → SidePair X
  weight : Occ → ℚ

namespace OccurrenceFamily

variable
    {Occ₁ Occ₂ : Type*}
    [Fintype Occ₁] [Fintype Occ₂]
    (F₁ : OccurrenceFamily (X := X) Occ₁)
    (F₂ : OccurrenceFamily (X := X) Occ₂)

/-- The double occurrence expansion of `f₁`. -/
def functional : ℚ :=
  ∑ η : Occ₁, ∑ θ : Occ₂,
    F₁.weight η * F₂.weight θ *
      sidePairDetSquare (F₁.sidePair η) (F₂.sidePair θ)

/-- The antisymmetric occurrence kernel. -/
def kernel (F : OccurrenceFamily (X := X) Occ₁)
    (q₁ q₂ q₃ q₄ : X) : ℚ :=
  ∑ η : Occ₁, F.weight η *
    phi (F.sidePair η) q₁ q₂ *
    phi (F.sidePair η) q₃ q₄

/-- Finite distributivity of the two occurrence sums inside the
ordered-quadruple sum. -/
private theorem kernel_product_expand (q₁ q₂ q₃ q₄ : X) :
    F₁.kernel q₁ q₂ q₃ q₄ * F₂.kernel q₁ q₂ q₃ q₄ =
      ∑ η : Occ₁, ∑ θ : Occ₂,
        (F₁.weight η * F₂.weight θ) *
        (phi (F₁.sidePair η) q₁ q₂ *
          phi (F₂.sidePair θ) q₁ q₂) *
        (phi (F₁.sidePair η) q₃ q₄ *
          phi (F₂.sidePair θ) q₃ q₄) := by
  unfold kernel
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  apply Finset.sum_congr rfl
  intro θ hθ
  ring

private theorem sum_pair_separable
    (f g : X → X → ℚ) :
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        f q₁ q₂ * g q₃ q₄) =
      (∑ q₁ : X, ∑ q₂ : X, f q₁ q₂) *
        ∑ q₃ : X, ∑ q₄ : X, g q₃ q₄ := by
  calc
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        f q₁ q₂ * g q₃ q₄) =
        ∑ q₁ : X, ∑ q₂ : X,
          f q₁ q₂ * (∑ q₃ : X, ∑ q₄ : X, g q₃ q₄) := by
            apply Finset.sum_congr rfl
            intro q₁ hq₁
            apply Finset.sum_congr rfl
            intro q₂ hq₂
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q₃ hq₃
            rw [Finset.mul_sum]
    _ = (∑ q₁ : X, ∑ q₂ : X, f q₁ q₂) *
          ∑ q₃ : X, ∑ q₄ : X, g q₃ q₄ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro q₁ hq₁
            rw [Finset.sum_mul]

private theorem quadruple_phi_product (o p : SidePair X) :
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        (phi o q₁ q₂ * phi p q₁ q₂) *
          (phi o q₃ q₄ * phi p q₃ q₄)) =
      4 * rawDelta o p ^ 2 := by
  calc
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        (phi o q₁ q₂ * phi p q₁ q₂) *
          (phi o q₃ q₄ * phi p q₃ q₄)) =
        (∑ q₁ : X, ∑ q₂ : X, phi o q₁ q₂ * phi p q₁ q₂) *
          ∑ q₃ : X, ∑ q₄ : X, phi o q₃ q₄ * phi p q₃ q₄ :=
      sum_pair_separable _ _
    _ = 4 * rawDelta o p ^ 2 := by
      rw [sum_phi_mul_phi]
      ring

private theorem sum_quadruple_occurrence_comm
    (h : X → X → X → X → Occ₁ → Occ₂ → ℚ) :
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        ∑ η : Occ₁, ∑ θ : Occ₂, h q₁ q₂ q₃ q₄ η θ) =
      ∑ η : Occ₁, ∑ θ : Occ₂,
        ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
          h q₁ q₂ q₃ q₄ η θ := by
  calc
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        ∑ η : Occ₁, ∑ θ : Occ₂, h q₁ q₂ q₃ q₄ η θ) =
        ∑ q : (X × X) × (X × X), ∑ o : Occ₁ × Occ₂,
          h q.1.1 q.1.2 q.2.1 q.2.2 o.1 o.2 := by
            simp only [Fintype.sum_prod_type]
    _ = ∑ o : Occ₁ × Occ₂, ∑ q : (X × X) × (X × X),
          h q.1.1 q.1.2 q.2.1 q.2.2 o.1 o.2 := by
            rw [Finset.sum_comm]
    _ = ∑ η : Occ₁, ∑ θ : Occ₂,
        ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
          h q₁ q₂ q₃ q₄ η θ := by
            simp only [Fintype.sum_prod_type]

private theorem sum_quadruple_const_mul
    (c : ℚ) (f : X → X → X → X → ℚ) :
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        c * f q₁ q₂ q₃ q₄) =
      c * ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        f q₁ q₂ q₃ q₄ := by
  simp only [Finset.mul_sum]

private theorem quadruple_kernel_sum :
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        F₁.kernel q₁ q₂ q₃ q₄ *
          F₂.kernel q₁ q₂ q₃ q₄) =
      ∑ η : Occ₁, ∑ θ : Occ₂,
        4 * (F₁.weight η * F₂.weight θ) *
          rawDelta (F₁.sidePair η) (F₂.sidePair θ) ^ 2 := by
  calc
    (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
        F₁.kernel q₁ q₂ q₃ q₄ *
          F₂.kernel q₁ q₂ q₃ q₄) =
        ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
          ∑ η : Occ₁, ∑ θ : Occ₂,
            (F₁.weight η * F₂.weight θ) *
            (phi (F₁.sidePair η) q₁ q₂ *
              phi (F₂.sidePair θ) q₁ q₂) *
            (phi (F₁.sidePair η) q₃ q₄ *
              phi (F₂.sidePair θ) q₃ q₄) := by
                apply Finset.sum_congr rfl
                intro q₁ hq₁
                apply Finset.sum_congr rfl
                intro q₂ hq₂
                apply Finset.sum_congr rfl
                intro q₃ hq₃
                apply Finset.sum_congr rfl
                intro q₄ hq₄
                exact kernel_product_expand F₁ F₂ q₁ q₂ q₃ q₄
    _ = ∑ η : Occ₁, ∑ θ : Occ₂,
        ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
          (F₁.weight η * F₂.weight θ) *
          (phi (F₁.sidePair η) q₁ q₂ *
            phi (F₂.sidePair θ) q₁ q₂) *
          (phi (F₁.sidePair η) q₃ q₄ *
            phi (F₂.sidePair θ) q₃ q₄) :=
      sum_quadruple_occurrence_comm _
    _ = ∑ η : Occ₁, ∑ θ : Occ₂,
        4 * (F₁.weight η * F₂.weight θ) *
          rawDelta (F₁.sidePair η) (F₂.sidePair θ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro η hη
            apply Finset.sum_congr rfl
            intro θ hθ
            calc
              (∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
                  (F₁.weight η * F₂.weight θ) *
                  (phi (F₁.sidePair η) q₁ q₂ *
                    phi (F₂.sidePair θ) q₁ q₂) *
                  (phi (F₁.sidePair η) q₃ q₄ *
                    phi (F₂.sidePair θ) q₃ q₄)) =
                  ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
                    (F₁.weight η * F₂.weight θ) *
                    ((phi (F₁.sidePair η) q₁ q₂ *
                      phi (F₂.sidePair θ) q₁ q₂) *
                    (phi (F₁.sidePair η) q₃ q₄ *
                      phi (F₂.sidePair θ) q₃ q₄)) := by
                        apply Finset.sum_congr rfl
                        intro q₁ hq₁
                        apply Finset.sum_congr rfl
                        intro q₂ hq₂
                        apply Finset.sum_congr rfl
                        intro q₃ hq₃
                        apply Finset.sum_congr rfl
                        intro q₄ hq₄
                        ring
              _ = (F₁.weight η * F₂.weight θ) *
                  ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
                    ((phi (F₁.sidePair η) q₁ q₂ *
                      phi (F₂.sidePair θ) q₁ q₂) *
                    (phi (F₁.sidePair η) q₃ q₄ *
                      phi (F₂.sidePair θ) q₃ q₄)) :=
                sum_quadruple_const_mul _ _
              _ = (F₁.weight η * F₂.weight θ) *
                  (4 * rawDelta (F₁.sidePair η)
                    (F₂.sidePair θ) ^ 2) := by
                      rw [quadruple_phi_product]
              _ = 4 * (F₁.weight η * F₂.weight θ) *
                  rawDelta (F₁.sidePair η)
                    (F₂.sidePair θ) ^ 2 := by
                      ring

/-- The ordered-quadruple kernel identity, including every repeated tuple. -/
theorem ordered_quadruple_kernel_identity :
    (Fintype.card X : ℚ) ^ 4 * F₁.functional F₂ =
      (1 / 4 : ℚ) *
        ∑ q₁ : X, ∑ q₂ : X, ∑ q₃ : X, ∑ q₄ : X,
          F₁.kernel q₁ q₂ q₃ q₄ *
            F₂.kernel q₁ q₂ q₃ q₄ := by
  classical
  have hN : (Fintype.card X : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [quadruple_kernel_sum F₁ F₂]
  unfold functional
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [sidePairDetSquare_eq_rawDelta]
  field_simp [hN]

end OccurrenceFamily

end

end Kernel

end QuartetV060
