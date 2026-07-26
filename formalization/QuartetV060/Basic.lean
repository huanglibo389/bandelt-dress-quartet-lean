import Mathlib

/-!
# Basic finite-mass notation for v0.60

The paper works with normalized cardinalities of subsets of a nonempty finite
taxon type.  The primary coefficient field is `ℚ`: every coefficient in the
finite tree calculation is rational, and no analytic completion is needed in
Appendix A.
-/

namespace QuartetV060

open scoped BigOperators

/-- Normalized cardinality of a finite set of taxa. -/
noncomputable def normalizedCard
    {X : Type*} [Fintype X] [Nonempty X] (A : Finset X) : ℚ :=
  (A.card : ℚ) / (Fintype.card X : ℚ)

theorem normalizedCard_nonneg
    {X : Type*} [Fintype X] [Nonempty X] (A : Finset X) :
    0 ≤ normalizedCard A := by
  unfold normalizedCard
  positivity

@[simp] theorem normalizedCard_univ
    {X : Type*} [Fintype X] [Nonempty X] :
    normalizedCard (Finset.univ : Finset X) = 1 := by
  unfold normalizedCard
  rw [Finset.card_univ]
  have hcard : (Fintype.card X : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Intersecting a finite set with a side and its complement partitions it
without changing normalized cardinality. -/
theorem normalizedCard_inter_add_inter_compl
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (A B : Finset X) :
    normalizedCard (A ∩ B) + normalizedCard (A ∩ Bᶜ) =
      normalizedCard A := by
  have hset : A ∩ Bᶜ = A \ B := by
    ext x
    simp
  have hcard :
      (A ∩ B).card + (A ∩ Bᶜ).card = A.card := by
    rw [hset]
    exact Finset.card_inter_add_card_sdiff A B
  have hcardQ :
      ((A ∩ B).card : ℚ) + ((A ∩ Bᶜ).card : ℚ) =
        (A.card : ℚ) := by
    exact_mod_cast hcard
  unfold normalizedCard
  rw [← add_div]
  rw [hcardQ]

/-- A finite side and its complement have total normalized mass one. -/
theorem normalizedCard_add_compl
    {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]
    (A : Finset X) :
    normalizedCard A + normalizedCard Aᶜ = 1 := by
  simpa using
    (normalizedCard_inter_add_inter_compl
      (A := (Finset.univ : Finset X)) (B := A))

end QuartetV060
