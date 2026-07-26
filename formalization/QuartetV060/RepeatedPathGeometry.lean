import QuartetV060.ActivePathGeometry

/-!
# Repeated-label path geometry

The common-path argument in `ActivePathGeometry` assumes that the two labels
within each displayed side are distinct.  This file removes that restriction.
For a repeated side `a a | b c`, a smallest active side containing `a`
contains a second taxon `d`.  Laminarity shows that `d` lies with `a` on every
active edge, so replacing one occurrence of `a` by `d` preserves the complete
active-edge and active-correction ledgers.  This reduces the repeated-label
case to the already proved distinct-within-side case.
-/

namespace QuartetV060

namespace RepeatedPathGeometry

open QuartetDistance PhyloOccurrences TreeKernel TreePathCounting
  TreeEdgeGeometry ActivePathGeometry

noncomputable section

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

omit [Fintype X] [Nonempty X] [DecidableEq X] in
/-- A separation of `a,d` from `b,c` also separates the repeated pair `a,a`
from `b,c`. -/
theorem separates_repeated_left_of_separates
    (A B : Finset X) (a d b c : X)
    (h : Positional.Separates A B a d b c) :
    Positional.Separates A B a a b c := by
  rcases h with h | h
  · exact Or.inl ⟨h.1, h.1, h.2.2.1, h.2.2.2⟩
  · exact Or.inr ⟨h.1, h.1, h.2.2.1, h.2.2.2⟩

/-- Replacing the second copy of a repeated left label cannot create a new
active edge. -/
theorem activeEdges_replace_left_subset
    (T : Tree.PhyloTree X) (a d b c : X) :
    activeEdges T a d b c ⊆ activeEdges T a a b c := by
  classical
  intro e he
  simp only [activeEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at he ⊢
  exact separates_repeated_left_of_separates _ _ _ _ _ _ he

/-- If `a,a | b,c` has an active relevant edge, one can replace the second
copy of `a` by a distinct taxon without changing the active-edge set. -/
theorem exists_left_replacement_preserving_activeEdges
    (T : Tree.PhyloTree X) (a b c : X)
    (hne : (activeEdges T a a b c).Nonempty) :
    ∃ d : X, d ≠ a ∧
      activeEdges T a a b c = activeEdges T a d b c := by
  classical
  obtain ⟨e₀, he₀, hmin⟩ :=
    Finset.exists_min_image
      (activeEdges T a a b c)
      (fun e : RelevantEdge T => (firstSide e.1 a).card)
      hne
  let e₀a : ActiveEdge T a a b c := ⟨e₀, he₀⟩
  have hside_card : 2 ≤ (firstSide e₀.1 a).card := by
    by_cases ha : a ∈ e₀.1.cluster
    · simpa [firstSide, ha] using e₀.2.1
    · simpa [firstSide, ha] using e₀.2.2
  have hnot_subset :
      ¬ firstSide e₀.1 a ⊆ ({a} : Finset X) := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  obtain ⟨d, hdside, hdnot⟩ := Set.not_subset.mp hnot_subset
  have hda : d ≠ a := by
    simpa using hdnot
  have hd_all :
      ∀ e : ActiveEdge T a a b c, d ∈ firstSide e.1.1 a := by
    intro e
    rcases firstSide_comparable_of_active T a a b c e₀a e with hsub | hsub
    · exact hsub hdside
    · have hcard_min :
          (firstSide e₀.1 a).card ≤
            (firstSide e.1.1 a).card :=
        hmin e.1 e.2
      have heq :
          firstSide e.1.1 a = firstSide e₀.1 a :=
        Finset.eq_of_subset_of_card_le hsub hcard_min
      exact heq.symm ▸ hdside
  refine ⟨d, hda, Finset.Subset.antisymm ?_ ?_⟩
  · intro e he
    let ea : ActiveEdge T a a b c := ⟨e, he⟩
    have hmem := active_firstSide_membership T a a b c ea
    have hd := hd_all ea
    change d ∈ firstSide e.1 a at hd
    change
      a ∈ firstSide e.1 a ∧
        b ∉ firstSide e.1 a ∧
        c ∉ firstSide e.1 a at hmem
    simp only [activeEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at ⊢
    by_cases ha : a ∈ e.1.cluster
    · have hd' : d ∈ e.1.cluster := by
        simpa [firstSide, ha] using hd
      have hb : b ∉ e.1.cluster := by
        simpa [firstSide, ha] using hmem.2.1
      have hc : c ∉ e.1.cluster := by
        simpa [firstSide, ha] using hmem.2.2
      exact Or.inl
        ⟨ha, hd', Finset.mem_compl.mpr hb,
          Finset.mem_compl.mpr hc⟩
    · have hd' : d ∈ e.1.clusterᶜ := by
        simpa [firstSide, ha] using hd
      have hb : b ∈ e.1.cluster := by
        have := hmem.2.1
        simpa [firstSide, ha] using this
      have hc : c ∈ e.1.cluster := by
        have := hmem.2.2
        simpa [firstSide, ha] using this
      exact Or.inr
        ⟨Finset.mem_compl.mpr ha, hd', hb, hc⟩
  · exact activeEdges_replace_left_subset T a d b c

/-- Equality of active-edge sets automatically transports the complete
active-correction ledger. -/
theorem activeCorrections_eq_of_activeEdges_eq
    (T : Tree.PhyloTree X)
    (q₁ q₂ q₃ q₄ r₁ r₂ r₃ r₄ : X)
    (h :
      activeEdges T q₁ q₂ q₃ q₄ =
        activeEdges T r₁ r₂ r₃ r₄) :
    activeCorrections T q₁ q₂ q₃ q₄ =
      activeCorrections T r₁ r₂ r₃ r₄ := by
  classical
  ext a
  rw [mem_activeCorrections_iff, mem_activeCorrections_iff, h]

/-- The path weight depends only on its active-edge set. -/
theorem pathWeight_eq_of_activeEdges_eq
    (T : Tree.PhyloTree X)
    (q₁ q₂ q₃ q₄ r₁ r₂ r₃ r₄ : X)
    (h :
      activeEdges T q₁ q₂ q₃ q₄ =
        activeEdges T r₁ r₂ r₃ r₄) :
    pathWeight T q₁ q₂ q₃ q₄ =
      pathWeight T r₁ r₂ r₃ r₄ := by
  rw [pathWeight_eq_card_sub_half_card,
    pathWeight_eq_card_sub_half_card, h,
    activeCorrections_eq_of_activeEdges_eq
      T q₁ q₂ q₃ q₄ r₁ r₂ r₃ r₄ h]

/-- Exchanging the two positional sides does not change the active-edge set. -/
theorem activeEdges_swap_position_pairs
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    activeEdges T q₁ q₂ q₃ q₄ =
      activeEdges T q₃ q₄ q₁ q₂ := by
  classical
  ext e
  simp only [activeEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, Positional.Separates]
  tauto

/-- Exchanging the two positional sides does not change the path weight. -/
theorem pathWeight_swap_position_pairs
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    pathWeight T q₁ q₂ q₃ q₄ =
      pathWeight T q₃ q₄ q₁ q₂ :=
  pathWeight_eq_of_activeEdges_eq
    T q₁ q₂ q₃ q₄ q₃ q₄ q₁ q₂
      (activeEdges_swap_position_pairs T q₁ q₂ q₃ q₄)

/-- A path weight with one repeated side is still zero or one when the
opposite side is distinct. -/
theorem pathWeight_repeated_left_eq_zero_or_one
    (T : Tree.PhyloTree X) (a b c : X)
    (hbc : b ≠ c) :
    pathWeight T a a b c = 0 ∨
      pathWeight T a a b c = 1 := by
  classical
  by_cases hempty : activeEdges T a a b c = ∅
  · exact Or.inl
      (pathWeight_eq_zero_of_activeEdges_eq_empty
        T a a b c hempty)
  · obtain ⟨d, hda, hactive⟩ :=
      exists_left_replacement_preserving_activeEdges
        T a b c (Finset.nonempty_iff_ne_empty.mpr hempty)
    have hweight :
        pathWeight T a a b c = pathWeight T a d b c :=
      pathWeight_eq_of_activeEdges_eq
        T a a b c a d b c hactive
    rcases pathWeight_eq_zero_or_one T a d b c hda.symm hbc with h | h
    · exact Or.inl (hweight.trans h)
    · exact Or.inr (hweight.trans h)

/-- Full-domain path-weight dichotomy, including every repeated-label
pattern in `X⁴`. -/
theorem pathWeight_eq_zero_or_one_full
    (T : Tree.PhyloTree X) (q₁ q₂ q₃ q₄ : X) :
    pathWeight T q₁ q₂ q₃ q₄ = 0 ∨
      pathWeight T q₁ q₂ q₃ q₄ = 1 := by
  classical
  by_cases h12 : q₁ = q₂
  · subst q₂
    by_cases h34 : q₃ = q₄
    · subst q₄
      by_cases hempty : activeEdges T q₁ q₁ q₃ q₃ = ∅
      · exact Or.inl
          (pathWeight_eq_zero_of_activeEdges_eq_empty
            T q₁ q₁ q₃ q₃ hempty)
      · obtain ⟨d, hd, hactive⟩ :=
          exists_left_replacement_preserving_activeEdges
            T q₁ q₃ q₃
              (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hfirst :
            pathWeight T q₁ q₁ q₃ q₃ =
              pathWeight T q₁ d q₃ q₃ :=
          pathWeight_eq_of_activeEdges_eq
            T q₁ q₁ q₃ q₃ q₁ d q₃ q₃ hactive
        have hswap :
            pathWeight T q₁ d q₃ q₃ =
              pathWeight T q₃ q₃ q₁ d :=
          pathWeight_swap_position_pairs T q₁ d q₃ q₃
        rcases
            pathWeight_repeated_left_eq_zero_or_one
              T q₃ q₁ d hd.symm with h | h
        · exact Or.inl (hfirst.trans (hswap.trans h))
        · exact Or.inr (hfirst.trans (hswap.trans h))
    · exact pathWeight_repeated_left_eq_zero_or_one
        T q₁ q₃ q₄ h34
  · by_cases h34 : q₃ = q₄
    · subst q₄
      have hswap :
          pathWeight T q₁ q₂ q₃ q₃ =
            pathWeight T q₃ q₃ q₁ q₂ :=
        pathWeight_swap_position_pairs T q₁ q₂ q₃ q₃
      rcases
          pathWeight_repeated_left_eq_zero_or_one
            T q₃ q₁ q₂ h12 with h | h
      · exact Or.inl (hswap.trans h)
      · exact Or.inr (hswap.trans h)
    · exact pathWeight_eq_zero_or_one T q₁ q₂ q₃ q₄ h12 h34

end

end RepeatedPathGeometry

end QuartetV060
