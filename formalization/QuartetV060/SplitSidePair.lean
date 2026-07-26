import QuartetV060.Determinant

/-!
# Finite oriented splits and adjacent side-pairs

The paper treats a split as orientation-free but performs local calculations
after choosing a side.  We therefore store an oriented representative and
prove that every squared determinant is invariant under reversal.
-/

namespace QuartetV060

open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X]

/-- An oriented representative `A | Aᶜ` of a nontrivial split. -/
structure OrientedSplit (X : Type*) [Fintype X] [DecidableEq X] where
  side : Finset X
  side_nonempty : side.Nonempty
  other_nonempty : sideᶜ.Nonempty

namespace OrientedSplit

def other (s : OrientedSplit X) : Finset X :=
  s.sideᶜ

/-- Reverse the chosen orientation of a split. -/
def reverse (s : OrientedSplit X) : OrientedSplit X where
  side := s.other
  side_nonempty := s.other_nonempty
  other_nonempty := by
    simpa [other] using s.side_nonempty

@[simp] theorem reverse_side (s : OrientedSplit X) :
    s.reverse.side = s.other := rfl

@[simp] theorem reverse_other (s : OrientedSplit X) :
    s.reverse.other = s.side := by
  simp [reverse, other]

@[simp] theorem reverse_reverse (s : OrientedSplit X) :
    s.reverse.reverse = s := by
  cases s
  simp [reverse, other]

end OrientedSplit

/-- An ordered pair of disjoint nonempty sides.  It need not cover `X`. -/
structure SidePair (X : Type*) [DecidableEq X] where
  left : Finset X
  right : Finset X
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  disjoint : Disjoint left right

namespace OrientedSplit

/-- Regard a split as the side-pair made of its two complementary sides. -/
def toSidePair (s : OrientedSplit X) : SidePair X where
  left := s.side
  right := s.other
  left_nonempty := s.side_nonempty
  right_nonempty := s.other_nonempty
  disjoint := by
    simp [OrientedSplit.other, Finset.disjoint_left]

end OrientedSplit

namespace SidePair

def reverse (p : SidePair X) : SidePair X where
  left := p.right
  right := p.left
  left_nonempty := p.right_nonempty
  right_nonempty := p.left_nonempty
  disjoint := p.disjoint.symm

@[simp] theorem reverse_reverse (p : SidePair X) :
    p.reverse.reverse = p := by
  cases p
  rfl

end SidePair

/-- Normalized mass of an intersection. -/
noncomputable def intersectionMass (A B : Finset X) : ℚ :=
  normalizedCard (A ∩ B)

/-- The normalized `2 x 2` table associated with two oriented splits. -/
noncomputable def splitTable
    (σ τ : OrientedSplit X) : Table2 ℚ where
  a := intersectionMass σ.side τ.side
  b := intersectionMass σ.side τ.other
  c := intersectionMass σ.other τ.side
  d := intersectionMass σ.other τ.other

theorem splitTable_total (σ τ : OrientedSplit X) :
    let t := splitTable σ τ
    t.a + t.b + t.c + t.d = 1 := by
  dsimp [splitTable, intersectionMass, OrientedSplit.other]
  calc
    normalizedCard (σ.side ∩ τ.side) +
          normalizedCard (σ.side ∩ τ.sideᶜ) +
          normalizedCard (σ.sideᶜ ∩ τ.side) +
          normalizedCard (σ.sideᶜ ∩ τ.sideᶜ)
        =
      (normalizedCard (σ.side ∩ τ.side) +
          normalizedCard (σ.side ∩ τ.sideᶜ)) +
      (normalizedCard (σ.sideᶜ ∩ τ.side) +
          normalizedCard (σ.sideᶜ ∩ τ.sideᶜ)) := by ring
    _ = normalizedCard σ.side + normalizedCard σ.sideᶜ := by
      rw [normalizedCard_inter_add_inter_compl]
      rw [normalizedCard_inter_add_inter_compl]
    _ = 1 := normalizedCard_add_compl σ.side

theorem splitTable_reverse_left (σ τ : OrientedSplit X) :
    splitTable σ.reverse τ = Table2.reverseRows (splitTable σ τ) := by
  ext <;>
    simp [splitTable, intersectionMass, OrientedSplit.other,
      Table2.reverseRows]

theorem splitTable_reverse_right (σ τ : OrientedSplit X) :
    splitTable σ τ.reverse = Table2.reverseCols (splitTable σ τ) := by
  ext <;>
    simp [splitTable, intersectionMass, OrientedSplit.other,
      Table2.reverseCols]

/-- The ordinary split determinant square. -/
noncomputable def splitDetSquare
    (σ τ : OrientedSplit X) : ℚ :=
  Table2.detSquare (splitTable σ τ)

/-- Swapping the two split coordinates transposes the normalized table. -/
theorem splitTable_swap (σ τ : OrientedSplit X) :
    splitTable σ τ = Table2.transpose (splitTable τ σ) := by
  ext <;>
    simp [splitTable, Table2.transpose, intersectionMass,
      Finset.inter_comm]

/-- A squared split determinant is symmetric in its two split arguments. -/
theorem splitDetSquare_comm (σ τ : OrientedSplit X) :
    splitDetSquare σ τ = splitDetSquare τ σ := by
  rw [splitDetSquare, splitTable_swap]
  simp [splitDetSquare]

@[simp] theorem splitDetSquare_reverse_left (σ τ : OrientedSplit X) :
    splitDetSquare σ.reverse τ = splitDetSquare σ τ := by
  simp [splitDetSquare, splitTable_reverse_left]

@[simp] theorem splitDetSquare_reverse_right (σ τ : OrientedSplit X) :
    splitDetSquare σ τ.reverse = splitDetSquare σ τ := by
  simp [splitDetSquare, splitTable_reverse_right]

theorem splitDetSquare_nonneg (σ τ : OrientedSplit X) :
    0 ≤ splitDetSquare σ τ := by
  exact Table2.detSquare_nonneg _

/-- The ordinary split determinant is the square of the centered mass of
the two selected sides.  This is the finite-set form used to identify the
entry determinant with a principal-chart centered coordinate. -/
theorem splitDetSquare_eq_centeredIntersection_sq
    (σ τ : OrientedSplit X) :
    splitDetSquare σ τ =
      (intersectionMass σ.side τ.side -
        normalizedCard σ.side * normalizedCard τ.side) ^ 2 := by
  have hdet :=
    Table2.centeredCovariance_eq_det
      (splitTable σ τ) (splitTable_total σ τ)
  unfold splitDetSquare Table2.detSquare
  rw [← hdet]
  unfold splitTable
  dsimp
  have hrow :
      intersectionMass σ.side τ.side +
          intersectionMass σ.side τ.other =
        normalizedCard σ.side := by
    exact normalizedCard_inter_add_inter_compl σ.side τ.side
  have hcol :
      intersectionMass σ.side τ.side +
          intersectionMass σ.other τ.side =
        normalizedCard τ.side := by
    simpa [intersectionMass, OrientedSplit.other, Finset.inter_comm] using
      (normalizedCard_inter_add_inter_compl τ.side σ.side)
  rw [hrow, hcol]

/-- The normalized table for two ordered side-pairs. -/
noncomputable def sidePairTable (p q : SidePair X) : Table2 ℚ where
  a := intersectionMass p.left q.left
  b := intersectionMass p.left q.right
  c := intersectionMass p.right q.left
  d := intersectionMass p.right q.right

noncomputable def sidePairDetSquare (p q : SidePair X) : ℚ :=
  Table2.detSquare (sidePairTable p q)

@[simp] theorem sidePairDetSquare_toSidePair_toSidePair
    (σ τ : OrientedSplit X) :
    sidePairDetSquare σ.toSidePair τ.toSidePair =
      splitDetSquare σ τ := rfl

theorem sidePairTable_reverse_left (p q : SidePair X) :
    sidePairTable p.reverse q = Table2.reverseRows (sidePairTable p q) := rfl

theorem sidePairTable_reverse_right (p q : SidePair X) :
    sidePairTable p q.reverse = Table2.reverseCols (sidePairTable p q) := rfl

@[simp] theorem sidePairDetSquare_reverse_left (p q : SidePair X) :
    sidePairDetSquare p.reverse q = sidePairDetSquare p q := by
  simp [sidePairDetSquare, sidePairTable_reverse_left]

@[simp] theorem sidePairDetSquare_reverse_right (p q : SidePair X) :
    sidePairDetSquare p q.reverse = sidePairDetSquare p q := by
  simp [sidePairDetSquare, sidePairTable_reverse_right]

theorem sidePairDetSquare_nonneg (p q : SidePair X) :
    0 ≤ sidePairDetSquare p q := by
  exact Table2.detSquare_nonneg _

/-- The normalized table for a side-pair in the row coordinate and a split
in the column coordinate. -/
noncomputable def sidePairSplitTable
    (p : SidePair X) (τ : OrientedSplit X) : Table2 ℚ where
  a := intersectionMass p.left τ.side
  b := intersectionMass p.left τ.other
  c := intersectionMass p.right τ.side
  d := intersectionMass p.right τ.other

noncomputable def sidePairSplitDetSquare
    (p : SidePair X) (τ : OrientedSplit X) : ℚ :=
  Table2.detSquare (sidePairSplitTable p τ)

@[simp] theorem sidePairSplitDetSquare_toSidePair
    (σ τ : OrientedSplit X) :
    sidePairSplitDetSquare σ.toSidePair τ =
      splitDetSquare σ τ := rfl

/-- The split/side-pair table is the transpose of the corresponding
side-pair/split table. -/
noncomputable def splitSidePairTable
    (σ : OrientedSplit X) (q : SidePair X) : Table2 ℚ :=
  Table2.transpose (sidePairSplitTable q σ)

noncomputable def splitSidePairDetSquare
    (σ : OrientedSplit X) (q : SidePair X) : ℚ :=
  Table2.detSquare (splitSidePairTable σ q)

@[simp] theorem sidePairDetSquare_toSidePair_right
    (p : SidePair X) (τ : OrientedSplit X) :
    sidePairDetSquare p τ.toSidePair =
      sidePairSplitDetSquare p τ := rfl

@[simp] theorem sidePairDetSquare_toSidePair_left
    (σ : OrientedSplit X) (q : SidePair X) :
    sidePairDetSquare σ.toSidePair q =
      splitSidePairDetSquare σ q := by
  unfold sidePairDetSquare sidePairTable splitSidePairDetSquare
    splitSidePairTable sidePairSplitTable
  congr 1
  ext <;>
    simp [intersectionMass, Finset.inter_comm, Table2.transpose,
      OrientedSplit.toSidePair]

@[simp] theorem splitSidePairDetSquare_eq_sidePairSplitDetSquare
    (σ : OrientedSplit X) (q : SidePair X) :
    splitSidePairDetSquare σ q = sidePairSplitDetSquare q σ := by
  simp [splitSidePairDetSquare, splitSidePairTable,
    sidePairSplitDetSquare]

theorem sidePairSplitTable_reverse_left
    (p : SidePair X) (τ : OrientedSplit X) :
    sidePairSplitTable p.reverse τ =
      Table2.reverseRows (sidePairSplitTable p τ) := rfl

theorem sidePairSplitTable_reverse_right
    (p : SidePair X) (τ : OrientedSplit X) :
    sidePairSplitTable p τ.reverse =
      Table2.reverseCols (sidePairSplitTable p τ) := by
  ext <;>
    simp [sidePairSplitTable, intersectionMass, OrientedSplit.other,
      Table2.reverseCols]

@[simp] theorem sidePairSplitDetSquare_reverse_left
    (p : SidePair X) (τ : OrientedSplit X) :
    sidePairSplitDetSquare p.reverse τ =
      sidePairSplitDetSquare p τ := by
  simp [sidePairSplitDetSquare, sidePairSplitTable_reverse_left]

@[simp] theorem sidePairSplitDetSquare_reverse_right
    (p : SidePair X) (τ : OrientedSplit X) :
    sidePairSplitDetSquare p τ.reverse =
      sidePairSplitDetSquare p τ := by
  simp [sidePairSplitDetSquare, sidePairSplitTable_reverse_right]

theorem sidePairSplitDetSquare_nonneg
    (p : SidePair X) (τ : OrientedSplit X) :
    0 ≤ sidePairSplitDetSquare p τ := by
  exact Table2.detSquare_nonneg _

/-- Scalar data for comparing an adjacent side-pair with an ordinary split. -/
noncomputable def sidePairAgainstSplitData
    (p : SidePair X) (τ : OrientedSplit X) : SidePairData ℚ where
  leftMass := normalizedCard p.left
  rightMass := normalizedCard p.right
  leftIntersection := intersectionMass p.left τ.side
  rightIntersection := intersectionMass p.right τ.side
  mean := normalizedCard τ.side

/-- The finite-set side-pair determinant is the square of the raw contrast
`c_L A - c_K C` used in the paper. -/
theorem sidePair_split_det_eq_rawContrast_sq
    (p : SidePair X) (τ : OrientedSplit X) :
    sidePairSplitDetSquare p τ =
      SidePairData.rawContrast (sidePairAgainstSplitData p τ) ^ 2 := by
  have hleft :=
    normalizedCard_inter_add_inter_compl p.left τ.side
  have hright :=
    normalizedCard_inter_add_inter_compl p.right τ.side
  have hleft' :
      intersectionMass p.left τ.other =
        normalizedCard p.left - intersectionMass p.left τ.side := by
    dsimp [intersectionMass, OrientedSplit.other]
    linarith
  have hright' :
      intersectionMass p.right τ.other =
        normalizedCard p.right - intersectionMass p.right τ.side := by
    dsimp [intersectionMass, OrientedSplit.other]
    linarith
  dsimp [sidePairSplitDetSquare, sidePairSplitTable, Table2.detSquare,
    Table2.det, sidePairAgainstSplitData, SidePairData.rawContrast]
  rw [hleft', hright']
  ring

/-- This is the exact finite-set form of the adjacent-pair calculation in
the paper: the side-pair determinant equals the neighboring centered
contrast squared. -/
theorem sidePair_split_det_eq_neighboringContrast_sq
    (p : SidePair X) (τ : OrientedSplit X) :
    sidePairSplitDetSquare p τ =
      SidePairData.neighboringContrast
        (sidePairAgainstSplitData p τ) ^ 2 := by
  rw [sidePair_split_det_eq_rawContrast_sq]
  exact SidePairData.rawContrast_sq_eq_neighboringContrast_sq _

end QuartetV060
