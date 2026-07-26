import QuartetV060.Auxiliary

/-!
# The four-sector index partition

The paper's letters `a,b,c,d` denote index classes, not scalar table entries.
Encoding an atom by its sector makes disjointness and exhaustiveness part of
the type-level data rather than a repeated side condition.
-/

namespace QuartetV060

open scoped BigOperators

/-- The four index classes in their paper names.  The two central sides are
`a ∪ c` and `b ∪ d`. -/
inductive Sector where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/-- The six disjoint classes in the paper's partition of `Ω²`. -/
inductive PairClass where
  | deltaA
  | deltaB
  | sameEndpoint
  | oppositeEndpoint
  | sameResidual
  | oppositeResidual
  deriving DecidableEq, Fintype, Repr

/-- A four-sector structure on an abstract finite atom type. -/
structure FourSector (Ω : Type*) where
  sector : Ω → Sector

namespace FourSector

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def atoms (F : FourSector Ω) (s : Sector) : Finset Ω :=
  Finset.univ.filter fun u => F.sector u = s

def a (F : FourSector Ω) : Finset Ω := F.atoms .a
def b (F : FourSector Ω) : Finset Ω := F.atoms .b
def c (F : FourSector Ω) : Finset Ω := F.atoms .c
def d (F : FourSector Ω) : Finset Ω := F.atoms .d

def isLeftSector : Sector → Bool
  | .a | .c => true
  | .b | .d => false

def sameSide (F : FourSector Ω) (u v : Ω) : Prop :=
  isLeftSector (F.sector u) = isLeftSector (F.sector v)

instance (F : FourSector Ω) (u v : Ω) : Decidable (F.sameSide u v) :=
  by
    unfold sameSide
    infer_instance

def isEndpoint (F : FourSector Ω) (u : Ω) : Prop :=
  F.sector u = .a ∨ F.sector u = .b

def isResidual (F : FourSector Ω) (u : Ω) : Prop :=
  F.sector u = .c ∨ F.sector u = .d

instance (F : FourSector Ω) (u : Ω) : Decidable (F.isEndpoint u) :=
  by
    unfold isEndpoint
    infer_instance

instance (F : FourSector Ω) (u : Ω) : Decidable (F.isResidual u) :=
  by
    unfold isResidual
    infer_instance

/-- `S(u)`, the full same-side block containing `u`. -/
def sameSideBlock (F : FourSector Ω) (u : Ω) : Finset Ω :=
  Finset.univ.filter fun v => F.sameSide u v

/-- `bar u`, the full central side opposite to `u`. -/
def oppositeSideBlock (F : FourSector Ω) (u : Ω) : Finset Ω :=
  Finset.univ.filter fun v => ¬F.sameSide u v

@[simp] theorem mem_sameSideBlock_iff (F : FourSector Ω) (u v : Ω) :
    v ∈ F.sameSideBlock u ↔ F.sameSide u v := by
  simp [sameSideBlock]

@[simp] theorem mem_oppositeSideBlock_iff (F : FourSector Ω) (u v : Ω) :
    v ∈ F.oppositeSideBlock u ↔ ¬F.sameSide u v := by
  simp [oppositeSideBlock]

theorem sameSideBlock_disjoint_opposite (F : FourSector Ω) (u : Ω) :
    Disjoint (F.sameSideBlock u) (F.oppositeSideBlock u) := by
  rw [Finset.disjoint_left]
  simp

theorem sameSideBlock_union_opposite (F : FourSector Ω) (u : Ω) :
    F.sameSideBlock u ∪ F.oppositeSideBlock u = Finset.univ := by
  ext v
  by_cases h : F.sameSide u v <;> simp [h]

/-- Classify one ordered pair exactly as in
`Δ_a ⊔ Δ_b ⊔ M_S ⊔ D ⊔ N_S ⊔ M_D`. -/
def pairClass (F : FourSector Ω) (u v : Ω) : PairClass :=
  match F.sector u with
  | .a =>
      if u = v then .deltaA
      else if F.sameSide u v then .sameEndpoint else .oppositeEndpoint
  | .b =>
      if u = v then .deltaB
      else if F.sameSide u v then .sameEndpoint else .oppositeEndpoint
  | .c =>
      if F.sameSide u v then .sameResidual else .oppositeResidual
  | .d =>
      if F.sameSide u v then .sameResidual else .oppositeResidual

def deltaA (F : FourSector Ω) (u v : Ω) : Prop :=
  F.pairClass u v = .deltaA

def deltaB (F : FourSector Ω) (u v : Ω) : Prop :=
  F.pairClass u v = .deltaB

/-- The paper's relation `M_S`. -/
def MS (F : FourSector Ω) (u v : Ω) : Prop :=
  F.pairClass u v = .sameEndpoint

/-- The paper's relation `D`. -/
def D (F : FourSector Ω) (u v : Ω) : Prop :=
  F.pairClass u v = .oppositeEndpoint

/-- The paper's relation `N_S`. -/
def NS (F : FourSector Ω) (u v : Ω) : Prop :=
  F.pairClass u v = .sameResidual

/-- The paper's relation `M_D`. -/
def MD (F : FourSector Ω) (u v : Ω) : Prop :=
  F.pairClass u v = .oppositeResidual

/-- The paper's relation `I = M_S ⊔ N_S ⊔ M_D`. -/
def I (F : FourSector Ω) (u v : Ω) : Prop :=
  F.MS u v ∨ F.NS u v ∨ F.MD u v

theorem deltaA_iff (F : FourSector Ω) (u v : Ω) :
    F.deltaA u v ↔ F.sector u = .a ∧ u = v := by
  cases hu : F.sector u <;>
    cases hv : F.sector v <;>
    by_cases huv : u = v <;>
    simp_all [deltaA, pairClass, sameSide, isLeftSector]

theorem deltaB_iff (F : FourSector Ω) (u v : Ω) :
    F.deltaB u v ↔ F.sector u = .b ∧ u = v := by
  cases hu : F.sector u <;>
    cases hv : F.sector v <;>
    by_cases huv : u = v <;>
    simp_all [deltaB, pairClass, sameSide, isLeftSector]

theorem MS_iff (F : FourSector Ω) (u v : Ω) :
    F.MS u v ↔
      F.isEndpoint u ∧ F.sameSide u v ∧ u ≠ v := by
  cases hu : F.sector u <;>
    cases hv : F.sector v <;>
    by_cases huv : u = v <;>
    simp_all [MS, pairClass, isEndpoint, sameSide, isLeftSector]

theorem D_iff (F : FourSector Ω) (u v : Ω) :
    F.D u v ↔ F.isEndpoint u ∧ ¬F.sameSide u v := by
  cases hu : F.sector u <;>
    cases hv : F.sector v <;>
    by_cases huv : u = v <;>
    simp_all [D, pairClass, isEndpoint, sameSide, isLeftSector]

theorem NS_iff (F : FourSector Ω) (u v : Ω) :
    F.NS u v ↔ F.isResidual u ∧ F.sameSide u v := by
  cases hu : F.sector u <;>
    cases hv : F.sector v <;>
    by_cases huv : u = v <;>
    simp_all [NS, pairClass, isResidual, sameSide, isLeftSector]

theorem MD_iff (F : FourSector Ω) (u v : Ω) :
    F.MD u v ↔ F.isResidual u ∧ ¬F.sameSide u v := by
  cases hu : F.sector u <;>
    cases hv : F.sector v <;>
    by_cases huv : u = v <;>
    simp_all [MD, pairClass, isResidual, sameSide, isLeftSector]

theorem I_iff (F : FourSector Ω) (u v : Ω) :
    F.I u v ↔
      (F.isEndpoint u ∧ F.sameSide u v ∧ u ≠ v) ∨
      F.isResidual u := by
  rw [I, MS_iff, NS_iff, MD_iff]
  by_cases hr : F.isResidual u
  · by_cases hs : F.sameSide u v <;> simp [hr, hs]
  · simp only [hr, false_and, false_or]

/-- Every ordered pair lies in exactly one of the six paper classes. -/
theorem exactly_one_pair_class (F : FourSector Ω) (u v : Ω) :
    ∃! R : PairClass, F.pairClass u v = R := by
  exact ⟨F.pairClass u v, rfl, fun R h => h.symm⟩

end FourSector

end QuartetV060
