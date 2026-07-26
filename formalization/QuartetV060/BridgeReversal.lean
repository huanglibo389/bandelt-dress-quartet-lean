import QuartetV060.LocalTable

/-!
# Ordered bridge charts and reversal

This module isolates the global symmetry used in Appendix A.  A bridge chart
has three ordered blocks `(K,H,L)`.  Reversal exchanges the outer blocks and
leaves the middle block fixed.  Crucially, all cancellation and coefficient
transport below are statements about the whole finite family of charts; no
equality of complete fixed-chart subtotals is asserted.
-/

namespace QuartetV060

open scoped BigOperators

/-- The ordered three-block decomposition `(K,H,L)` attached to a bridge
chart.  Pairwise disjointness and exhaustiveness are part of the data. -/
@[ext]
structure ThreeBlock (X : Type*) [Fintype X] [DecidableEq X] where
  K : Finset X
  H : Finset X
  L : Finset X
  disjoint_KH : Disjoint K H
  disjoint_KL : Disjoint K L
  disjoint_HL : Disjoint H L
  cover : K ∪ H ∪ L = Finset.univ

namespace ThreeBlock

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Bridge reversal sends `(K,H,L)` to `(L,H,K)`. -/
def reverse (P : ThreeBlock X) : ThreeBlock X where
  K := P.L
  H := P.H
  L := P.K
  disjoint_KH := P.disjoint_HL.symm
  disjoint_KL := P.disjoint_KL.symm
  disjoint_HL := P.disjoint_KH.symm
  cover := by
    calc
      P.L ∪ P.H ∪ P.K = P.K ∪ P.H ∪ P.L := by ac_rfl
      _ = Finset.univ := P.cover

@[simp] theorem reverse_K (P : ThreeBlock X) : P.reverse.K = P.L := rfl
@[simp] theorem reverse_H (P : ThreeBlock X) : P.reverse.H = P.H := rfl
@[simp] theorem reverse_L (P : ThreeBlock X) : P.reverse.L = P.K := rfl

@[simp] theorem reverse_reverse (P : ThreeBlock X) :
    P.reverse.reverse = P := by
  ext <;> rfl

end ThreeBlock

/-- A finite family of ordered bridge charts equipped with the paper's
fixed-point-free reversal involution. -/
structure BridgeSystem
    (X : Type*) (Chart : Type*)
    [Fintype X] [DecidableEq X] where
  blocks : Chart → ThreeBlock X
  rho : Chart → Chart
  rho_involutive : Function.Involutive rho
  rho_ne : ∀ α, rho α ≠ α
  blocks_rho : ∀ α, blocks (rho α) = (blocks α).reverse

namespace BridgeSystem

variable
    {X Chart : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Chart] [DecidableEq Chart]
    (S : BridgeSystem X Chart)

/-- Reversal as an actual equivalence of the finite chart type. -/
def rhoEquiv : Chart ≃ Chart where
  toFun := S.rho
  invFun := S.rho
  left_inv := S.rho_involutive
  right_inv := S.rho_involutive

@[simp] theorem rhoEquiv_apply (α : Chart) :
    S.rhoEquiv α = S.rho α := rfl

@[simp] theorem rho_rho (α : Chart) :
    S.rho (S.rho α) = α :=
  S.rho_involutive α

@[simp] theorem blocks_rho_K (α : Chart) :
    (S.blocks (S.rho α)).K = (S.blocks α).L := by
  rw [S.blocks_rho]
  rfl

@[simp] theorem blocks_rho_H (α : Chart) :
    (S.blocks (S.rho α)).H = (S.blocks α).H := by
  rw [S.blocks_rho]
  rfl

@[simp] theorem blocks_rho_L (α : Chart) :
    (S.blocks (S.rho α)).L = (S.blocks α).K := by
  rw [S.blocks_rho]
  rfl

/-- The two charts in one bridge-reversal orbit. -/
def orbit (α : Chart) : Finset Chart :=
  {α, S.rho α}

@[simp] theorem card_orbit (α : Chart) :
    (S.orbit α).card = 2 := by
  exact Finset.card_pair (S.rho_ne α).symm

/-- Reindexing a sum by bridge reversal does not change its value. -/
theorem sum_comp_rho (F : Chart → ℚ) :
    (∑ α, F (S.rho α)) = ∑ α, F α := by
  exact S.rhoEquiv.sum_comp F

/-- A coefficient attached to a source chart may be transported to the
reversed target chart and then summed globally. -/
theorem sum_transport
    (source target : Chart → ℚ)
    (h : ∀ α, source α = target (S.rho α)) :
    (∑ α, source α) = ∑ α, target α := by
  calc
    (∑ α, source α) = ∑ α, target (S.rho α) := by
      apply Finset.sum_congr rfl
      intro α _
      exact h α
    _ = ∑ α, target α := S.sum_comp_rho target

/-- An anti-invariant chart contribution cancels only after summing over the
whole bridge orbit ledger. -/
theorem sum_eq_zero_of_antiInvariant
    (F : Chart → ℚ)
    (h : ∀ α, F (S.rho α) = -F α) :
    (∑ α, F α) = 0 := by
  have hneg : (∑ α, F (S.rho α)) = -(∑ α, F α) := by
    calc
      (∑ α, F (S.rho α)) = ∑ α, -F α := by
        apply Finset.sum_congr rfl
        intro α _
        exact h α
      _ = -(∑ α, F α) := by simp
  have hinv : (∑ α, F (S.rho α)) = ∑ α, F α :=
    S.sum_comp_rho F
  linarith

end BridgeSystem

/-- A genuine occurrence-level transport from omitted source faces to target
faces.  The equivalence records the bijection; `chart_transport` records that
the target occurrence belongs to the reversed chart. -/
structure BridgeOccurrenceTransport
    {X Chart : Type*}
    [Fintype X] [DecidableEq X]
    (S : BridgeSystem X Chart)
    (SourceOcc TargetOcc : Type*) where
  sourceChart : SourceOcc → Chart
  targetChart : TargetOcc → Chart
  equiv : SourceOcc ≃ TargetOcc
  chart_transport :
    ∀ o, targetChart (equiv o) = S.rho (sourceChart o)

namespace BridgeOccurrenceTransport

variable
    {X Chart SourceOcc TargetOcc : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Chart] [DecidableEq Chart]
    [Fintype SourceOcc] [Fintype TargetOcc]
    {S : BridgeSystem X Chart}
    (T : BridgeOccurrenceTransport S SourceOcc TargetOcc)

/-- The inverse transport also reverses the chart label. -/
theorem sourceChart_symm (t : TargetOcc) :
    T.sourceChart (T.equiv.symm t) = S.rho (T.targetChart t) := by
  have h := T.chart_transport (T.equiv.symm t)
  have hr := congrArg S.rho h
  simpa using hr.symm

/-- A coefficient-preserving occurrence bijection gives equality of the two
global coefficient ledgers. -/
theorem coefficient_sum_eq
    (sourceCoeff : SourceOcc → ℚ)
    (targetCoeff : TargetOcc → ℚ)
    (hcoeff : ∀ o, sourceCoeff o = targetCoeff (T.equiv o)) :
    (∑ o, sourceCoeff o) = ∑ t, targetCoeff t := by
  exact Fintype.sum_equiv T.equiv sourceCoeff targetCoeff hcoeff

end BridgeOccurrenceTransport

end QuartetV060
