import QuartetV060.CompletedSquares

/-!
# Occurrence-wise row settlement `(A.29c₀)`--`(A.29c₂)`

The column term is held fixed in this module.  The row coordinate is
partitioned into `I`, `D`, and the endpoint diagonal.  We prove the exact
boundary identity and then cancel that boundary only after summing a
fixed-point-free row-bridge involution.  The last theorem records the
adjacent-edge/endpoint-atom bijection as an actual equivalence of finite
index types, so multiplicity one is a theorem rather than prose.
-/

namespace QuartetV060

open scoped BigOperators

namespace OccurrenceSettlement

variable
    {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]

def retainedI
    (P : ResidualPartition Ω) (w X : Ω → ℚ) : ℚ :=
  ∑ z ∈ P.I, w z.1 * w z.2 * X z.1 ^ 2

def retainedD
    (P : ResidualPartition Ω) (w X Y : Ω → ℚ) : ℚ :=
  ∑ z ∈ P.D, w z.1 * w z.2 * (X z.1 + Y z.1) ^ 2

def neighboringN
    (P : ResidualPartition Ω) (w X Y : Ω → ℚ) : ℚ :=
  ∑ i ∈ P.endpoint,
    (w i * X i - P.oppositeWeight w i * Y i) ^ 2

def omittedQ
    (P : ResidualPartition Ω) (w Y : Ω → ℚ) : ℚ :=
  ∑ i ∈ P.endpoint,
    P.oppositeWeight w i *
      (w i + P.oppositeWeight w i) * Y i ^ 2

/-- The row-boundary polynomial in `(A.29c₀)`. -/
def boundary
    (P : ResidualPartition Ω) (w X Y : Ω → ℚ) : ℚ :=
  ∑ i ∈ P.endpoint,
    (w i + P.oppositeWeight w i) *
      (w i * X i ^ 2 - P.oppositeWeight w i * Y i ^ 2)

/-- The complement of the retained `I` pool is exactly the two endpoint
diagonal contributions. -/
theorem totalSquare_sub_retainedI
    (P : ResidualPartition Ω)
    (w X : Ω → ℚ) (Xsq : ℚ)
    (hsum : (∑ i, w i) = 1)
    (hXsq : ∀ i, X i ^ 2 = Xsq) :
    Xsq - retainedI P w X =
      ∑ i ∈ P.endpoint,
        (w i + P.oppositeWeight w i) * w i * X i ^ 2 := by
  have htotal :
      (∑ z ∈ P.allPairs, w z.1 * w z.2 * X z.1 ^ 2) = Xsq := by
    rw [P.sum_allPairs_first w (fun i => X i ^ 2)]
    have hfirst : (∑ i, w i * X i ^ 2) = Xsq := by
      calc
        (∑ i, w i * X i ^ 2) = ∑ i, w i * Xsq := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hXsq i]
        _ = (∑ i, w i) * Xsq := by rw [Finset.sum_mul]
        _ = Xsq := by rw [hsum]; ring
    rw [hfirst, hsum]
    ring
  have hpart := P.sum_partition
    (fun z => w z.1 * w z.2 * X z.1 ^ 2)
  rw [P.sum_D_first w (fun i => X i ^ 2)] at hpart
  rw [P.sum_deltaE
    (fun z => w z.1 * w z.2 * X z.1 ^ 2)] at hpart
  simp only at hpart
  have hdiag :
      (∑ i ∈ P.endpoint, w i * w i * X i ^ 2) =
        ∑ i ∈ P.endpoint, w i ^ 2 * X i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag, htotal] at hpart
  unfold retainedI
  calc
    Xsq - ∑ z ∈ P.I, w z.1 * w z.2 * X z.1 ^ 2 =
        (∑ i ∈ P.endpoint,
          w i * P.oppositeWeight w i * X i ^ 2) +
        ∑ i ∈ P.endpoint, w i ^ 2 * X i ^ 2 := by
          linarith
    _ = ∑ i ∈ P.endpoint,
        (w i + P.oppositeWeight w i) * w i * X i ^ 2 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- The displayed row boundary is `(E-I)-Q`, with no omitted coefficient. -/
theorem boundary_eq_totalSquare_sub_I_sub_Q
    (P : ResidualPartition Ω)
    (w X Y : Ω → ℚ) (Xsq : ℚ)
    (hsum : (∑ i, w i) = 1)
    (hXsq : ∀ i, X i ^ 2 = Xsq) :
    boundary P w X Y =
      Xsq - retainedI P w X - omittedQ P w Y := by
  rw [totalSquare_sub_retainedI P w X Xsq hsum hXsq]
  unfold boundary omittedQ
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact occurrence-wise settlement `(A.29c₀)`:
`2E-N = 2I+D+B_boundary`. -/
theorem twoE_sub_N
    (P : ResidualPartition Ω)
    (w X Y : Ω → ℚ) (Xsq : ℚ)
    (hsum : (∑ i, w i) = 1)
    (hXsq : ∀ i, X i ^ 2 = Xsq) :
    2 * Xsq - neighboringN P w X Y =
      2 * retainedI P w X + retainedD P w X Y +
        boundary P w X Y := by
  have hres := P.exact_residual_identity w X Y Xsq hsum hXsq
  have hboundary :=
    boundary_eq_totalSquare_sub_I_sub_Q P w X Y Xsq hsum hXsq
  unfold boundary retainedI omittedQ at hboundary
  unfold neighboringN retainedI retainedD boundary
  linarith

section BridgeBoundary

variable
    {X Chart : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype Chart] [DecidableEq Chart]
    (S : BridgeSystem X Chart)

/-- One endpoint boundary occurrence on every ordered row bridge. -/
structure BoundaryOrbitData where
  wK : Chart → ℚ
  wL : Chart → ℚ
  xK : Chart → ℚ
  xL : Chart → ℚ
  wK_rho : ∀ α, wK (S.rho α) = wL α
  wL_rho : ∀ α, wL (S.rho α) = wK α
  xK_sq_rho : ∀ α, xK (S.rho α) ^ 2 = xL α ^ 2
  xL_sq_rho : ∀ α, xL (S.rho α) ^ 2 = xK α ^ 2

namespace BoundaryOrbitData

variable (B : BoundaryOrbitData S)

def contribution (α : Chart) : ℚ :=
  (B.wK α + B.wL α) *
    (B.wK α * B.xK α ^ 2 - B.wL α * B.xL α ^ 2)

/-- Reversing `(K,H,L)` to `(L,H,K)` negates one boundary occurrence. -/
theorem contribution_rho (α : Chart) :
    contribution S B (S.rho α) = -contribution S B α := by
  unfold contribution
  rw [BoundaryOrbitData.wK_rho B, BoundaryOrbitData.wL_rho B,
    BoundaryOrbitData.xK_sq_rho B, BoundaryOrbitData.xL_sq_rho B]
  ring

/-- The row boundary cancels only over the complete ordered bridge range,
which is `(A.29c₁)`. -/
theorem sum_contribution_eq_zero :
    (∑ α, contribution S B α) = 0 := by
  exact BridgeSystem.sum_eq_zero_of_antiInvariant S
    (contribution S B) (contribution_rho S B)

end BoundaryOrbitData

end BridgeBoundary

section Crosswalk

variable
    {H K : Type*}
    [Fintype H] [Fintype K]

/-- The formal version of the bijection `h ↦ k(f,h)`: every corrected
column occurrence contributes to exactly one endpoint atom and every endpoint
atom is reached exactly once. -/
theorem sum_adjacent_eq_sum_endpoint
    (endpointOf : H ≃ K) (F : K → ℚ) :
    (∑ h, F (endpointOf h)) = ∑ k, F k := by
  exact endpointOf.sum_comp F

/-- The same multiplicity-one statement for a family carrying additional
row data. -/
theorem sum_adjacent_row_eq_sum_endpoint
    {R : Type*} [Fintype R]
    (endpointOf : H ≃ K) (F : R → K → ℚ) :
    (∑ i, ∑ h, F i (endpointOf h)) =
      ∑ i, ∑ k, F i k := by
  apply Fintype.sum_congr
  intro i
  exact endpointOf.sum_comp (F i)

end Crosswalk

end OccurrenceSettlement

end QuartetV060
