import QuartetV060.OccurrenceSettlement

/-!
# Global endpoint-face and completed-package ledgers `(A.29e)`--`(A.29f)`

The type `Occ` contains the complete chart/row/endpoint indexing range.
Reversal is an equivalence of that whole range.  The proofs below therefore
cannot be misread as fixed-chart coefficient identities.
-/

namespace QuartetV060

open scoped BigOperators

namespace PackageLedger

variable
    {Occ : Type*}
    [Fintype Occ]

/-- Equality of the negative endpoint second-face ledger and the positive
endpoint first-face ledger after the full reversal reindexing. -/
theorem sum_endpoint_second_eq_first
    (rho : Occ ≃ Occ)
    (d e Z W : Occ → ℝ)
    (hd : ∀ o, d (rho o) = e o)
    (hZ : ∀ o, Z (rho o) ^ 2 = W o ^ 2) :
    (∑ o, e o * W o ^ 2) =
      ∑ o, d o * Z o ^ 2 := by
  calc
    (∑ o, e o * W o ^ 2) =
        ∑ o, d (rho o) * Z (rho o) ^ 2 := by
          apply Fintype.sum_congr
          intro o
          rw [hd o, hZ o]
    _ = ∑ o, d o * Z o ^ 2 := rho.sum_comp
      (fun o => d o * Z o ^ 2)

/-- The signed ordinary endpoint faces cancel globally, which is `(A.29e)`.
No fixed-point-free hypothesis is needed for the sum identity itself; a
fixed point would simply force its own signed contribution to vanish under
the stated transport equations. -/
theorem sum_endpoint_signed_eq_zero
    (rho : Occ ≃ Occ)
    (d e Z W : Occ → ℝ)
    (hd : ∀ o, d (rho o) = e o)
    (hZ : ∀ o, Z (rho o) ^ 2 = W o ^ 2) :
    (∑ o, (d o * Z o ^ 2 - e o * W o ^ 2)) = 0 := by
  rw [Finset.sum_sub_distrib]
  rw [sum_endpoint_second_eq_first rho d e Z W hd hZ]
  ring

/-- Reversal transports a completed package's second-square coefficient to
the first-square coefficient of the reversed package. -/
theorem sum_package_second_eq_first
    (rho : Occ ≃ Occ)
    (p q Z W : Occ → ℝ)
    (hq : ∀ o, q o = p (rho o))
    (hW : ∀ o, W o ^ 2 = Z (rho o) ^ 2) :
    (∑ o, q o * W o ^ 2) =
      ∑ o, p o * Z o ^ 2 := by
  calc
    (∑ o, q o * W o ^ 2) =
        ∑ o, p (rho o) * Z (rho o) ^ 2 := by
          apply Fintype.sum_congr
          intro o
          rw [hq o, hW o]
    _ = ∑ o, p o * Z o ^ 2 := rho.sum_comp
      (fun o => p o * Z o ^ 2)

/-- One occurrence of the package extraction before summing. -/
theorem pointwise_package_extraction
    (A p q m P Z W : ℝ)
    (hP : P = p * Z ^ 2 + m * Z * W + q * W ^ 2) :
    2 * A * Z ^ 2 + m * Z * W =
      P + (2 * A - p) * Z ^ 2 - q * W ^ 2 := by
  rw [hP]
  ring

/-- The full `(A.29f)` ledger.  The only cross-occurrence step is the
explicitly assumed coefficient-preserving reversal `q W² ↔ p Z²`. -/
theorem global_package_extraction
    (rho : Occ ≃ Occ)
    (A p q m package Z W : Occ → ℝ)
    (hpackage :
      ∀ o, package o =
        p o * Z o ^ 2 + m o * Z o * W o + q o * W o ^ 2)
    (hq : ∀ o, q o = p (rho o))
    (hW : ∀ o, W o ^ 2 = Z (rho o) ^ 2) :
    (∑ o, (2 * A o * Z o ^ 2 + m o * Z o * W o)) =
      ∑ o, (package o + 2 * (A o - p o) * Z o ^ 2) := by
  have hpoint :
      (∑ o, (2 * A o * Z o ^ 2 + m o * Z o * W o)) =
        ∑ o,
          (package o + (2 * A o - p o) * Z o ^ 2 -
            q o * W o ^ 2) := by
    apply Fintype.sum_congr
    intro o
    exact pointwise_package_extraction
      (A o) (p o) (q o) (m o) (package o) (Z o) (W o)
      (hpackage o)
  calc
    (∑ o, (2 * A o * Z o ^ 2 + m o * Z o * W o)) =
        ∑ o,
          (package o + (2 * A o - p o) * Z o ^ 2 -
            q o * W o ^ 2) := hpoint
    _ =
        (∑ o, (package o + (2 * A o - p o) * Z o ^ 2)) -
          ∑ o, (q o * W o ^ 2) := by
            rw [Finset.sum_sub_distrib]
    _ =
        (∑ o, (package o + (2 * A o - p o) * Z o ^ 2)) -
          ∑ o, (p o * Z o ^ 2) := by
            rw [sum_package_second_eq_first rho p q Z W hq hW]
    _ = ∑ o, (package o + 2 * (A o - p o) * Z o ^ 2) := by
          rw [← Finset.sum_sub_distrib]
          apply Fintype.sum_congr
          intro o
          ring

end PackageLedger

end QuartetV060
