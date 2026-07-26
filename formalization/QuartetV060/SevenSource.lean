import QuartetV060.RetainedSquares

/-!
# From four determinant levels to the seven-source numerator

These are the exact substitutions surrounding `(A.29a)` and `(A.29b)`.
They explain algebraically why the calligraphic residual quantities may
disappear after the two occurrence polynomials `2U-R` and `2C-B` have been
formed.
-/

namespace QuartetV060

/-- The three residual identities obtained from `(A.15a)`, its formal
row-column transpose, and `(A.15b)`. -/
structure SevenSourceData where
  U : ℚ
  R : ℚ
  C : ℚ
  B : ℚ
  R1 : ℚ
  Q1 : ℚ
  R1transpose : ℚ
  Q1transpose : ℚ
  R2 : ℚ
  Q2 : ℚ
  rowResidual : R = U - R1 + Q1
  colResidual : C = U - R1transpose + Q1transpose
  neighborResidual : B = C - R2 + Q2

namespace SevenSourceData

def fourLevelNumerator (S : SevenSourceData) : ℚ :=
  4 * S.U - 2 * S.R - 2 * S.C + S.B

def sevenSourceNumerator (S : SevenSourceData) : ℚ :=
  S.U + 2 * S.R1 + S.R1transpose - S.R2
    - 2 * S.Q1 - S.Q1transpose + S.Q2

def firstOccurrencePolynomial (S : SevenSourceData) : ℚ :=
  S.U + S.R1 - S.Q1

def secondOccurrencePolynomial (S : SevenSourceData) : ℚ :=
  S.U - S.R1transpose + S.Q1transpose + S.R2 - S.Q2

/-- Exact seven-source identity `(A.29a)`. -/
theorem fourLevel_eq_sevenSource (S : SevenSourceData) :
    S.fourLevelNumerator = S.sevenSourceNumerator := by
  unfold fourLevelNumerator sevenSourceNumerator
  rw [S.rowResidual, S.neighborResidual, S.colResidual]
  ring

/-- Direct regrouping `(A.29b)` into two occurrence polynomials. -/
theorem sevenSource_eq_occurrence_regrouping (S : SevenSourceData) :
    S.sevenSourceNumerator =
      2 * S.firstOccurrencePolynomial -
        S.secondOccurrencePolynomial := by
  unfold sevenSourceNumerator firstOccurrencePolynomial
    secondOccurrencePolynomial
  ring

theorem firstOccurrence_eq_twoU_sub_R (S : SevenSourceData) :
    S.firstOccurrencePolynomial = 2 * S.U - S.R := by
  unfold firstOccurrencePolynomial
  rw [S.rowResidual]
  ring

theorem secondOccurrence_eq_twoC_sub_B (S : SevenSourceData) :
    S.secondOccurrencePolynomial = 2 * S.C - S.B := by
  unfold secondOccurrencePolynomial
  rw [S.neighborResidual, S.colResidual]
  ring

/-- The complete four-level numerator in the occurrence form used after
`(A.29b)`. -/
theorem fourLevel_eq_two_occurrences (S : SevenSourceData) :
    S.fourLevelNumerator =
      2 * (2 * S.U - S.R) - (2 * S.C - S.B) := by
  rw [S.fourLevel_eq_sevenSource]
  rw [S.sevenSource_eq_occurrence_regrouping]
  rw [S.firstOccurrence_eq_twoU_sub_R]
  rw [S.secondOccurrence_eq_twoC_sub_B]

end SevenSourceData

end QuartetV060
