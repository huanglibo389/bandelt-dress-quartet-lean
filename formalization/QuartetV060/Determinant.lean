import QuartetV060.Basic

/-!
# Split determinants and adjacent side-pair contrasts

This file formalizes the algebra in the paper's sections "One pair of splits",
"Indicator form of the split determinant", and the first calculation in
"Adjacent-pair correction operator".
-/

namespace QuartetV060

/-- A normalized `2 x 2` intersection table. -/
@[ext] structure Table2 (K : Type*) where
  a : K
  b : K
  c : K
  d : K

namespace Table2

variable {K : Type*}

/-- The unsquared determinant `ad - bc`. -/
def det [Mul K] [Sub K] (t : Table2 K) : K :=
  t.a * t.d - t.b * t.c

/-- The determinant square used in the definition of `f₁`. -/
def detSquare [CommRing K] (t : Table2 K) : K :=
  det t ^ 2

/-- Reverse the two row sides of the table. -/
def reverseRows (t : Table2 K) : Table2 K :=
  ⟨t.c, t.d, t.a, t.b⟩

/-- Reverse the two column sides of the table. -/
def reverseCols (t : Table2 K) : Table2 K :=
  ⟨t.b, t.a, t.d, t.c⟩

/-- Exchange the row and column coordinates. -/
def transpose (t : Table2 K) : Table2 K :=
  ⟨t.a, t.c, t.b, t.d⟩

@[simp] theorem reverseRows_reverseRows (t : Table2 K) :
    reverseRows (reverseRows t) = t := by
  cases t
  rfl

@[simp] theorem reverseCols_reverseCols (t : Table2 K) :
    reverseCols (reverseCols t) = t := by
  cases t
  rfl

@[simp] theorem transpose_transpose (t : Table2 K) :
    transpose (transpose t) = t := by
  cases t
  rfl

theorem det_reverseRows [CommRing K] (t : Table2 K) :
    det (reverseRows t) = -det t := by
  simp [det, reverseRows]
  ring

theorem det_reverseCols [CommRing K] (t : Table2 K) :
    det (reverseCols t) = -det t := by
  simp [det, reverseCols]

@[simp] theorem det_transpose [CommRing K] (t : Table2 K) :
    det (transpose t) = det t := by
  simp [det, transpose]
  ring

@[simp] theorem detSquare_reverseRows [CommRing K] (t : Table2 K) :
    detSquare (reverseRows t) = detSquare t := by
  rw [detSquare, det_reverseRows, detSquare]
  ring

@[simp] theorem detSquare_reverseCols [CommRing K] (t : Table2 K) :
    detSquare (reverseCols t) = detSquare t := by
  rw [detSquare, det_reverseCols, detSquare]
  ring

@[simp] theorem detSquare_transpose [CommRing K] (t : Table2 K) :
    detSquare (transpose t) = detSquare t := by
  simp [detSquare]

/-- The centered-indicator covariance equals the determinant when the four
table entries have total mass one. -/
theorem centeredCovariance_eq_det [CommRing K]
    (t : Table2 K) (htotal : t.a + t.b + t.c + t.d = 1) :
    t.a - (t.a + t.b) * (t.a + t.c) = det t := by
  have hd : 1 - t.a - t.b - t.c = t.d := by
    rw [← htotal]
    ring
  calc
    t.a - (t.a + t.b) * (t.a + t.c)
        = t.a * (1 - t.a - t.b - t.c) - t.b * t.c := by ring
    _ = t.a * t.d - t.b * t.c := by rw [hd]
    _ = det t := rfl

theorem detSquare_nonneg (t : Table2 ℚ) :
    0 ≤ detSquare t := by
  unfold detSquare
  positivity

end Table2

/-- The five scalar data entering one adjacent side-pair comparison.

`leftIntersection` and `rightIntersection` are the masses called `A` and `C`
in the paper; `leftMass` and `rightMass` are `c_K` and `c_L`; `mean` is the
mass of the chosen side of the comparison split.
-/
structure SidePairData (K : Type*) where
  leftMass : K
  rightMass : K
  leftIntersection : K
  rightIntersection : K
  mean : K

namespace SidePairData

variable {K : Type*} [CommRing K]

def centeredLeft (s : SidePairData K) : K :=
  s.leftIntersection - s.leftMass * s.mean

def centeredRight (s : SidePairData K) : K :=
  s.rightIntersection - s.rightMass * s.mean

/-- The determinant before squaring:
`c_L A - c_K C` in the notation of the paper. -/
def rawContrast (s : SidePairData K) : K :=
  s.rightMass * s.leftIntersection -
    s.leftMass * s.rightIntersection

/-- The neighboring centered contrast:
`c_K x_{Z,L} - c_L x_{Z,K}` in the notation of the paper. -/
def neighboringContrast (s : SidePairData K) : K :=
  s.leftMass * centeredRight s -
    s.rightMass * centeredLeft s

/-- Centering changes the sign of the side-pair determinant, and therefore
does not change its square. -/
theorem rawContrast_eq_neg_neighboringContrast (s : SidePairData K) :
    rawContrast s = -neighboringContrast s := by
  simp [rawContrast, neighboringContrast, centeredLeft, centeredRight]
  ring

theorem rawContrast_sq_eq_neighboringContrast_sq (s : SidePairData K) :
    rawContrast s ^ 2 = neighboringContrast s ^ 2 := by
  rw [rawContrast_eq_neg_neighboringContrast]
  ring

end SidePairData

end QuartetV060
