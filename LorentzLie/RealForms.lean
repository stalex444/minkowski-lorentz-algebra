module
public import Mathlib
public import LorentzLie.Defs

@[expose] public section

/-!
# Real forms of the `η`-skew `4 × 4` matrices

For a diagonal `η : Fin 4 → ℝ` with entries `±1`, the Lie algebra `etaSkew η` is identified
explicitly in each of the three cases:

* `etaSkewEquivSl2C` — product of the entries `-1`: `etaSkew η ≃ₗ⁅ℝ⁆ sl(2, ℂ)` (as a real Lie
  algebra), with `etaSkewEquivSl2C_gen` on generators and `etaSkewEquivSl2C_hodge` for the Hodge
  operator;
* `etaSkewEquivSo3Prod` — all entries equal: `etaSkew η ≃ₗ⁅ℝ⁆ so(3) × so(3)`, with
  `etaSkewEquivSo3Prod_apply`;
* `etaSkewEquivSl2RProd` — sum of the entries `0`: `etaSkew η ≃ₗ⁅ℝ⁆ sl(2, ℝ) × sl(2, ℝ)`, with
  `etaSkewEquivSl2RProd_gen` on generators.

Method. An `η`-skew matrix is `skewMat η c` for six real coordinates `c` (`eq_skewMat`); each
equivalence is an explicit linear map in these coordinates with an explicit inverse, and the
bracket identity is checked entry by entry after splitting on the signs of `η`. The helper
declarations are in the namespace `LorentzLie.RealForms`.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

namespace LorentzLie

open Matrix

namespace RealForms

/-! ### Coordinates on the `η`-skew matrices -/

section Entries

/-- An entry `±1` has square `1`. -/
theorem eta_mul_self {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (i : Fin 4) :
    η i * η i = 1 := by
  rcases hη i with h | h <;> rw [h] <;> norm_num

/-- Below the diagonal: `X j i = -(η i * η j) * X i j` for an `η`-skew `X`, entries of `η` being
`±1`. -/
theorem etaSkew_lower {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X : etaSkew η)
    (i j : Fin 4) : X.1 j i = -(η i * η j) * X.1 i j := by
  have h := (mem_etaSkew_iff η X.1).mp X.2 i j
  have hs := eta_mul_self hη j
  linear_combination (η j) * h - (X.1 j i) * hs

/-- The diagonal of an `η`-skew matrix vanishes (entries of `η` being `±1`). -/
theorem etaSkew_diag {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X : etaSkew η)
    (i : Fin 4) : X.1 i i = 0 := by
  have h := (mem_etaSkew_iff η X.1).mp X.2 i i
  have hs := eta_mul_self hη i
  linear_combination (η i / 2) * h - (X.1 i i) * hs

/-- The `η`-skew matrix with coordinates `c i j` (`i < j`): `∑ c i j • gen η i j`, written out. -/
def skewMat (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, η 1 * c01, η 2 * c02, η 3 * c03;
     -(η 0 * c01), 0, η 2 * c12, η 3 * c13;
     -(η 0 * c02), -(η 1 * c12), 0, η 3 * c23;
     -(η 0 * c03), -(η 1 * c13), -(η 2 * c23), 0]

/-- Entry `(0, 0)` of `skewMat η c`. -/
theorem skewMat_00 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 0 0 = 0 := rfl

/-- Entry `(0, 1)` of `skewMat η c`. -/
theorem skewMat_01 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 0 1 = η 1 * c01 := rfl

/-- Entry `(0, 2)` of `skewMat η c`. -/
theorem skewMat_02 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 0 2 = η 2 * c02 := rfl

/-- Entry `(0, 3)` of `skewMat η c`. -/
theorem skewMat_03 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 0 3 = η 3 * c03 := rfl

/-- Entry `(1, 0)` of `skewMat η c`. -/
theorem skewMat_10 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 1 0 = -(η 0 * c01) := rfl

/-- Entry `(1, 1)` of `skewMat η c`. -/
theorem skewMat_11 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 1 1 = 0 := rfl

/-- Entry `(1, 2)` of `skewMat η c`. -/
theorem skewMat_12 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 1 2 = η 2 * c12 := rfl

/-- Entry `(1, 3)` of `skewMat η c`. -/
theorem skewMat_13 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 1 3 = η 3 * c13 := rfl

/-- Entry `(2, 0)` of `skewMat η c`. -/
theorem skewMat_20 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 2 0 = -(η 0 * c02) := rfl

/-- Entry `(2, 1)` of `skewMat η c`. -/
theorem skewMat_21 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 2 1 = -(η 1 * c12) := rfl

/-- Entry `(2, 2)` of `skewMat η c`. -/
theorem skewMat_22 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 2 2 = 0 := rfl

/-- Entry `(2, 3)` of `skewMat η c`. -/
theorem skewMat_23 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 2 3 = η 3 * c23 := rfl

/-- Entry `(3, 1)` of `skewMat η c`. -/
theorem skewMat_31 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 3 1 = -(η 1 * c13) := rfl

/-- Entry `(3, 2)` of `skewMat η c`. -/
theorem skewMat_32 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 3 2 = -(η 2 * c23) := rfl

/-- Entry `(3, 3)` of `skewMat η c`. -/
theorem skewMat_33 (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 3 3 = 0 := rfl

/-- `skewMat η c` is `η`-skew, for every `η`. -/
theorem skewMat_mem (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    skewMat η c01 c02 c03 c12 c13 c23 ∈ etaSkew η := by
  rw [mem_etaSkew_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [skewMat] <;> ring

/-- Every `η`-skew matrix is `skewMat η c` with `c i j = η j * X i j` (entries of `η` being
`±1`). -/
theorem eq_skewMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X : etaSkew η) :
    X.1 = skewMat η (η 1 * X.1 0 1) (η 2 * X.1 0 2) (η 3 * X.1 0 3) (η 2 * X.1 1 2)
      (η 3 * X.1 1 3) (η 3 * X.1 2 3) := by
  have hl := etaSkew_lower hη X
  have hd := etaSkew_diag hη X
  have hs := eta_mul_self hη
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMat]
  · exact hd 0
  · linear_combination (-(X.1 0 1)) * hs 1
  · linear_combination (-(X.1 0 2)) * hs 2
  · linear_combination (-(X.1 0 3)) * hs 3
  · linear_combination hl 0 1
  · exact hd 1
  · linear_combination (-(X.1 1 2)) * hs 2
  · linear_combination (-(X.1 1 3)) * hs 3
  · linear_combination hl 0 2
  · linear_combination hl 1 2
  · exact hd 2
  · linear_combination (-(X.1 2 3)) * hs 3
  · linear_combination hl 0 3
  · linear_combination hl 1 3
  · linear_combination hl 2 3
  · exact hd 3

end Entries

/-! ### The case of product `-1`: `sl(2, ℂ)` -/

section Pauli

/-- The trace-zero complex `2 × 2` matrix `∑ₖ (uₖ + i vₖ) • eₖ`, where `eₖ = -½ quat k`
(`k = 1, 2, 3`) satisfy `⁅e₁, e₂⁆ = e₃` and cyclic. -/
noncomputable def pauliR (u1 v1 u2 v2 u3 v3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨v3 / 2, -(u3 / 2)⟩, ⟨(v1 - u2) / 2, -((u1 + v2) / 2)⟩;
     ⟨(v1 + u2) / 2, (v2 - u1) / 2⟩, ⟨-(v3 / 2), u3 / 2⟩]

/-- `pauliR` has trace zero. -/
theorem pauliR_trace (u1 v1 u2 v2 u3 v3 : ℝ) : (pauliR u1 v1 u2 v2 u3 v3).trace = 0 := by
  apply Complex.ext <;> simp [pauliR, Matrix.trace, Fin.sum_univ_two]

/-- The commutator of two `pauliR` matrices is the `pauliR` matrix of the complex cross product. -/
theorem pauliR_bracket (u1 v1 u2 v2 u3 v3 a1 b1 a2 b2 a3 b3 : ℝ) :
    pauliR u1 v1 u2 v2 u3 v3 * pauliR a1 b1 a2 b2 a3 b3 -
        pauliR a1 b1 a2 b2 a3 b3 * pauliR u1 v1 u2 v2 u3 v3 =
      pauliR (u2 * a3 - v2 * b3 - u3 * a2 + v3 * b2) (u2 * b3 + v2 * a3 - u3 * b2 - v3 * a2)
        (u3 * a1 - v3 * b1 - u1 * a3 + v1 * b3) (u3 * b1 + v3 * a1 - u1 * b3 - v1 * a3)
        (u1 * a2 - v1 * b2 - u2 * a1 + v2 * b1) (u1 * b2 + v1 * a2 - u2 * b1 - v2 * a1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (apply Complex.ext <;> simp [pauliR] <;> ring)

/-- `pauliR` is additive. -/
theorem pauliR_add (u1 v1 u2 v2 u3 v3 a1 b1 a2 b2 a3 b3 : ℝ) :
    pauliR u1 v1 u2 v2 u3 v3 + pauliR a1 b1 a2 b2 a3 b3 =
      pauliR (u1 + a1) (v1 + b1) (u2 + a2) (v2 + b2) (u3 + a3) (v3 + b3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (apply Complex.ext <;> simp [pauliR] <;> ring)

/-- `pauliR` commutes with multiplication by a real number. -/
theorem pauliR_smul (r u1 v1 u2 v2 u3 v3 : ℝ) :
    (r : ℂ) • pauliR u1 v1 u2 v2 u3 v3 =
      pauliR (r * u1) (r * v1) (r * u2) (r * v2) (r * u3) (r * v3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (apply Complex.ext <;> simp [pauliR] <;> ring)

/-- Every trace-zero complex `2 × 2` matrix is a `pauliR` matrix. -/
theorem eq_pauliR (m : Matrix (Fin 2) (Fin 2) ℂ) (hm : m.trace = 0) :
    m = pauliR (-((m 0 1).im + (m 1 0).im)) ((m 0 1).re + (m 1 0).re)
      ((m 1 0).re - (m 0 1).re) ((m 1 0).im - (m 0 1).im)
      (-(2 * (m 0 0).im)) (2 * (m 0 0).re) := by
  have h1 : m 0 0 + m 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using hm
  have hre : (m 1 1).re = -(m 0 0).re := by
    have := congrArg Complex.re h1; simp at this; linarith
  have him : (m 1 1).im = -(m 0 0).im := by
    have := congrArg Complex.im h1; simp at this; linarith
  ext i j
  fin_cases i <;> fin_cases j <;> (apply Complex.ext <;> simp [pauliR, hre, him] <;> ring)

end Pauli

section Spin

/-- Real part of `lam (η i) * lam (η j)`. -/
noncomputable def lamRe (η : Fin 4 → ℝ) (i j : Fin 4) : ℝ := (η i + η j) / 2

/-- Imaginary part of `lam (η i) * lam (η j)`. -/
noncomputable def lamIm (η : Fin 4 → ℝ) (i j : Fin 4) : ℝ := (1 - η i * η j) / 2

/-- `lam (η i) * lam (η j)` in real and imaginary parts. -/
theorem lam_mul_lam (η : Fin 4 → ℝ) (i j : Fin 4) :
    lam (η i) * lam (η j) = ⟨lamRe η i j, lamIm η i j⟩ := by
  apply Complex.ext <;> simp [lam, lamRe, lamIm] <;> ring

/-- The image of `skewMat η c` in `sl(2, ℂ)`: `∑ c i j • spinPlus η i j` over `i < j`, written
as a `pauliR` matrix. -/
noncomputable def spinCoords (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  pauliR (c01 * lamRe η 0 1 - c23 * lamRe η 2 3) (c01 * lamIm η 0 1 - c23 * lamIm η 2 3)
    (c02 * lamRe η 0 2 + c13 * lamRe η 1 3) (c02 * lamIm η 0 2 + c13 * lamIm η 1 3)
    (c03 * lamRe η 0 3 - c12 * lamRe η 1 2) (c03 * lamIm η 0 3 - c12 * lamIm η 1 2)

/-- The linear map behind `etaSkewEquivSl2C`, on all `4 × 4` real matrices: it reads the entries
above the diagonal. -/
noncomputable def spinMat (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  spinCoords η (η 1 * X 0 1) (η 2 * X 0 2) (η 3 * X 0 3) (η 2 * X 1 2) (η 3 * X 1 3)
    (η 3 * X 2 3)

/-- The inverse of `spinMat η` on trace-zero matrices, for product of the entries `-1`. -/
noncomputable def unspinMat (η : Fin 4 → ℝ) (m : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  skewMat η
    (lamRe η 0 1 * (-((m 0 1).im + (m 1 0).im)) + lamIm η 0 1 * ((m 0 1).re + (m 1 0).re))
    (lamRe η 0 2 * ((m 1 0).re - (m 0 1).re) + lamIm η 0 2 * ((m 1 0).im - (m 0 1).im))
    (lamRe η 0 3 * (-(2 * (m 0 0).im)) + lamIm η 0 3 * (2 * (m 0 0).re))
    (-(lamRe η 1 2 * (-(2 * (m 0 0).im)) + lamIm η 1 2 * (2 * (m 0 0).re)))
    (lamRe η 1 3 * ((m 1 0).re - (m 0 1).re) + lamIm η 1 3 * ((m 1 0).im - (m 0 1).im))
    (-(lamRe η 2 3 * (-((m 0 1).im + (m 1 0).im)) + lamIm η 2 3 * ((m 0 1).re + (m 1 0).re)))

/-- `spinMat η X` has trace zero. -/
theorem spinMat_trace (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    (spinMat η X).trace = 0 :=
  pauliR_trace _ _ _ _ _ _

/-- `spinMat η` on `skewMat η c` is `spinCoords η c`. -/
theorem spinMat_skewMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (c01 c02 c03 c12 c13 c23 : ℝ) :
    spinMat η (skewMat η c01 c02 c03 c12 c13 c23) = spinCoords η c01 c02 c03 c12 c13 c23 := by
  have h1 := eta_mul_self hη 1
  have h2 := eta_mul_self hη 2
  have h3 := eta_mul_self hη 3
  have e1 : η 1 * (η 1 * c01) = c01 := by linear_combination c01 * h1
  have e2 : η 2 * (η 2 * c02) = c02 := by linear_combination c02 * h2
  have e3 : η 3 * (η 3 * c03) = c03 := by linear_combination c03 * h3
  have e4 : η 2 * (η 2 * c12) = c12 := by linear_combination c12 * h2
  have e5 : η 3 * (η 3 * c13) = c13 := by linear_combination c13 * h3
  have e6 : η 3 * (η 3 * c23) = c23 := by linear_combination c23 * h3
  simp only [spinMat, skewMat_01, skewMat_02, skewMat_03, skewMat_12, skewMat_13, skewMat_23,
    e1, e2, e3, e4, e5, e6]

/-- `spinMat η` is additive. -/
theorem spinMat_add (η : Fin 4 → ℝ) (X Y : Matrix (Fin 4) (Fin 4) ℝ) :
    spinMat η (X + Y) = spinMat η X + spinMat η Y := by
  simp only [spinMat, spinCoords, pauliR_add, Matrix.add_apply]
  congr 1 <;> ring

/-- `spinMat η` is real-linear. -/
theorem spinMat_smul (η : Fin 4 → ℝ) (r : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    spinMat η (r • X) = (r : ℂ) • spinMat η X := by
  simp only [spinMat, spinCoords, pauliR_smul, Matrix.smul_apply, smul_eq_mul]
  congr 1 <;> ring

/-- The bracket identity in coordinates, for every diagonal with entries `±1`. -/
theorem spinMat_bracket_skewMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (c01 c02 c03 c12 c13 c23 d01 d02 d03 d12 d13 d23 : ℝ) :
    spinMat η (skewMat η c01 c02 c03 c12 c13 c23 * skewMat η d01 d02 d03 d12 d13 d23 -
        skewMat η d01 d02 d03 d12 d13 d23 * skewMat η c01 c02 c03 c12 c13 c23) =
      spinCoords η c01 c02 c03 c12 c13 c23 * spinCoords η d01 d02 d03 d12 d13 d23 -
        spinCoords η d01 d02 d03 d12 d13 d23 * spinCoords η c01 c02 c03 c12 c13 c23 := by
  simp only [spinCoords, pauliR_bracket, spinMat]
  congr 1 <;>
  · simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four, lamRe, lamIm,
      skewMat_00, skewMat_01, skewMat_02, skewMat_03, skewMat_10, skewMat_11, skewMat_12,
      skewMat_13, skewMat_20, skewMat_21, skewMat_22, skewMat_23, skewMat_31, skewMat_32,
      skewMat_33]
    rcases hη 0 with h0 | h0 <;> rcases hη 1 with h1 | h1 <;> rcases hη 2 with h2 | h2 <;>
      rcases hη 3 with h3 | h3 <;> simp only [h0, h1, h2, h3] <;> ring

/-- `spinMat η` preserves the bracket of `η`-skew matrices, for every diagonal with entries `±1`. -/
theorem spinMat_bracket {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X Y : etaSkew η) :
    spinMat η (X.1 * Y.1 - Y.1 * X.1) =
      spinMat η X.1 * spinMat η Y.1 - spinMat η Y.1 * spinMat η X.1 := by
  have eX := eq_skewMat hη X
  have eY := eq_skewMat hη Y
  rw [eX, eY, spinMat_skewMat hη, spinMat_skewMat hη]
  exact spinMat_bracket_skewMat hη _ _ _ _ _ _ _ _ _ _ _ _

/-- The eight diagonals with entries `±1` and product `-1`. -/
theorem lorentz_cases {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∏ i, η i = -1) :
    (η 0 = 1 ∧ η 1 = 1 ∧ η 2 = 1 ∧ η 3 = -1) ∨ (η 0 = 1 ∧ η 1 = 1 ∧ η 2 = -1 ∧ η 3 = 1) ∨
    (η 0 = 1 ∧ η 1 = -1 ∧ η 2 = 1 ∧ η 3 = 1) ∨ (η 0 = -1 ∧ η 1 = 1 ∧ η 2 = 1 ∧ η 3 = 1) ∨
    (η 0 = -1 ∧ η 1 = -1 ∧ η 2 = -1 ∧ η 3 = 1) ∨ (η 0 = -1 ∧ η 1 = -1 ∧ η 2 = 1 ∧ η 3 = -1) ∨
    (η 0 = -1 ∧ η 1 = 1 ∧ η 2 = -1 ∧ η 3 = -1) ∨ (η 0 = 1 ∧ η 1 = -1 ∧ η 2 = -1 ∧ η 3 = -1) := by
  rw [Fin.prod_univ_four] at h
  rcases hη 0 with h0 | h0 <;> rcases hη 1 with h1 | h1 <;> rcases hη 2 with h2 | h2 <;>
    rcases hη 3 with h3 | h3 <;> rw [h0, h1, h2, h3] at h ⊢ <;>
    first | (exfalso; norm_num at h; done) | norm_num

/-- `unspinMat η` on a `pauliR` matrix. -/
theorem unspinMat_pauliR (η : Fin 4 → ℝ) (u1 v1 u2 v2 u3 v3 : ℝ) :
    unspinMat η (pauliR u1 v1 u2 v2 u3 v3) =
      skewMat η (lamRe η 0 1 * u1 + lamIm η 0 1 * v1) (lamRe η 0 2 * u2 + lamIm η 0 2 * v2)
        (lamRe η 0 3 * u3 + lamIm η 0 3 * v3) (-(lamRe η 1 2 * u3 + lamIm η 1 2 * v3))
        (lamRe η 1 3 * u2 + lamIm η 1 3 * v2) (-(lamRe η 2 3 * u1 + lamIm η 2 3 * v1)) := by
  unfold unspinMat
  congr 1 <;> simp [pauliR] <;> ring

/-- `unspinMat η` is a left inverse of `spinCoords η` in coordinates, for product `-1`. -/
theorem unspinMat_spinCoords {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∏ i, η i = -1) (c01 c02 c03 c12 c13 c23 : ℝ) :
    unspinMat η (spinCoords η c01 c02 c03 c12 c13 c23) = skewMat η c01 c02 c03 c12 c13 c23 := by
  rw [spinCoords, unspinMat_pauliR]
  congr 1 <;>
  · simp only [lamRe, lamIm]
    rcases lorentz_cases hη h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
      ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
      ⟨h0, h1, h2, h3⟩ <;> simp only [h0, h1, h2, h3] <;> ring

/-- `unspinMat η` is a left inverse of `spinMat η` on `η`-skew matrices, for product `-1`. -/
theorem unspinMat_spinMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∏ i, η i = -1) (X : etaSkew η) : unspinMat η (spinMat η X.1) = X.1 := by
  have eX := eq_skewMat hη X
  rw [eX, spinMat_skewMat hη, unspinMat_spinCoords hη h]

/-- `unspinMat η` is a right inverse of `spinMat η` on trace-zero matrices, for product `-1`. -/
theorem spinMat_unspinMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∏ i, η i = -1) (m : Matrix (Fin 2) (Fin 2) ℂ) (hm : m.trace = 0) :
    spinMat η (unspinMat η m) = m := by
  refine Eq.trans ?_ (eq_pauliR m hm).symm
  rw [unspinMat, spinMat_skewMat hη, spinCoords]
  congr 1 <;>
  · simp only [lamRe, lamIm]
    rcases lorentz_cases hη h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
      ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
      ⟨h0, h1, h2, h3⟩ <;> simp only [h0, h1, h2, h3] <;> ring

end Spin

section Sl2CReal

/-- The element of `sl2CReal` with a given trace-zero matrix. -/
def toSl2CReal (m : Matrix (Fin 2) (Fin 2) ℂ) (hm : m.trace = 0) : sl2CReal :=
  (RestrictScalars.addEquiv ℝ ℂ sl2C).symm ⟨m, LinearMap.mem_ker.2 hm⟩

/-- The matrix of `toSl2CReal m hm` is `m`. -/
@[simp] theorem sl2CRealMat_toSl2CReal (m : Matrix (Fin 2) (Fin 2) ℂ) (hm : m.trace = 0) :
    sl2CRealMat (toSl2CReal m hm) = m :=
  rfl

/-- An element of `sl2CReal` is determined by its matrix. -/
theorem sl2CRealMat_injective : Function.Injective sl2CRealMat := by
  intro x y hxy
  exact (RestrictScalars.addEquiv ℝ ℂ sl2C).injective (Subtype.ext hxy)

/-- The matrix of an element of `sl2CReal` has trace zero. -/
theorem sl2CRealMat_trace (x : sl2CReal) : (sl2CRealMat x).trace = 0 :=
  LinearMap.mem_ker.1 (RestrictScalars.addEquiv ℝ ℂ sl2C x).2

/-- `sl2CRealMat` is additive. -/
theorem sl2CRealMat_add (x y : sl2CReal) :
    sl2CRealMat (x + y) = sl2CRealMat x + sl2CRealMat y :=
  rfl

/-- `sl2CRealMat` of a real multiple. -/
theorem sl2CRealMat_smul (r : ℝ) (x : sl2CReal) :
    sl2CRealMat (r • x) = (r : ℂ) • sl2CRealMat x := by
  simp [sl2CRealMat]

/-- `sl2CRealMat` of a bracket is the commutator of the matrices. -/
theorem sl2CRealMat_lie (x y : sl2CReal) :
    sl2CRealMat ⁅x, y⁆ = sl2CRealMat x * sl2CRealMat y - sl2CRealMat y * sl2CRealMat x :=
  rfl

end Sl2CReal

/-- Coordinate of `gen η i j` at the pair `(k, l)`: `1` at `(i, j)`, `-1` at `(j, i)`, else `0`. -/
def unitC (i j k l : Fin 4) : ℝ :=
  if i = k ∧ j = l then 1 else if j = k ∧ i = l then -1 else 0

/-- The generator `gen η i j` in coordinates. -/
theorem gen_eq_skewMat (η : Fin 4 → ℝ) (i j : Fin 4) :
    (gen η i j).1 = skewMat η (unitC i j 0 1) (unitC i j 0 2) (unitC i j 0 3) (unitC i j 1 2)
      (unitC i j 1 3) (unitC i j 2 3) := by
  rw [gen_coe]
  fin_cases i <;> fin_cases j <;>
    (ext a b; fin_cases a <;> fin_cases b <;> simp [unitC, skewMat])

/-- `spinPlus η i j` (`i ≠ j`) is `spinCoords η` at the coordinates of `gen η i j`. -/
theorem spinPlus_eq_spinCoords (η : Fin 4 → ℝ) (i j : Fin 4) (hij : i ≠ j) :
    spinPlus η i j = spinCoords η (unitC i j 0 1) (unitC i j 0 2) (unitC i j 0 3) (unitC i j 1 2)
      (unitC i j 1 3) (unitC i j 2 3) := by
  rw [spinPlus, mul_assoc, lam_mul_lam]
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (ext a b
       fin_cases a <;> fin_cases b <;>
         (apply Complex.ext <;>
           simp [unitC, spinCoords, pauliR, quat, quatBar, lamRe, lamIm] <;> ring))



/-! ### The Hodge operator under `spinMat η` -/

section HodgeSpin

/-- Entry `(0, 1)` of `hodgeMat η X`. -/
theorem hodgeMat_01 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeMat η X 0 1 = η 2 * X 2 3 * η 1 := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change (Matrix.diagonal η * X) 2 3 * η 1 = _
  rw [Matrix.diagonal_mul]

/-- Entry `(0, 2)` of `hodgeMat η X`. -/
theorem hodgeMat_02 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeMat η X 0 2 = -(η 1 * X 1 3) * η 2 := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change -(Matrix.diagonal η * X) 1 3 * η 2 = _
  rw [Matrix.diagonal_mul]

/-- Entry `(0, 3)` of `hodgeMat η X`. -/
theorem hodgeMat_03 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeMat η X 0 3 = η 1 * X 1 2 * η 3 := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change (Matrix.diagonal η * X) 1 2 * η 3 = _
  rw [Matrix.diagonal_mul]

/-- Entry `(1, 2)` of `hodgeMat η X`. -/
theorem hodgeMat_12 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeMat η X 1 2 = η 0 * X 0 3 * η 2 := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change (Matrix.diagonal η * X) 0 3 * η 2 = _
  rw [Matrix.diagonal_mul]

/-- Entry `(1, 3)` of `hodgeMat η X`. -/
theorem hodgeMat_13 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeMat η X 1 3 = -(η 0 * X 0 2) * η 3 := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change -(Matrix.diagonal η * X) 0 2 * η 3 = _
  rw [Matrix.diagonal_mul]

/-- Entry `(2, 3)` of `hodgeMat η X`. -/
theorem hodgeMat_23 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeMat η X 2 3 = η 0 * X 0 1 * η 3 := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change (Matrix.diagonal η * X) 0 1 * η 3 = _
  rw [Matrix.diagonal_mul]

/-- A complex multiple of a `pauliR` matrix. -/
theorem pauliR_csmul (w : ℂ) (u1 v1 u2 v2 u3 v3 : ℝ) :
    w • pauliR u1 v1 u2 v2 u3 v3 =
      pauliR (w.re * u1 - w.im * v1) (w.re * v1 + w.im * u1) (w.re * u2 - w.im * v2)
        (w.re * v2 + w.im * u2) (w.re * u3 - w.im * v3) (w.re * v3 + w.im * u3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (apply Complex.ext <;> simp [pauliR] <;> ring)

/-- `lamProd η` in real and imaginary parts. -/
theorem lamProd_eq (η : Fin 4 → ℝ) :
    lamProd η = ⟨lamRe η 0 1 * lamRe η 2 3 - lamIm η 0 1 * lamIm η 2 3,
      lamRe η 0 1 * lamIm η 2 3 + lamIm η 0 1 * lamRe η 2 3⟩ := by
  rw [lamProd, Fin.prod_univ_four, mul_assoc, lam_mul_lam, lam_mul_lam]
  apply Complex.ext <;> simp

/-- `spinMat η` carries `hodgeMat η` to multiplication by `-lamProd η`, for product of the entries
`-1`. -/
theorem spinMat_hodgeMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∏ i, η i = -1)
    (X : etaSkew η) : spinMat η (hodgeMat η X.1) = (-lamProd η) • spinMat η X.1 := by
  have eX := eq_skewMat hη X
  rw [eX, spinMat_skewMat hη, spinMat, spinCoords, spinCoords, pauliR_csmul, lamProd_eq]
  simp only [hodgeMat_01, hodgeMat_02, hodgeMat_03, hodgeMat_12, hodgeMat_13, hodgeMat_23,
    skewMat_01, skewMat_02, skewMat_03, skewMat_12, skewMat_13, skewMat_23, Complex.neg_re,
    Complex.neg_im, lamRe, lamIm]
  congr 1 <;>
  · rcases lorentz_cases hη h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
      ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
      ⟨h0, h1, h2, h3⟩ <;> simp only [h0, h1, h2, h3] <;> ring

end HodgeSpin


/-! ### The case of equal entries: `so(3) × so(3)` -/

section Definite

/-- The two diagonals with entries `±1` and all entries equal. -/
theorem definite_cases {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∀ i j, η i = η j) :
    (η 0 = 1 ∧ η 1 = 1 ∧ η 2 = 1 ∧ η 3 = 1) ∨ (η 0 = -1 ∧ η 1 = -1 ∧ η 2 = -1 ∧ η 3 = -1) := by
  rcases hη 0 with h0 | h0
  · exact Or.inl ⟨h0, (h 1 0).trans h0, (h 2 0).trans h0, (h 3 0).trans h0⟩
  · exact Or.inr ⟨h0, (h 1 0).trans h0, (h 2 0).trans h0, (h 3 0).trans h0⟩

/-- The skew-symmetric `3 × 3` matrix of a vector `(a₁, a₂, a₃)`. -/
def so3Vec (a1 a2 a3 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -a3, a2; a3, 0, -a1; -a2, a1, 0]

/-- Entry `(2, 1)` of `so3Vec a1 a2 a3`. -/
theorem so3Vec_21 (a1 a2 a3 : ℝ) : so3Vec a1 a2 a3 2 1 = a1 := rfl

/-- Entry `(0, 2)` of `so3Vec a1 a2 a3`. -/
theorem so3Vec_02 (a1 a2 a3 : ℝ) : so3Vec a1 a2 a3 0 2 = a2 := rfl

/-- Entry `(1, 0)` of `so3Vec a1 a2 a3`. -/
theorem so3Vec_10 (a1 a2 a3 : ℝ) : so3Vec a1 a2 a3 1 0 = a3 := rfl

/-- `so3Vec` is skew-symmetric. -/
theorem so3Vec_mem (a1 a2 a3 : ℝ) : so3Vec a1 a2 a3 ∈ so3 := by
  rw [LieAlgebra.Orthogonal.mem_so]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so3Vec]

/-- The commutator of two `so3Vec` matrices is the `so3Vec` matrix of the cross product. -/
theorem so3Vec_bracket (a1 a2 a3 b1 b2 b3 : ℝ) :
    so3Vec a1 a2 a3 * so3Vec b1 b2 b3 - so3Vec b1 b2 b3 * so3Vec a1 a2 a3 =
      so3Vec (a2 * b3 - a3 * b2) (a3 * b1 - a1 * b3) (a1 * b2 - a2 * b1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [so3Vec] <;> ring

/-- `so3Vec` is additive. -/
theorem so3Vec_add (a1 a2 a3 b1 b2 b3 : ℝ) :
    so3Vec a1 a2 a3 + so3Vec b1 b2 b3 = so3Vec (a1 + b1) (a2 + b2) (a3 + b3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so3Vec] <;> ring

/-- `so3Vec` is real-linear. -/
theorem so3Vec_smul (r a1 a2 a3 : ℝ) :
    r • so3Vec a1 a2 a3 = so3Vec (r * a1) (r * a2) (r * a3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so3Vec]

/-- Every skew-symmetric `3 × 3` matrix is a `so3Vec` matrix. -/
theorem eq_so3Vec (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = -A) :
    A = so3Vec (A 2 1) (A 0 2) (A 1 0) := by
  have hA' : ∀ i j, A j i = -A i j := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa using this
  have h00 : A 0 0 = 0 := by linarith [hA' 0 0]
  have h11 : A 1 1 = 0 := by linarith [hA' 1 1]
  have h22 : A 2 2 = 0 := by linarith [hA' 2 2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so3Vec, h00, h11, h22]
  · exact hA' 1 0
  · exact hA' 2 1
  · exact hA' 0 2

/-- `so3Plus X` as a `so3Vec` matrix. -/
theorem so3Plus_eq (X : Matrix (Fin 4) (Fin 4) ℝ) :
    so3Plus X = so3Vec (X 0 1 - X 2 3) (X 0 2 + X 1 3) (X 0 3 - X 1 2) := rfl

/-- `so3Minus X` as a `so3Vec` matrix. -/
theorem so3Minus_eq (X : Matrix (Fin 4) (Fin 4) ℝ) :
    so3Minus X = so3Vec (-X 0 1 - X 2 3) (-X 0 2 + X 1 3) (-X 0 3 - X 1 2) := rfl

/-- `so3Plus` is additive. -/
theorem so3Plus_add (X Y : Matrix (Fin 4) (Fin 4) ℝ) :
    so3Plus (X + Y) = so3Plus X + so3Plus Y := by
  simp only [so3Plus_eq, so3Vec_add, Matrix.add_apply]
  congr 1 <;> ring

/-- `so3Minus` is additive. -/
theorem so3Minus_add (X Y : Matrix (Fin 4) (Fin 4) ℝ) :
    so3Minus (X + Y) = so3Minus X + so3Minus Y := by
  simp only [so3Minus_eq, so3Vec_add, Matrix.add_apply]
  congr 1 <;> ring

/-- `so3Plus` is real-linear. -/
theorem so3Plus_smul (r : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    so3Plus (r • X) = r • so3Plus X := by
  simp only [so3Plus_eq, so3Vec_smul, Matrix.smul_apply, smul_eq_mul]
  congr 1 <;> ring

/-- `so3Minus` is real-linear. -/
theorem so3Minus_smul (r : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    so3Minus (r • X) = r • so3Minus X := by
  simp only [so3Minus_eq, so3Vec_smul, Matrix.smul_apply, smul_eq_mul]
  congr 1 <;> ring

/-- `so3Plus` preserves the bracket of `η`-skew matrices when all entries of `η` are equal. -/
theorem so3Plus_bracket {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∀ i j, η i = η j)
    (X Y : etaSkew η) :
    so3Plus (X.1 * Y.1 - Y.1 * X.1) = so3Plus X.1 * so3Plus Y.1 - so3Plus Y.1 * so3Plus X.1 := by
  have eX := eq_skewMat hη X
  have eY := eq_skewMat hη Y
  rw [eX, eY]
  simp only [so3Plus_eq, so3Vec_bracket]
  congr 1 <;>
  · simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four,
      skewMat_00, skewMat_01, skewMat_02, skewMat_03, skewMat_10, skewMat_11, skewMat_12,
      skewMat_13, skewMat_20, skewMat_21, skewMat_22, skewMat_23, skewMat_31,
      skewMat_32, skewMat_33]
    rcases definite_cases hη h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;>
      simp only [h0, h1, h2, h3] <;> ring

/-- `so3Minus` preserves the bracket of `η`-skew matrices when all entries of `η` are equal. -/
theorem so3Minus_bracket {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∀ i j, η i = η j) (X Y : etaSkew η) :
    so3Minus (X.1 * Y.1 - Y.1 * X.1) =
      so3Minus X.1 * so3Minus Y.1 - so3Minus Y.1 * so3Minus X.1 := by
  have eX := eq_skewMat hη X
  have eY := eq_skewMat hη Y
  rw [eX, eY]
  simp only [so3Minus_eq, so3Vec_bracket]
  congr 1 <;>
  · simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four,
      skewMat_00, skewMat_01, skewMat_02, skewMat_03, skewMat_10, skewMat_11, skewMat_12,
      skewMat_13, skewMat_20, skewMat_21, skewMat_22, skewMat_23, skewMat_31,
      skewMat_32, skewMat_33]
    rcases definite_cases hη h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;>
      simp only [h0, h1, h2, h3] <;> ring

/-- The inverse of `X ↦ (so3Plus X, so3Minus X)`, in coordinates. -/
noncomputable def unso3 (η : Fin 4 → ℝ) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  skewMat η (η 1 * ((A 2 1 - B 2 1) / 2)) (η 2 * ((A 0 2 - B 0 2) / 2))
    (η 3 * ((A 1 0 - B 1 0) / 2)) (η 2 * (-(A 1 0 + B 1 0) / 2)) (η 3 * ((A 0 2 + B 0 2) / 2))
    (η 3 * (-(A 2 1 + B 2 1) / 2))

/-- `unso3 η` is a left inverse on `η`-skew matrices. -/
theorem unso3_so3 {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X : etaSkew η) :
    unso3 η (so3Plus X.1) (so3Minus X.1) = X.1 := by
  refine Eq.trans ?_ (eq_skewMat hη X).symm
  simp only [unso3, so3Plus_eq, so3Minus_eq, so3Vec_21, so3Vec_02, so3Vec_10]
  congr 1 <;> ring

/-- `unso3 η` is a right inverse on skew-symmetric matrices (first component). -/
theorem so3Plus_unso3 {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hA : Aᵀ = -A) : so3Plus (unso3 η A B) = A := by
  have h1 := eta_mul_self hη 1
  have h2 := eta_mul_self hη 2
  have h3 := eta_mul_self hη 3
  refine Eq.trans ?_ (eq_so3Vec A hA).symm
  simp only [so3Plus_eq, unso3, skewMat_01, skewMat_02, skewMat_03, skewMat_12, skewMat_13,
    skewMat_23]
  congr 1
  · linear_combination ((A 2 1 - B 2 1) / 2) * h1 + ((A 2 1 + B 2 1) / 2) * h3
  · linear_combination ((A 0 2 - B 0 2) / 2) * h2 + ((A 0 2 + B 0 2) / 2) * h3
  · linear_combination ((A 1 0 - B 1 0) / 2) * h3 + ((A 1 0 + B 1 0) / 2) * h2

/-- `unso3 η` is a right inverse on skew-symmetric matrices (second component). -/
theorem so3Minus_unso3 {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hB : Bᵀ = -B) : so3Minus (unso3 η A B) = B := by
  have h1 := eta_mul_self hη 1
  have h2 := eta_mul_self hη 2
  have h3 := eta_mul_self hη 3
  refine Eq.trans ?_ (eq_so3Vec B hB).symm
  simp only [so3Minus_eq, unso3, skewMat_01, skewMat_02, skewMat_03, skewMat_12, skewMat_13,
    skewMat_23]
  congr 1
  · linear_combination (-(A 2 1 - B 2 1) / 2) * h1 + ((A 2 1 + B 2 1) / 2) * h3
  · linear_combination (-(A 0 2 - B 0 2) / 2) * h2 + ((A 0 2 + B 0 2) / 2) * h3
  · linear_combination (-(A 1 0 - B 1 0) / 2) * h3 + ((A 1 0 + B 1 0) / 2) * h2

end Definite


/-! ### The case of sum `0`: `sl(2, ℝ) × sl(2, ℝ)` -/

section Split

/-- An existential over `Fin 4`, written out. -/
theorem exists_fin_four (P : Fin 4 → Prop) : (∃ j, P j) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 := by
  constructor
  · rintro ⟨j, hj⟩
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inr (Or.inr (Or.inr hj))
  · rintro (h | h | h | h) <;> exact ⟨_, h⟩

/-- The six diagonals with entries `±1` and sum `0`, each with the values of `splitFrame η`. -/
theorem split_cases {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∑ i, η i = 0) :
    (η 0 = 1 ∧ η 1 = 1 ∧ η 2 = -1 ∧ η 3 = -1 ∧
      splitFrame η 0 = !![1, 0; 0, 1] ∧ splitFrame η 1 = !![0, -1; 1, 0] ∧
      splitFrame η 2 = !![0, 1; 1, 0] ∧ splitFrame η 3 = !![1, 0; 0, -1]) ∨
    (η 0 = 1 ∧ η 1 = -1 ∧ η 2 = 1 ∧ η 3 = -1 ∧
      splitFrame η 0 = !![1, 0; 0, 1] ∧ splitFrame η 1 = !![0, 1; 1, 0] ∧
      splitFrame η 2 = !![0, -1; 1, 0] ∧ splitFrame η 3 = !![1, 0; 0, -1]) ∨
    (η 0 = 1 ∧ η 1 = -1 ∧ η 2 = -1 ∧ η 3 = 1 ∧
      splitFrame η 0 = !![1, 0; 0, 1] ∧ splitFrame η 1 = !![0, 1; 1, 0] ∧
      splitFrame η 2 = !![1, 0; 0, -1] ∧ splitFrame η 3 = !![0, -1; 1, 0]) ∨
    (η 0 = -1 ∧ η 1 = 1 ∧ η 2 = 1 ∧ η 3 = -1 ∧
      splitFrame η 0 = !![0, 1; 1, 0] ∧ splitFrame η 1 = !![1, 0; 0, 1] ∧
      splitFrame η 2 = !![0, -1; 1, 0] ∧ splitFrame η 3 = !![1, 0; 0, -1]) ∨
    (η 0 = -1 ∧ η 1 = 1 ∧ η 2 = -1 ∧ η 3 = 1 ∧
      splitFrame η 0 = !![0, 1; 1, 0] ∧ splitFrame η 1 = !![1, 0; 0, 1] ∧
      splitFrame η 2 = !![1, 0; 0, -1] ∧ splitFrame η 3 = !![0, -1; 1, 0]) ∨
    (η 0 = -1 ∧ η 1 = -1 ∧ η 2 = 1 ∧ η 3 = 1 ∧
      splitFrame η 0 = !![0, 1; 1, 0] ∧ splitFrame η 1 = !![1, 0; 0, -1] ∧
      splitFrame η 2 = !![1, 0; 0, 1] ∧ splitFrame η 3 = !![0, -1; 1, 0]) := by
  rw [Fin.sum_univ_four] at h
  rcases hη 0 with h0 | h0 <;> rcases hη 1 with h1 | h1 <;> rcases hη 2 with h2 | h2 <;>
    rcases hη 3 with h3 | h3 <;>
    first
    | (exfalso; rw [h0, h1, h2, h3] at h; norm_num at h; done)
    | norm_num [splitFrame, exists_fin_four, h0, h1, h2, h3]

/-- The trace-zero real `2 × 2` matrix `½ (x J + y S + z D)` with `J = !![0, -1; 1, 0]`,
`S = !![0, 1; 1, 0]`, `D = !![1, 0; 0, -1]`. -/
noncomputable def sl2Vec (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z / 2, (y - x) / 2; (y + x) / 2, -(z / 2)]

/-- `sl2Vec` has trace zero. -/
theorem sl2Vec_trace (x y z : ℝ) : (sl2Vec x y z).trace = 0 := by
  simp [sl2Vec, Matrix.trace, Fin.sum_univ_two]

/-- The commutator of two `sl2Vec` matrices. -/
theorem sl2Vec_bracket (x y z x' y' z' : ℝ) :
    sl2Vec x y z * sl2Vec x' y' z' - sl2Vec x' y' z' * sl2Vec x y z =
      sl2Vec (y * z' - z * y') (x * z' - z * x') (y * x' - x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Vec] <;> ring

/-- The trace of a product of two `sl2Vec` matrices. -/
theorem sl2Vec_trace_mul (x y z x' y' z' : ℝ) :
    (sl2Vec x y z * sl2Vec x' y' z').trace = (-(x * x') + y * y' + z * z') / 2 := by
  simp [sl2Vec, Matrix.trace, Fin.sum_univ_two]
  ring

/-- Every trace-zero real `2 × 2` matrix is a `sl2Vec` matrix. -/
theorem eq_sl2Vec (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.trace = 0) :
    A = sl2Vec (A 1 0 - A 0 1) (A 1 0 + A 0 1) (2 * A 0 0) := by
  have h1 : A 1 1 = -A 0 0 := by
    have : A 0 0 + A 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using hA
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Vec, h1]

/-- `∑ c i j • splitPlus η i j` over `i < j`. -/
noncomputable def splitCoordsPlus (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  c01 • splitPlus η 0 1 + c02 • splitPlus η 0 2 + c03 • splitPlus η 0 3 + c12 • splitPlus η 1 2 +
    c13 • splitPlus η 1 3 + c23 • splitPlus η 2 3

/-- `∑ c i j • splitMinus η i j` over `i < j`. -/
noncomputable def splitCoordsMinus (η : Fin 4 → ℝ) (c01 c02 c03 c12 c13 c23 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  c01 • splitMinus η 0 1 + c02 • splitMinus η 0 2 + c03 • splitMinus η 0 3 +
    c12 • splitMinus η 1 2 + c13 • splitMinus η 1 3 + c23 • splitMinus η 2 3

/-- The first component of the linear map behind `etaSkewEquivSl2RProd`. -/
noncomputable def splitMatPlus (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  splitCoordsPlus η (η 1 * X 0 1) (η 2 * X 0 2) (η 3 * X 0 3) (η 2 * X 1 2) (η 3 * X 1 3)
    (η 3 * X 2 3)

/-- The second component of the linear map behind `etaSkewEquivSl2RProd`. -/
noncomputable def splitMatMinus (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  splitCoordsMinus η (η 1 * X 0 1) (η 2 * X 0 2) (η 3 * X 0 3) (η 2 * X 1 2) (η 3 * X 1 3)
    (η 3 * X 2 3)

/-- The six diagonals with entries `±1` and sum `0`, each with `splitCoordsPlus η` and
`splitCoordsMinus η` as `sl2Vec` matrices. -/
theorem split_forms {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∑ i, η i = 0) :
    (η 0 = 1 ∧ η 1 = 1 ∧ η 2 = -1 ∧ η 3 = -1 ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsPlus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c01 - c23) (-c02 - c13) (-c03 + c12)) ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsMinus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (c01 - c23) (c02 - c13) (c03 + c12))) ∨
    (η 0 = 1 ∧ η 1 = -1 ∧ η 2 = 1 ∧ η 3 = -1 ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsPlus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c02 - c13) (-c01 - c23) (-c03 - c12)) ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsMinus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (c02 - c13) (c01 - c23) (c03 - c12))) ∨
    (η 0 = 1 ∧ η 1 = -1 ∧ η 2 = -1 ∧ η 3 = 1 ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsPlus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c03 - c12) (-c01 + c23) (-c02 - c13)) ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsMinus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (c03 - c12) (c01 + c23) (c02 - c13))) ∨
    (η 0 = -1 ∧ η 1 = 1 ∧ η 2 = 1 ∧ η 3 = -1 ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsPlus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c03 - c12) (c01 - c23) (-c02 - c13)) ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsMinus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c03 + c12) (-c01 - c23) (-c02 + c13))) ∨
    (η 0 = -1 ∧ η 1 = 1 ∧ η 2 = -1 ∧ η 3 = 1 ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsPlus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c02 - c13) (c01 + c23) (-c03 - c12)) ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsMinus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c02 + c13) (-c01 + c23) (-c03 + c12))) ∨
    (η 0 = -1 ∧ η 1 = -1 ∧ η 2 = 1 ∧ η 3 = 1 ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsPlus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c01 - c23) (c02 + c13) (-c03 + c12)) ∧
      (∀ c01 c02 c03 c12 c13 c23 : ℝ, splitCoordsMinus η c01 c02 c03 c12 c13 c23 =
        sl2Vec (-c01 + c23) (-c02 + c13) (-c03 - c12))) := by
  rcases split_cases hη h with ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ | ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ | ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩
  · exact Or.inl ⟨h0, h1, h2, h3, fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsPlus, splitPlus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring,
      fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsMinus, splitMinus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring⟩
  · exact Or.inr (Or.inl ⟨h0, h1, h2, h3, fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsPlus, splitPlus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring,
      fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsMinus, splitMinus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h0, h1, h2, h3, fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsPlus, splitPlus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring,
      fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsMinus, splitMinus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, h2, h3, fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsPlus, splitPlus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring,
      fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsMinus, splitMinus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, h2, h3, fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsPlus, splitPlus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring,
      fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsMinus, splitMinus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h0, h1, h2, h3, fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsPlus, splitPlus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring,
      fun c01 c02 c03 c12 c13 c23 => by
      simp only [splitCoordsMinus, splitMinus, f0, f1, f2, f3]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [sl2Vec] <;> ring⟩)))))

/-- `splitCoordsPlus η c` has trace zero when the sum of the entries of `η` is `0`. -/
theorem splitCoordsPlus_trace {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (c01 c02 c03 c12 c13 c23 : ℝ) :
    (splitCoordsPlus η c01 c02 c03 c12 c13 c23).trace = 0 := by
  rcases split_forms hη h with ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ |
    ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ |
    ⟨h0, h1, h2, h3, hP, hM⟩ <;>
  · rw [hP]
    exact sl2Vec_trace _ _ _

/-- `splitMatPlus η` on `skewMat η c` is `splitCoordsPlus η c`. -/
theorem splitMatPlus_skewMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (c01 c02 c03 c12 c13 c23 : ℝ) :
    splitMatPlus η (skewMat η c01 c02 c03 c12 c13 c23) =
      splitCoordsPlus η c01 c02 c03 c12 c13 c23 := by
  have h1 := eta_mul_self hη 1
  have h2 := eta_mul_self hη 2
  have h3 := eta_mul_self hη 3
  have e1 : η 1 * (η 1 * c01) = c01 := by linear_combination c01 * h1
  have e2 : η 2 * (η 2 * c02) = c02 := by linear_combination c02 * h2
  have e3 : η 3 * (η 3 * c03) = c03 := by linear_combination c03 * h3
  have e4 : η 2 * (η 2 * c12) = c12 := by linear_combination c12 * h2
  have e5 : η 3 * (η 3 * c13) = c13 := by linear_combination c13 * h3
  have e6 : η 3 * (η 3 * c23) = c23 := by linear_combination c23 * h3
  simp only [splitMatPlus, skewMat_01, skewMat_02, skewMat_03, skewMat_12, skewMat_13,
    skewMat_23, e1, e2, e3, e4, e5, e6]

/-- `splitMatPlus η` is additive. -/
theorem splitMatPlus_add (η : Fin 4 → ℝ) (X Y : Matrix (Fin 4) (Fin 4) ℝ) :
    splitMatPlus η (X + Y) = splitMatPlus η X + splitMatPlus η Y := by
  simp only [splitMatPlus, splitCoordsPlus, Matrix.add_apply]
  module

/-- `splitMatPlus η` is real-linear. -/
theorem splitMatPlus_smul (η : Fin 4 → ℝ) (r : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    splitMatPlus η (r • X) = r • splitMatPlus η X := by
  simp only [splitMatPlus, splitCoordsPlus, Matrix.smul_apply, smul_eq_mul]
  module

/-- The bracket identity in coordinates (first component), for sum of the entries `0`. -/
theorem splitMatPlus_bracket_skewMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (c01 c02 c03 c12 c13 c23 d01 d02 d03 d12 d13 d23 : ℝ) :
    splitMatPlus η (skewMat η c01 c02 c03 c12 c13 c23 * skewMat η d01 d02 d03 d12 d13 d23 -
        skewMat η d01 d02 d03 d12 d13 d23 * skewMat η c01 c02 c03 c12 c13 c23) =
      splitCoordsPlus η c01 c02 c03 c12 c13 c23 * splitCoordsPlus η d01 d02 d03 d12 d13 d23 -
        splitCoordsPlus η d01 d02 d03 d12 d13 d23 *
          splitCoordsPlus η c01 c02 c03 c12 c13 c23 := by
  simp only [splitMatPlus, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four,
    skewMat_00, skewMat_01, skewMat_02, skewMat_03, skewMat_10, skewMat_11, skewMat_12,
    skewMat_13, skewMat_20, skewMat_21, skewMat_22, skewMat_23, skewMat_31, skewMat_32, skewMat_33]
  rcases split_forms hη h with ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ |
    ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ |
    ⟨h0, h1, h2, h3, hP, hM⟩ <;>
  · simp only [hP, sl2Vec_bracket, h0, h1, h2, h3]
    congr 1 <;> ring

/-- `splitMatPlus η` preserves the bracket of `η`-skew matrices, for sum of the entries `0`. -/
theorem splitMatPlus_bracket {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (X Y : etaSkew η) :
    splitMatPlus η (X.1 * Y.1 - Y.1 * X.1) =
      splitMatPlus η X.1 * splitMatPlus η Y.1 - splitMatPlus η Y.1 * splitMatPlus η X.1 := by
  have eX := eq_skewMat hη X
  have eY := eq_skewMat hη Y
  rw [eX, eY, splitMatPlus_skewMat hη, splitMatPlus_skewMat hη]
  exact splitMatPlus_bracket_skewMat hη h _ _ _ _ _ _ _ _ _ _ _ _

/-- For `i < j`: `splitPlus η j i = -splitPlus η i j`, for sum of the entries `0`. -/
theorem splitPlus_antisymm {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) :
    splitPlus η 1 0 = -splitPlus η 0 1 ∧ splitPlus η 2 0 = -splitPlus η 0 2 ∧
      splitPlus η 3 0 = -splitPlus η 0 3 ∧ splitPlus η 2 1 = -splitPlus η 1 2 ∧
      splitPlus η 3 1 = -splitPlus η 1 3 ∧ splitPlus η 3 2 = -splitPlus η 2 3 := by
  rcases split_cases hη h with ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ | ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ | ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ <;>
  · simp only [splitPlus, f0, f1, f2, f3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext a b
      fin_cases a <;> fin_cases b <;> simp

/-- `splitPlus η i j` for `i < j` as values of `splitCoordsPlus η`. -/
theorem splitPlus_eq_coords (η : Fin 4 → ℝ) :
    splitPlus η 0 1 = splitCoordsPlus η 1 0 0 0 0 0 ∧
      splitPlus η 0 2 = splitCoordsPlus η 0 1 0 0 0 0 ∧
      splitPlus η 0 3 = splitCoordsPlus η 0 0 1 0 0 0 ∧
      splitPlus η 1 2 = splitCoordsPlus η 0 0 0 1 0 0 ∧
      splitPlus η 1 3 = splitCoordsPlus η 0 0 0 0 1 0 ∧
      splitPlus η 2 3 = splitCoordsPlus η 0 0 0 0 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [splitCoordsPlus]

/-- `splitPlus η i j` (`i ≠ j`) is `splitCoordsPlus η` at the coordinates of `gen η i j`. -/
theorem splitCoordsPlus_unitC {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (i j : Fin 4) (hij : i ≠ j) :
    splitCoordsPlus η (unitC i j 0 1) (unitC i j 0 2) (unitC i j 0 3) (unitC i j 1 2)
      (unitC i j 1 3) (unitC i j 2 3) = splitPlus η i j := by
  obtain ⟨a01, a02, a03, a12, a13, a23⟩ := splitPlus_antisymm hη h
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [unitC, splitCoordsPlus, a01, a02, a03, a12, a13, a23]

/-- `splitCoordsMinus η c` has trace zero when the sum of the entries of `η` is `0`. -/
theorem splitCoordsMinus_trace {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (c01 c02 c03 c12 c13 c23 : ℝ) :
    (splitCoordsMinus η c01 c02 c03 c12 c13 c23).trace = 0 := by
  rcases split_forms hη h with ⟨h0, h1, h2, h3, hM, hM⟩ | ⟨h0, h1, h2, h3, hM, hM⟩ |
    ⟨h0, h1, h2, h3, hM, hM⟩ | ⟨h0, h1, h2, h3, hM, hM⟩ | ⟨h0, h1, h2, h3, hM, hM⟩ |
    ⟨h0, h1, h2, h3, hM, hM⟩ <;>
  · rw [hM]
    exact sl2Vec_trace _ _ _

/-- `splitMatMinus η` on `skewMat η c` is `splitCoordsMinus η c`. -/
theorem splitMatMinus_skewMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (c01 c02 c03 c12 c13 c23 : ℝ) :
    splitMatMinus η (skewMat η c01 c02 c03 c12 c13 c23) =
      splitCoordsMinus η c01 c02 c03 c12 c13 c23 := by
  have h1 := eta_mul_self hη 1
  have h2 := eta_mul_self hη 2
  have h3 := eta_mul_self hη 3
  have e1 : η 1 * (η 1 * c01) = c01 := by linear_combination c01 * h1
  have e2 : η 2 * (η 2 * c02) = c02 := by linear_combination c02 * h2
  have e3 : η 3 * (η 3 * c03) = c03 := by linear_combination c03 * h3
  have e4 : η 2 * (η 2 * c12) = c12 := by linear_combination c12 * h2
  have e5 : η 3 * (η 3 * c13) = c13 := by linear_combination c13 * h3
  have e6 : η 3 * (η 3 * c23) = c23 := by linear_combination c23 * h3
  simp only [splitMatMinus, skewMat_01, skewMat_02, skewMat_03, skewMat_12, skewMat_13,
    skewMat_23, e1, e2, e3, e4, e5, e6]

/-- `splitMatMinus η` is additive. -/
theorem splitMatMinus_add (η : Fin 4 → ℝ) (X Y : Matrix (Fin 4) (Fin 4) ℝ) :
    splitMatMinus η (X + Y) = splitMatMinus η X + splitMatMinus η Y := by
  simp only [splitMatMinus, splitCoordsMinus, Matrix.add_apply]
  module

/-- `splitMatMinus η` is real-linear. -/
theorem splitMatMinus_smul (η : Fin 4 → ℝ) (r : ℝ) (X : Matrix (Fin 4) (Fin 4) ℝ) :
    splitMatMinus η (r • X) = r • splitMatMinus η X := by
  simp only [splitMatMinus, splitCoordsMinus, Matrix.smul_apply, smul_eq_mul]
  module

/-- The bracket identity in coordinates (second component), for sum of the entries `0`. -/
theorem splitMatMinus_bracket_skewMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (c01 c02 c03 c12 c13 c23 d01 d02 d03 d12 d13 d23 : ℝ) :
    splitMatMinus η (skewMat η c01 c02 c03 c12 c13 c23 * skewMat η d01 d02 d03 d12 d13 d23 -
        skewMat η d01 d02 d03 d12 d13 d23 * skewMat η c01 c02 c03 c12 c13 c23) =
      splitCoordsMinus η c01 c02 c03 c12 c13 c23 * splitCoordsMinus η d01 d02 d03 d12 d13 d23 -
        splitCoordsMinus η d01 d02 d03 d12 d13 d23 *
          splitCoordsMinus η c01 c02 c03 c12 c13 c23 := by
  simp only [splitMatMinus, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four,
    skewMat_00, skewMat_01, skewMat_02, skewMat_03, skewMat_10, skewMat_11, skewMat_12,
    skewMat_13, skewMat_20, skewMat_21, skewMat_22, skewMat_23, skewMat_31, skewMat_32, skewMat_33]
  rcases split_forms hη h with ⟨h0, h1, h2, h3, hM, hM⟩ | ⟨h0, h1, h2, h3, hM, hM⟩ |
    ⟨h0, h1, h2, h3, hM, hM⟩ | ⟨h0, h1, h2, h3, hM, hM⟩ | ⟨h0, h1, h2, h3, hM, hM⟩ |
    ⟨h0, h1, h2, h3, hM, hM⟩ <;>
  · simp only [hM, sl2Vec_bracket, h0, h1, h2, h3]
    congr 1 <;> ring

/-- `splitMatMinus η` preserves the bracket of `η`-skew matrices, for sum of the entries `0`. -/
theorem splitMatMinus_bracket {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (X Y : etaSkew η) :
    splitMatMinus η (X.1 * Y.1 - Y.1 * X.1) =
      splitMatMinus η X.1 * splitMatMinus η Y.1 - splitMatMinus η Y.1 * splitMatMinus η X.1 := by
  have eX := eq_skewMat hη X
  have eY := eq_skewMat hη Y
  rw [eX, eY, splitMatMinus_skewMat hη, splitMatMinus_skewMat hη]
  exact splitMatMinus_bracket_skewMat hη h _ _ _ _ _ _ _ _ _ _ _ _

/-- For `i < j`: `splitMinus η j i = -splitMinus η i j`, for sum of the entries `0`. -/
theorem splitMinus_antisymm {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) :
    splitMinus η 1 0 = -splitMinus η 0 1 ∧ splitMinus η 2 0 = -splitMinus η 0 2 ∧
      splitMinus η 3 0 = -splitMinus η 0 3 ∧ splitMinus η 2 1 = -splitMinus η 1 2 ∧
      splitMinus η 3 1 = -splitMinus η 1 3 ∧ splitMinus η 3 2 = -splitMinus η 2 3 := by
  rcases split_cases hη h with ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ | ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ | ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ |
    ⟨h0, h1, h2, h3, f0, f1, f2, f3⟩ <;>
  · simp only [splitMinus, f0, f1, f2, f3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext a b
      fin_cases a <;> fin_cases b <;> simp

/-- `splitMinus η i j` for `i < j` as values of `splitCoordsMinus η`. -/
theorem splitMinus_eq_coords (η : Fin 4 → ℝ) :
    splitMinus η 0 1 = splitCoordsMinus η 1 0 0 0 0 0 ∧
      splitMinus η 0 2 = splitCoordsMinus η 0 1 0 0 0 0 ∧
      splitMinus η 0 3 = splitCoordsMinus η 0 0 1 0 0 0 ∧
      splitMinus η 1 2 = splitCoordsMinus η 0 0 0 1 0 0 ∧
      splitMinus η 1 3 = splitCoordsMinus η 0 0 0 0 1 0 ∧
      splitMinus η 2 3 = splitCoordsMinus η 0 0 0 0 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [splitCoordsMinus]

/-- `splitMinus η i j` (`i ≠ j`) is `splitCoordsMinus η` at the coordinates of `gen η i j`. -/
theorem splitCoordsMinus_unitC {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (i j : Fin 4) (hij : i ≠ j) :
    splitCoordsMinus η (unitC i j 0 1) (unitC i j 0 2) (unitC i j 0 3) (unitC i j 1 2)
      (unitC i j 1 3) (unitC i j 2 3) = splitMinus η i j := by
  obtain ⟨a01, a02, a03, a12, a13, a23⟩ := splitMinus_antisymm hη h
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [unitC, splitCoordsMinus, a01, a02, a03, a12, a13, a23]

/-- The coordinate of the inverse at the pair `(i, j)`: a trace pairing with `splitPlus η i j` and
`splitMinus η i j`. -/
noncomputable def splitK (η : Fin 4 → ℝ) (A B : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 4) : ℝ :=
  -(η i * η j) * ((A * splitPlus η i j).trace + (B * splitMinus η i j).trace)

/-- The inverse of `X ↦ (splitMatPlus η X, splitMatMinus η X)`, in coordinates. -/
noncomputable def unsplitMat (η : Fin 4 → ℝ) (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  skewMat η (splitK η A B 0 1) (splitK η A B 0 2) (splitK η A B 0 3) (splitK η A B 1 2)
    (splitK η A B 1 3) (splitK η A B 2 3)

/-- `unsplitMat η` is a left inverse in coordinates, for sum of the entries `0`. -/
theorem unsplitMat_splitCoords {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (c01 c02 c03 c12 c13 c23 : ℝ) :
    unsplitMat η (splitCoordsPlus η c01 c02 c03 c12 c13 c23)
        (splitCoordsMinus η c01 c02 c03 c12 c13 c23) =
      skewMat η c01 c02 c03 c12 c13 c23 := by
  obtain ⟨p01, p02, p03, p12, p13, p23⟩ := splitPlus_eq_coords η
  obtain ⟨m01, m02, m03, m12, m13, m23⟩ := splitMinus_eq_coords η
  simp only [unsplitMat, splitK, p01, p02, p03, p12, p13, p23, m01, m02, m03, m12, m13, m23]
  rcases split_forms hη h with ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ |
    ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ |
    ⟨h0, h1, h2, h3, hP, hM⟩ <;>
  · simp only [hP, hM, sl2Vec_trace_mul, h0, h1, h2, h3]
    congr 1 <;> ring

/-- `unsplitMat η` is a left inverse on `η`-skew matrices, for sum of the entries `0`. -/
theorem unsplitMat_splitMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (X : etaSkew η) :
    unsplitMat η (splitMatPlus η X.1) (splitMatMinus η X.1) = X.1 := by
  have eX := eq_skewMat hη X
  rw [eX, splitMatPlus_skewMat hη, splitMatMinus_skewMat hη, unsplitMat_splitCoords hη h]

/-- `unsplitMat η` is a right inverse on pairs of `sl2Vec` matrices, for sum of the entries
`0`. -/
theorem splitMat_unsplitMat_sl2Vec {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (x y z x' y' z' : ℝ) :
    splitMatPlus η (unsplitMat η (sl2Vec x y z) (sl2Vec x' y' z')) = sl2Vec x y z ∧
      splitMatMinus η (unsplitMat η (sl2Vec x y z) (sl2Vec x' y' z')) = sl2Vec x' y' z' := by
  obtain ⟨p01, p02, p03, p12, p13, p23⟩ := splitPlus_eq_coords η
  obtain ⟨m01, m02, m03, m12, m13, m23⟩ := splitMinus_eq_coords η
  rw [unsplitMat, splitMatPlus_skewMat hη, splitMatMinus_skewMat hη]
  simp only [splitK, p01, p02, p03, p12, p13, p23, m01, m02, m03, m12, m13, m23]
  rcases split_forms hη h with ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ |
    ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ | ⟨h0, h1, h2, h3, hP, hM⟩ |
    ⟨h0, h1, h2, h3, hP, hM⟩ <;>
  · simp only [hP, hM, sl2Vec_trace_mul, h0, h1, h2, h3]
    constructor <;> (congr 1 <;> ring)

/-- `unsplitMat η` is a right inverse on trace-zero matrices, for sum of the entries `0`. -/
theorem splitMat_unsplitMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (A B : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.trace = 0) (hB : B.trace = 0) :
    splitMatPlus η (unsplitMat η A B) = A ∧ splitMatMinus η (unsplitMat η A B) = B := by
  have eA := eq_sl2Vec A hA
  have eB := eq_sl2Vec B hB
  rw [eA, eB]
  exact splitMat_unsplitMat_sl2Vec hη h _ _ _ _ _ _

end Split

end RealForms

open RealForms

/-- **L2 (the equivalence).** For `η : Fin 4 → ℝ` with every entry `1` or `-1` and
`∏ i, η i = -1`: a Lie algebra equivalence over `ℝ` from `etaSkew η` to `sl(2, ℂ)` regarded as a
real Lie algebra. It is pinned down by `etaSkewEquivSl2C_gen`. -/
noncomputable def etaSkewEquivSl2C (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∏ i, η i = -1) : etaSkew η ≃ₗ⁅ℝ⁆ sl2CReal :=
  { toFun := fun X => toSl2CReal (spinMat η X.1) (spinMat_trace η X.1)
    map_add' := fun X Y => sl2CRealMat_injective (by
      rw [sl2CRealMat_add]
      exact spinMat_add η X.1 Y.1)
    map_smul' := fun r X => sl2CRealMat_injective (by
      rw [RingHom.id_apply, sl2CRealMat_smul]
      exact spinMat_smul η r X.1)
    map_lie' := fun {X Y} => sl2CRealMat_injective (by
      rw [sl2CRealMat_lie]
      exact spinMat_bracket hη X Y)
    invFun := fun x => ⟨unspinMat η (sl2CRealMat x), skewMat_mem η _ _ _ _ _ _⟩
    left_inv := fun X => Subtype.ext (unspinMat_spinMat hη h X)
    right_inv := fun x => sl2CRealMat_injective
      (spinMat_unspinMat hη h (sl2CRealMat x) (sl2CRealMat_trace x)) }

/-- **L2 (on generators).** For `i ≠ j`, the equivalence `etaSkewEquivSl2C η hη h` sends the
generator `gen η i j = η j • E i j - η i • E j i` to the element of `sl(2, ℂ)` whose matrix
(`sl2CRealMat`) is `spinPlus η i j = ½ · lam (η i) · lam (η j) · quat i · quatBar j`. -/
theorem etaSkewEquivSl2C_gen (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∏ i, η i = -1) (i j : Fin 4) (hij : i ≠ j) :
    sl2CRealMat (etaSkewEquivSl2C η hη h (gen η i j)) = spinPlus η i j := by
  change spinMat η (gen η i j).1 = spinPlus η i j
  rw [gen_eq_skewMat, spinMat_skewMat hη, spinPlus_eq_spinCoords η i j hij]

/-- **L2 (Hodge operator; OPTIONAL, follows from the images of the generators).** The equivalence
`etaSkewEquivSl2C η hη h` carries `hodge η` to multiplication by the complex number
`-lamProd η`: the matrix (`sl2CRealMat`) of the image of `hodge η X` is `(-lamProd η)` times the
matrix of the image of `X`. -/
theorem etaSkewEquivSl2C_hodge (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∏ i, η i = -1) (X : etaSkew η) :
    sl2CRealMat (etaSkewEquivSl2C η hη h (hodge η X)) =
      (-lamProd η) • sl2CRealMat (etaSkewEquivSl2C η hη h X) := by
  change spinMat η (hodgeMat η X.1) = (-lamProd η) • spinMat η X.1
  exact spinMat_hodgeMat hη h X

/-- **L3, definite (the equivalence).** For `η : Fin 4 → ℝ` with every entry `1` or `-1` and all
entries equal: a Lie algebra equivalence over `ℝ` from `etaSkew η` to `so(3) × so(3)`. It is
pinned down by `etaSkewEquivSo3Prod_apply`. -/
noncomputable def etaSkewEquivSo3Prod (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∀ i j, η i = η j) : etaSkew η ≃ₗ⁅ℝ⁆ so3 × so3 :=
  { toFun := fun X => (⟨so3Plus X.1, so3Vec_mem _ _ _⟩, ⟨so3Minus X.1, so3Vec_mem _ _ _⟩)
    map_add' := fun X Y =>
      Prod.ext (Subtype.ext (so3Plus_add X.1 Y.1)) (Subtype.ext (so3Minus_add X.1 Y.1))
    map_smul' := fun r X =>
      Prod.ext (Subtype.ext (so3Plus_smul r X.1)) (Subtype.ext (so3Minus_smul r X.1))
    map_lie' := fun {X Y} =>
      Prod.ext (Subtype.ext (so3Plus_bracket hη h X Y)) (Subtype.ext (so3Minus_bracket hη h X Y))
    invFun := fun AB => ⟨unso3 η AB.1.1 AB.2.1, skewMat_mem η _ _ _ _ _ _⟩
    left_inv := fun X => Subtype.ext (unso3_so3 hη X)
    right_inv := fun AB =>
      Prod.ext
        (Subtype.ext (so3Plus_unso3 hη AB.1.1 AB.2.1
          ((LieAlgebra.Orthogonal.mem_so (Fin 3) ℝ AB.1.1).mp AB.1.2)))
        (Subtype.ext (so3Minus_unso3 hη AB.1.1 AB.2.1
          ((LieAlgebra.Orthogonal.mem_so (Fin 3) ℝ AB.2.1).mp AB.2.2))) }

/-- **L3, definite (apply).** For every `X` in `etaSkew η`, the two components of
`etaSkewEquivSo3Prod η hη h X` are the skew-symmetric `3 × 3` matrices `so3Plus X` and
`so3Minus X` (explicit in the entries `X 0 1, X 0 2, X 0 3, X 1 2, X 1 3, X 2 3`). -/
theorem etaSkewEquivSo3Prod_apply (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∀ i j, η i = η j) (X : etaSkew η) :
    ((etaSkewEquivSo3Prod η hη h X).1 : Matrix (Fin 3) (Fin 3) ℝ) = so3Plus X.1 ∧
    ((etaSkewEquivSo3Prod η hη h X).2 : Matrix (Fin 3) (Fin 3) ℝ) = so3Minus X.1 := by
  exact ⟨rfl, rfl⟩

/-- **L3, split (the equivalence).** For `η : Fin 4 → ℝ` with every entry `1` or `-1` and
`∑ i, η i = 0`: a Lie algebra equivalence over `ℝ` from `etaSkew η` to `sl(2, ℝ) × sl(2, ℝ)`. It is
pinned down by `etaSkewEquivSl2RProd_gen`. -/
noncomputable def etaSkewEquivSl2RProd (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) : etaSkew η ≃ₗ⁅ℝ⁆ sl2R × sl2R :=
  { toFun := fun X =>
      (⟨splitMatPlus η X.1, LinearMap.mem_ker.2 (splitCoordsPlus_trace hη h _ _ _ _ _ _)⟩,
        ⟨splitMatMinus η X.1, LinearMap.mem_ker.2 (splitCoordsMinus_trace hη h _ _ _ _ _ _)⟩)
    map_add' := fun X Y =>
      Prod.ext (Subtype.ext (splitMatPlus_add η X.1 Y.1))
        (Subtype.ext (splitMatMinus_add η X.1 Y.1))
    map_smul' := fun r X =>
      Prod.ext (Subtype.ext (splitMatPlus_smul η r X.1))
        (Subtype.ext (splitMatMinus_smul η r X.1))
    map_lie' := fun {X Y} =>
      Prod.ext (Subtype.ext (splitMatPlus_bracket hη h X Y))
        (Subtype.ext (splitMatMinus_bracket hη h X Y))
    invFun := fun AB => ⟨unsplitMat η AB.1.1 AB.2.1, skewMat_mem η _ _ _ _ _ _⟩
    left_inv := fun X => Subtype.ext (unsplitMat_splitMat hη h X)
    right_inv := fun AB =>
      Prod.ext
        (Subtype.ext (splitMat_unsplitMat hη h AB.1.1 AB.2.1 (LinearMap.mem_ker.1 AB.1.2)
          (LinearMap.mem_ker.1 AB.2.2)).1)
        (Subtype.ext (splitMat_unsplitMat hη h AB.1.1 AB.2.1 (LinearMap.mem_ker.1 AB.1.2)
          (LinearMap.mem_ker.1 AB.2.2)).2) }

/-- **L3, split (on generators).** For `i ≠ j`, the two components of the image of the generator
`gen η i j` under `etaSkewEquivSl2RProd η hη h` are
`splitPlus η i j = ½ · splitFrame η i · adjugate (splitFrame η j)` and
`splitMinus η i j = ½ · adjugate (splitFrame η i) · splitFrame η j`. -/
theorem etaSkewEquivSl2RProd_gen (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∑ i, η i = 0) (i j : Fin 4) (hij : i ≠ j) :
    ((etaSkewEquivSl2RProd η hη h (gen η i j)).1 : Matrix (Fin 2) (Fin 2) ℝ) = splitPlus η i j ∧
    ((etaSkewEquivSl2RProd η hη h (gen η i j)).2 : Matrix (Fin 2) (Fin 2) ℝ) =
      splitMinus η i j := by
  constructor
  · change splitMatPlus η (gen η i j).1 = splitPlus η i j
    rw [gen_eq_skewMat, splitMatPlus_skewMat hη]
    exact splitCoordsPlus_unitC hη h i j hij
  · change splitMatMinus η (gen η i j).1 = splitMinus η i j
    rw [gen_eq_skewMat, splitMatMinus_skewMat hη]
    exact splitCoordsMinus_unitC hη h i j hij

end LorentzLie
