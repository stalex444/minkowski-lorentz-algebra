module
public import Mathlib
public import LorentzLie.Defs
public import LorentzLie.Centroid
public import LorentzLie.RealForms

@[expose] public section

/-!
# Controls: the Hodge operator in Lorentzian signature, a zero entry, and simplicity

* `lorentzian_hodge_control` — for `η : Fin 4 → ℝ` with entries `±1` and `∏ i, η i = -1`, the
  operator `hodge η` is bracket-commuting, squares to `-1`, and is not a real scalar.
* `centroid_control_zero_entry` — on `etaSkew ![1, 1, 0]` there is a bracket-commuting linear
  endomorphism that is not a scalar: the hypothesis that every entry of `η` is nonzero cannot be
  dropped from `centroid_scalar`.
* `hodge_control_zero_entry` — at `η = ![1, 1, 0, -1]` the operator `hodge η` is not
  bracket-commuting.
* `etaSkew_isSimple` — for `η : Fin 4 → ℝ` with entries `±1` and `∏ i, η i = -1`, the real Lie
  algebra `etaSkew η` is simple.
* `Controls.not_isSimple_of_prod_eq_one` — for entries `±1` and `∏ i, η i = 1` it is not simple:
  the hypothesis on the product cannot be dropped from `etaSkew_isSimple`.

Simplicity is proved directly. Writing an element in the six parameters of
`skewMat4 η` (`Controls.sk`), four brackets with generators project it onto a pair of
complementary positions, two more brackets give a second element on the same pair, and a
combination of the two is a generator times `±(a ^ 2 + b ^ 2)` (`Controls.pair01`,
`Controls.pair02`, `Controls.pair03`, `Controls.pair_coeffs`); the sign pattern `∏ i, η i = -1`
is what makes the coefficient a sum of squares. One generator generates everything
(`gen_mem_of_lie_closed`, `eq_sum_gen`).

Helper declarations are in the namespace `LorentzLie.Controls`.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

namespace LorentzLie

open Matrix

/-! ### The Hodge operator in Lorentzian signature -/

/-- **L8 (operator half).** For `η : Fin 4 → ℝ` with every entry `1` or `-1` and
`∏ i, η i = -1`: `hodge η` is bracket-commuting, `hodge η (hodge η X) = -X` for all `X`, and there
is no real `c` with `hodge η = c • id`. -/
theorem lorentzian_hodge_control (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∏ i, η i = -1) :
    IsBracketCommuting (hodge η) ∧ (∀ X : etaSkew η, hodge η (hodge η X) = -X) ∧
      ¬ ∃ c : ℝ, hodge η = c • LinearMap.id := by
  have hη0 : ∀ i, η i ≠ 0 := fun i => by rcases hη i with h | h <;> rw [h] <;> norm_num
  refine ⟨fun X Y => hodge_lie two_ne_zero η hη0 X Y, fun X => ?_,
    centroid_control_card_four η hη0⟩
  rw [hodge_hodge two_ne_zero η hη0 X, h, neg_one_smul]

/-! ### Control: an entry of `η` equal to zero -/

namespace Controls

/-- The explicit map on `3 × 3` matrices used for the zero-entry control: in the basis
`A = E 0 1 - E 1 0`, `P = E 2 0`, `Q = E 2 1`, `D = E 2 2` of the matrices skew for
`diagonal ![1, 1, 0]` it is `A ↦ D`, `D ↦ -A`, `P ↦ Q`, `Q ↦ -P`. -/
def zeroEntryMat (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -X 2 2, 0; X 2 2, 0, 0; -X 2 1, X 2 0, X 0 1]

/-- `zeroEntryMat X` is skew for `diagonal ![1, 1, 0]`, for every `X`. -/
theorem zeroEntryMat_mem (X : Matrix (Fin 3) (Fin 3) ℝ) :
    zeroEntryMat X ∈ etaSkew (![1, 1, 0] : Fin 3 → ℝ) := by
  rw [mem_etaSkew_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [zeroEntryMat]

/-- Entries of a matrix skew for `diagonal ![1, 1, 0]`. -/
theorem zeroEntry_entries (X : etaSkew (![1, 1, 0] : Fin 3 → ℝ)) :
    (X : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 0 ∧ (X : Matrix (Fin 3) (Fin 3) ℝ) 1 1 = 0 ∧
    (X : Matrix (Fin 3) (Fin 3) ℝ) 1 0 = -(X : Matrix (Fin 3) (Fin 3) ℝ) 0 1 ∧
    (X : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = 0 ∧ (X : Matrix (Fin 3) (Fin 3) ℝ) 1 2 = 0 := by
  have hX := (mem_etaSkew_iff _ X.1).mp X.2
  have h00 := hX 0 0
  have h11 := hX 1 1
  have h01 := hX 0 1
  have h20 := hX 2 0
  have h21 := hX 2 1
  simp at h00 h11 h01 h20 h21
  refine ⟨by linarith, by linarith, h01, h20, h21⟩

/-- The zero-entry control as a linear endomorphism of `etaSkew ![1, 1, 0]`. -/
noncomputable def zeroEntryMap :
    etaSkew (![1, 1, 0] : Fin 3 → ℝ) →ₗ[ℝ] etaSkew (![1, 1, 0] : Fin 3 → ℝ) where
  toFun X := ⟨zeroEntryMat X.1, zeroEntryMat_mem X.1⟩
  map_add' X Y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [zeroEntryMat] <;> ring
  map_smul' c X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [zeroEntryMat]

/-- `zeroEntryMap` is bracket-commuting. -/
theorem zeroEntryMap_lie (X Y : etaSkew (![1, 1, 0] : Fin 3 → ℝ)) :
    zeroEntryMap ⁅X, Y⁆ = ⁅X, zeroEntryMap Y⁆ := by
  obtain ⟨x00, x11, x10, x02, x12⟩ := zeroEntry_entries X
  obtain ⟨y00, y11, y10, y02, y12⟩ := zeroEntry_entries Y
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  change zeroEntryMat ⁅(X : Matrix (Fin 3) (Fin 3) ℝ), (Y : Matrix (Fin 3) (Fin 3) ℝ)⁆ =
    ⁅(X : Matrix (Fin 3) (Fin 3) ℝ), zeroEntryMat (Y : Matrix (Fin 3) (Fin 3) ℝ)⁆
  rw [Ring.lie_def, Ring.lie_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroEntryMat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, x00,
      x11, x10, x02, x12, y00, y11, y10, y02, y12] <;> ring

/-- The matrix unit at `(2, 2)` is skew for `diagonal ![1, 1, 0, -1]`. -/
theorem single_two_two_mem :
    (Matrix.single 2 2 1 : Matrix (Fin 4) (Fin 4) ℝ) ∈ etaSkew (![1, 1, 0, -1] : Fin 4 → ℝ) := by
  rw [mem_etaSkew_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp

end Controls

/-- **Control of L5, hypothesis `η i ≠ 0` deleted.** On the Lie algebra of matrices skew for
`diagonal ![1, 1, 0]` there is a real-linear endomorphism `R` with `R ⁅X, Y⁆ = ⁅X, R Y⁆` for all
`X`, `Y` that is not of the form `c • id`. -/
theorem centroid_control_zero_entry :
    ∃ R : etaSkew (![1, 1, 0] : Fin 3 → ℝ) →ₗ[ℝ] etaSkew (![1, 1, 0] : Fin 3 → ℝ),
      (∀ X Y : etaSkew (![1, 1, 0] : Fin 3 → ℝ), R ⁅X, Y⁆ = ⁅X, R Y⁆) ∧
        ¬ ∃ c : ℝ, R = c • LinearMap.id := by
  refine ⟨Controls.zeroEntryMap, Controls.zeroEntryMap_lie, ?_⟩
  rintro ⟨c, hc⟩
  have h1 := congrArg (fun Z : etaSkew (![1, 1, 0] : Fin 3 → ℝ) =>
    (Z : Matrix (Fin 3) (Fin 3) ℝ) 2 2) (LinearMap.congr_fun hc (gen _ 0 1))
  simp [Controls.zeroEntryMap, Controls.zeroEntryMat, gen_coe] at h1

/-- **Control of L1K, hypothesis `η i ≠ 0` deleted (OPTIONAL).** At `η = ![1, 1, 0, -1]` part (i)
of L1K fails: there are `X`, `Y` in `etaSkew η` with `hodge η ⁅X, Y⁆ ≠ ⁅X, hodge η Y⁆`. -/
theorem hodge_control_zero_entry :
    ∃ X Y : etaSkew (![1, 1, 0, -1] : Fin 4 → ℝ),
      hodge (![1, 1, 0, -1] : Fin 4 → ℝ) ⁅X, Y⁆ ≠ ⁅X, hodge (![1, 1, 0, -1] : Fin 4 → ℝ) Y⁆ := by
  refine ⟨⟨Matrix.single 2 2 1, Controls.single_two_two_mem⟩, gen _ 0 1, fun hh => ?_⟩
  have h1 := congrArg (fun Z : etaSkew (![1, 1, 0, -1] : Fin 4 → ℝ) =>
    (Z : Matrix (Fin 4) (Fin 4) ℝ) 2 3) hh
  simp [hodgeMat, star0, gen_coe, Ring.lie_def, Matrix.mul_apply, Matrix.single_apply,
    Matrix.diagonal_apply, Matrix.vecMul, dotProduct] at h1

/-! ### Simplicity in Lorentzian signature -/

namespace Controls

/-- The matrices `skewMat4 η s` are `η`-skew. -/
theorem skewMat4_mem (η : Fin 4 → ℝ) (s01 s02 s03 s12 s13 s23 : ℝ) :
    skewMat4 η s01 s02 s03 s12 s13 s23 ∈ etaSkew η := by
  rw [mem_etaSkew_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [skewMat4] <;> ring1

/-- The element of `etaSkew η` with underlying matrix `skewMat4 η s`. -/
noncomputable def sk (η : Fin 4 → ℝ) (s01 s02 s03 s12 s13 s23 : ℝ) : etaSkew η :=
  ⟨skewMat4 η s01 s02 s03 s12 s13 s23, skewMat4_mem η s01 s02 s03 s12 s13 s23⟩

/-- Equal parameters give equal elements `sk η s`. -/
theorem sk_congr (η : Fin 4 → ℝ) {s01 s02 s03 s12 s13 s23 t01 t02 t03 t12 t13 t23 : ℝ}
    (h01 : s01 = t01) (h02 : s02 = t02) (h03 : s03 = t03) (h12 : s12 = t12) (h13 : s13 = t13)
    (h23 : s23 = t23) : sk η s01 s02 s03 s12 s13 s23 = sk η t01 t02 t03 t12 t13 t23 := by
  rw [h01, h02, h03, h12, h13, h23]

/-- The bracket of two elements `sk η s`, `sk η t`. -/
theorem sk_lie (η : Fin 4 → ℝ) (s01 s02 s03 s12 s13 s23 t01 t02 t03 t12 t13 t23 : ℝ) :
    ⁅sk η s01 s02 s03 s12 s13 s23, sk η t01 t02 t03 t12 t13 t23⁆ =
      sk η
        (η 2 * (s12 * t02 - s02 * t12) + η 3 * (s13 * t03 - s03 * t13))
        (η 1 * (s01 * t12 - s12 * t01) + η 3 * (s23 * t03 - s03 * t23))
        (η 1 * (s01 * t13 - s13 * t01) + η 2 * (s02 * t23 - s23 * t02))
        (η 0 * (s02 * t01 - s01 * t02) + η 3 * (s23 * t13 - s13 * t23))
        (η 0 * (s03 * t01 - s01 * t03) + η 2 * (s12 * t23 - s23 * t12))
        (η 0 * (s03 * t02 - s02 * t03) + η 1 * (s13 * t12 - s12 * t13)) := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  exact lie_skewMat4 η _ _ _ _ _ _ _ _ _ _ _ _

/-- A scalar multiple of `sk η s` is `sk η (c * s)`. -/
theorem sk_smul (η : Fin 4 → ℝ) (c s01 s02 s03 s12 s13 s23 : ℝ) :
    c • sk η s01 s02 s03 s12 s13 s23 =
      sk η (c * s01) (c * s02) (c * s03) (c * s12) (c * s13) (c * s23) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sk, skewMat4] <;> ring1

/-- A difference of elements `sk η s`, `sk η t` is `sk η (s - t)`. -/
theorem sk_sub (η : Fin 4 → ℝ) (s01 s02 s03 s12 s13 s23 t01 t02 t03 t12 t13 t23 : ℝ) :
    sk η s01 s02 s03 s12 s13 s23 - sk η t01 t02 t03 t12 t13 t23 =
      sk η (s01 - t01) (s02 - t02) (s03 - t03) (s12 - t12) (s13 - t13) (s23 - t23) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sk, skewMat4] <;> ring1

/-- `sk η 0 = 0`. -/
theorem sk_zero (η : Fin 4 → ℝ) : sk η 0 0 0 0 0 0 = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sk, skewMat4]

/-- Every element of `etaSkew η` is an element `sk η s`, when no entry of `η` is zero. -/
theorem exists_eq_sk (η : Fin 4 → ℝ) (hη : ∀ i, η i ≠ 0) (X : etaSkew η) :
    ∃ s01 s02 s03 s12 s13 s23 : ℝ, X = sk η s01 s02 s03 s12 s13 s23 :=
  ⟨_, _, _, _, _, _, Subtype.ext (etaSkew_eq_skewMat4 two_ne_zero η hη X)⟩

/-- `gen η 0 1` in the parameters of `sk`. -/
theorem gen_zero_one_eq_sk (η : Fin 4 → ℝ) : gen η 0 1 = sk η 1 0 0 0 0 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sk, skewMat4, gen_coe]

/-- `gen η 0 2` in the parameters of `sk`. -/
theorem gen_zero_two_eq_sk (η : Fin 4 → ℝ) : gen η 0 2 = sk η 0 1 0 0 0 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sk, skewMat4, gen_coe]

/-- `gen η 0 3` in the parameters of `sk`. -/
theorem gen_zero_three_eq_sk (η : Fin 4 → ℝ) : gen η 0 3 = sk η 0 0 1 0 0 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sk, skewMat4, gen_coe]

/-- If a submodule stable under every `⁅X, ·⁆` contains `sk η s`, it contains the multiple of
`gen η 0 3` with the displayed coefficient, a quadratic form in `s03`, `s12`. -/
theorem pair03 (η : Fin 4 → ℝ) (S : Submodule ℝ (etaSkew η))
    (hS : ∀ X : etaSkew η, ∀ Y ∈ S, ⁅X, Y⁆ ∈ S) (s01 s02 s03 s12 s13 s23 : ℝ)
    (h : sk η s01 s02 s03 s12 s13 s23 ∈ S) :
    sk η 0 0 (-(η 0 ^ 5 * η 1 ^ 2 * η 2 ^ 2 * η 3 * s03 ^ 2) +
      η 0 ^ 4 * η 1 ^ 3 * η 2 ^ 3 * s12 ^ 2) 0 0 0 ∈ S := by
  have hY := hS (sk η 0 1 0 0 0 0) _ (hS (sk η 0 1 0 0 0 0) _
    (hS (sk η 1 0 0 0 0 0) _ (hS (sk η 1 0 0 0 0 0) _ h)))
  have hZ := hS (sk η 0 0 0 0 0 1) _ (hS (sk η 1 0 0 0 0 0) _ hY)
  have hc := S.sub_mem (S.smul_mem (-(η 0 * η 3) * (η 0 ^ 2 * η 1 * η 2 * s03)) hY)
    (S.smul_mem (η 0 ^ 2 * η 1 * η 2 * s12) hZ)
  simp only [sk_lie, sk_smul, sk_sub] at hc
  convert hc using 1
  exact sk_congr η (by ring1) (by ring1) (by ring1) (by ring1) (by ring1) (by ring1)

/-- The analogue of `pair03` for `gen η 0 2`: the coefficient is a quadratic form in `s02`,
`s13`. -/
theorem pair02 (η : Fin 4 → ℝ) (S : Submodule ℝ (etaSkew η))
    (hS : ∀ X : etaSkew η, ∀ Y ∈ S, ⁅X, Y⁆ ∈ S) (s01 s02 s03 s12 s13 s23 : ℝ)
    (h : sk η s01 s02 s03 s12 s13 s23 ∈ S) :
    sk η 0 (η 0 ^ 5 * η 1 ^ 2 * η 2 * η 3 ^ 2 * s02 ^ 2 -
      η 0 ^ 4 * η 1 ^ 3 * η 3 ^ 3 * s13 ^ 2) 0 0 0 0 ∈ S := by
  have hY := hS (sk η 0 0 1 0 0 0) _ (hS (sk η 0 0 1 0 0 0) _
    (hS (sk η 1 0 0 0 0 0) _ (hS (sk η 1 0 0 0 0 0) _ h)))
  have hZ := hS (sk η 0 0 0 0 0 1) _ (hS (sk η 1 0 0 0 0 0) _ hY)
  have hc := S.sub_mem (S.smul_mem (η 0 * η 2 * (η 0 ^ 2 * η 1 * η 3 * s02)) hY)
    (S.smul_mem (η 0 ^ 2 * η 1 * η 3 * s13) hZ)
  simp only [sk_lie, sk_smul, sk_sub] at hc
  convert hc using 1
  exact sk_congr η (by ring1) (by ring1) (by ring1) (by ring1) (by ring1) (by ring1)

/-- The analogue of `pair03` for `gen η 0 1`: the coefficient is a quadratic form in `s01`,
`s23`. -/
theorem pair01 (η : Fin 4 → ℝ) (S : Submodule ℝ (etaSkew η))
    (hS : ∀ X : etaSkew η, ∀ Y ∈ S, ⁅X, Y⁆ ∈ S) (s01 s02 s03 s12 s13 s23 : ℝ)
    (h : sk η s01 s02 s03 s12 s13 s23 ∈ S) :
    sk η (η 0 ^ 5 * η 1 * η 2 ^ 2 * η 3 ^ 2 * s01 ^ 2 -
      η 0 ^ 4 * η 2 ^ 3 * η 3 ^ 3 * s23 ^ 2) 0 0 0 0 0 ∈ S := by
  have hY := hS (sk η 0 0 1 0 0 0) _ (hS (sk η 0 0 1 0 0 0) _
    (hS (sk η 0 1 0 0 0 0) _ (hS (sk η 0 1 0 0 0 0) _ h)))
  have hZ := hS (sk η 0 0 0 0 1 0) _ (hS (sk η 0 1 0 0 0 0) _ hY)
  have hc := S.sub_mem (S.smul_mem (η 0 * η 1 * (η 0 ^ 2 * η 2 * η 3 * s01)) hY)
    (S.smul_mem (η 0 ^ 2 * η 2 * η 3 * s23) hZ)
  simp only [sk_lie, sk_smul, sk_sub] at hc
  convert hc using 1
  exact sk_congr η (by ring1) (by ring1) (by ring1) (by ring1) (by ring1) (by ring1)

/-- A sum of two real squares vanishes only if both terms do. -/
theorem sq_add_sq_ne_zero {a b : ℝ} (h : ¬(a = 0 ∧ b = 0)) : a ^ 2 + b ^ 2 ≠ 0 := by
  intro h0
  apply h
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

/-- In Lorentzian signature the three coefficients of `pair01`, `pair02`, `pair03` are, up to the
signs `η 0 * η 1`, `η 0 * η 2`, `-(η 0 * η 3)`, sums of two squares. -/
theorem pair_coeffs (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∏ i, η i = -1)
    (a b : ℝ) :
    η 0 ^ 5 * η 1 * η 2 ^ 2 * η 3 ^ 2 * a ^ 2 - η 0 ^ 4 * η 2 ^ 3 * η 3 ^ 3 * b ^ 2 =
        η 0 * η 1 * (a ^ 2 + b ^ 2) ∧
      η 0 ^ 5 * η 1 ^ 2 * η 2 * η 3 ^ 2 * a ^ 2 - η 0 ^ 4 * η 1 ^ 3 * η 3 ^ 3 * b ^ 2 =
        η 0 * η 2 * (a ^ 2 + b ^ 2) ∧
      -(η 0 ^ 5 * η 1 ^ 2 * η 2 ^ 2 * η 3 * a ^ 2) + η 0 ^ 4 * η 1 ^ 3 * η 2 ^ 3 * b ^ 2 =
        -(η 0 * η 3) * (a ^ 2 + b ^ 2) := by
  rw [Fin.prod_univ_four] at h
  rcases hη 0 with h0 | h0 <;> rcases hη 1 with h1 | h1 <;> rcases hη 2 with h2 | h2 <;>
    rcases hη 3 with h3 | h3 <;> rw [h0, h1, h2, h3] at h ⊢ <;>
    first
      | (exfalso; norm_num at h; done)
      | (refine ⟨?_, ?_, ?_⟩ <;> ring1)

/-- In Lorentzian signature, a submodule of `etaSkew η` stable under every `⁅X, ·⁆` that contains
a nonzero element contains a generator `gen η a b` with `a ≠ b` (the proof produces one of
`gen η 0 1`, `gen η 0 2`, `gen η 0 3`). -/
theorem exists_gen_mem (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∏ i, η i = -1)
    (S : Submodule ℝ (etaSkew η)) (hS : ∀ X : etaSkew η, ∀ Y ∈ S, ⁅X, Y⁆ ∈ S)
    (X : etaSkew η) (hX : X ∈ S) (hX0 : X ≠ 0) :
    ∃ a b : Fin 4, a ≠ b ∧ gen η a b ∈ S := by
  have hη0 : ∀ i, η i ≠ 0 := fun i => by rcases hη i with h | h <;> rw [h] <;> norm_num
  obtain ⟨s01, s02, s03, s12, s13, s23, rfl⟩ := exists_eq_sk η hη0 X
  by_cases h03 : s03 = 0 ∧ s12 = 0
  · by_cases h02 : s02 = 0 ∧ s13 = 0
    · by_cases h01 : s01 = 0 ∧ s23 = 0
      · exfalso
        apply hX0
        rw [h01.1, h01.2, h02.1, h02.2, h03.1, h03.2]
        exact sk_zero η
      · refine ⟨0, 1, by decide, ?_⟩
        have hm := pair01 η S hS _ _ _ _ _ _ hX
        rw [(pair_coeffs η hη h s01 s23).1] at hm
        have hq : η 0 * η 1 * (s01 ^ 2 + s23 ^ 2) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (hη0 0) (hη0 1)) (sq_add_sq_ne_zero h01)
        have hm' := S.smul_mem (η 0 * η 1 * (s01 ^ 2 + s23 ^ 2))⁻¹ hm
        rw [sk_smul] at hm'
        rw [gen_zero_one_eq_sk]
        convert hm' using 1
        exact sk_congr η (inv_mul_cancel₀ hq).symm (mul_zero _).symm (mul_zero _).symm
          (mul_zero _).symm (mul_zero _).symm (mul_zero _).symm
    · refine ⟨0, 2, by decide, ?_⟩
      have hm := pair02 η S hS _ _ _ _ _ _ hX
      rw [(pair_coeffs η hη h s02 s13).2.1] at hm
      have hq : η 0 * η 2 * (s02 ^ 2 + s13 ^ 2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (hη0 0) (hη0 2)) (sq_add_sq_ne_zero h02)
      have hm' := S.smul_mem (η 0 * η 2 * (s02 ^ 2 + s13 ^ 2))⁻¹ hm
      rw [sk_smul] at hm'
      rw [gen_zero_two_eq_sk]
      convert hm' using 1
      exact sk_congr η (mul_zero _).symm (inv_mul_cancel₀ hq).symm (mul_zero _).symm
        (mul_zero _).symm (mul_zero _).symm (mul_zero _).symm
  · refine ⟨0, 3, by decide, ?_⟩
    have hm := pair03 η S hS _ _ _ _ _ _ hX
    rw [(pair_coeffs η hη h s03 s12).2.2] at hm
    have hq : -(η 0 * η 3) * (s03 ^ 2 + s12 ^ 2) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (hη0 0) (hη0 3))) (sq_add_sq_ne_zero h03)
    have hm' := S.smul_mem (-(η 0 * η 3) * (s03 ^ 2 + s12 ^ 2))⁻¹ hm
    rw [sk_smul] at hm'
    rw [gen_zero_three_eq_sk]
    convert hm' using 1
    exact sk_congr η (mul_zero _).symm (mul_zero _).symm (inv_mul_cancel₀ hq).symm
      (mul_zero _).symm (mul_zero _).symm (mul_zero _).symm

end Controls

/-- **L8 (simplicity; OPTIONAL, attempted only if cheap).** For `η : Fin 4 → ℝ` with every entry
`1` or `-1` and `∏ i, η i = -1`, the real Lie algebra `etaSkew η` is simple
(`LieAlgebra.IsSimple ℝ`). -/
theorem etaSkew_isSimple (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∏ i, η i = -1) :
    LieAlgebra.IsSimple ℝ (etaSkew η) := by
  have hη0 : ∀ i, η i ≠ 0 := fun i => by rcases hη i with h | h <;> rw [h] <;> norm_num
  refine ⟨fun I => ?_, fun hab => ?_⟩
  · by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      rw [LieSubmodule.eq_bot_iff] at hI
      push Not at hI
      obtain ⟨X, hXI, hX0⟩ := hI
      have hS : ∀ X : etaSkew η, ∀ Y ∈ (I : Submodule ℝ (etaSkew η)),
          ⁅X, Y⁆ ∈ (I : Submodule ℝ (etaSkew η)) := fun X Y hY => I.lie_mem hY
      obtain ⟨a, b, hab, hg⟩ := Controls.exists_gen_mem η hη h _ hS X hXI hX0
      have hall := gen_mem_of_lie_closed η hη0 _ hS hab hg
      rw [eq_top_iff]
      intro Y _
      change Y ∈ (I : Submodule ℝ (etaSkew η))
      rw [eq_sum_gen two_ne_zero η hη0 Y]
      exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (hall i j)
  · have h1 := hab.trivial (gen η 0 1) (gen η 1 2)
    rw [lie_gen_gen η (by decide) (by decide) (by decide)] at h1
    have h2 := congrArg (fun Z : etaSkew η => (Z : Matrix (Fin 4) (Fin 4) ℝ) 0 2) h1
    simp [gen_coe, hη0] at h2

/-! ### Control of simplicity: signature with product `1` -/

namespace Controls

/-- **Control of `etaSkew_isSimple`, the hypothesis `∏ i, η i = -1` replaced by `∏ i, η i = 1`.**
For `η : Fin 4 → ℝ` with every entry `1` or `-1` and `∏ i, η i = 1`, the real Lie algebra
`etaSkew η` is not simple: the fixed points of `hodge η` form an ideal that is neither zero nor
everything. -/
theorem not_isSimple_of_prod_eq_one (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (h : ∏ i, η i = 1) : ¬ LieAlgebra.IsSimple ℝ (etaSkew η) := by
  have hη0 : ∀ i, η i ≠ 0 := fun i => by rcases hη i with h | h <;> rw [h] <;> norm_num
  intro hs
  have hH : ∀ X Y : etaSkew η, hodge η ⁅X, Y⁆ = ⁅X, hodge η Y⁆ := hodge_lie two_ne_zero η hη0
  have hHH : ∀ X : etaSkew η, hodge η (hodge η X) = X := fun X => by
    rw [hodge_hodge two_ne_zero η hη0 X, h, one_smul]
  let I : LieIdeal ℝ (etaSkew η) :=
    { toSubmodule := LinearMap.ker (hodge η - LinearMap.id)
      lie_mem := by
        intro X Y hY
        have hY' : hodge η Y - Y = 0 := hY
        show hodge η ⁅X, Y⁆ - ⁅X, Y⁆ = 0
        rw [hH, sub_eq_zero.mp hY', sub_self] }
  have hmem : ∀ X : etaSkew η, X ∈ I ↔ hodge η X - X = 0 := fun X => Iff.rfl
  rcases hs.eq_bot_or_eq_top I with hI | hI
  · apply centroid_control_card_four η hη0
    refine ⟨-1, LinearMap.ext fun X => ?_⟩
    have hm : X + hodge η X ∈ I := by
      rw [hmem, map_add, hHH]
      abel
    rw [hI, LieSubmodule.mem_bot] at hm
    rw [LinearMap.smul_apply, LinearMap.id_apply, neg_one_smul]
    exact eq_neg_of_add_eq_zero_right hm
  · apply centroid_control_card_four η hη0
    refine ⟨1, LinearMap.ext fun X => ?_⟩
    have hm : X ∈ I := by
      rw [hI]
      exact LieSubmodule.mem_top X
    rw [hmem, sub_eq_zero] at hm
    rw [hm, LinearMap.smul_apply, LinearMap.id_apply, one_smul]

end Controls

/-! ### Simplicity for every real `η` with negative product -/

namespace Controls

/-- If the product of the entries of `η` is negative, no entry of `η` is zero. -/
theorem ne_zero_of_prod_neg (η : Fin 4 → ℝ) (h : ∏ i, η i < 0) : ∀ i, η i ≠ 0 := by
  intro i hi
  have h0 : ∏ i, η i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [h0] at h
  exact lt_irrefl _ h

/-- For real `p`, `q` with `p * q < 0`, the form `p * a ^ 2 - q * b ^ 2` vanishes only at
`a = b = 0`. -/
theorem mul_sq_sub_mul_sq_ne_zero (p q a b : ℝ) (hpq : p * q < 0) (hab : ¬(a = 0 ∧ b = 0)) :
    p * a ^ 2 - q * b ^ 2 ≠ 0 := by
  intro h0
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hpq
  have e : p ^ 2 * a ^ 2 = (p * q) * b ^ 2 := by linear_combination p * h0
  have h1 : 0 ≤ p ^ 2 * a ^ 2 := by positivity
  have h2 : (p * q) * b ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hpq.le (sq_nonneg b)
  have h3 : p ^ 2 * a ^ 2 = 0 := le_antisymm (by rw [e]; exact h2) h1
  have h4 : (p * q) * b ^ 2 = 0 := by rw [← e]; exact h3
  have ha : a = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (by simpa using h) hp
    · simpa using h
  have hb : b = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h hpq.ne
    · simpa using h
  exact hab ⟨ha, hb⟩

/-- A submodule containing a nonzero multiple of `gen η 0 1` contains `gen η 0 1`. -/
theorem gen_zero_one_mem (η : Fin 4 → ℝ) (S : Submodule ℝ (etaSkew η)) (c : ℝ) (hc : c ≠ 0)
    (hm : sk η c 0 0 0 0 0 ∈ S) : gen η 0 1 ∈ S := by
  have hm' := S.smul_mem c⁻¹ hm
  rw [sk_smul] at hm'
  rw [gen_zero_one_eq_sk]
  convert hm' using 1
  exact sk_congr η (inv_mul_cancel₀ hc).symm (mul_zero _).symm (mul_zero _).symm
    (mul_zero _).symm (mul_zero _).symm (mul_zero _).symm

/-- A submodule containing a nonzero multiple of `gen η 0 2` contains `gen η 0 2`. -/
theorem gen_zero_two_mem (η : Fin 4 → ℝ) (S : Submodule ℝ (etaSkew η)) (c : ℝ) (hc : c ≠ 0)
    (hm : sk η 0 c 0 0 0 0 ∈ S) : gen η 0 2 ∈ S := by
  have hm' := S.smul_mem c⁻¹ hm
  rw [sk_smul] at hm'
  rw [gen_zero_two_eq_sk]
  convert hm' using 1
  exact sk_congr η (mul_zero _).symm (inv_mul_cancel₀ hc).symm (mul_zero _).symm
    (mul_zero _).symm (mul_zero _).symm (mul_zero _).symm

/-- A submodule containing a nonzero multiple of `gen η 0 3` contains `gen η 0 3`. -/
theorem gen_zero_three_mem (η : Fin 4 → ℝ) (S : Submodule ℝ (etaSkew η)) (c : ℝ) (hc : c ≠ 0)
    (hm : sk η 0 0 c 0 0 0 ∈ S) : gen η 0 3 ∈ S := by
  have hm' := S.smul_mem c⁻¹ hm
  rw [sk_smul] at hm'
  rw [gen_zero_three_eq_sk]
  convert hm' using 1
  exact sk_congr η (mul_zero _).symm (mul_zero _).symm (inv_mul_cancel₀ hc).symm
    (mul_zero _).symm (mul_zero _).symm (mul_zero _).symm

/-- For real `η` with negative product, a submodule of `etaSkew η` stable under every `⁅X, ·⁆`
that contains a nonzero element contains a generator `gen η a b` with `a ≠ b`. -/
theorem exists_gen_mem_of_prod_neg (η : Fin 4 → ℝ) (h : ∏ i, η i < 0)
    (S : Submodule ℝ (etaSkew η)) (hS : ∀ X : etaSkew η, ∀ Y ∈ S, ⁅X, Y⁆ ∈ S)
    (X : etaSkew η) (hX : X ∈ S) (hX0 : X ≠ 0) :
    ∃ a b : Fin 4, a ≠ b ∧ gen η a b ∈ S := by
  have hη0 := ne_zero_of_prod_neg η h
  have hprod : η 0 * η 1 * η 2 * η 3 < 0 := by rwa [Fin.prod_univ_four] at h
  obtain ⟨s01, s02, s03, s12, s13, s23, rfl⟩ := exists_eq_sk η hη0 X
  by_cases h03 : s03 = 0 ∧ s12 = 0
  · by_cases h02 : s02 = 0 ∧ s13 = 0
    · by_cases h01 : s01 = 0 ∧ s23 = 0
      · exfalso
        apply hX0
        rw [h01.1, h01.2, h02.1, h02.2, h03.1, h03.2]
        exact sk_zero η
      · refine ⟨0, 1, by decide, ?_⟩
        have hm := pair01 η S hS _ _ _ _ _ _ hX
        have hk := mul_sq_sub_mul_sq_ne_zero (η 0 * η 1) (η 2 * η 3) s01 s23 (by nlinarith) h01
        have hsq : (η 0 ^ 2 * η 2 * η 3) ^ 2 ≠ 0 :=
          pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (hη0 0)) (hη0 2)) (hη0 3))
        have e : η 0 ^ 5 * η 1 * η 2 ^ 2 * η 3 ^ 2 * s01 ^ 2 -
            η 0 ^ 4 * η 2 ^ 3 * η 3 ^ 3 * s23 ^ 2 =
            (η 0 ^ 2 * η 2 * η 3) ^ 2 * (η 0 * η 1 * s01 ^ 2 - η 2 * η 3 * s23 ^ 2) := by ring
        exact gen_zero_one_mem η S _ (by rw [e]; exact mul_ne_zero hsq hk) hm
    · refine ⟨0, 2, by decide, ?_⟩
      have hm := pair02 η S hS _ _ _ _ _ _ hX
      have hk := mul_sq_sub_mul_sq_ne_zero (η 0 * η 2) (η 1 * η 3) s02 s13 (by nlinarith) h02
      have hsq : (η 0 ^ 2 * η 1 * η 3) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (hη0 0)) (hη0 1)) (hη0 3))
      have e : η 0 ^ 5 * η 1 ^ 2 * η 2 * η 3 ^ 2 * s02 ^ 2 -
          η 0 ^ 4 * η 1 ^ 3 * η 3 ^ 3 * s13 ^ 2 =
          (η 0 ^ 2 * η 1 * η 3) ^ 2 * (η 0 * η 2 * s02 ^ 2 - η 1 * η 3 * s13 ^ 2) := by ring
      exact gen_zero_two_mem η S _ (by rw [e]; exact mul_ne_zero hsq hk) hm
  · refine ⟨0, 3, by decide, ?_⟩
    have hm := pair03 η S hS _ _ _ _ _ _ hX
    have hk := mul_sq_sub_mul_sq_ne_zero (η 0 * η 3) (η 1 * η 2) s03 s12 (by nlinarith) h03
    have hsq : -(η 0 ^ 2 * η 1 * η 2) ^ 2 ≠ 0 :=
      neg_ne_zero.mpr
        (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (hη0 0)) (hη0 1)) (hη0 2)))
    have e : -(η 0 ^ 5 * η 1 ^ 2 * η 2 ^ 2 * η 3 * s03 ^ 2) +
        η 0 ^ 4 * η 1 ^ 3 * η 2 ^ 3 * s12 ^ 2 =
        -(η 0 ^ 2 * η 1 * η 2) ^ 2 * (η 0 * η 3 * s03 ^ 2 - η 1 * η 2 * s12 ^ 2) := by ring
    exact gen_zero_three_mem η S _ (by rw [e]; exact mul_ne_zero hsq hk) hm

/-- For every `η : Fin 4 → ℝ` with `∏ i, η i < 0`, the real Lie algebra `etaSkew η` is simple.
(No hypothesis on the size of the entries: the product being negative already makes every entry
nonzero.) -/
theorem isSimple_of_prod_neg (η : Fin 4 → ℝ) (h : ∏ i, η i < 0) :
    LieAlgebra.IsSimple ℝ (etaSkew η) := by
  have hη0 := ne_zero_of_prod_neg η h
  refine ⟨fun I => ?_, fun hab => ?_⟩
  · by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      rw [LieSubmodule.eq_bot_iff] at hI
      push Not at hI
      obtain ⟨X, hXI, hX0⟩ := hI
      have hS : ∀ X : etaSkew η, ∀ Y ∈ (I : Submodule ℝ (etaSkew η)),
          ⁅X, Y⁆ ∈ (I : Submodule ℝ (etaSkew η)) := fun X Y hY => I.lie_mem hY
      obtain ⟨a, b, hab, hg⟩ := exists_gen_mem_of_prod_neg η h _ hS X hXI hX0
      have hall := gen_mem_of_lie_closed η hη0 _ hS hab hg
      rw [eq_top_iff]
      intro Y _
      change Y ∈ (I : Submodule ℝ (etaSkew η))
      rw [eq_sum_gen two_ne_zero η hη0 Y]
      exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (hall i j)
  · have h1 := hab.trivial (gen η 0 1) (gen η 1 2)
    rw [lie_gen_gen η (by decide) (by decide) (by decide)] at h1
    have h2 := congrArg (fun Z : etaSkew η => (Z : Matrix (Fin 4) (Fin 4) ℝ) 0 2) h1
    simp [gen_coe, hη0] at h2

/-- For every `η : Fin 4 → ℝ` with no zero entry and `0 < ∏ i, η i`, the real Lie algebra
`etaSkew η` is not simple: with `r * r = ∏ i, η i`, the `r`-eigenspace of `hodge η` is an ideal
that is neither zero nor everything. -/
theorem not_isSimple_of_prod_pos (η : Fin 4 → ℝ) (hη0 : ∀ i, η i ≠ 0) (h : 0 < ∏ i, η i) :
    ¬ LieAlgebra.IsSimple ℝ (etaSkew η) := by
  intro hs
  obtain ⟨r, hrr⟩ : ∃ r : ℝ, r * r = ∏ i, η i :=
    ⟨Real.sqrt (∏ i, η i), Real.mul_self_sqrt h.le⟩
  have hH : ∀ X Y : etaSkew η, hodge η ⁅X, Y⁆ = ⁅X, hodge η Y⁆ := hodge_lie two_ne_zero η hη0
  have hHH : ∀ X : etaSkew η, hodge η (hodge η X) = (r * r) • X := fun X => by
    rw [hodge_hodge two_ne_zero η hη0 X, hrr]
  let I : LieIdeal ℝ (etaSkew η) :=
    { toSubmodule := LinearMap.ker (hodge η - r • LinearMap.id)
      lie_mem := by
        intro X Y hY
        have hY' : hodge η Y - r • Y = 0 := hY
        show hodge η ⁅X, Y⁆ - r • ⁅X, Y⁆ = 0
        rw [hH, sub_eq_zero.mp hY', lie_smul, sub_self] }
  have hmem : ∀ X : etaSkew η, X ∈ I ↔ hodge η X - r • X = 0 := fun X => Iff.rfl
  rcases hs.eq_bot_or_eq_top I with hI | hI
  · apply centroid_control_card_four η hη0
    refine ⟨-r, LinearMap.ext fun X => ?_⟩
    have hm : r • X + hodge η X ∈ I := by
      rw [hmem, map_add, map_smul, hHH, smul_add, mul_smul]
      abel
    rw [hI, LieSubmodule.mem_bot] at hm
    rw [LinearMap.smul_apply, LinearMap.id_apply, neg_smul]
    exact eq_neg_of_add_eq_zero_right hm
  · apply centroid_control_card_four η hη0
    refine ⟨r, LinearMap.ext fun X => ?_⟩
    have hm : X ∈ I := by
      rw [hI]
      exact LieSubmodule.mem_top X
    rw [hmem, sub_eq_zero] at hm
    rw [hm, LinearMap.smul_apply, LinearMap.id_apply]

/-- For `η : Fin 4 → ℝ` with no zero entry, the real Lie algebra `etaSkew η` is simple if and only
if `∏ i, η i < 0`. -/
theorem isSimple_iff_prod_neg (η : Fin 4 → ℝ) (hη0 : ∀ i, η i ≠ 0) :
    LieAlgebra.IsSimple ℝ (etaSkew η) ↔ ∏ i, η i < 0 := by
  refine ⟨fun hs => ?_, isSimple_of_prod_neg η⟩
  by_contra hneg
  have hne : ∏ i, η i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hη0 i
  exact not_isSimple_of_prod_pos η hη0 (lt_of_le_of_ne (not_lt.mp hneg) hne.symm) hs

end Controls

end LorentzLie
