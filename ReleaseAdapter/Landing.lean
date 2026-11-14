module
public import Mathlib
public import ReleaseAdapter.Carried

@[expose] public section

/-!
# The adapter lane: the place space, the mixed space of a number field, and `Spacetime`

* A1 — `placeIso`: the explicit real-linear equivalence `PlaceSpace 2 ≃ₗ[ℝ] Spacetime` with
  coordinate formula `placeLin`, with `minkowskiSquare (placeIso p) = -traceB 2 p p` and
  `time (placeIso p) = √2 · Im (p.2 0)`.
* A3, A2 — `properLorentz_iff_boost_fourSign`: a place-preserving isometry `g` of the trace form
  is carried by `placeIso` to an element of `ProperLorentz` exactly when it is
  `boost 2 β ∘ fourSign k` for some real `β` and some `k : Fin 4`; `boost_properLorentz` is the
  case of `boost 2 β` itself.
* A4 — `time_canonical_place`: an equivalence `e'` that carries minus the trace form to
  `minkowskiSquare` and `galoisConj 2` to `timeReflection` is `placeIso` followed by an orthogonal
  `3 × 3` matrix on the spatial part and a sign `s = ±1` on the time coordinate;
  `time_canonical_place_control`: the sign `s = -1` occurs.
* A5 — `mixedIso`: for a number field with a labelling of two real places and one complex place,
  the equivalence `mixedSpace K ≃ₗ[ℝ] Spacetime`, with `minkowskiSquare = -Tr_{K/ℚ}(x * x)` on the
  image of the field; `exists_mixedSpace_isometry` is the form without a labelling.
* A6 — `blockPreserving_eq_mul`, `blockPreserving_isometry_eq_id_or_neg`: for a number field `K`
  with a real place, a block-preserving real-linear endomorphism of `mixedSpace K` that maps the
  image of `K` into itself is multiplication by an element of `K`, and it is `id` or `-id` if it
  also preserves the place form; `placeBoost_not_preserves_field` is the corollary for
  `placeBoost β`, `β ≠ 0`. `isBlockPreserving_iff_placePreserving` compares the two definitions of
  place-preserving; `swapConj_control` and `automorphism_control` are the controls.

The helper declarations of A6 and A4 are in the namespace `ReleaseAdapter.LandingAux`.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

open Matrix
open scoped TensorProduct

namespace ReleaseAdapter

open YangMills HermitianExclusion
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

/-! ### A1 -/

/-- **A1 (the equivalence).** A real-linear equivalence from the place space
`PlaceSpace 2 = (Fin 2 → ℝ) × (Fin 1 → ℂ)` to `Spacetime`. It is pinned down by
`placeIso_apply`. -/
noncomputable def placeIso : PlaceSpace 2 ≃ₗ[ℝ] Spacetime :=
  { placeLin with
    invFun := fun x => (![x 0, x 1], fun _ => ⟨x 2 / √2, x 3 / √2⟩)
    left_inv := fun p => by
      have h2 : (√2 : ℝ) ≠ 0 := by positivity
      change (![(placeLin p) 0, (placeLin p) 1],
        fun _ => (⟨(placeLin p) 2 / √2, (placeLin p) 3 / √2⟩ : ℂ)) = p
      refine Prod.ext ?_ ?_
      · funext i; fin_cases i <;> simp [placeLin_apply]
      · funext j
        have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        apply Complex.ext <;> simp [placeLin_apply, h2]
    right_inv := fun x => by
      have h2 : (√2 : ℝ) ≠ 0 := by positivity
      change placeLin (![x 0, x 1], fun _ => (⟨x 2 / √2, x 3 / √2⟩ : ℂ)) = x
      ext i; fin_cases i <;> simp [placeLin_apply] <;> field_simp }

/-- **A1 (formula).** `placeIso p = placeLin p`, the vector with coordinates
`(p.1 0, p.1 1, √2 · Re (p.2 0), √2 · Im (p.2 0))`. -/
theorem placeIso_apply (p : PlaceSpace 2) : placeIso p = placeLin p := by
  rfl

/-- **A1 (form).** `minkowskiSquare (placeIso p) = -traceB 2 p p` for every `p`. -/
theorem minkowskiSquare_placeIso (p : PlaceSpace 2) :
    minkowskiSquare (placeIso p) = -traceB 2 p p := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [placeIso_apply, minkowskiSquare_coords]
  simp [placeLin, traceB, Fin.sum_univ_succ, Complex.mul_re]
  linear_combination ((p.2 0).im ^ 2 - (p.2 0).re ^ 2) * h2

/-- **A1 (time).** `time (placeIso p) = √2 · Im (p.2 0)` for every `p`. -/
theorem time_placeIso (p : PlaceSpace 2) : time (placeIso p) = √2 * (p.2 0).im := by
  rfl

/-! ### A3 and A2 -/

/-- The real `4 × 4` matrix with upper block `diag(l₀, l₁)` and lower block `[[a, b], [c, d]]`. -/
def blockMat (l₀ l₁ a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![l₀, 0, 0, 0; 0, l₁, 0, 0; 0, 0, a, b; 0, 0, c, d]

/-- The determinant of `blockMat l₀ l₁ a b c d` is `l₀ * l₁ * (a * d - b * c)`. -/
theorem det_blockMat (l₀ l₁ a b c d : ℝ) :
    (blockMat l₀ l₁ a b c d).det = l₀ * l₁ * (a * d - b * c) := by
  rw [Matrix.det_succ_row_zero]
  simp [blockMat, Fin.sum_univ_succ, Matrix.det_fin_three]
  ring

/-- The determinant of the endomorphism `Matrix.toEuclideanLin M` of `Spacetime` is `M.det`. -/
theorem det_toEuclideanLin (M : Matrix (Fin 4) (Fin 4) ℝ) :
    LinearMap.det (Matrix.toEuclideanLin M) = M.det := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

/-- In the coordinates of `placeIso`, a map of the place space that scales the two real
coordinates by `l₀`, `l₁` and acts on `(Re z, Im z)` by `[[a, b], [c, d]]` has matrix
`blockMat l₀ l₁ a b c d`. -/
theorem toEuclideanLin_blockMat (l₀ l₁ a b c d : ℝ) (p q : PlaceSpace 2)
    (h0 : q.1 0 = l₀ * p.1 0) (h1 : q.1 1 = l₁ * p.1 1)
    (hre : (q.2 0).re = a * (p.2 0).re + b * (p.2 0).im)
    (him : (q.2 0).im = c * (p.2 0).re + d * (p.2 0).im) :
    Matrix.toEuclideanLin (blockMat l₀ l₁ a b c d) (placeIso p) = placeIso q := by
  ext i
  fin_cases i <;>
    simp [placeIso_apply, placeLin_apply, blockMat, h0, h1, hre, him] <;>
    ring

/-- Two endomorphisms of `Spacetime` that agree on the image of `placeIso` are equal. -/
theorem linearMap_eq_of_placeIso {Λ Λ' : Spacetime →ₗ[ℝ] Spacetime}
    (h : ∀ p, Λ (placeIso p) = Λ' (placeIso p)) : Λ = Λ' :=
  LinearMap.ext fun x => by
    obtain ⟨p, rfl⟩ := placeIso.surjective x
    exact h p

/-- The forward cone in coordinates: the time coordinate is nonnegative and the form is
nonnegative. -/
theorem mem_forwardCone_iff (x : Spacetime) :
    x ∈ forwardCone ↔ 0 ≤ x 3 ∧ 0 ≤ minkowskiSquare x := by
  have hn : 0 ≤ ‖spatial x‖ := norm_nonneg _
  have ht : time x = x 3 := rfl
  constructor
  · intro h
    have h' : ‖spatial x‖ ≤ time x := h
    refine ⟨by rw [← ht]; linarith, ?_⟩
    rw [minkowskiSquare]
    nlinarith
  · rintro ⟨h0, h1⟩
    show ‖spatial x‖ ≤ time x
    rw [minkowskiSquare] at h1
    rw [← ht] at h0
    by_contra hlt
    have hlt := not_le.mp hlt
    have : 0 < (‖spatial x‖ - time x) * (‖spatial x‖ + time x) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

/-- A hyperbolic rotation `(u, v) ↦ (·, s u + c v)` with `c > 0`, `c² - s² = 1` keeps the sign of
`v` on the set `u² ≤ v²`. -/
theorem boost_time_nonneg_iff (c s u v : ℝ) (hc : 0 < c) (hcs : c ^ 2 - s ^ 2 = 1)
    (huv : u ^ 2 ≤ v ^ 2) : 0 ≤ s * u + c * v ↔ 0 ≤ v := by
  have e : (c * v) ^ 2 - (s * u) ^ 2 - v ^ 2 = s ^ 2 * (v ^ 2 - u ^ 2) := by
    linear_combination v ^ 2 * hcs
  have key : 0 ≤ (c * v) ^ 2 - (s * u) ^ 2 - v ^ 2 := by
    rw [e]; exact mul_nonneg (sq_nonneg s) (sub_nonneg.mpr huv)
  constructor
  · intro h
    by_contra hv
    have hv := not_le.mp hv
    have hA : c * v < 0 := mul_neg_of_pos_of_neg hc hv
    have h2 : 0 ≤ (s * u + c * v) * (s * u - c * v) := mul_nonneg h (by linarith)
    nlinarith [sq_pos_of_neg hv]
  · intro hv
    by_contra h
    have h := not_le.mp h
    have hA : 0 ≤ c * v := mul_nonneg hc.le hv
    have h2 : 0 < (-(s * u) - c * v) * (-(s * u) + c * v) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg v]

/-- A sign map `diagSign ε₀ ε₁ ε₂` whose three entries square to `1` is an involution. -/
theorem diagSign_diagSign (ε₀ ε₁ ε₂ : ℝ) (h0 : ε₀ * ε₀ = 1) (h1 : ε₁ * ε₁ = 1)
    (h2 : ε₂ * ε₂ = 1) (p : PlaceSpace 2) :
    diagSign ε₀ ε₁ ε₂ (diagSign ε₀ ε₁ ε₂ p) = p := by
  refine Prod.ext ?_ ?_
  · funext i; fin_cases i <;> simp [diagSign, ← mul_assoc, h0, h1]
  · funext j; apply Complex.ext <;> simp [diagSign, ← mul_assoc, h2]

/-- A sign map `diagSign ε₀ ε₁ ε₂` whose three entries square to `1` preserves the trace form. -/
theorem traceB_diagSign (ε₀ ε₁ ε₂ : ℝ) (h0 : ε₀ * ε₀ = 1) (h1 : ε₁ * ε₁ = 1)
    (h2 : ε₂ * ε₂ = 1) (X Y : PlaceSpace 2) :
    traceB 2 (diagSign ε₀ ε₁ ε₂ X) (diagSign ε₀ ε₁ ε₂ Y) = traceB 2 X Y := by
  simp [traceB, diagSign, Fin.sum_univ_succ, Complex.mul_re]
  linear_combination (X.1 0 * Y.1 0) * h0 + (X.1 1 * Y.1 1) * h1 +
    (2 * (X.2 0).re * (Y.2 0).re) * h2

/-- The real part of `boostC β z` is `cosh β · Re z + sinh β · Im z`. -/
theorem boostC_re (β : ℝ) (z : ℂ) :
    (boostC β z).re = Real.cosh β * z.re + Real.sinh β * z.im := by
  simp only [boostC, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The imaginary part of `boostC β z` is `sinh β · Re z + cosh β · Im z`. -/
theorem boostC_im (β : ℝ) (z : ℂ) :
    (boostC β z).im = Real.sinh β * z.re + Real.cosh β * z.im := by
  simp only [boostC, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The formula for `boost 2 β (diagSign ε₀ ε₁ ε₂ p)`. -/
theorem boost_diagSign_apply (ε₀ ε₁ ε₂ β : ℝ) (p : PlaceSpace 2) :
    boost 2 β (diagSign ε₀ ε₁ ε₂ p) =
      (![ε₀ * p.1 0, ε₁ * p.1 1], fun j => boostC β ⟨ε₂ * (p.2 j).re, (p.2 j).im⟩) :=
  rfl

/-- The boost of the complex place composed with a sign map `diag(ε₀, ε₁, ε₂, 1)` of determinant
one is carried by `placeIso` to an element of `ProperLorentz`. -/
theorem exists_properLorentz_boost_diagSign (ε₀ ε₁ ε₂ β : ℝ) (h0 : ε₀ * ε₀ = 1)
    (h1 : ε₁ * ε₁ = 1) (h2 : ε₂ * ε₂ = 1) (hdet : ε₀ * ε₁ * ε₂ = 1) :
    ∃ Λ : ProperLorentz,
      ∀ p, Λ.val.val (placeIso p) = placeIso (boost 2 β (diagSign ε₀ ε₁ ε₂ p)) := by
  let g : PlaceSpace 2 ≃ₗ[ℝ] PlaceSpace 2 :=
    LinearEquiv.ofLinearMap ((boost 2 β).comp (diagSign ε₀ ε₁ ε₂))
      ((diagSign ε₀ ε₁ ε₂).comp (boost 2 (-β)))
      (LinearMap.ext fun q => by
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [diagSign_diagSign ε₀ ε₁ ε₂ h0 h1 h2, boost_boost, add_neg_cancel, boost_zero])
      (LinearMap.ext fun q => by
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [boost_neg_boost, diagSign_diagSign ε₀ ε₁ ε₂ h0 h1 h2])
  let E : Spacetime ≃ₗ[ℝ] Spacetime := (placeIso.symm.trans g).trans placeIso
  have hE : ∀ p, E (placeIso p) = placeIso (boost 2 β (diagSign ε₀ ε₁ ε₂ p)) := fun p => by
    show placeIso (g (placeIso.symm (placeIso p))) = _
    rw [placeIso.symm_apply_apply]
    rfl
  have hM : ∀ p, Matrix.toEuclideanLin
      (blockMat ε₀ ε₁ (ε₂ * Real.cosh β) (Real.sinh β) (ε₂ * Real.sinh β) (Real.cosh β))
      (placeIso p) = placeIso (boost 2 β (diagSign ε₀ ε₁ ε₂ p)) := fun p => by
    apply toEuclideanLin_blockMat <;> simp [boost_diagSign_apply, boostC_re, boostC_im] <;> ring
  have hEM : E.toLinearMap = Matrix.toEuclideanLin
      (blockMat ε₀ ε₁ (ε₂ * Real.cosh β) (Real.sinh β) (ε₂ * Real.sinh β) (Real.cosh β)) :=
    linearMap_eq_of_placeIso fun p => by rw [hM]; exact hE p
  have hform : ∀ x, minkowskiSquare (E x) = minkowskiSquare x := fun x => by
    obtain ⟨p, rfl⟩ := placeIso.surjective x
    rw [hE, minkowskiSquare_placeIso, minkowskiSquare_placeIso, traceB_boost,
      traceB_diagSign ε₀ ε₁ ε₂ h0 h1 h2]
  have htime : ∀ x : Spacetime,
      (E x) 3 = (ε₂ * Real.sinh β) * x 2 + Real.cosh β * x 3 := fun x => by
    have hx : E x = Matrix.toEuclideanLin
        (blockMat ε₀ ε₁ (ε₂ * Real.cosh β) (Real.sinh β) (ε₂ * Real.sinh β) (Real.cosh β)) x :=
      LinearMap.congr_fun hEM x
    rw [hx]
    simp [blockMat, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_succ]
  refine ⟨⟨⟨LinearMap.toContinuousLinearMap E.toLinearMap,
      LinearMap.toContinuousLinearMap E.symm.toLinearMap,
      ContinuousLinearMap.ext fun x => E.apply_symm_apply x,
      ContinuousLinearMap.ext fun x => E.symm_apply_apply x⟩, ?_, ?_, ?_⟩, fun p => hE p⟩
  · show LinearMap.det E.toLinearMap = 1
    rw [hEM, det_toEuclideanLin, det_blockMat]
    have hc := Real.cosh_sq β
    linear_combination (ε₀ * ε₁ * ε₂) * hc + hdet
  · exact hform
  · intro x
    show E x ∈ forwardCone ↔ x ∈ forwardCone
    rw [mem_forwardCone_iff, mem_forwardCone_iff, hform, htime]
    refine and_congr_left fun hx => ?_
    refine boost_time_nonneg_iff _ _ _ _ (Real.cosh_pos β) ?_ ?_
    · have hc := Real.cosh_sq β
      linear_combination hc - Real.sinh β ^ 2 * h2
    · rw [minkowskiSquare_coords] at hx
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- **A3.** Let `g` be a linear endomorphism of `PlaceSpace 2` that is place-preserving
(`PlacePreserving g`) and an isometry of the trace form (`IsIsometry g`). Then the following are
equivalent: (a) there is `Λ` in `ProperLorentz` with `Λ (placeIso p) = placeIso (g p)` for all
`p`; (b) there are a real `β` and an index `k : Fin 4` with `g p = boost 2 β (fourSign k p)` for
all `p`, where `fourSign` lists the sign maps `diag(1, 1, 1, 1)`, `diag(-1, -1, 1, 1)`,
`diag(1, -1, -1, 1)`, `diag(-1, 1, -1, 1)` in the coordinates `(a, b, Re z, Im z)`. -/
theorem properLorentz_iff_boost_fourSign (g : PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2)
    (hP : PlacePreserving g) (hg : IsIsometry g) :
    (∃ Λ : ProperLorentz, ∀ p, Λ.val.val (placeIso p) = placeIso (g p)) ↔
      ∃ (β : ℝ) (k : Fin 4), ∀ p, g p = boost 2 β (fourSign k p) := by
  constructor
  · rintro ⟨Λ, hΛ⟩
    obtain ⟨hdet, -, hcone⟩ := Λ.property
    obtain ⟨ε, ε', β, hε, hε', hcase⟩ := placePreserving_isometry_classification g hP hg
    have hx₀ : placeIso ((0 : Fin 2 → ℝ), fun _ => Complex.I) ∈ forwardCone := by
      rw [mem_forwardCone_iff, minkowskiSquare_placeIso]
      constructor
      · show 0 ≤ time (placeIso ((0 : Fin 2 → ℝ), fun _ => Complex.I))
        rw [time_placeIso]
        simp
      · simp [traceB]
    have ht : 0 ≤ time (Λ.val.val (placeIso ((0 : Fin 2 → ℝ), fun _ => Complex.I))) :=
      ((mem_forwardCone_iff _).mp ((hcone _).mpr hx₀)).1
    rw [hΛ, time_placeIso] at ht
    have ht' : 0 ≤ ((g ((0 : Fin 2 → ℝ), fun _ => Complex.I)).2 0).im :=
      (mul_nonneg_iff_of_pos_left (by positivity)).mp ht
    have hc := Real.cosh_sq β
    have hcp := Real.cosh_pos β
    rcases hcase with hA | hB
    · have hM : ∀ p, Matrix.toEuclideanLin
          (blockMat (ε 0) (ε 1) (ε' * Real.cosh β) (ε' * Real.sinh β) (ε' * Real.sinh β)
            (ε' * Real.cosh β)) (placeIso p) = placeIso (g p) := fun p => by
        apply toEuclideanLin_blockMat <;> simp [hA, boostC_re, boostC_im] <;> ring
      have hEM : Λ.val.val.toLinearMap = Matrix.toEuclideanLin
          (blockMat (ε 0) (ε 1) (ε' * Real.cosh β) (ε' * Real.sinh β) (ε' * Real.sinh β)
            (ε' * Real.cosh β)) :=
        linearMap_eq_of_placeIso fun p => by rw [hM]; exact hΛ p
      rw [hEM, det_toEuclideanLin, det_blockMat] at hdet
      have hε'1 : ε' = 1 := by
        rcases hε' with h | h
        · exact h
        · exfalso
          rw [hA, h] at ht'
          simp [boostC_im] at ht'
          linarith
      have h01 : ε 0 * ε 1 = 1 := by
        rw [hε'1] at hdet
        linear_combination hdet - (ε 0 * ε 1) * hc
      rcases hε 0 with e0 | e0 <;> rcases hε 1 with e1 | e1
      · refine ⟨β, 0, fun p => ?_⟩
        rw [hA p]
        show _ = boost 2 β (diagSign 1 1 1 p)
        rw [boost_diagSign_apply]
        refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
        · fin_cases i <;> simp [e0, e1]
        · apply Complex.ext <;> simp [boostC_re, boostC_im, hε'1]
      · exfalso; rw [e0, e1] at h01; norm_num at h01
      · exfalso; rw [e0, e1] at h01; norm_num at h01
      · refine ⟨β, 1, fun p => ?_⟩
        rw [hA p]
        show _ = boost 2 β (diagSign (-1) (-1) 1 p)
        rw [boost_diagSign_apply]
        refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
        · fin_cases i <;> simp [e0, e1]
        · apply Complex.ext <;> simp [boostC_re, boostC_im, hε'1]
    · have hM : ∀ p, Matrix.toEuclideanLin
          (blockMat (ε 0) (ε 1) (ε' * Real.cosh β) (-(ε' * Real.sinh β)) (ε' * Real.sinh β)
            (-(ε' * Real.cosh β))) (placeIso p) = placeIso (g p) := fun p => by
        apply toEuclideanLin_blockMat <;> simp [hB, boostC_re, boostC_im] <;> ring
      have hEM : Λ.val.val.toLinearMap = Matrix.toEuclideanLin
          (blockMat (ε 0) (ε 1) (ε' * Real.cosh β) (-(ε' * Real.sinh β)) (ε' * Real.sinh β)
            (-(ε' * Real.cosh β))) :=
        linearMap_eq_of_placeIso fun p => by rw [hM]; exact hΛ p
      rw [hEM, det_toEuclideanLin, det_blockMat] at hdet
      have hε'1 : ε' = -1 := by
        rcases hε' with h | h
        · exfalso
          rw [hB, h] at ht'
          simp [boostC_im] at ht'
          linarith
        · exact h
      have h01 : ε 0 * ε 1 = -1 := by
        rw [hε'1] at hdet
        linear_combination -hdet - (ε 0 * ε 1) * hc
      rcases hε 0 with e0 | e0 <;> rcases hε 1 with e1 | e1
      · exfalso; rw [e0, e1] at h01; norm_num at h01
      · refine ⟨β, 2, fun p => ?_⟩
        rw [hB p]
        show _ = boost 2 β (diagSign 1 (-1) (-1) p)
        rw [boost_diagSign_apply]
        refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
        · fin_cases i <;> simp [e0, e1]
        · apply Complex.ext <;> simp [boostC_re, boostC_im, hε'1] <;> ring
      · refine ⟨β, 3, fun p => ?_⟩
        rw [hB p]
        show _ = boost 2 β (diagSign (-1) 1 (-1) p)
        rw [boost_diagSign_apply]
        refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
        · fin_cases i <;> simp [e0, e1]
        · apply Complex.ext <;> simp [boostC_re, boostC_im, hε'1] <;> ring
      · exfalso; rw [e0, e1] at h01; norm_num at h01
  · rintro ⟨β, k, hk⟩
    have key : ∃ Λ : ProperLorentz,
        ∀ p, Λ.val.val (placeIso p) = placeIso (boost 2 β (fourSign k p)) := by
      fin_cases k
      · exact exists_properLorentz_boost_diagSign 1 1 1 β (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
      · exact exists_properLorentz_boost_diagSign (-1) (-1) 1 β (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
      · exact exists_properLorentz_boost_diagSign 1 (-1) (-1) β (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
      · exact exists_properLorentz_boost_diagSign (-1) 1 (-1) β (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)
    obtain ⟨Λ, hΛ⟩ := key
    exact ⟨Λ, fun p => by rw [hk]; exact hΛ p⟩

/-- **A2 (corollary of A3).** For every real `β` there is `Λ` in `ProperLorentz` with
`Λ (placeIso p) = placeIso (boost 2 β p)` for all `p`. -/
theorem boost_properLorentz (β : ℝ) :
    ∃ Λ : ProperLorentz, ∀ p, Λ.val.val (placeIso p) = placeIso (boost 2 β p) := by
  refine (properLorentz_iff_boost_fourSign (boost 2 β) (boost_placePreserving β)
    (boost_isIsometry β)).mpr ⟨β, 0, fun p => ?_⟩
  show boost 2 β p = boost 2 β (diagSign 1 1 1 p)
  congr 1
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · fin_cases i <;> simp [diagSign]
  · apply Complex.ext <;> simp [diagSign]

section A5

variable {K : Type*} [Field K] [NumberField K]

/-- **A5 (the equivalence for a labelling).** For a number field `K`, a labelling `e₁` of its
real places by `Fin 2` and a labelling `e₂` of its complex places by `Fin 1`: a real-linear
equivalence from `mixedSpace K` to `Spacetime`. It is pinned down by `mixedIso_apply`. -/
noncomputable def mixedIso (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) : mixedSpace K ≃ₗ[ℝ] Spacetime :=
  (relabel e₁ e₂).trans placeIso

/-- **A5 (formula).** `mixedIso e₁ e₂ v = placeLin (relabel e₁ e₂ v)`: the vector with
coordinates `(v.1 (e₁.symm 0), v.1 (e₁.symm 1), √2 · Re (v.2 (e₂.symm 0)),
√2 · Im (v.2 (e₂.symm 0)))`. -/
theorem mixedIso_apply (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (v : mixedSpace K) :
    mixedIso e₁ e₂ v = placeLin (relabel e₁ e₂ v) := by
  rfl

open scoped Classical in
/-- **A5 (form, on the whole mixed space).** `minkowskiSquare (mixedIso e₁ e₂ v)` is minus the
place form `Σ x_w² + Σ 2 Re(z_w²)` of `v`, for every `v` in `mixedSpace K`. -/
theorem minkowskiSquare_mixedIso (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (v : mixedSpace K) :
    minkowskiSquare (mixedIso e₁ e₂ v) =
      -placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w} v := by
  have h := minkowskiSquare_placeIso (relabel e₁ e₂ v)
  rw [placeIso_apply] at h
  rw [mixedIso_apply, h, traceB_self]
  congr 1
  obtain ⟨x, z⟩ := v
  rw [relabel_apply, placeForm_apply, placeForm_apply,
    Equiv.sum_comp e₁.symm (fun w => x w ^ 2), Equiv.sum_comp e₂.symm (fun w => 2 * (z w ^ 2).re)]

/-- **A5 (form, on the field).** `minkowskiSquare (mixedIso e₁ e₂ (mixedEmbedding K x)) =
-Tr_{K/ℚ}(x * x)` for every `x` in `K`. -/
theorem minkowskiSquare_mixedIso_mixedEmbedding
    (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (x : K) :
    minkowskiSquare (mixedIso e₁ e₂ (mixedEmbedding K x)) =
      -((Algebra.trace ℚ K (x * x) : ℚ) : ℝ) := by
  rw [minkowskiSquare_mixedIso, trace_sq_eq_placeForm]

/-- **A5 (time).** `time (mixedIso e₁ e₂ (mixedEmbedding K x))` is `√2` times the imaginary part
of the image of `x` under the embedding `(e₂.symm 0).1.embedding` chosen by Mathlib for the
complex place labelled `0`. -/
theorem time_mixedIso_mixedEmbedding (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (x : K) :
    time (mixedIso e₁ e₂ (mixedEmbedding K x)) = √2 * ((e₂.symm 0).1.embedding x).im := by
  have h := time_placeIso (relabel e₁ e₂ (mixedEmbedding K x))
  rw [placeIso_apply] at h
  rw [mixedIso_apply, h, relabel_apply, mixedEmbedding_apply_isComplex]

variable (K) in
/-- **A5 (existential corollary).** If `K` has exactly two real places and exactly one complex
place, there is a real-linear equivalence `e` from `mixedSpace K` to `Spacetime` with
`minkowskiSquare (e (mixedEmbedding K x)) = -Tr_{K/ℚ}(x * x)` for every `x` in `K`. -/
theorem exists_mixedSpace_isometry (h1 : nrRealPlaces K = 2) (h2 : nrComplexPlaces K = 1) :
    ∃ e : mixedSpace K ≃ₗ[ℝ] Spacetime, ∀ x : K,
      minkowskiSquare (e (mixedEmbedding K x)) = -((Algebra.trace ℚ K (x * x) : ℚ) : ℝ) := by
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := nonempty_labelling_iff.mpr ⟨h1, h2⟩
  exact ⟨mixedIso e₁ e₂, minkowskiSquare_mixedIso_mixedEmbedding e₁ e₂⟩

end A5

/-! ### A6 -/

namespace LandingAux

section Places

variable {ι₁ ι₂ : Type*}

/-- Two real-linear maps out of `(ι₁ → ℝ) × (ι₂ → ℂ)` (finite index types) that agree on the
vectors supported on one real coordinate and on the vectors supported on one complex coordinate
are equal. -/
theorem linearMap_ext_single [Finite ι₁] [Finite ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {M : Type*} [AddCommGroup M] [Module ℝ M] {f g : ((ι₁ → ℝ) × (ι₂ → ℂ)) →ₗ[ℝ] M}
    (h1 : ∀ (i : ι₁) (a : ℝ), f (Pi.single i a, 0) = g (Pi.single i a, 0))
    (h2 : ∀ (j : ι₂) (z : ℂ), f (0, Pi.single j z) = g (0, Pi.single j z)) : f = g := by
  apply LinearMap.prod_ext
  · apply LinearMap.pi_ext
    intro i a
    simpa using h1 i a
  · apply LinearMap.pi_ext
    intro j z
    simpa using h2 j z

/-- A block-preserving map acts on each real coordinate by a real scalar. -/
theorem isBlockPreserving_real_coord [Finite ι₁] [Finite ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (T : ((ι₁ → ℝ) × (ι₂ → ℂ)) →ₗ[ℝ] ((ι₁ → ℝ) × (ι₂ → ℂ))) (hT : IsBlockPreserving T)
    (i : ι₁) (v : (ι₁ → ℝ) × (ι₂ → ℂ)) :
    (T v).1 i = (T (Pi.single i 1, 0)).1 i * v.1 i := by
  have key : (LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι₁ → ℝ) (ι₂ → ℂ)) ∘ₗ T =
      (T (Pi.single i 1, 0)).1 i •
        (LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι₁ → ℝ) (ι₂ → ℂ)) := by
    apply linearMap_ext_single
    · intro i' a
      by_cases hi : i' = i
      · subst hi
        have ha : ((Pi.single i' a : ι₁ → ℝ), (0 : ι₂ → ℂ)) =
            a • ((Pi.single i' 1 : ι₁ → ℝ), (0 : ι₂ → ℂ)) := by
          refine Prod.ext ?_ (by simp)
          funext k
          by_cases hk : k = i' <;> simp [hk]
        rw [ha, map_smul]
        simp [mul_comm]
      · have h0 := (hT.1 i' ((Pi.single i' a : ι₁ → ℝ), (0 : ι₂ → ℂ))
          (fun k hk => by simp [hk]) rfl).1 i (Ne.symm hi)
        simp [h0, Ne.symm hi]
    · intro j z
      have h0 := (hT.2 j ((0 : ι₁ → ℝ), (Pi.single j z : ι₂ → ℂ)) rfl
          (fun k hk => by simp [hk])).1
      simp [h0]
  have h := LinearMap.congr_fun key v
  simpa using h

/-- The boost `placeBoost β` is block-preserving. -/
theorem placeBoost_isBlockPreserving (β : ℝ) :
    IsBlockPreserving (placeBoost β : ((ι₁ → ℝ) × (ι₂ → ℂ)) →ₗ[ℝ] ((ι₁ → ℝ) × (ι₂ → ℂ))) := by
  refine ⟨fun i v h1 h2 => ⟨h1, ?_⟩, fun j v h1 h2 => ⟨h1, fun j' hj => ?_⟩⟩
  · funext j; simp [placeBoost_apply, h2, boostC]
  · simp [placeBoost_apply, h2 j' hj, boostC]

end Places

section Field

variable {K : Type*} [Field K] [NumberField K]

/-- The mixed embedding carries multiplication by a rational number to multiplication by the same
number seen as a real number. -/
theorem mixedEmbedding_rat_smul (q : ℚ) (y : K) :
    mixedEmbedding K (q • y) = (q : ℝ) • mixedEmbedding K y := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simp [Rat.smul_def]
  · simp [Rat.smul_def]

/-- The image of `x` in the mixed space, expanded in the basis `latticeBasis K` with the
rational coordinates of `x` in `integralBasis K`. -/
theorem mixedEmbedding_eq_sum (x : K) :
    mixedEmbedding K x =
      ∑ i, ((integralBasis K).repr x i : ℝ) • latticeBasis K i := by
  conv_lhs => rw [← (latticeBasis K).sum_repr (mixedEmbedding K x)]
  exact Finset.sum_congr rfl fun i _ => by rw [latticeBasis_repr_apply]

/-- The real-linear map of the mixed space that sends the image of `b` to the image of `σ b` for
every `b` in the integral basis sends the image of `x` to the image of `σ x` for every `x`. -/
theorem constr_mixedEmbedding (σ : K ≃+* K) (x : K) :
    (latticeBasis K).constr ℝ (fun i => mixedEmbedding K (σ (integralBasis K i)))
      (mixedEmbedding K x) = mixedEmbedding K (σ x) := by
  have hx : σ x = ∑ i, (integralBasis K).repr x i • σ (integralBasis K i) := by
    conv_lhs => rw [← (integralBasis K).sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Rat.smul_def, Rat.smul_def, map_mul, map_ratCast]
  rw [mixedEmbedding_eq_sum x, map_sum, hx, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, mixedEmbedding_rat_smul]

end Field

section Coord

/-- The point of the place space with place coordinates `u = (a, b, Re z, Im z)`. -/
def placeVec (u : Fin 4 → ℝ) : PlaceSpace 2 := (![u 0, u 1], fun _ => ⟨u 2, u 3⟩)

/-- The place coordinates of `placeVec u` are `u`. -/
theorem placeCoords_placeVec (u : Fin 4 → ℝ) : placeCoords (placeVec u) = u := by
  funext i; fin_cases i <;> simp [placeCoords, placeVec]

/-- The matrix of a real-linear map from the place space to `Spacetime`, from place coordinates
to the standard coordinates. -/
def coordMat (e : PlaceSpace 2 →ₗ[ℝ] Spacetime) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => e (placeVec (Pi.single j 1)) i

/-- A point of the place space is the combination of the four points `placeVec (Pi.single j 1)`
with its place coordinates as coefficients. -/
theorem eq_sum_placeVec (p : PlaceSpace 2) :
    p = ∑ j, placeCoords p j • placeVec (Pi.single j 1) := by
  rw [Fin.sum_univ_four]
  refine Prod.ext ?_ ?_
  · funext i; fin_cases i <;> simp [placeCoords, placeVec]
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    apply Complex.ext <;> simp [placeCoords, placeVec]

/-- The coordinates of `e p` are `coordMat e` applied to the place coordinates of `p`. -/
theorem coordMat_mulVec (e : PlaceSpace 2 →ₗ[ℝ] Spacetime) (p : PlaceSpace 2) (i : Fin 4) :
    e p i = (coordMat e).mulVec (placeCoords p) i := by
  conv_lhs => rw [eq_sum_placeVec p]
  rw [map_sum]
  simp only [map_smul, Fin.sum_univ_four, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, coordMat, Matrix.of_apply]
  ring

/-- Two symmetric real matrices with the same quadratic form are equal. -/
theorem matrix_eq_of_quadratic {n : Type*} [Fintype n] [DecidableEq n] (M N : Matrix n n ℝ)
    (hM : Mᵀ = M) (hN : Nᵀ = N)
    (h : ∀ u : n → ℝ, u ⬝ᵥ M.mulVec u = u ⬝ᵥ N.mulVec u) : M = N := by
  ext i j
  have hii := h (Pi.single i 1)
  have hjj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single_one,
    single_one_dotProduct, Matrix.col_apply] at hii hjj hij
  have hMs : M j i = M i j := congrFun (congrFun hM i) j
  have hNs : N j i = N i j := congrFun (congrFun hN i) j
  linarith

end Coord

section Canonical

/-- The quadratic form of `η4` is `y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - y 3 ^ 2`. -/
theorem η4_dotProduct (y : Fin 4 → ℝ) :
    y ⬝ᵥ η4.mulVec y = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - y 3 ^ 2 := by
  simp [η4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The matrix `Preg` changes the sign of the last coordinate. -/
theorem Preg_mulVec (y : Fin 4 → ℝ) : Preg.mulVec y = ![y 0, y 1, y 2, -y 3] := by
  funext i; fin_cases i <;> simp [Preg, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The matrix, from place coordinates to standard coordinates, of an equivalence that carries
minus the trace form to `minkowskiSquare` and Galois conjugation to the time reflection is
`blockDiag R s * Smat` with `R` orthogonal and `s = ±1`. -/
theorem coordMat_eq_blockDiag (e' : PlaceSpace 2 ≃ₗ[ℝ] Spacetime)
    (hQ : ∀ p, minkowskiSquare (e' p) = -traceB 2 p p)
    (hc : ∀ p, e' (galoisConj 2 p) = timeReflection (e' p)) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ), Rᵀ * R = 1 ∧ (s = 1 ∨ s = -1) ∧
      coordMat (e' : PlaceSpace 2 →ₗ[ℝ] Spacetime) = blockDiag R s * Smat := by
  have hcoord : ∀ p i, e' p i =
      (coordMat (e' : PlaceSpace 2 →ₗ[ℝ] Spacetime)).mulVec (placeCoords p) i :=
    fun p i => coordMat_mulVec (e' : PlaceSpace 2 →ₗ[ℝ] Spacetime) p i
  generalize coordMat (e' : PlaceSpace 2 →ₗ[ℝ] Spacetime) = Λ at hcoord ⊢
  have hη : η4ᵀ = η4 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [η4]
  have hTs : Tarithᵀ = Tarith := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Tarith]
  have hT : Λᵀ * η4 * Λ = Tarith := by
    refine matrix_eq_of_quadratic _ _ ?_ hTs ?_
    · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hη,
        Matrix.mul_assoc]
    · intro u
      have h := hQ (placeVec u)
      rw [minkowskiSquare_coords, traceB_eq_placeCoords, hcoord, hcoord, hcoord, hcoord,
        placeCoords_placeVec] at h
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose, η4_dotProduct]
      linarith
  have hcm : Λ * cArith = Preg * Λ := by
    apply Matrix.mulVec_injective
    funext u
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h := hc (placeVec u)
    funext i
    have hi := congrArg (fun x : Spacetime => x i) h
    simp only [] at hi
    rw [hcoord, placeCoords_galoisConj, placeCoords_placeVec] at hi
    rw [hi, Preg_mulVec]
    have hu : ∀ k, e' (placeVec u) k = Λ.mulVec u k := fun k => by
      rw [hcoord, placeCoords_placeVec]
    fin_cases i <;> simp [timeReflection, hu]
  have hB : (Tinv * Λᵀ * η4) * Λ = 1 := by
    calc Tinv * Λᵀ * η4 * Λ = Tinv * (Λᵀ * η4 * Λ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, Tinv_mul_T]
  exact time_canonical' Λ hT ((conj_eq_iff Λ _ hB cArith Preg).mpr hcm)

end Canonical

end LandingAux

section A6

variable (K : Type*) [Field K] [NumberField K]

/-- **A6 (first part).** Let `K` be a number field with at least one real place, and let `T` be a
real-linear endomorphism of `mixedSpace K` that is block-preserving (`IsBlockPreserving T`: each
real coordinate line and each complex coordinate block is mapped into itself) and maps the image
of `K` into itself (for every `x` in `K` there is `y` in `K` with
`T (mixedEmbedding K x) = mixedEmbedding K y`). Then there is `c` in `K` with
`T v = mixedEmbedding K c * v` for every `v` in `mixedSpace K`. -/
theorem blockPreserving_eq_mul (hr : ∃ w : InfinitePlace K, IsReal w)
    (T : mixedSpace K →ₗ[ℝ] mixedSpace K) (hT : IsBlockPreserving T)
    (hK : ∀ x : K, ∃ y : K, T (mixedEmbedding K x) = mixedEmbedding K y) :
    ∃ c : K, ∀ v : mixedSpace K, T v = mixedEmbedding K c * v := by
  classical
  obtain ⟨w₀, hw₀⟩ := hr
  choose f hf using hK
  have ht : ∀ x : K, embedding_of_isReal hw₀ (f x) =
      (T (Pi.single ⟨w₀, hw₀⟩ 1, 0)).1 ⟨w₀, hw₀⟩ * embedding_of_isReal hw₀ x := by
    intro x
    have h := LandingAux.isBlockPreserving_real_coord T hT ⟨w₀, hw₀⟩ (mixedEmbedding K x)
    rw [hf x] at h
    simpa using h
  have hc : embedding_of_isReal hw₀ (f 1) = (T (Pi.single ⟨w₀, hw₀⟩ 1, 0)).1 ⟨w₀, hw₀⟩ := by
    simpa using ht 1
  have hfx : ∀ x : K, f x = f 1 * x := fun x =>
    (embedding_of_isReal hw₀).injective (by rw [ht, map_mul, hc])
  have hTeq : T = LinearMap.mulLeft ℝ (mixedEmbedding K (f 1)) := by
    apply (latticeBasis K).ext
    intro i
    rw [latticeBasis_apply, hf, hfx, map_mul]
    rfl
  exact ⟨f 1, fun v => by rw [hTeq]; rfl⟩

open scoped Classical in
/-- **A6 (second part).** With the hypotheses of the first part, if moreover `T` preserves the
place form (`placeForm (T v) = placeForm v` for every `v`), then `T = id` or `T = -id`. -/
theorem blockPreserving_isometry_eq_id_or_neg (hr : ∃ w : InfinitePlace K, IsReal w)
    (T : mixedSpace K →ₗ[ℝ] mixedSpace K) (hT : IsBlockPreserving T)
    (hK : ∀ x : K, ∃ y : K, T (mixedEmbedding K x) = mixedEmbedding K y)
    (hQ : ∀ v : mixedSpace K,
      placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w} (T v) =
        placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w} v) :
    T = LinearMap.id ∨ T = -LinearMap.id := by
  obtain ⟨c, hc⟩ := blockPreserving_eq_mul K hr T hT hK
  obtain ⟨w₀, hw₀⟩ := hr
  have h := hQ ((Pi.single ⟨w₀, hw₀⟩ 1 : {w : InfinitePlace K // IsReal w} → ℝ), 0)
  have h1 : mixedEmbedding K c *
      (((Pi.single ⟨w₀, hw₀⟩ 1 : {w : InfinitePlace K // IsReal w} → ℝ), 0) : mixedSpace K) =
      ((Pi.single ⟨w₀, hw₀⟩ (embedding_of_isReal hw₀ c) :
        {w : InfinitePlace K // IsReal w} → ℝ), 0) := by
    refine Prod.ext ?_ (by simp)
    funext i
    by_cases hi : i = ⟨w₀, hw₀⟩
    · subst hi; simp
    · simp [hi]
  rw [hc, h1, placeForm_apply, placeForm_apply] at h
  simp [Pi.single_apply, ite_pow] at h
  have h2 : (embedding_of_isReal hw₀ c - 1) * (embedding_of_isReal hw₀ c + 1) = 0 := by
    rcases h with h | h <;> rw [h] <;> ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left
    have hc1 : c = 1 := (embedding_of_isReal hw₀).injective (by rw [map_one]; linarith)
    exact LinearMap.ext fun v => by rw [hc, hc1, map_one, one_mul]; rfl
  · right
    have hc1 : c = -1 :=
      (embedding_of_isReal hw₀).injective (by rw [map_neg, map_one]; linarith)
    exact LinearMap.ext fun v => by rw [hc, hc1, map_neg, map_one, neg_one_mul]; rfl

/-- **A6 (corollary for the boost).** Let `K` be a number field with at least one real place and
at least one complex place, and let `β ≠ 0`. Then the boost `placeBoost β` of `mixedSpace K`
(identity on the real coordinates, `boostC β` on every complex coordinate) does not map the image
of `K` into itself: it is not the case that for every `x` in `K` there is `y` in `K` with
`placeBoost β (mixedEmbedding K x) = mixedEmbedding K y`. -/
theorem placeBoost_not_preserves_field (hr : ∃ w : InfinitePlace K, IsReal w)
    (hc : ∃ w : InfinitePlace K, IsComplex w) (β : ℝ) (hβ : β ≠ 0) :
    ¬ ∀ x : K, ∃ y : K,
      (placeBoost β : mixedSpace K →ₗ[ℝ] mixedSpace K) (mixedEmbedding K x) =
        mixedEmbedding K y := by
  intro hK
  obtain ⟨c, hmul⟩ := blockPreserving_eq_mul K hr _ (LandingAux.placeBoost_isBlockPreserving β) hK
  obtain ⟨w₀, hw₀⟩ := hr
  obtain ⟨w₁, hw₁⟩ := hc
  have h1 := congrArg (fun v : mixedSpace K => v.1 ⟨w₀, hw₀⟩) (hmul (mixedEmbedding K 1))
  simp [placeBoost_apply] at h1
  have hc1 : c = 1 := (embedding_of_isReal hw₀).injective (by rw [← h1, map_one])
  have h2 := congrArg (fun v : mixedSpace K => (v.2 ⟨w₁, hw₁⟩).im) (hmul (mixedEmbedding K 1))
  rw [hc1] at h2
  simp [placeBoost_apply, boostC] at h2
  rw [← Complex.ofReal_sinh, Complex.ofReal_re] at h2
  exact hβ (Real.sinh_eq_zero.mp h2)

/-- **A6 (consistency of the two definitions of place-preserving).** On `PlaceSpace r₁` (one
complex coordinate), `IsBlockPreserving L` is equivalent to `HermitianExclusion.PlacePreserving L`. -/
theorem isBlockPreserving_iff_placePreserving (r₁ : ℕ) (L : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁) :
    IsBlockPreserving L ↔ PlacePreserving L := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i a => ?_, fun z => ?_⟩
    · obtain ⟨ha, hb⟩ := h1 i ((Pi.single i a : Fin r₁ → ℝ), (0 : Fin 1 → ℂ))
        (fun i' hi' => by simp [hi']) rfl
      refine ⟨(L ((Pi.single i a : Fin r₁ → ℝ), (0 : Fin 1 → ℂ))).1 i, Prod.ext ?_ hb⟩
      funext i'
      by_cases hi' : i' = i
      · subst hi'; simp
      · rw [ha i' hi']; simp [hi']
    · exact (h2 0 (0, z) rfl (fun j' hj' => absurd (Subsingleton.elim j' 0) hj')).1
  · rintro ⟨h1, h2⟩
    refine ⟨fun i v hv hv2 => ?_, fun j v hv _ => ?_⟩
    · have hveq : v = ((Pi.single i (v.1 i) : Fin r₁ → ℝ), (0 : Fin 1 → ℂ)) := by
        refine Prod.ext ?_ hv2
        funext i'
        by_cases hi' : i' = i
        · subst hi'; simp
        · rw [hv i' hi']; simp [hi']
      obtain ⟨a', ha'⟩ := h1 i (v.1 i)
      rw [hveq, ha']
      exact ⟨fun i' hi' => by simp [hi'], rfl⟩
    · have hveq : v = ((0 : Fin r₁ → ℝ), v.2) := Prod.ext hv rfl
      refine ⟨by rw [hveq]; exact h2 v.2, fun j' hj' => absurd (Subsingleton.elim j' j) hj'⟩

/-- **A6 (control: a map that permutes places).** The map `swapConj : (a, b, z) ↦ (b, a, conj z)`
of `PlaceSpace 2` is an isometry of the trace form, is not block-preserving, is not
place-preserving, is not the identity and is not minus the identity. -/
theorem swapConj_control :
    IsIsometry swapConj ∧ ¬ IsBlockPreserving swapConj ∧ ¬ PlacePreserving swapConj ∧
      swapConj ≠ LinearMap.id ∧ swapConj ≠ -LinearMap.id := by
  have hnb : ¬ IsBlockPreserving swapConj := by
    rintro ⟨h1, -⟩
    have h := (h1 0 ((Pi.single 0 1 : Fin 2 → ℝ), (0 : Fin 1 → ℂ))
      (fun i' hi' => by simp [hi']) rfl).1 1 (by decide)
    simp [swapConj] at h
  refine ⟨fun X Y => ?_, hnb, fun h => hnb ((isBlockPreserving_iff_placePreserving 2 _).mpr h),
    fun h => ?_, fun h => ?_⟩
  · simp [traceB, swapConj, Fin.sum_univ_succ, Complex.mul_re]
    ring
  · have h' := congrArg (fun f : PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2 =>
      (f ((![1, 0] : Fin 2 → ℝ), (0 : Fin 1 → ℂ))).1 0) h
    simp [swapConj] at h'
  · have h' := congrArg (fun f : PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2 =>
      (f ((![1, 1] : Fin 2 → ℝ), (0 : Fin 1 → ℂ))).1 0) h
    simp [swapConj] at h'
    norm_num at h'

open scoped Classical in
/-- **A6 (control in field form: the hypothesis "block-preserving" deleted).** Let `K` be a number
field and `σ` a ring automorphism of `K` different from the identity. Then there is a real-linear
endomorphism `T` of `mixedSpace K` with `T (mixedEmbedding K x) = mixedEmbedding K (σ x)` for every
`x` in `K` (so `T` maps the image of `K` into itself), preserving the place form, equal neither to
the identity nor to minus the identity, and, if `K` has a real place, not block-preserving. -/
theorem automorphism_control (σ : K ≃+* K) (hσ : σ ≠ RingEquiv.refl K) :
    ∃ T : mixedSpace K →ₗ[ℝ] mixedSpace K,
      (∀ x : K, T (mixedEmbedding K x) = mixedEmbedding K (σ x)) ∧
      (∀ v : mixedSpace K,
        placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w} (T v) =
          placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w} v) ∧
      T ≠ LinearMap.id ∧ T ≠ -LinearMap.id ∧
      ((∃ w : InfinitePlace K, IsReal w) → ¬ IsBlockPreserving T) := by
  have hT : ∀ x : K,
      (latticeBasis K).constr ℝ (fun i => mixedEmbedding K (σ (integralBasis K i)))
        (mixedEmbedding K x) = mixedEmbedding K (σ x) :=
    LandingAux.constr_mixedEmbedding σ
  generalize (latticeBasis K).constr ℝ
    (fun i => mixedEmbedding K (σ (integralBasis K i))) = T at hT
  have hne : T ≠ LinearMap.id := by
    intro h
    apply hσ
    ext x
    apply mixedEmbedding_injective K
    rw [← hT x, h]
    rfl
  refine ⟨T, hT, fun v => ?_, hne, fun h => ?_, fun hr hB => ?_⟩
  · -- the form
    have hP : ∀ y : K,
        placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w}
          (mixedEmbedding K (σ y)) =
        placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w}
          (mixedEmbedding K y) := by
      intro y
      rw [← trace_sq_eq_placeForm, ← trace_sq_eq_placeForm, ← map_mul]
      exact congrArg _ (Algebra.trace_eq_of_algEquiv σ.toRatAlgEquiv (y * y))
    have hB : (QuadraticMap.polarBilin (placeForm {w : InfinitePlace K // IsReal w}
        {w : InfinitePlace K // IsComplex w})).compl₁₂ T T =
        QuadraticMap.polarBilin (placeForm {w : InfinitePlace K // IsReal w}
          {w : InfinitePlace K // IsComplex w}) := by
      apply LinearMap.ext_basis (latticeBasis K) (latticeBasis K)
      intro i j
      simp only [LinearMap.compl₁₂_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polar, latticeBasis_apply, hT]
      have e1 : mixedEmbedding K (σ (integralBasis K i)) +
          mixedEmbedding K (σ (integralBasis K j)) =
          mixedEmbedding K (σ (integralBasis K i + integralBasis K j)) := by
        rw [map_add, map_add]
      have e2 : mixedEmbedding K (integralBasis K i) + mixedEmbedding K (integralBasis K j) =
          mixedEmbedding K (integralBasis K i + integralBasis K j) := by
        rw [map_add]
      rw [e1, e2, hP, hP, hP]
    have h := LinearMap.congr_fun (LinearMap.congr_fun hB v) v
    simp only [LinearMap.compl₁₂_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_self] at h
    rw [two_nsmul, two_nsmul] at h
    linarith
  · -- not minus the identity
    have h1 := LinearMap.congr_fun h (mixedEmbedding K 1)
    rw [hT, map_one] at h1
    have h2 : mixedEmbedding K 1 = mixedEmbedding K (-1) := by
      rw [map_neg]; exact h1
    have h3 : (1 : K) = -1 := mixedEmbedding_injective K h2
    have h4 : (2 : K) = 0 := by linear_combination h3
    exact two_ne_zero h4
  · -- not block-preserving when there is a real place
    obtain ⟨c, hc⟩ := blockPreserving_eq_mul K hr T hB fun x => ⟨σ x, hT x⟩
    have h1 := hc (mixedEmbedding K 1)
    rw [hT, map_one, map_one, mul_one] at h1
    have hc1 : c = 1 := mixedEmbedding_injective K (by rw [← h1, map_one])
    exact hne (LinearMap.ext fun v => by rw [hc, hc1, map_one, one_mul]; rfl)

end A6

/-! ### A4 -/

/-- **A4.** Let `e'` be a real-linear equivalence from `PlaceSpace 2` to `Spacetime` with
`minkowskiSquare (e' p) = -traceB 2 p p` for all `p` and
`e' (galoisConj 2 p) = timeReflection (e' p)` for all `p`. Then there are a real `3 × 3` matrix `R`
with `Rᵀ * R = 1` and a real `s` equal to `1` or `-1` such that, for all `p`:
`spatial (e' p)` is `R` applied to `spatial (placeIso p)`; `time (e' p) = s * time (placeIso p)`;
and `e' (boostGen 2 p)` is `-s` times the endomorphism of `Spacetime` with matrix
`R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r`, applied to `e' p`. -/
theorem time_canonical_place (e' : PlaceSpace 2 ≃ₗ[ℝ] Spacetime)
    (hQ : ∀ p, minkowskiSquare (e' p) = -traceB 2 p p)
    (hc : ∀ p, e' (galoisConj 2 p) = timeReflection (e' p)) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ), Rᵀ * R = 1 ∧ (s = 1 ∨ s = -1) ∧
      (∀ p, spatial (e' p) = Matrix.toEuclideanLin R (spatial (placeIso p))) ∧
      (∀ p, time (e' p) = s * time (placeIso p)) ∧
      ∀ p, e' (boostGen 2 p) =
        (-s) • Matrix.toEuclideanLin (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r) (e' p) := by
  obtain ⟨R, s, hR, hs, hΛ⟩ := LandingAux.coordMat_eq_blockDiag e' hQ hc
  have hcoord : ∀ p i, e' p i = (blockDiag R s * Smat).mulVec (placeCoords p) i := fun p i => by
    rw [← hΛ]
    exact LandingAux.coordMat_mulVec (e' : PlaceSpace 2 →ₗ[ℝ] Spacetime) p i
  have hss : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  refine ⟨R, s, hR, hs, fun p => ?_, fun p => ?_, fun p => ?_⟩
  · ext i
    have hi : spatial (e' p) i = e' p i.castSucc := rfl
    rw [hi, hcoord]
    fin_cases i <;>
      simp [spatial, placeIso_apply, placeLin_apply, HermitianExclusion.blockDiag, Smat,
        Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ, placeCoords,
        Matrix.toLpLin_apply] <;>
      ring
  · have h3 : time (e' p) = e' p 3 := rfl
    rw [h3, hcoord, time_placeIso]
    simp [HermitianExclusion.blockDiag, Smat, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_succ,
      placeCoords]
    ring
  · have hinv : (blockDiag R s * Smat)⁻¹ * (blockDiag R s * Smat) = 1 := by
      rw [blockDiag_S_inv R s hR hss]
      calc Sinv * blockDiag Rᵀ s * (blockDiag R s * Smat)
          = Sinv * (blockDiag Rᵀ s * blockDiag R s) * Smat := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [blockDiagT_mul_blockDiag R s hR hss, Matrix.mul_one, Sinv_mul_Smat]
    have hK : ((-s) • (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r)) * (blockDiag R s * Smat) =
        (blockDiag R s * Smat) * Kmat := by
      rw [← boost_span' R s hR hss, Matrix.mul_assoc, hinv, Matrix.mul_one]
    have hx : (WithLp.ofLp (e' p) : Fin 4 → ℝ) =
        (blockDiag R s * Smat).mulVec (placeCoords p) := funext fun k => hcoord p k
    have e1 : (-s) • Matrix.toEuclideanLin (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r) (e' p) =
        Matrix.toEuclideanLin ((-s) • (R 0 2 • L03r + R 1 2 • L13r + R 2 2 • L23r)) (e' p) := by
      rw [map_smul, LinearMap.smul_apply]
    rw [e1]
    ext i
    rw [Matrix.toLpLin_apply, hx, Matrix.mulVec_mulVec, hK, ← Matrix.mulVec_mulVec,
      ← placeCoords_boostGen]
    exact hcoord _ i

/-- **Control of A4 (OPTIONAL): the sign `s = -1` occurs.** There is a real-linear equivalence
`e'` from `PlaceSpace 2` to `Spacetime` satisfying both hypotheses of A4 with
`time (e' p) = -time (placeIso p)` for all `p`. -/
theorem time_canonical_place_control :
    ∃ e' : PlaceSpace 2 ≃ₗ[ℝ] Spacetime,
      (∀ p, minkowskiSquare (e' p) = -traceB 2 p p) ∧
      (∀ p, e' (galoisConj 2 p) = timeReflection (e' p)) ∧
      ∀ p, time (e' p) = -time (placeIso p) := by
  have hinv : ∀ x : Spacetime, timeReflection (timeReflection x) = x := fun x => by
    ext i; fin_cases i <;> simp [timeReflection]
  have hform : ∀ x : Spacetime, minkowskiSquare (timeReflection x) = minkowskiSquare x :=
    fun x => by
      rw [minkowskiSquare_coords, minkowskiSquare_coords]
      simp [timeReflection]
  have h1 : timeReflection ∘ₗ timeReflection = LinearMap.id := LinearMap.ext fun x => hinv x
  have key : ∃ τ : Spacetime ≃ₗ[ℝ] Spacetime, ∀ x, τ x = timeReflection x :=
    ⟨LinearEquiv.ofLinearMap timeReflection timeReflection h1 h1, fun _ => rfl⟩
  obtain ⟨τ, hτ⟩ := key
  refine ⟨placeIso.trans τ, ?_, ?_, ?_⟩
  · intro p
    rw [LinearEquiv.trans_apply, hτ, hform, minkowskiSquare_placeIso]
  · intro p
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hτ, hτ]
    congr 1
    ext i; fin_cases i <;> simp [placeIso_apply, placeLin, timeReflection, galoisConj]
  · intro p
    rw [LinearEquiv.trans_apply, hτ]
    show (timeReflection (placeIso p)) (3 : Fin 4) = -(placeIso p) (3 : Fin 4)
    simp [timeReflection]

end ReleaseAdapter
