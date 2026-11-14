module
public import Mathlib
public import LorentzLie.Defs
public import LorentzLie.Centroid
public import LorentzLie.Landings
public import ReleaseAdapter.Carried
public import ReleaseAdapter.Landing

@[expose] public section

/-!
# The trace-form-skew Lie algebra of a number field with two real places and one complex place

For a number field `K` with exactly two real places and exactly one complex place,
`ReleaseAdapter.traceSkew K` is the Lie algebra of the real-linear endomorphisms of `mixedSpace K`
that are skew-adjoint for the polar form of the place form `(x, z) ↦ Σ x_w² + Σ 2 Re(z_w²)`.

* `traceSkew_centroid` — there is a bracket-commuting endomorphism `H` of `traceSkew K` with
  `H (H X) = -X`, and every bracket-commuting endomorphism is uniquely `a • id + b • H`;
* `traceSkew_hodge_eq_or_eq_neg` — two bracket-commuting endomorphisms with square `-1` are equal
  or opposite.

The argument: a labelling of the places gives `ReleaseAdapter.mixedIso`, which carries the polar
form of the place form to `-2` times `minkowskiBilin`; conjugation by it is a Lie algebra
equivalence from `traceSkew K` to `ReleaseAdapter.lorentzAlgebra`
(`NumberFieldAux.traceSkewEquivLorentzAlgebra`), which `lorentzAlgebraEquivEtaSkew` continues to
`etaSkew ![1, 1, 1, -1]`; there `hodge_centroid_real` applies, and its three conclusions are
transported back (`NumberFieldAux.centroid_transport`). The sign statement is derived from the
centroid description alone (`NumberFieldAux.eq_or_eq_neg_of_centroid`), so it does not depend on
the labelling.

Helper statements are in the namespace `LorentzLie.NumberFieldAux`.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

open Matrix
open scoped TensorProduct

namespace LorentzLie

open YangMills ReleaseAdapter

namespace NumberFieldAux

/-! ### Two statements about a real Lie algebra with a complex structure in its centroid -/

section General

variable {L L' : Type*} [LieRing L] [LieAlgebra ℝ L] [LieRing L'] [LieAlgebra ℝ L']

/-- Transport of the centroid description along a Lie equivalence `φ : L ≃ₗ⁅ℝ⁆ L'`: if `H'` on
`L'` is bracket-commuting with `H' (H' X) = -X`, and every bracket-commuting endomorphism of `L'`
is uniquely `a • id + b • H'`, then there is `H` on `L` with the same three properties (the proof
takes `φ⁻¹ ∘ H' ∘ φ`). -/
theorem centroid_transport (φ : L ≃ₗ⁅ℝ⁆ L') (H' : L' →ₗ[ℝ] L')
    (hc : IsBracketCommuting H') (hsq : ∀ X, H' (H' X) = -X)
    (hu : ∀ R : L' →ₗ[ℝ] L', IsBracketCommuting R →
      ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • H') :
    ∃ H : L →ₗ[ℝ] L,
      IsBracketCommuting H ∧ (∀ X, H (H X) = -X) ∧
      ∀ R : L →ₗ[ℝ] L, IsBracketCommuting R →
        ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • H := by
  refine ⟨(φ.symm.toLinearEquiv : L' →ₗ[ℝ] L) ∘ₗ H' ∘ₗ (φ.toLinearEquiv : L →ₗ[ℝ] L'),
    hc.lieEquivConj φ.symm, ?_, ?_⟩
  · intro X
    change φ.symm (H' (φ (φ.symm (H' (φ X))))) = -X
    rw [LieEquiv.apply_symm_apply, hsq, map_neg, LieEquiv.symm_apply_apply]
  · intro R hR
    obtain ⟨ab, hab, huniq⟩ := hu _ (hR.lieEquivConj φ)
    have key : ∀ (S : L →ₗ[ℝ] L) (cd : ℝ × ℝ),
        S = cd.1 • LinearMap.id + cd.2 •
            ((φ.symm.toLinearEquiv : L' →ₗ[ℝ] L) ∘ₗ H' ∘ₗ (φ.toLinearEquiv : L →ₗ[ℝ] L')) ↔
          (φ.toLinearEquiv : L →ₗ[ℝ] L') ∘ₗ S ∘ₗ (φ.symm.toLinearEquiv : L' →ₗ[ℝ] L) =
            cd.1 • LinearMap.id + cd.2 • H' := by
      intro S cd
      constructor
      · intro h
        ext Y
        change φ (S (φ.symm Y)) = cd.1 • Y + cd.2 • H' Y
        rw [h]
        change φ (cd.1 • φ.symm Y + cd.2 • φ.symm (H' (φ (φ.symm Y)))) = _
        rw [map_add, map_smul, map_smul, LieEquiv.apply_symm_apply,
          LieEquiv.apply_symm_apply]
      · intro h
        ext X
        have h1 := LinearMap.congr_fun h (φ X)
        change φ (S (φ.symm (φ X))) = cd.1 • φ X + cd.2 • H' (φ X) at h1
        rw [LieEquiv.symm_apply_apply] at h1
        change S X = cd.1 • X + cd.2 • φ.symm (H' (φ X))
        refine φ.injective ?_
        change φ (S X) = φ (cd.1 • X + cd.2 • φ.symm (H' (φ X)))
        rw [h1, map_add, map_smul, map_smul, LieEquiv.apply_symm_apply]
    exact ⟨ab, (key R ab).mpr hab, fun cd hcd => huniq cd ((key R cd).mp hcd)⟩

/-- If `H₀ (H₀ X) = -X` for all `X` and every bracket-commuting endomorphism is uniquely
`a • id + b • H₀`, then a bracket-commuting `H` with `H (H X) = -X` is `H₀` or `-H₀`. -/
theorem eq_or_eq_neg_of_centroid (H₀ : L →ₗ[ℝ] L) (h0sq : ∀ X, H₀ (H₀ X) = -X)
    (hu : ∀ R : L →ₗ[ℝ] L, IsBracketCommuting R →
      ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • H₀)
    (H : L →ₗ[ℝ] L) (hH : IsBracketCommuting H) (hH2 : ∀ X, H (H X) = -X) :
    H = H₀ ∨ H = -H₀ := by
  obtain ⟨⟨a, b⟩, hab, -⟩ := hu H hH
  simp only at hab
  have hneg : IsBracketCommuting ((-1 : ℝ) • (LinearMap.id : L →ₗ[ℝ] L)) :=
    isBracketCommuting_id.smul (-1)
  have e1 : (-1 : ℝ) • (LinearMap.id : L →ₗ[ℝ] L) =
      ((-1 : ℝ), (0 : ℝ)).1 • LinearMap.id + ((-1 : ℝ), (0 : ℝ)).2 • H₀ := by
    simp
  have e2 : (-1 : ℝ) • (LinearMap.id : L →ₗ[ℝ] L) =
      (a ^ 2 - b ^ 2, 2 * a * b).1 • LinearMap.id + (a ^ 2 - b ^ 2, 2 * a * b).2 • H₀ := by
    ext X
    have h := hH2 X
    rw [hab] at h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul,
      h0sq] at h ⊢
    have h' : (-1 : ℝ) • X = -X := by simp
    rw [h', ← h]
    module
  have hpair := (hu _ hneg).unique e2 e1
  have h1 : a ^ 2 - b ^ 2 = -1 := congrArg Prod.fst hpair
  have h2 : 2 * a * b = 0 := congrArg Prod.snd hpair
  have ha : a = 0 := by
    by_contra ha
    have hb : b = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (by linarith : a = 0) ha
      · exact h
    rw [hb] at h1
    nlinarith [sq_nonneg a]
  rw [ha] at h1 hab
  have hb : b = 1 ∨ b = -1 := by
    have h3 : (b - 1) * (b + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · left; linarith
    · right; linarith
  rcases hb with rfl | rfl
  · left
    rw [hab]; simp
  · right
    rw [hab]; simp

end General

/-! ### The place form and `minkowskiBilin` -/

open HermitianExclusion
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

/-- Polarization: `2 * minkowskiBilin x y` in terms of `minkowskiSquare`. -/
theorem two_mul_minkowskiBilin (x y : Spacetime) :
    2 * minkowskiBilin x y =
      minkowskiSquare (x + y) - minkowskiSquare x - minkowskiSquare y := by
  simp only [← minkowskiBilin_self, minkowskiBilin_apply, PiLp.add_apply]
  ring

section Field

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- The polar form of the place form of `mixedSpace K` is `-2` times `minkowskiBilin` read along
`mixedIso e₁ e₂`. -/
theorem polarBilin_placeForm_eq (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (v w : mixedSpace K) :
    QuadraticMap.polarBilin
        (placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w}) v w =
      -(2 * minkowskiBilin (mixedIso e₁ e₂ v) (mixedIso e₁ e₂ w)) := by
  rw [two_mul_minkowskiBilin, ← map_add, minkowskiSquare_mixedIso, minkowskiSquare_mixedIso,
    minkowskiSquare_mixedIso, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

open scoped Classical in
/-- Membership in `traceSkew K`, unfolded. -/
theorem mem_traceSkew_iff (A : Module.End ℝ (mixedSpace K)) :
    A ∈ traceSkew K ↔ ∀ v w : mixedSpace K,
      QuadraticMap.polarBilin
          (placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w})
          (A v) w =
        -QuadraticMap.polarBilin
          (placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w})
          v (A w) := by
  change (∀ v w : mixedSpace K,
    QuadraticMap.polarBilin
        (placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w})
        (A v) w =
      (-QuadraticMap.polarBilin
        (placeForm {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w}))
        v (A w)) ↔ _
  simp only [LinearMap.neg_apply]

/-- Membership in `traceSkew K` in terms of `minkowskiBilin` read along `mixedIso e₁ e₂`. -/
theorem mem_traceSkew_iff_minkowskiBilin (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (A : Module.End ℝ (mixedSpace K)) :
    A ∈ traceSkew K ↔ ∀ v w : mixedSpace K,
      minkowskiBilin (mixedIso e₁ e₂ (A v)) (mixedIso e₁ e₂ w) =
        -minkowskiBilin (mixedIso e₁ e₂ v) (mixedIso e₁ e₂ (A w)) := by
  rw [mem_traceSkew_iff]
  refine forall₂_congr fun v w => ?_
  rw [polarBilin_placeForm_eq e₁ e₂, polarBilin_placeForm_eq e₁ e₂]
  constructor <;> intro h <;> linarith

/-- For a labelling `e₁`, `e₂` of the places: conjugation by `mixedIso e₁ e₂` is a Lie algebra
equivalence from `traceSkew K` to `lorentzAlgebra`. It is pinned down by
`traceSkewEquivLorentzAlgebra_apply`. -/
noncomputable def traceSkewEquivLorentzAlgebra (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) : traceSkew K ≃ₗ⁅ℝ⁆ lorentzAlgebra :=
  LieEquiv.ofSubalgebras _ _ (mixedIso e₁ e₂).lieConj <| by
    ext B
    rw [LieSubalgebra.mem_map]
    constructor
    · rintro ⟨A, hA, rfl⟩
      rw [Landings.mem_lorentzAlgebra_iff]
      intro x y
      have h := (mem_traceSkew_iff_minkowskiBilin e₁ e₂ A).mp hA
        ((mixedIso e₁ e₂).symm x) ((mixedIso e₁ e₂).symm y)
      simp only [LinearEquiv.apply_symm_apply] at h
      exact h
    · intro hB
      refine ⟨(mixedIso e₁ e₂).symm.lieConj B, ?_, ?_⟩
      · rw [mem_traceSkew_iff_minkowskiBilin e₁ e₂]
        intro v w
        have h := (Landings.mem_lorentzAlgebra_iff B).mp hB (mixedIso e₁ e₂ v) (mixedIso e₁ e₂ w)
        change minkowskiBilin
            (mixedIso e₁ e₂ ((mixedIso e₁ e₂).symm (B (mixedIso e₁ e₂ v)))) (mixedIso e₁ e₂ w) =
          -minkowskiBilin (mixedIso e₁ e₂ v)
            (mixedIso e₁ e₂ ((mixedIso e₁ e₂).symm (B (mixedIso e₁ e₂ w))))
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact h
      · exact (mixedIso e₁ e₂).lieConj.apply_symm_apply B

/-- The endomorphism of `Spacetime` underlying `traceSkewEquivLorentzAlgebra e₁ e₂ A` is
`mixedIso e₁ e₂ ∘ A ∘ (mixedIso e₁ e₂)⁻¹`. -/
theorem traceSkewEquivLorentzAlgebra_apply (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (A : traceSkew K) (x : Spacetime) :
    (traceSkewEquivLorentzAlgebra e₁ e₂ A : Module.End ℝ Spacetime) x =
      mixedIso e₁ e₂ ((A : Module.End ℝ (mixedSpace K)) ((mixedIso e₁ e₂).symm x)) :=
  rfl

/-- `traceSkew K` has dimension `6` over `ℝ` when `K` has a labelling of two real places and one
complex place. -/
theorem finrank_traceSkew (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) : Module.finrank ℝ (traceSkew K) = 6 := by
  rw [LinearEquiv.finrank_eq (traceSkewEquivLorentzAlgebra e₁ e₂).toLinearEquiv]
  exact finrank_lorentzAlgebra

end Field

end NumberFieldAux

/-! ### The two statements for a number field -/

section L7

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

/-- **L7 (existence and the centroid).** Let `K` be a number field with exactly two real places
and exactly one complex place, and let `traceSkew K` be the Lie algebra of the endomorphisms of
`mixedSpace K` skew-adjoint for the polar form of the place form. Then there is a real-linear
endomorphism `H` of `traceSkew K` that is bracket-commuting, satisfies `H (H X) = -X` for all `X`,
and such that for every bracket-commuting real-linear endomorphism `R` of `traceSkew K` there is
exactly one pair `(a, b)` in `ℝ × ℝ` with `R = a • id + b • H`. -/
theorem traceSkew_centroid (h1 : nrRealPlaces K = 2) (h2 : nrComplexPlaces K = 1) :
    ∃ H : traceSkew K →ₗ[ℝ] traceSkew K,
      IsBracketCommuting H ∧ (∀ X, H (H X) = -X) ∧
      ∀ R : traceSkew K →ₗ[ℝ] traceSkew K, IsBracketCommuting R →
        ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • H := by
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := HermitianExclusion.nonempty_labelling_iff.mpr ⟨h1, h2⟩
  obtain ⟨hc, hsq, hu⟩ := hodge_centroid_real (![1, 1, 1, -1] : Fin 4 → ℝ) Landings.eta4_sign
  refine NumberFieldAux.centroid_transport
    ((NumberFieldAux.traceSkewEquivLorentzAlgebra e₁ e₂).trans lorentzAlgebraEquivEtaSkew)
    (hodge (![1, 1, 1, -1] : Fin 4 → ℝ)) hc (fun X => ?_) hu
  rw [hsq, Landings.eta4_prod, neg_one_smul]

/-- **L7 (uniqueness up to sign).** Let `K` be a number field with exactly two real places and
exactly one complex place. If `H` and `H'` are real-linear endomorphisms of `traceSkew K`, each
bracket-commuting and each with square `-1` (`H (H X) = -X`, `H' (H' X) = -X` for all `X`), then
`H' = H` or `H' = -H`. -/
theorem traceSkew_hodge_eq_or_eq_neg (h1 : nrRealPlaces K = 2) (h2 : nrComplexPlaces K = 1)
    (H H' : traceSkew K →ₗ[ℝ] traceSkew K)
    (hH : IsBracketCommuting H) (hH2 : ∀ X, H (H X) = -X)
    (hH' : IsBracketCommuting H') (hH'2 : ∀ X, H' (H' X) = -X) :
    H' = H ∨ H' = -H := by
  obtain ⟨H₀, -, h0sq, hu⟩ := traceSkew_centroid K h1 h2
  rcases NumberFieldAux.eq_or_eq_neg_of_centroid H₀ h0sq hu H hH hH2 with h | h <;>
    rcases NumberFieldAux.eq_or_eq_neg_of_centroid H₀ h0sq hu H' hH' hH'2 with h' | h' <;>
    rw [h, h']
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr (neg_neg H₀).symm
  · exact Or.inl rfl

end L7

end LorentzLie
