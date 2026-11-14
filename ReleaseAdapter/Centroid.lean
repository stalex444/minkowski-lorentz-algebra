module
public import Mathlib
public import LorentzLie.Defs
public import LorentzLie.Centroid
public import LorentzLie.Controls
public import LorentzLie.Landings
public import LorentzLie.NumberField
public import LorentzLie.FormCentroid
public import ReleaseAdapter.Carried
public import ReleaseAdapter.CentroidDefs

@[expose] public section

/-!
# The bracket-commuting maps and the invariant bilinear forms of `lorentzAlgebra`

`YangMills.Spacetime`, `YangMills.time`, `YangMills.spatial`, `YangMills.minkowskiSquare` are
copies carried from the public statement of the Yang–Mills release (`ReleaseAdapter/Carried.lean`,
Part 1). `ReleaseAdapter.minkowskiBilin` and `ReleaseAdapter.lorentzAlgebra` (the Lie algebra of
the endomorphisms of `Spacetime` that are skew-adjoint for `minkowskiBilin`) are this package's
(Part 2). `lorentzHodge`, `lorentzBoost`, `lorentzRot` and `lorentzTraceForm` are defined, with
their pinning statements, in `ReleaseAdapter/CentroidDefs.lean`.

Contents (19 statements).

* `lorentzAlgebra_centroid`, `lorentzAlgebra_hodge_eq_or_eq_neg` — the bracket-commuting
  real-linear endomorphisms of `lorentzAlgebra` are `a • id + b • H` for a bracket-commuting `H`
  with `H (H X) = -X`, the pair `(a, b)` being unique; a bracket-commuting `H` with
  `H (H X) = -X` is unique up to sign.
* `lorentzHodge_isBracketCommuting`, `lorentzHodge_lorentzHodge`,
  `lorentzAlgebra_centroid_lorentzHodge`, `lorentzHodge_lorentzBoost`, `lorentzHodge_lorentzRot`
  — the same with the operator `lorentzHodge` named, and its values on the six generators.
* `lorentzHodge_not_smul_id`, `neg_lorentzHodge_lorentzBoost_zero_ne`,
  `eq_lorentzHodge_of_lorentzBoost_zero`, `exists_ne_smul_id_add_smul_lorentzHodge`,
  `eq_lorentzHodge_of_generators` — controls.
* `lorentzTraceForm_invariant`, `lorentzTraceForm_lorentzHodge_invariant`, `lorentzTraceForm_comm`,
  `lorentzTraceForm_lorentzHodge_comm`, `lorentzAlgebra_invariant_form`,
  `lorentzAlgebra_invariant_form_symm`, `exists_bilinForm_ne_smul_lorentzTraceForm` — the
  invariant bilinear forms of `lorentzAlgebra` are
  `a * lorentzTraceForm X Y + b * lorentzTraceForm (lorentzHodge X) Y`, the pair `(a, b)` being
  unique, and each of them is symmetric.

Conventions. Bracket-commuting means `∀ X Y, R ⁅X, Y⁆ = ⁅X, R Y⁆` (`LorentzLie.IsBracketCommuting`).
A bilinear form `B` on a Lie algebra is called invariant when `B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0` for all
`X`, `Y`, `Z`. The indices `k + 1`, `k + 2` are sums in `Fin 3`. The time axis is index `3`, and
`LorentzLie.hodgeMat η X = LorentzLie.star0 (diagonal η * X) * diagonal η` with `ε₀₁₂₃ = +1`.

The three helpers are in the namespace `ReleaseAdapter.Centroid`.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

namespace ReleaseAdapter

/-! ====================================================================================
## T1, T2. The bracket-commuting maps of `lorentzAlgebra`, without naming an operator
==================================================================================== -/

/-- **T1 (the bracket-commuting maps of `lorentzAlgebra`).** `lorentzAlgebra` is the Lie algebra of
the endomorphisms of `Spacetime` that are skew-adjoint for `minkowskiBilin`; `Spacetime` is a copy
carried from the public statement of the Yang–Mills release. There is a real-linear endomorphism `H`
of `lorentzAlgebra` such that: `H` is bracket-commuting, `H ⁅X, Y⁆ = ⁅X, H Y⁆` for all `X`, `Y`;
`H (H X) = -X` for all `X`; and for every bracket-commuting real-linear endomorphism `R` of
`lorentzAlgebra` there is exactly one pair `(a, b)` of real numbers with `R = a • id + b • H`. -/
theorem lorentzAlgebra_centroid :
    ∃ H : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra,
      LorentzLie.IsBracketCommuting H ∧ (∀ X : lorentzAlgebra, H (H X) = -X) ∧
      ∀ R : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra, LorentzLie.IsBracketCommuting R →
        ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • H := by
  obtain ⟨hc, hsq, hu⟩ :=
    LorentzLie.hodge_centroid_real (![1, 1, 1, -1] : Fin 4 → ℝ) LorentzLie.Landings.eta4_sign
  refine LorentzLie.NumberFieldAux.centroid_transport LorentzLie.lorentzAlgebraEquivEtaSkew
    (LorentzLie.hodge (![1, 1, 1, -1] : Fin 4 → ℝ)) hc (fun X => ?_) hu
  rw [hsq, LorentzLie.Landings.eta4_prod, neg_one_smul]

/-- **T2 (uniqueness up to sign).** Let `H` and `H'` be real-linear endomorphisms of
`lorentzAlgebra`. Suppose both are bracket-commuting, `H (H X) = -X` for all `X`, and
`H' (H' X) = -X` for all `X`. Then `H' = H` or `H' = -H`. -/
theorem lorentzAlgebra_hodge_eq_or_eq_neg
    (H H' : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra)
    (hH : LorentzLie.IsBracketCommuting H) (hH2 : ∀ X : lorentzAlgebra, H (H X) = -X)
    (hH' : LorentzLie.IsBracketCommuting H') (hH'2 : ∀ X : lorentzAlgebra, H' (H' X) = -X) :
    H' = H ∨ H' = -H := by
  obtain ⟨H₀, -, h0sq, hu⟩ := lorentzAlgebra_centroid
  rcases LorentzLie.NumberFieldAux.eq_or_eq_neg_of_centroid H₀ h0sq hu H hH hH2 with h | h <;>
    rcases LorentzLie.NumberFieldAux.eq_or_eq_neg_of_centroid H₀ h0sq hu H' hH' hH'2
      with h' | h' <;>
    rw [h, h']
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr (neg_neg H₀).symm
  · exact Or.inl rfl

/-! ====================================================================================
## T3. The explicit operator `lorentzHodge`
==================================================================================== -/

/-- **T3(a).** The operator `lorentzHodge` on `lorentzAlgebra` is bracket-commuting:
`lorentzHodge ⁅X, Y⁆ = ⁅X, lorentzHodge Y⁆` for all `X`, `Y` in `lorentzAlgebra`. -/
theorem lorentzHodge_isBracketCommuting : LorentzLie.IsBracketCommuting lorentzHodge := by
  have hc : LorentzLie.IsBracketCommuting (LorentzLie.hodge (![1, 1, 1, -1] : Fin 4 → ℝ)) :=
    (LorentzLie.lorentzian_hodge_control _ LorentzLie.Landings.eta4_sign
      LorentzLie.Landings.eta4_prod).1
  exact hc.lieEquivConj LorentzLie.lorentzAlgebraEquivEtaSkew.symm

/-- **T3(b).** For every `X` in `lorentzAlgebra`, `lorentzHodge (lorentzHodge X) = -X`. -/
theorem lorentzHodge_lorentzHodge (X : lorentzAlgebra) : lorentzHodge (lorentzHodge X) = -X := by
  have key : LorentzLie.lorentzAlgebraEquivEtaSkew (lorentzHodge (lorentzHodge X)) =
      LorentzLie.lorentzAlgebraEquivEtaSkew (-X) := by
    rw [lorentzAlgebraEquivEtaSkew_lorentzHodge, lorentzAlgebraEquivEtaSkew_lorentzHodge,
      (LorentzLie.lorentzian_hodge_control _ LorentzLie.Landings.eta4_sign
        LorentzLie.Landings.eta4_prod).2.1, map_neg]
  exact LorentzLie.lorentzAlgebraEquivEtaSkew.injective key

/-- **T3(c) (the bracket-commuting maps, with the operator named).** Let `R` be a real-linear
endomorphism of `lorentzAlgebra` that is bracket-commuting. Then there is exactly one pair `(a, b)`
of real numbers with `R = a • id + b • lorentzHodge`. -/
theorem lorentzAlgebra_centroid_lorentzHodge (R : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra)
    (hR : LorentzLie.IsBracketCommuting R) :
    ∃! ab : ℝ × ℝ, R = ab.1 • LinearMap.id + ab.2 • lorentzHodge := by
  obtain ⟨H₀, hc0, h0sq, hu⟩ := lorentzAlgebra_centroid
  rcases LorentzLie.NumberFieldAux.eq_or_eq_neg_of_centroid H₀ h0sq hu lorentzHodge
    lorentzHodge_isBracketCommuting lorentzHodge_lorentzHodge with h | h
  · rw [h]; exact hu R hR
  · have h' : lorentzHodge = (-1 : ℝ) • H₀ := h.trans (neg_one_smul ℝ H₀).symm
    rw [h']
    exact (LorentzLie.FormCentroid.description_smul H₀ (-1) (-1) (by norm_num) hc0
      (fun X => by rw [h0sq, neg_one_smul]) hu).2.2 R hR

/-- **T3(d), boosts.** For every space axis `k : Fin 3`, `lorentzHodge` sends the boost generator
`lorentzBoost k` (the endomorphism `x ↦ x 3 • e_k + x k • e_3` of `Spacetime`) to minus the rotation
generator in the plane of the two other space axes, taken in cyclic order:
`lorentzHodge (lorentzBoost k) = -lorentzRot (k + 1) (k + 2)`, the sums being in `Fin 3`. Written
out: `lorentzBoost 0 ↦ -lorentzRot 1 2`, `lorentzBoost 1 ↦ -lorentzRot 2 0`,
`lorentzBoost 2 ↦ -lorentzRot 0 1`. -/
theorem lorentzHodge_lorentzBoost (k : Fin 3) :
    lorentzHodge (lorentzBoost k) = -lorentzRot (k + 1) (k + 2) := by
  have key : (LorentzLie.lorentzAlgebraEquivEtaSkew (lorentzHodge (lorentzBoost k)) :
        Matrix (Fin 4) (Fin 4) ℝ) =
      (LorentzLie.lorentzAlgebraEquivEtaSkew (-lorentzRot (k + 1) (k + 2)) :
        Matrix (Fin 4) (Fin 4) ℝ) := by
    rw [lorentzAlgebraEquivEtaSkew_lorentzHodge, LorentzLie.hodge_coe,
      lorentzAlgebraEquivEtaSkew_lorentzBoost, map_neg, NegMemClass.coe_neg,
      lorentzAlgebraEquivEtaSkew_lorentzRot]
    fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [LorentzLie.hodgeMat, LorentzLie.star0, YangMills.timeAxis]
  exact LorentzLie.lorentzAlgebraEquivEtaSkew.injective (Subtype.ext key)

/-- **T3(d), rotations.** For every space axis `k : Fin 3`, `lorentzHodge` sends the rotation
generator `lorentzRot (k + 1) (k + 2)` in the plane of the two other space axes, taken in cyclic
order (the endomorphism `x ↦ x (k + 1) • e_(k + 2) - x (k + 2) • e_(k + 1)` of `Spacetime`, the
sums being in `Fin 3`), to the boost generator `lorentzBoost k`. Written out:
`lorentzRot 1 2 ↦ lorentzBoost 0`, `lorentzRot 2 0 ↦ lorentzBoost 1`,
`lorentzRot 0 1 ↦ lorentzBoost 2`. -/
theorem lorentzHodge_lorentzRot (k : Fin 3) :
    lorentzHodge (lorentzRot (k + 1) (k + 2)) = lorentzBoost k := by
  have h := neg_eq_iff_eq_neg.mpr (lorentzHodge_lorentzBoost k)
  rw [← h, map_neg, lorentzHodge_lorentzHodge, neg_neg]

/-! ====================================================================================
## T4. Controls
==================================================================================== -/

/-- **T4 (the operator is not a scalar).** There is no real number `c` with
`lorentzHodge = c • id`. So in T3(c) the term `b • lorentzHodge` cannot be absorbed into
`a • id`. -/
theorem lorentzHodge_not_smul_id : ¬ ∃ c : ℝ, lorentzHodge = c • LinearMap.id := by
  exact LorentzLie.FormCentroid.not_scalar lorentzHodge lorentzHodge_isBracketCommuting
    lorentzAlgebra_centroid_lorentzHodge

namespace Centroid

/-- The rotation generator `lorentzRot 1 2` is not the zero element of `lorentzAlgebra`. -/
theorem lorentzRot_one_two_ne_zero : lorentzRot 1 2 ≠ 0 := by
  intro h
  have h1 := congrArg
    (fun X : lorentzAlgebra =>
      (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 1 1) 2) h
  simp [lorentzRot_one_two_apply] at h1

end Centroid

/-- **T4 (the value on one generator fixes the sign).** The operator `-lorentzHodge`, which is also
bracket-commuting with square `-1`, does not have the value of T3(d) on the boost generator
`lorentzBoost 0`: `(-lorentzHodge) (lorentzBoost 0) ≠ -lorentzRot 1 2`. -/
theorem neg_lorentzHodge_lorentzBoost_zero_ne :
    (-lorentzHodge) (lorentzBoost 0) ≠ -lorentzRot 1 2 := by
  intro h
  have e0 : lorentzHodge (lorentzBoost 0) = -lorentzRot 1 2 := lorentzHodge_lorentzBoost 0
  rw [LinearMap.neg_apply, e0, neg_neg] at h
  have h2 : (2 : ℝ) • lorentzRot 1 2 = 0 :=
    (two_smul ℝ (lorentzRot 1 2)).trans (eq_neg_iff_add_eq_zero.mp h)
  rcases smul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact Centroid.lorentzRot_one_two_ne_zero h3

/-- **T4 (characterisation of `lorentzHodge`).** Let `H` be a real-linear endomorphism of
`lorentzAlgebra`. Suppose `H` is bracket-commuting and `H (lorentzBoost 0) = -lorentzRot 1 2`. Then
`H = lorentzHodge`. (No hypothesis on `H ∘ H` is needed.) -/
theorem eq_lorentzHodge_of_lorentzBoost_zero (H : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra)
    (hH : LorentzLie.IsBracketCommuting H)
    (h : H (lorentzBoost 0) = -lorentzRot 1 2) : H = lorentzHodge := by
  obtain ⟨⟨a, b⟩, hab, -⟩ := lorentzAlgebra_centroid_lorentzHodge H hH
  have e0 : lorentzHodge (lorentzBoost 0) = -lorentzRot 1 2 := lorentzHodge_lorentzBoost 0
  rw [hab] at h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, e0] at h
  have ha := congrArg
    (fun X : lorentzAlgebra =>
      (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 3 1) 0) h
  have hb := congrArg
    (fun X : lorentzAlgebra =>
      (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 1 1) 2) h
  simp [lorentzBoost_zero_apply, lorentzRot_one_two_apply] at ha hb
  have ha' : a = 0 := by linarith
  have hb' : b = 1 := by linarith
  rw [hab]
  simp [ha', hb']

/-- **T4 (the bracket-commuting hypothesis is needed).** There is a real-linear endomorphism `R` of
`lorentzAlgebra` that is not of the form `a • id + b • lorentzHodge` for any real numbers `a`, `b`.
So the conclusion of T1 and T3(c) does not hold for every real-linear endomorphism. (One such `R`
is `X ↦ ⁅lorentzBoost 0, X⁆`.) -/
theorem exists_ne_smul_id_add_smul_lorentzHodge :
    ∃ R : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra,
      ∀ a b : ℝ, R ≠ a • LinearMap.id + b • lorentzHodge := by
  refine ⟨{ toFun := fun X => ⁅lorentzBoost 0, X⁆
            map_add' := fun X Y => lie_add _ X Y
            map_smul' := fun c X => lie_smul c _ X }, fun a b hab => ?_⟩
  have e0 : lorentzHodge (lorentzBoost 0) = -lorentzRot 1 2 := lorentzHodge_lorentzBoost 0
  -- at `lorentzBoost 0`: `0 = a • lorentzBoost 0 - b • lorentzRot 1 2`
  have h0 := congrArg (fun T : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra => T (lorentzBoost 0)) hab
  simp only [LinearMap.coe_mk, AddHom.coe_mk, lie_self, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, e0] at h0
  have ha := congrArg
    (fun X : lorentzAlgebra =>
      (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 3 1) 0) h0
  have hb := congrArg
    (fun X : lorentzAlgebra =>
      (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 1 1) 2) h0
  simp [lorentzBoost_zero_apply, lorentzRot_one_two_apply] at ha hb
  -- at `lorentzBoost 1`: `⁅lorentzBoost 0, lorentzBoost 1⁆ ≠ 0`
  rw [← ha, hb, zero_smul, zero_smul, add_zero] at hab
  have h1 := congrArg (fun T : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra => T (lorentzBoost 1)) hab
  have h2 := congrArg
    (fun X : lorentzAlgebra =>
      (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 1 1) 0) h1
  simp [LieSubalgebra.coe_bracket, Ring.lie_def, lorentzBoost_zero_apply,
    lorentzBoost_one_apply] at h2

/-! ====================================================================================
## T5. The invariant bilinear forms of `lorentzAlgebra`
==================================================================================== -/

/-- **T5 (the trace form is invariant).** For all `X`, `Y`, `Z` in `lorentzAlgebra`,
`lorentzTraceForm ⁅Z, X⁆ Y + lorentzTraceForm X ⁅Z, Y⁆ = 0`, where `lorentzTraceForm X Y` is the
trace of the composition `X ∘ Y` of endomorphisms of `Spacetime`. -/
theorem lorentzTraceForm_invariant (X Y Z : lorentzAlgebra) :
    lorentzTraceForm ⁅Z, X⁆ Y + lorentzTraceForm X ⁅Z, Y⁆ = 0 := by
  have h := LieModule.traceForm_lieInvariant ℝ lorentzAlgebra YangMills.Spacetime Z X Y
  rw [← lorentzTraceForm_eq_traceForm] at h
  rw [h, neg_add_cancel]

/-- **T5 (the second form is invariant).** For all `X`, `Y`, `Z` in `lorentzAlgebra`, the bilinear
form `(X, Y) ↦ lorentzTraceForm (lorentzHodge X) Y` satisfies
`lorentzTraceForm (lorentzHodge ⁅Z, X⁆) Y + lorentzTraceForm (lorentzHodge X) ⁅Z, Y⁆ = 0`. -/
theorem lorentzTraceForm_lorentzHodge_invariant (X Y Z : lorentzAlgebra) :
    lorentzTraceForm (lorentzHodge ⁅Z, X⁆) Y + lorentzTraceForm (lorentzHodge X) ⁅Z, Y⁆ = 0 := by
  rw [lorentzHodge_isBracketCommuting Z X]
  exact lorentzTraceForm_invariant _ _ _

/-- **T5 (the trace form is symmetric).** For all `X`, `Y` in `lorentzAlgebra`,
`lorentzTraceForm X Y = lorentzTraceForm Y X`. -/
theorem lorentzTraceForm_comm (X Y : lorentzAlgebra) :
    lorentzTraceForm X Y = lorentzTraceForm Y X := by
  rw [lorentzTraceForm_eq_traceForm]
  exact LieModule.traceForm_comm ℝ lorentzAlgebra YangMills.Spacetime X Y

/-- **T5 (`lorentzHodge` is self-adjoint for the trace form).** For all `X`, `Y` in
`lorentzAlgebra`, `lorentzTraceForm (lorentzHodge X) Y = lorentzTraceForm X (lorentzHodge Y)`.
With `lorentzTraceForm_comm`, the bilinear form `(X, Y) ↦ lorentzTraceForm (lorentzHodge X) Y` is
symmetric. -/
theorem lorentzTraceForm_lorentzHodge_comm (X Y : lorentzAlgebra) :
    lorentzTraceForm (lorentzHodge X) Y = lorentzTraceForm X (lorentzHodge Y) := by
  have hη : ∀ i, (![1, 1, 1, -1] : Fin 4 → ℝ) i ≠ 0 := fun i => by fin_cases i <;> simp
  rw [lorentzTraceForm_eq_matrix_trace, lorentzTraceForm_eq_matrix_trace,
    lorentzAlgebraEquivEtaSkew_lorentzHodge, lorentzAlgebraEquivEtaSkew_lorentzHodge,
    LorentzLie.hodge_coe, LorentzLie.hodge_coe,
    LorentzLie.etaSkew_eq_skewMat4 two_ne_zero _ hη (LorentzLie.lorentzAlgebraEquivEtaSkew X),
    LorentzLie.etaSkew_eq_skewMat4 two_ne_zero _ hη (LorentzLie.lorentzAlgebraEquivEtaSkew Y),
    LorentzLie.hodgeMat_skewMat4, LorentzLie.hodgeMat_skewMat4]
  simp [Matrix.trace, Fin.sum_univ_four, LorentzLie.skewMat4]
  ring

namespace Centroid

/-- If `X` in `lorentzAlgebra` satisfies `lorentzTraceForm X Y = 0` for every `Y` in
`lorentzAlgebra`, then `X = 0`. -/
theorem lorentzTraceForm_separatingLeft (X : lorentzAlgebra)
    (h : ∀ Y : lorentzAlgebra, lorentzTraceForm X Y = 0) : X = 0 := by
  have hη : ∀ i, (![1, 1, 1, -1] : Fin 4 → ℝ) i ≠ 0 := fun i => by fin_cases i <;> simp
  have hM := LorentzLie.etaSkew_eq_skewMat4 two_ne_zero _ hη
    (LorentzLie.lorentzAlgebraEquivEtaSkew X)
  have hsk := (LorentzLie.mem_etaSkew_iff _ _).mp (LorentzLie.lorentzAlgebraEquivEtaSkew X).2
  have b0 := h (lorentzBoost 0)
  have b1 := h (lorentzBoost 1)
  have b2 := h (lorentzBoost 2)
  have r0 := h (lorentzRot 1 2)
  have r1 := h (lorentzRot 2 0)
  have r2 := h (lorentzRot 0 1)
  rw [lorentzTraceForm_eq_matrix_trace, lorentzAlgebraEquivEtaSkew_lorentzBoost] at b0 b1 b2
  rw [lorentzTraceForm_eq_matrix_trace, lorentzAlgebraEquivEtaSkew_lorentzRot] at r0 r1 r2
  generalize hMdef : (LorentzLie.lorentzAlgebraEquivEtaSkew X : Matrix (Fin 4) (Fin 4) ℝ) = M
    at hM hsk b0 b1 b2 r0 r1 r2
  have s01 : M 1 0 = -M 0 1 := by simpa using hsk 0 1
  have s02 : M 2 0 = -M 0 2 := by simpa using hsk 0 2
  have s03 : M 3 0 = M 0 3 := by simpa using hsk 0 3
  have s12 : M 2 1 = -M 1 2 := by simpa using hsk 1 2
  have s13 : M 3 1 = M 1 3 := by simpa using hsk 1 3
  have s23 : M 3 2 = M 2 3 := by simpa using hsk 2 3
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
    YangMills.timeAxis] at b0 b1 b2 r0 r1 r2
  have e01 : M 0 1 = 0 := by linarith
  have e02 : M 0 2 = 0 := by linarith
  have e03 : M 0 3 = 0 := by linarith
  have e12 : M 1 2 = 0 := by linarith
  have e13 : M 1 3 = 0 := by linarith
  have e23 : M 2 3 = 0 := by linarith
  have key : LorentzLie.lorentzAlgebraEquivEtaSkew X = 0 := by
    apply Subtype.ext
    rw [hMdef, hM, e01, e02, e03, e12, e13, e23]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LorentzLie.skewMat4]
  exact LorentzLie.lorentzAlgebraEquivEtaSkew.injective (key.trans (map_zero _).symm)

end Centroid

/-- **T5 (the invariant bilinear forms).** Let `B` be a real bilinear form on `lorentzAlgebra`
that is invariant: `B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0` for all `X`, `Y`, `Z`. No symmetry of `B` is
assumed. Then there is exactly one pair `(a, b)` of real numbers such that, for all `X`, `Y`,
`B X Y = a * lorentzTraceForm X Y + b * lorentzTraceForm (lorentzHodge X) Y`. (Up to
normalisation, the quadratic forms of the two forms on the right are what physicists call the
kinetic term and the θ-term of a field strength.) -/
theorem lorentzAlgebra_invariant_form (B : LinearMap.BilinForm ℝ lorentzAlgebra)
    (hB : ∀ X Y Z : lorentzAlgebra, B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0) :
    ∃! ab : ℝ × ℝ, ∀ X Y : lorentzAlgebra,
      B X Y = ab.1 * lorentzTraceForm X Y + ab.2 * lorentzTraceForm (lorentzHodge X) Y := by
  have : Module.Finite ℝ lorentzAlgebra :=
    Module.finite_of_finrank_pos (by rw [LorentzLie.finrank_lorentzAlgebra]; norm_num)
  have hnd : lorentzTraceForm.Nondegenerate :=
    ⟨Centroid.lorentzTraceForm_separatingLeft, fun Y hY =>
      Centroid.lorentzTraceForm_separatingLeft Y
        (fun X => by rw [lorentzTraceForm_comm]; exact hY X)⟩
  obtain ⟨T, hTB⟩ : ∃ T : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra,
      ∀ X Y : lorentzAlgebra, lorentzTraceForm (T X) Y = B X Y :=
    ⟨B.symmCompOfNondegenerate lorentzTraceForm hnd, fun X Y =>
      LinearMap.BilinForm.symmCompOfNondegenerate_left_apply B hnd Y X⟩
  have hTc : LorentzLie.IsBracketCommuting T := by
    intro X Y
    have h0 : T ⁅X, Y⁆ - ⁅X, T Y⁆ = 0 := by
      apply Centroid.lorentzTraceForm_separatingLeft
      intro W
      have h1 := hB Y W X
      have h2 := lorentzTraceForm_invariant (T Y) W X
      rw [hTB] at h2
      rw [map_sub, LinearMap.sub_apply, hTB]
      linarith
    exact sub_eq_zero.mp h0
  obtain ⟨⟨a, b⟩, hab, -⟩ := lorentzAlgebra_centroid_lorentzHodge T hTc
  refine ⟨(a, b), fun X Y => ?_, ?_⟩
  · rw [← hTB X Y, hab]
    simp
  · rintro ⟨a', b'⟩ h'
    have hT' : T = a' • LinearMap.id + b' • lorentzHodge := by
      refine LinearMap.ext fun X => ?_
      have h0 : T X - (a' • X + b' • lorentzHodge X) = 0 := by
        apply Centroid.lorentzTraceForm_separatingLeft
        intro W
        rw [map_sub, LinearMap.sub_apply, hTB, h' X W]
        simp
      rw [sub_eq_zero.mp h0]
      simp
    exact (lorentzAlgebra_centroid_lorentzHodge T hTc).unique hT' hab

/-- **T5 (an invariant bilinear form is symmetric).** Let `B` be a real bilinear form on
`lorentzAlgebra` that is invariant: `B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0` for all `X`, `Y`, `Z`. Then
`B X Y = B Y X` for all `X`, `Y`. -/
theorem lorentzAlgebra_invariant_form_symm (B : LinearMap.BilinForm ℝ lorentzAlgebra)
    (hB : ∀ X Y Z : lorentzAlgebra, B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0) (X Y : lorentzAlgebra) :
    B X Y = B Y X := by
  obtain ⟨ab, hab, -⟩ := lorentzAlgebra_invariant_form B hB
  rw [hab X Y, hab Y X, lorentzTraceForm_comm X Y, lorentzTraceForm_lorentzHodge_comm X Y,
    lorentzTraceForm_comm X (lorentzHodge Y)]

/-- **T5 (the invariance hypothesis is needed).** There is a real bilinear form `B` on
`lorentzAlgebra` such that for no real numbers `a`, `b` does
`B X Y = a * lorentzTraceForm X Y + b * lorentzTraceForm (lorentzHodge X) Y` hold for all `X`, `Y`.
So the conclusion of `lorentzAlgebra_invariant_form` does not hold for every bilinear form. -/
theorem exists_bilinForm_ne_smul_lorentzTraceForm :
    ∃ B : LinearMap.BilinForm ℝ lorentzAlgebra, ∀ a b : ℝ,
      ¬ ∀ X Y : lorentzAlgebra,
        B X Y = a * lorentzTraceForm X Y + b * lorentzTraceForm (lorentzHodge X) Y := by
  obtain ⟨B, hBdef⟩ : ∃ B : LinearMap.BilinForm ℝ lorentzAlgebra, ∀ X Y : lorentzAlgebra,
      B X Y = (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 3 1) 0 *
          (Y : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 1 1) 2 -
        (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 1 1) 2 *
          (Y : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 3 1) 0 :=
    ⟨LinearMap.mk₂ ℝ (fun X Y : lorentzAlgebra =>
      (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 3 1) 0 *
          (Y : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 1 1) 2 -
        (X : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 1 1) 2 *
          (Y : Module.End ℝ YangMills.Spacetime) (EuclideanSpace.single 3 1) 0)
      (fun X₁ X₂ Y => by simp; ring) (fun c X Y => by simp; ring)
      (fun X Y₁ Y₂ => by simp; ring) (fun c X Y => by simp; ring), fun X Y => rfl⟩
  refine ⟨B, fun a b h => ?_⟩
  have h1 := h (lorentzBoost 0) (lorentzRot 1 2)
  have h2 := h (lorentzRot 1 2) (lorentzBoost 0)
  have e1 : lorentzTraceForm (lorentzRot 1 2) (lorentzBoost 0) =
      lorentzTraceForm (lorentzBoost 0) (lorentzRot 1 2) := lorentzTraceForm_comm _ _
  have e2 : lorentzTraceForm (lorentzHodge (lorentzRot 1 2)) (lorentzBoost 0) =
      lorentzTraceForm (lorentzHodge (lorentzBoost 0)) (lorentzRot 1 2) := by
    rw [lorentzTraceForm_lorentzHodge_comm, lorentzTraceForm_comm]
  rw [e1, e2] at h2
  generalize lorentzTraceForm (lorentzBoost 0) (lorentzRot 1 2) = p at h1 h2
  generalize lorentzTraceForm (lorentzHodge (lorentzBoost 0)) (lorentzRot 1 2) = q at h1 h2
  rw [hBdef] at h1 h2
  simp [lorentzBoost_zero_apply, lorentzRot_one_two_apply] at h1 h2
  linarith

namespace Centroid

/-- Every `X` in `lorentzAlgebra` is a real linear combination of the six generators
`lorentzBoost 0`, `lorentzBoost 1`, `lorentzBoost 2`, `lorentzRot 1 2`, `lorentzRot 2 0`,
`lorentzRot 0 1`. -/
theorem eq_sum_generators (X : lorentzAlgebra) :
    ∃ b0 b1 b2 r0 r1 r2 : ℝ,
      X = b0 • lorentzBoost 0 + b1 • lorentzBoost 1 + b2 • lorentzBoost 2 +
        r0 • lorentzRot 1 2 + r1 • lorentzRot 2 0 + r2 • lorentzRot 0 1 := by
  have hsk := (LorentzLie.mem_etaSkew_iff _ _).mp (LorentzLie.lorentzAlgebraEquivEtaSkew X).2
  generalize hMdef : (LorentzLie.lorentzAlgebraEquivEtaSkew X : Matrix (Fin 4) (Fin 4) ℝ) = M
    at hsk
  have d0 : M 0 0 = 0 := by have := hsk 0 0; simp at this; linarith
  have d1 : M 1 1 = 0 := by have := hsk 1 1; simp at this; linarith
  have d2 : M 2 2 = 0 := by have := hsk 2 2; simp at this; linarith
  have d3 : M 3 3 = 0 := by have := hsk 3 3; simp at this; linarith
  have s01 : M 1 0 = -M 0 1 := by simpa using hsk 0 1
  have s02 : M 2 0 = -M 0 2 := by simpa using hsk 0 2
  have s03 : M 3 0 = M 0 3 := by simpa using hsk 0 3
  have s12 : M 2 1 = -M 1 2 := by simpa using hsk 1 2
  have s13 : M 3 1 = M 1 3 := by simpa using hsk 1 3
  have s23 : M 3 2 = M 2 3 := by simpa using hsk 2 3
  refine ⟨M 0 3, M 1 3, M 2 3, M 2 1, M 0 2, M 1 0, ?_⟩
  have key : M = (LorentzLie.lorentzAlgebraEquivEtaSkew
      (M 0 3 • lorentzBoost 0 + M 1 3 • lorentzBoost 1 + M 2 3 • lorentzBoost 2 +
        M 2 1 • lorentzRot 1 2 + M 0 2 • lorentzRot 2 0 + M 1 0 • lorentzRot 0 1) :
        Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lorentzAlgebraEquivEtaSkew_lorentzBoost, lorentzAlgebraEquivEtaSkew_lorentzRot,
        YangMills.timeAxis, d0, d1, d2, d3, s01, s02, s03, s12, s13, s23]
  exact LorentzLie.lorentzAlgebraEquivEtaSkew.injective (Subtype.ext (hMdef.trans key))

end Centroid

/-- **T4 (the six values determine the operator; added after the statement review).** Let `H` be a
real-linear endomorphism of `lorentzAlgebra` with `H (lorentzBoost k) = -lorentzRot (k + 1) (k + 2)`
and `H (lorentzRot (k + 1) (k + 2)) = lorentzBoost k` for every `k : Fin 3`, the sums being in
`Fin 3`. Then `H = lorentzHodge`. (No bracket-commuting hypothesis: the six generators span
`lorentzAlgebra`.) -/
theorem eq_lorentzHodge_of_generators (H : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra)
    (hb : ∀ k : Fin 3, H (lorentzBoost k) = -lorentzRot (k + 1) (k + 2))
    (hr : ∀ k : Fin 3, H (lorentzRot (k + 1) (k + 2)) = lorentzBoost k) : H = lorentzHodge := by
  refine LinearMap.ext fun X => ?_
  obtain ⟨b0, b1, b2, r0, r1, r2, rfl⟩ := Centroid.eq_sum_generators X
  have e0 : H (lorentzBoost 0) = lorentzHodge (lorentzBoost 0) :=
    (hb 0).trans (lorentzHodge_lorentzBoost 0).symm
  have e1 : H (lorentzBoost 1) = lorentzHodge (lorentzBoost 1) :=
    (hb 1).trans (lorentzHodge_lorentzBoost 1).symm
  have e2 : H (lorentzBoost 2) = lorentzHodge (lorentzBoost 2) :=
    (hb 2).trans (lorentzHodge_lorentzBoost 2).symm
  have f0 : H (lorentzRot 1 2) = lorentzHodge (lorentzRot 1 2) :=
    (hr 0).trans (lorentzHodge_lorentzRot 0).symm
  have f1 : H (lorentzRot 2 0) = lorentzHodge (lorentzRot 2 0) :=
    (hr 1).trans (lorentzHodge_lorentzRot 1).symm
  have f2 : H (lorentzRot 0 1) = lorentzHodge (lorentzRot 0 1) :=
    (hr 2).trans (lorentzHodge_lorentzRot 2).symm
  simp only [map_add, map_smul, e0, e1, e2, f0, f1, f2]

end ReleaseAdapter
