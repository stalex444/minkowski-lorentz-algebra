module
public import Mathlib
public import LorentzLie.Defs
public import LorentzLie.RealForms
public import ReleaseAdapter.Carried

@[expose] public section

/-!
# Landings of the `η`-skew matrices on Mathlib's `so'` and on the carried `Spacetime`

* `so'EquivEtaSkew` — Mathlib's `LieAlgebra.Orthogonal.so' p q ℝ`, reindexed along a bijection
  `e : p ⊕ q ≃ ι`, is `etaSkew (indefEta e)`; `so'OneThreeEquivSl2C` composes it at
  `so' (Fin 1) (Fin 3) ℝ` with `etaSkewEquivSl2C`.
* `lorentzAlgebraEquivEtaSkew` — the Lie algebra `ReleaseAdapter.lorentzAlgebra` of the
  endomorphisms of `Spacetime` skew-adjoint for `minkowskiBilin` is `etaSkew ![1, 1, 1, -1]`, by
  taking the matrix in the standard coordinates; `finrank_lorentzAlgebra` (dimension `6`);
  `lorentzAlgebraEquivSl2C`.
* `mem_lorentzAlgebra_iff_exp` — membership in `lorentzAlgebra` in terms of the one-parameter
  group `t ↦ NormedSpace.exp (t • A)`.

Helper statements are in the namespace `LorentzLie.Landings`.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

open Matrix
open scoped TensorProduct

namespace LorentzLie

open YangMills ReleaseAdapter

namespace Landings

/-- The indefinite diagonal of Mathlib's `so' p q ℝ`, reindexed along `e : p ⊕ q ≃ ι`, is the
diagonal matrix of `indefEta e`. -/
theorem reindex_indefiniteDiagonal {p q ι : Type*} [DecidableEq p] [DecidableEq q]
    [DecidableEq ι] (e : p ⊕ q ≃ ι) :
    Matrix.reindex e e (LieAlgebra.Orthogonal.indefiniteDiagonal p q ℝ) =
      Matrix.diagonal (indefEta e) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.diagonal_apply, indefEta,
    e.symm.injective.eq_iff]

/-- A matrix is in `so' p q ℝ` exactly when its reindexing along `e` is `indefEta e`-skew. -/
theorem reindex_mem_etaSkew_iff {p q ι : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] [Fintype ι] [DecidableEq ι] (e : p ⊕ q ≃ ι)
    (X : Matrix (p ⊕ q) (p ⊕ q) ℝ) :
    Matrix.reindex e e X ∈ etaSkew (indefEta e) ↔ X ∈ LieAlgebra.Orthogonal.so' p q ℝ := by
  rw [LieAlgebra.Orthogonal.so', mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule,
    mem_skewAdjointMatricesSubmodule, ← reindex_indefiniteDiagonal]
  unfold Matrix.IsSkewAdjoint Matrix.IsAdjointPair
  have h1 : Matrix.reindex e e (Xᵀ * LieAlgebra.Orthogonal.indefiniteDiagonal p q ℝ) =
      (Matrix.reindex e e X)ᵀ *
        Matrix.reindex e e (LieAlgebra.Orthogonal.indefiniteDiagonal p q ℝ) := by
    simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  have h2 : Matrix.reindex e e (LieAlgebra.Orthogonal.indefiniteDiagonal p q ℝ * -X) =
      Matrix.reindex e e (LieAlgebra.Orthogonal.indefiniteDiagonal p q ℝ) *
        -Matrix.reindex e e X := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      ← Matrix.submatrix_mul_equiv _ _ _ e.symm]
    rfl
  rw [← h1, ← h2, (Matrix.reindex e e).injective.eq_iff]

end Landings

/-- **L6 (Mathlib's `so'`, reindexed; the equivalence).** For finite types `p`, `q`, `ι` and a
bijection `e : p ⊕ q ≃ ι`: a Lie algebra equivalence over `ℝ` from Mathlib's `so' p q ℝ` to
`etaSkew (indefEta e)`, where `indefEta e i` is `1` if `e.symm i` is in `p` and `-1` if it is in
`q`. It is pinned down by `so'EquivEtaSkew_apply`. -/
noncomputable def so'EquivEtaSkew {p q ι : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] [Fintype ι] [DecidableEq ι] (e : p ⊕ q ≃ ι) :
    LieAlgebra.Orthogonal.so' p q ℝ ≃ₗ⁅ℝ⁆ etaSkew (indefEta e) :=
  LieEquiv.ofSubalgebras _ _ (Matrix.reindexLieEquiv e) <| by
    ext A
    rw [LieSubalgebra.mem_map]
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (Landings.reindex_mem_etaSkew_iff e X).mpr hX
    · intro hA
      refine ⟨Matrix.reindex e.symm e.symm A, ?_, ?_⟩
      · rw [← Landings.reindex_mem_etaSkew_iff e]
        simpa using hA
      · simp

/-- **L6 (Mathlib's `so'`, reindexed; apply).** The matrix of `so'EquivEtaSkew e X` is the matrix
of `X` reindexed along `e` in rows and columns. -/
theorem so'EquivEtaSkew_apply {p q ι : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] [Fintype ι] [DecidableEq ι] (e : p ⊕ q ≃ ι)
    (X : LieAlgebra.Orthogonal.so' p q ℝ) :
    (so'EquivEtaSkew e X : Matrix ι ι ℝ) = Matrix.reindex e e X.1 := by
  rfl

namespace Landings

/-- The diagonal of `so' (Fin 1) (Fin 3) ℝ` read along `finSumFinEquiv` is `(1, -1, -1, -1)`. -/
theorem indefEta_finSumFinEquiv :
    indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) = ![1, -1, -1, -1] := by
  have h0 : (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4).symm 0 = Sum.inl 0 := by
    rw [Equiv.symm_apply_eq]; rfl
  have h1 : (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4).symm 1 = Sum.inr 0 := by
    rw [Equiv.symm_apply_eq]; rfl
  have h2 : (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4).symm 2 = Sum.inr 1 := by
    rw [Equiv.symm_apply_eq]; rfl
  have h3 : (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4).symm 3 = Sum.inr 2 := by
    rw [Equiv.symm_apply_eq]; rfl
  funext i
  fin_cases i <;> simp [indefEta, h0, h1, h2, h3]

/-- Every entry of `indefEta finSumFinEquiv` (at `Fin 1 ⊕ Fin 3`) is `1` or `-1`. -/
theorem indefEta_one_three_sign (i : Fin 4) :
    indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) i = 1 ∨
      indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) i = -1 := by
  rw [indefEta_finSumFinEquiv]
  fin_cases i <;> simp

/-- The product of the entries of `indefEta finSumFinEquiv` (at `Fin 1 ⊕ Fin 3`) is `-1`. -/
theorem indefEta_one_three_prod :
    ∏ i, indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) i = -1 := by
  rw [indefEta_finSumFinEquiv]
  simp [Fin.prod_univ_succ]

/-- Every entry of `![1, 1, 1, -1]` is `1` or `-1`. -/
theorem eta4_sign (i : Fin 4) :
    (![1, 1, 1, -1] : Fin 4 → ℝ) i = 1 ∨ (![1, 1, 1, -1] : Fin 4 → ℝ) i = -1 := by
  fin_cases i <;> simp

/-- The product of the entries of `![1, 1, 1, -1]` is `-1`. -/
theorem eta4_prod : ∏ i, (![1, 1, 1, -1] : Fin 4 → ℝ) i = -1 := by
  simp [Fin.prod_univ_succ]

end Landings

/-- **L6 (`so' (Fin 1) (Fin 3) ℝ`; the equivalence).** A Lie algebra equivalence over `ℝ` from
Mathlib's `so' (Fin 1) (Fin 3) ℝ` to `sl(2, ℂ)` regarded as a real Lie algebra. It is pinned down
by `so'OneThreeEquivSl2C_apply`. -/
noncomputable def so'OneThreeEquivSl2C :
    LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ ≃ₗ⁅ℝ⁆ sl2CReal :=
  (so'EquivEtaSkew finSumFinEquiv).trans
    (etaSkewEquivSl2C (indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4))
      Landings.indefEta_one_three_sign Landings.indefEta_one_three_prod)

/-- **L6 (`so' (Fin 1) (Fin 3) ℝ`; apply).** Write `η = indefEta finSumFinEquiv`
(`finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`). For any proofs `hη`, `h` of the hypotheses of
`etaSkewEquivSl2C` at this `η`, `so'OneThreeEquivSl2C X` is `etaSkewEquivSl2C η hη h` applied to
`so'EquivEtaSkew finSumFinEquiv X`. -/
theorem so'OneThreeEquivSl2C_apply
    (hη : ∀ i, indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) i = 1 ∨
      indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) i = -1)
    (h : ∏ i, indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) i = -1)
    (X : LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ) :
    so'OneThreeEquivSl2C X =
      etaSkewEquivSl2C (indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4)) hη h
        (so'EquivEtaSkew finSumFinEquiv X) := by
  rfl

namespace Landings

/-- Membership in `lorentzAlgebra`, unfolded:
`minkowskiBilin (A x) y = -minkowskiBilin x (A y)` for all `x`, `y`. -/
theorem mem_lorentzAlgebra_iff (A : Module.End ℝ Spacetime) :
    A ∈ lorentzAlgebra ↔
      ∀ x y : Spacetime, minkowskiBilin (A x) y = -minkowskiBilin x (A y) := by
  change (∀ x y : Spacetime, minkowskiBilin (A x) y = (-minkowskiBilin) x (A y)) ↔ _
  simp only [LinearMap.neg_apply]

/-- The endomorphism of `Spacetime` with matrix `M` in the standard coordinates is skew-adjoint
for `minkowskiBilin` exactly when `M` is `![1, 1, 1, -1]`-skew. -/
theorem toEuclideanLin_mem_lorentzAlgebra_iff (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (Matrix.toEuclideanLin M : Module.End ℝ Spacetime) ∈ lorentzAlgebra ↔
      M ∈ etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ) := by
  rw [mem_etaSkew_iff, mem_lorentzAlgebra_iff]
  constructor
  · intro h i j
    have hij := h (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp only [minkowskiBilin_apply, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  · intro h x y
    have d0 : M 0 0 = 0 := by have := h 0 0; simp at this; linarith
    have d1 : M 1 1 = 0 := by have := h 1 1; simp at this; linarith
    have d2 : M 2 2 = 0 := by have := h 2 2; simp at this; linarith
    have d3 : M 3 3 = 0 := by have := h 3 3; simp at this; linarith
    have h01 : M 1 0 = -M 0 1 := by simpa using h 0 1
    have h02 : M 2 0 = -M 0 2 := by simpa using h 0 2
    have h03 : M 3 0 = M 0 3 := by simpa using h 0 3
    have h12 : M 2 1 = -M 1 2 := by simpa using h 1 2
    have h13 : M 3 1 = M 1 3 := by simpa using h 1 3
    have h23 : M 3 2 = M 2 3 := by simpa using h 2 3
    simp only [minkowskiBilin_apply, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    rw [d0, d1, d2, d3, h01, h02, h03, h12, h13, h23]
    ring

/-- The matrix, in the standard coordinates, of an endomorphism of `Spacetime` is
`![1, 1, 1, -1]`-skew exactly when the endomorphism is in `lorentzAlgebra`. -/
theorem toEuclideanLin_symm_mem_etaSkew_iff (A : Module.End ℝ Spacetime) :
    Matrix.toEuclideanLin.symm A ∈ etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ) ↔ A ∈ lorentzAlgebra := by
  rw [← toEuclideanLin_mem_lorentzAlgebra_iff, LinearEquiv.apply_symm_apply]

/-- `etaSkew ![1, 1, 1, -1]`, as a submodule, is the span `so31` of the six generators. -/
theorem etaSkew_toSubmodule_eq_so31 :
    (etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ)).toSubmodule = HermitianExclusion.so31 := by
  ext X
  rw [HermitianExclusion.mem_so31_iff, isEtaSkew4_iff_mem]
  exact Iff.rfl

/-- `etaSkew ![1, 1, 1, -1]` has dimension `6`. -/
theorem finrank_etaSkew_eta4 :
    Module.finrank ℝ (etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ)) = 6 := by
  have h : Module.finrank ℝ (etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ)).toSubmodule = 6 := by
    rw [etaSkew_toSubmodule_eq_so31]; exact HermitianExclusion.finrank_so31
  exact h

end Landings

/-- **L6 (`Spacetime`; matrices; the equivalence).** A Lie algebra equivalence over `ℝ` from
`lorentzAlgebra` to `etaSkew ![1, 1, 1, -1]`. It is pinned down by
`lorentzAlgebraEquivEtaSkew_apply`. -/
noncomputable def lorentzAlgebraEquivEtaSkew :
    lorentzAlgebra ≃ₗ⁅ℝ⁆ etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ) :=
  LieEquiv.ofSubalgebras _ _ (Matrix.toLpLinAlgEquiv (R := ℝ) (n := Fin 4) 2).symm.toLieEquiv <| by
    ext M
    rw [LieSubalgebra.mem_map]
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact (Landings.toEuclideanLin_symm_mem_etaSkew_iff A).mpr hA
    · intro hM
      exact ⟨Matrix.toEuclideanLin M,
        (Landings.toEuclideanLin_mem_lorentzAlgebra_iff M).mpr hM,
        (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin 4) (n := Fin 4)).symm_apply_apply M⟩

/-- **L6 (`Spacetime`; matrices; apply).** The matrix of `lorentzAlgebraEquivEtaSkew A` is the
matrix of the endomorphism `A` of `Spacetime = EuclideanSpace ℝ (Fin 4)` in the standard
coordinates (`Matrix.toEuclideanLin.symm`). -/
theorem lorentzAlgebraEquivEtaSkew_apply (A : lorentzAlgebra) :
    (lorentzAlgebraEquivEtaSkew A : Matrix (Fin 4) (Fin 4) ℝ) =
      Matrix.toEuclideanLin.symm (A : Module.End ℝ Spacetime) := by
  rfl

/-- **L6 (`Spacetime`; dimension).** The Lie algebra `lorentzAlgebra` of the endomorphisms of
`Spacetime` skew-adjoint for `minkowskiBilin` has dimension `6` over `ℝ`. -/
theorem finrank_lorentzAlgebra : Module.finrank ℝ lorentzAlgebra = 6 := by
  rw [LinearEquiv.finrank_eq lorentzAlgebraEquivEtaSkew.toLinearEquiv]
  exact Landings.finrank_etaSkew_eta4

/-- **L6 (`Spacetime`; `sl(2, ℂ)`; the equivalence).** A Lie algebra equivalence over `ℝ` from
`lorentzAlgebra` to `sl(2, ℂ)` regarded as a real Lie algebra. It is pinned down by
`lorentzAlgebraEquivSl2C_apply`. -/
noncomputable def lorentzAlgebraEquivSl2C : lorentzAlgebra ≃ₗ⁅ℝ⁆ sl2CReal :=
  lorentzAlgebraEquivEtaSkew.trans
    (etaSkewEquivSl2C (![1, 1, 1, -1] : Fin 4 → ℝ) Landings.eta4_sign Landings.eta4_prod)

/-- **L6 (`Spacetime`; `sl(2, ℂ)`; apply).** For any proofs `hη`, `h` of the hypotheses of
`etaSkewEquivSl2C` at `![1, 1, 1, -1]`, `lorentzAlgebraEquivSl2C A` is
`etaSkewEquivSl2C ![1, 1, 1, -1] hη h` applied to `lorentzAlgebraEquivEtaSkew A`. -/
theorem lorentzAlgebraEquivSl2C_apply
    (hη : ∀ i, (![1, 1, 1, -1] : Fin 4 → ℝ) i = 1 ∨ (![1, 1, 1, -1] : Fin 4 → ℝ) i = -1)
    (h : ∏ i, (![1, 1, 1, -1] : Fin 4 → ℝ) i = -1) (A : lorentzAlgebra) :
    lorentzAlgebraEquivSl2C A =
      etaSkewEquivSl2C (![1, 1, 1, -1] : Fin 4 → ℝ) hη h (lorentzAlgebraEquivEtaSkew A) := by
  rfl

namespace Landings

/-- The continuous endomorphisms of `Spacetime` form a complete space (a shortcut for instance
search, by finite dimensionality). -/
theorem completeSpace_spacetimeEnd : CompleteSpace (Spacetime →L[ℝ] Spacetime) :=
  FiniteDimensional.complete ℝ _

attribute [local instance] completeSpace_spacetimeEnd

/-- Along `s ↦ NormedSpace.exp (s • A) x`, each coordinate has derivative the coordinate of
`A (NormedSpace.exp (t • A) x)`. -/
theorem hasDerivAt_exp_apply_coord (A : Spacetime →L[ℝ] Spacetime) (x : Spacetime) (t : ℝ)
    (i : Fin 4) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A) x) i)
      ((A (NormedSpace.exp (t • A) x)) i) t := by
  have h1 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) x)
      (A (NormedSpace.exp (t • A) x)) t := by
    have h := (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t x)
    simpa using h
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t h1

/-- The derivative of `s ↦ minkowskiBilin (exp (s • A) x) (exp (s • A) y)`. -/
theorem hasDerivAt_minkowskiBilin_exp (A : Spacetime →L[ℝ] Spacetime) (x y : Spacetime)
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => minkowskiBilin (NormedSpace.exp (s • A) x) (NormedSpace.exp (s • A) y))
      (minkowskiBilin (A (NormedSpace.exp (t • A) x)) (NormedSpace.exp (t • A) y) +
        minkowskiBilin (NormedSpace.exp (t • A) x) (A (NormedSpace.exp (t • A) y))) t := by
  have hx := hasDerivAt_exp_apply_coord A x t
  have hy := hasDerivAt_exp_apply_coord A y t
  have h := ((hx 3).mul (hy 3)).sub
    ((((hx 0).mul (hy 0)).add ((hx 1).mul (hy 1))).add ((hx 2).mul (hy 2)))
  convert h using 1
  · funext s
    simp only [minkowskiBilin_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  · simp only [minkowskiBilin_apply]
    ring

/-- If `A` is in `lorentzAlgebra`, every `exp (t • A)` preserves `minkowskiBilin`. -/
theorem minkowskiBilin_exp_of_mem (A : Spacetime →L[ℝ] Spacetime)
    (hA : A.toLinearMap ∈ lorentzAlgebra) (t : ℝ) (x y : Spacetime) :
    minkowskiBilin (NormedSpace.exp (t • A) x) (NormedSpace.exp (t • A) y) =
      minkowskiBilin x y := by
  have hd : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => minkowskiBilin (NormedSpace.exp (s • A) x) (NormedSpace.exp (s • A) y))
      0 s := by
    intro s
    have h := hasDerivAt_minkowskiBilin_exp A x y s
    have h0 := (mem_lorentzAlgebra_iff A.toLinearMap).mp hA
      (NormedSpace.exp (s • A) x) (NormedSpace.exp (s • A) y)
    simp only [ContinuousLinearMap.coe_coe] at h0
    rw [h0, neg_add_cancel] at h
    exact h
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have h0 : (0 : ℝ) • A = 0 := zero_smul ℝ A
  rw [h0, NormedSpace.exp_zero] at hc
  exact hc

/-- `exp (A + B) = exp A * exp B` for commuting continuous endomorphisms of `Spacetime`. -/
theorem exp_add_of_commute_spacetime {A B : Spacetime →L[ℝ] Spacetime} (h : Commute A B) :
    NormedSpace.exp (A + B) = NormedSpace.exp A * NormedSpace.exp B := by
  have hr := NormedSpace.expSeries_radius_eq_top ℝ (Spacetime →L[ℝ] Spacetime)
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    (hr.symm ▸ edist_lt_top _ _) (hr.symm ▸ edist_lt_top _ _)

/-- `exp (s • A) * exp (t • A) = exp ((s + t) • A)`. -/
theorem exp_smul_mul_exp_smul (A : Spacetime →L[ℝ] Spacetime) (s t : ℝ) :
    NormedSpace.exp (s • A) * NormedSpace.exp (t • A) = NormedSpace.exp ((s + t) • A) := by
  have h1 : (s + t) • A = s • A + t • A := add_smul s t A
  have h2 : Commute (s • A) (t • A) := by
    change (s • A) * (t • A) = (t • A) * (s • A)
    ext x i
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      FunLike.coe_smul, Pi.smul_apply, map_smul, smul_smul, mul_comm]
  rw [h1, exp_add_of_commute_spacetime h2]

/-- `exp ((-t) • A) * exp (t • A) = 1`. -/
theorem exp_neg_smul_mul_exp_smul (A : Spacetime →L[ℝ] Spacetime) (t : ℝ) :
    NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) = 1 := by
  have h0 : (0 : ℝ) • A = 0 := zero_smul ℝ A
  rw [exp_smul_mul_exp_smul, neg_add_cancel, h0, NormedSpace.exp_zero]

/-- `exp (t • A) * exp ((-t) • A) = 1`. -/
theorem exp_smul_mul_exp_neg_smul (A : Spacetime →L[ℝ] Spacetime) (t : ℝ) :
    NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A) = 1 := by
  have h0 : (0 : ℝ) • A = 0 := zero_smul ℝ A
  rw [exp_smul_mul_exp_smul, add_neg_cancel, h0, NormedSpace.exp_zero]

/-- Polarization: `minkowskiBilin` in terms of `minkowskiSquare`. -/
theorem minkowskiBilin_eq_polar (x y : Spacetime) :
    minkowskiBilin x y =
      (minkowskiSquare (x + y) - minkowskiSquare x - minkowskiSquare y) / 2 := by
  rw [← minkowskiBilin_self, ← minkowskiBilin_self, ← minkowskiBilin_self]
  simp only [minkowskiBilin_apply, PiLp.add_apply]
  ring

/-- A linear map preserving `minkowskiSquare` preserves `minkowskiBilin`. -/
theorem minkowskiBilin_of_minkowskiSquare (g : Spacetime →ₗ[ℝ] Spacetime)
    (hq : ∀ x, minkowskiSquare (g x) = minkowskiSquare x) (x y : Spacetime) :
    minkowskiBilin (g x) (g y) = minkowskiBilin x y := by
  rw [minkowskiBilin_eq_polar, minkowskiBilin_eq_polar x y, ← map_add, hq, hq, hq]

/-- If every `exp (t • A)` preserves `minkowskiSquare`, then `A` is in `lorentzAlgebra`. -/
theorem mem_lorentzAlgebra_of_minkowskiSquare_exp (A : Spacetime →L[ℝ] Spacetime)
    (h : ∀ (t : ℝ) (x : Spacetime),
      minkowskiSquare (NormedSpace.exp (t • A) x) = minkowskiSquare x) :
    A.toLinearMap ∈ lorentzAlgebra := by
  rw [mem_lorentzAlgebra_iff]
  intro x y
  have hconst : (fun s : ℝ =>
      minkowskiBilin (NormedSpace.exp (s • A) x) (NormedSpace.exp (s • A) y)) =
      fun _ => minkowskiBilin x y := by
    funext s
    exact minkowskiBilin_of_minkowskiSquare (NormedSpace.exp (s • A)).toLinearMap (h s) x y
  have hd := hasDerivAt_minkowskiBilin_exp A x y 0
  rw [hconst] at hd
  have h0 := hd.unique (hasDerivAt_const (0 : ℝ) (minkowskiBilin x y))
  have hz : (0 : ℝ) • A = 0 := zero_smul ℝ A
  rw [hz, NormedSpace.exp_zero] at h0
  have h0' : minkowskiBilin (A x) y + minkowskiBilin x (A y) = 0 := h0
  change minkowskiBilin (A x) y = -minkowskiBilin x (A y)
  linarith

/-- Real arithmetic behind the cone clause: if `w` has form value `1` and positive last
coordinate, `u` has nonnegative form value, and the form pairing of `u` and `w` is nonnegative,
then the last coordinate of `u` is nonnegative. -/
theorem last_nonneg_arith (u0 u1 u2 u3 w0 w1 w2 w3 : ℝ)
    (ha : w3 ^ 2 - (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) = 1)
    (hb : 0 ≤ u3 ^ 2 - (u0 ^ 2 + u1 ^ 2 + u2 ^ 2))
    (hc : 0 ≤ u3 * w3 - (u0 * w0 + u1 * w1 + u2 * w2)) (hw : 0 < w3) : 0 ≤ u3 := by
  by_contra hneg
  rw [not_le] at hneg
  have h1 : u3 * w3 < 0 := mul_neg_of_neg_of_pos hneg hw
  have h2 : (u3 * w3) ^ 2 ≤ (u0 * w0 + u1 * w1 + u2 * w2) ^ 2 := by
    have := mul_nonneg_of_nonpos_of_nonpos
      (show (u0 * w0 + u1 * w1 + u2 * w2) - u3 * w3 ≤ 0 by linarith)
      (show (u0 * w0 + u1 * w1 + u2 * w2) + u3 * w3 ≤ 0 by linarith)
    nlinarith
  have hCS : (u0 * w0 + u1 * w1 + u2 * w2) ^ 2 ≤
      (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) := by
    nlinarith [sq_nonneg (u0 * w1 - u1 * w0), sq_nonneg (u0 * w2 - u2 * w0),
      sq_nonneg (u1 * w2 - u2 * w1)]
  have hW0 : 0 ≤ w0 ^ 2 + w1 ^ 2 + w2 ^ 2 := by positivity
  have h3 : (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) ≤
      u3 ^ 2 * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hW0
  have hW : w0 ^ 2 + w1 ^ 2 + w2 ^ 2 = w3 ^ 2 - 1 := by linarith
  rw [hW] at h3 hCS
  have h4 : u3 ^ 2 ≤ 0 := by
    have h5 : (u3 * w3) ^ 2 = u3 ^ 2 * w3 ^ 2 := by ring
    have h6 : u3 ^ 2 * (w3 ^ 2 - 1) = u3 ^ 2 * w3 ^ 2 - u3 ^ 2 := by ring
    linarith
  nlinarith [mul_pos_of_neg_of_neg hneg hneg]

/-- The carried forward cone in coordinates. -/
theorem mem_forwardCone_iff (x : Spacetime) :
    x ∈ forwardCone ↔ 0 ≤ x 3 ∧ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ x 3 ^ 2 := by
  have hn : ‖spatial x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [spatial, Fin.sum_univ_three]
  have ht : time x = x 3 := rfl
  change ‖spatial x‖ ≤ time x ↔ _
  rw [ht, ← hn]
  constructor
  · intro h
    exact ⟨le_trans (norm_nonneg _) h, pow_le_pow_left₀ (norm_nonneg _) h 2⟩
  · rintro ⟨h0, h2⟩
    exact (sq_le_sq₀ (norm_nonneg _) h0).mp h2

/-- A linear map preserving `minkowskiBilin` maps the forward cone into itself, or its negative
does. -/
theorem forwardCone_or (g : Spacetime →ₗ[ℝ] Spacetime)
    (hB : ∀ x y, minkowskiBilin (g x) (g y) = minkowskiBilin x y) :
    (∀ x ∈ forwardCone, g x ∈ forwardCone) ∨ (∀ x ∈ forwardCone, -(g x) ∈ forwardCone) := by
  have ha := hB (EuclideanSpace.single (3 : Fin 4) (1 : ℝ)) (EuclideanSpace.single 3 1)
  have h2' := fun x => hB x (EuclideanSpace.single (3 : Fin 4) (1 : ℝ))
  generalize g (EuclideanSpace.single (3 : Fin 4) (1 : ℝ)) = w at ha h2'
  simp only [minkowskiBilin_apply] at ha h2'
  simp at ha h2'
  have hw : w 3 ^ 2 - (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) = 1 := by linarith
  have key : ∀ x ∈ forwardCone,
      0 ≤ (g x) 3 ^ 2 - ((g x) 0 ^ 2 + (g x) 1 ^ 2 + (g x) 2 ^ 2) ∧
      0 ≤ (g x) 3 * w 3 - ((g x) 0 * w 0 + (g x) 1 * w 1 + (g x) 2 * w 2) := by
    intro x hx
    rw [mem_forwardCone_iff] at hx
    have h1 := hB x x
    simp only [minkowskiBilin_apply] at h1
    have h2 := h2' x
    constructor
    · nlinarith [hx.2]
    · linarith [hx.1]
  have hw3 : w 3 ≠ 0 := by
    intro h0
    rw [h0] at hw
    nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
  rcases lt_or_gt_of_ne hw3 with hneg | hpos
  · right
    intro x hx
    obtain ⟨k1, k2⟩ := key x hx
    rw [mem_forwardCone_iff]
    simp only [PiLp.neg_apply, neg_sq]
    refine ⟨?_, by linarith⟩
    exact last_nonneg_arith (-(g x) 0) (-(g x) 1) (-(g x) 2) (-(g x) 3) (-w 0) (-w 1) (-w 2)
      (-w 3) (by simp only [neg_sq]; exact hw) (by simp only [neg_sq]; exact k1)
      (by simp only [neg_mul_neg]; exact k2) (by linarith)
  · left
    intro x hx
    obtain ⟨k1, k2⟩ := key x hx
    rw [mem_forwardCone_iff]
    exact ⟨last_nonneg_arith _ _ _ _ _ _ _ _ hw k1 k2 hpos, by linarith⟩

/-- A linear endomorphism of `Spacetime` preserving `minkowskiBilin` has determinant of square
`1`. -/
theorem det_sq_of_minkowskiBilin (g : Spacetime →ₗ[ℝ] Spacetime)
    (hB : ∀ x y, minkowskiBilin (g x) (g y) = minkowskiBilin x y) :
    LinearMap.det g ^ 2 = 1 := by
  obtain ⟨M, rfl⟩ : ∃ M : Matrix (Fin 4) (Fin 4) ℝ, Matrix.toEuclideanLin M = g :=
    ⟨Matrix.toEuclideanLin.symm g, LinearEquiv.apply_symm_apply _ _⟩
  have hM : Mᵀ * Matrix.diagonal (![1, 1, 1, -1] : Fin 4 → ℝ) * M =
      Matrix.diagonal (![1, 1, 1, -1] : Fin 4 → ℝ) := by
    ext i j
    have hij := hB (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp only [minkowskiBilin_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] at hij
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] at hij ⊢ <;> linarith
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, eta4_prod]
    at hdet
  rw [show LinearMap.det (Matrix.toEuclideanLin M) = M.det from LinearMap.det_toLpLin 2 M]
  linear_combination -hdet

end Landings

/-- **L6 (`Spacetime`; one-parameter groups).** For a continuous linear endomorphism `A` of
`Spacetime`: `A` belongs to `lorentzAlgebra` if and only if for every real `t` the exponential
`NormedSpace.exp (t • A)` is the underlying map of an element of `ProperLorentz`. -/
theorem mem_lorentzAlgebra_iff_exp (A : Spacetime →L[ℝ] Spacetime) :
    A.toLinearMap ∈ lorentzAlgebra ↔
      ∀ t : ℝ, ∃ g : ProperLorentz, g.val.val = NormedSpace.exp (t • A) := by
  constructor
  · intro hA t
    have hform : ∀ (s : ℝ) (x y : Spacetime),
        minkowskiBilin (NormedSpace.exp (s • A) x) (NormedSpace.exp (s • A) y) =
          minkowskiBilin x y := fun s => Landings.minkowskiBilin_exp_of_mem A hA s
    have hhalf : ∀ s : ℝ, NormedSpace.exp (s • A) =
        NormedSpace.exp ((s / 2) • A) * NormedSpace.exp ((s / 2) • A) := by
      intro s
      rw [Landings.exp_smul_mul_exp_smul, add_halves]
    have hcone : ∀ s : ℝ, ∀ x ∈ forwardCone, NormedSpace.exp (s • A) x ∈ forwardCone := by
      intro s x hx
      rw [hhalf s]
      change NormedSpace.exp ((s / 2) • A) (NormedSpace.exp ((s / 2) • A) x) ∈ forwardCone
      rcases Landings.forwardCone_or (NormedSpace.exp ((s / 2) • A)).toLinearMap
        (hform (s / 2)) with h | h
      · exact h _ (h x hx)
      · have h1 := h _ (h x hx)
        simpa using h1
    refine ⟨⟨⟨NormedSpace.exp (t • A), NormedSpace.exp ((-t) • A),
      Landings.exp_smul_mul_exp_neg_smul A t, Landings.exp_neg_smul_mul_exp_smul A t⟩,
      ?_, ?_, ?_⟩, rfl⟩
    · change LinearMap.det (NormedSpace.exp (t • A)).toLinearMap = 1
      rw [hhalf t]
      have hd := Landings.det_sq_of_minkowskiBilin
        (NormedSpace.exp ((t / 2) • A)).toLinearMap (hform (t / 2))
      rw [show ((NormedSpace.exp ((t / 2) • A) * NormedSpace.exp ((t / 2) • A) :
          Spacetime →L[ℝ] Spacetime) : Spacetime →ₗ[ℝ] Spacetime) =
          (NormedSpace.exp ((t / 2) • A)).toLinearMap *
            (NormedSpace.exp ((t / 2) • A)).toLinearMap from rfl, map_mul, ← sq]
      exact hd
    · intro x
      change minkowskiSquare (NormedSpace.exp (t • A) x) = minkowskiSquare x
      rw [← minkowskiBilin_self, ← minkowskiBilin_self]
      exact hform t x x
    · intro x
      change NormedSpace.exp (t • A) x ∈ forwardCone ↔ x ∈ forwardCone
      refine ⟨fun h => ?_, hcone t x⟩
      have h1 := hcone (-t) _ h
      have h2 : NormedSpace.exp ((-t) • A) (NormedSpace.exp (t • A) x) = x :=
        congrArg (fun f : Spacetime →L[ℝ] Spacetime => f x)
          (Landings.exp_neg_smul_mul_exp_smul A t)
      rwa [h2] at h1
  · intro h
    apply Landings.mem_lorentzAlgebra_of_minkowskiSquare_exp
    intro t x
    obtain ⟨g, hg⟩ := h t
    have hq := g.2.2.1 x
    rw [← hg]
    exact hq

end LorentzLie
