module
public import Mathlib
public import LorentzLie.Landings
public import LorentzLie.Complexification
public import LorentzLie.Controls
public import ReleaseAdapter.Centroid

@[expose] public section
/-!
# The Lorentz Lie algebra of four-dimensional Minkowski space: proofs of the compared statements

Each of the nine statements of `Challenge.lean` is proved here, with the identical statement.

Layout.
* The definitions of this entry (namespace `MinkowskiLorentz`) are repeated here verbatim, before
  any other declaration and in the order of `Challenge.lean`.
* The carried block (namespace `YangMills`) is not repeated in this file. It is declared by the
  library module `ReleaseAdapter/Carried.lean`, which this file imports through
  `ReleaseAdapter.Centroid`. The block of that module, between its markers `BEGIN CARRIED` and
  `END CARRIED`, is the same text as the block of `Challenge.lean`.
* The helper declarations are in the namespace `MinkowskiLorentz.Bridge`. They show that the
  entry's definitions are the library's (`lorentzAlgebra_eq`, `sl2CRealMat_eq`, `hodgeMatrix_eq`,
  `lorentzHodge_coe`, `form_eq`) and carry the library's theorems to the statements as compared.

The library, by module, and the statements it proves.
* Statement 1: `LorentzLie.so'OneThreeEquivSl2C` (`LorentzLie/Landings.lean`), which is
  `so'EquivEtaSkew` followed by `etaSkewEquivSl2C` (`LorentzLie/RealForms.lean`); the formula is
  `Bridge.s1_apply`.
* Statement 2: (a) `LorentzLie.finrank_lorentzAlgebra`; (b) `LorentzLie.lorentzAlgebraEquivSl2C`
  (`LorentzLie/Landings.lean`) followed by the conjugation `x ↦ g x g⁻¹` of `sl(2, ℂ)` with
  `g = !![1, -1; 1, 1]` (`Bridge.conjG`, `Bridge.e2`); the composite has the values stated
  (`Bridge.e2_apply`); (c) `ReleaseAdapter.lorentzBoost`, `ReleaseAdapter.lorentzRot`
  (`ReleaseAdapter/CentroidDefs.lean`) for the memberships, and a direct computation for the
  values (`Bridge.spinMatrix_boostEnd`, `Bridge.spinMatrix_rotEnd`).
* Statement 3: (a) `ReleaseAdapter.minkowskiBilin_self` (`ReleaseAdapter/Carried.lean`);
  (b) `LorentzLie.mem_lorentzAlgebra_iff_exp` (`LorentzLie/Landings.lean`).
* Statement 4: `ReleaseAdapter.lorentzHodge` (`ReleaseAdapter/CentroidDefs.lean`) with
  `lorentzHodge_isBracketCommuting`, `lorentzHodge_lorentzHodge`, `lorentzHodge_lorentzBoost`,
  `lorentzHodge_lorentzRot` (`ReleaseAdapter/Centroid.lean`); the clause on multiplication by
  `-i` is computed here (`Bridge.spinOf_hodgeMatrix`).
* Statement 5: `LorentzLie.lorentzAlgebraEquivEtaSkew` (`LorentzLie/Landings.lean`), and
  `tensorEquivC`, `etaSkewCEquiv`, `etaSkewCEquiv_hodgeProj`
  (`LorentzLie/Complexification.lean`); the transport to `ℂ ⊗[ℝ] lorentzAlgebra` is built here
  (`Bridge.baseChangeEquiv`, `Bridge.psi`, `Bridge.bigE`, `Bridge.s5`).
* Statement 6: `ReleaseAdapter.lorentzAlgebra_invariant_form`,
  `lorentzAlgebra_invariant_form_symm`, `lorentzTraceForm_invariant`,
  `lorentzTraceForm_lorentzHodge_invariant` (`ReleaseAdapter/Centroid.lean`). The proof of
  `lorentzAlgebra_invariant_form` uses `ReleaseAdapter.lorentzAlgebra_centroid_lorentzHodge`, the
  classification of the linear maps `R` of `lorentzAlgebra` with `R ⁅X, Y⁆ = ⁅X, R Y⁆`. That
  classification is used here and is not a compared statement of this entry.
* Statement 7: `LorentzLie.etaSkewEquivSo3Prod`, `LorentzLie.etaSkewEquivSl2RProd`
  (`LorentzLie/RealForms.lean`); `LorentzLie.etaSkew_isSimple` and
  `LorentzLie.Controls.not_isSimple_of_prod_eq_one` (`LorentzLie/Controls.lean`) with
  `Bridge.isSimple_of_lieEquiv`.
* Statement 8: `ReleaseAdapter.exists_bilinForm_ne_smul_lorentzTraceForm`
  (`ReleaseAdapter/Centroid.lean`).
* Statement 9: proved here (`Bridge.s9`): `A = 2π J` for an endomorphism `J` with `J * J = -1`,
  so `exp A = 1`, and `A` is not skew-adjoint for the Minkowski form.

Provenance of the library modules. The modules under `LorentzLie/` and `ReleaseAdapter/` are the
proof library of this entry. The seven modules under `ArithmeticLorentz/` are modules of the
author's earlier library, copied unchanged; the module `GravityScreening/SignedLieGeneration.lean`
is copied unchanged from an earlier repository of the author's. `README.md` gives the
repositories and commits.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

namespace MinkowskiLorentz

open YangMills
open scoped TensorProduct

/-! ### Definitions of this entry -/

/-- The Minkowski bilinear form on `Spacetime`, time at index `3` and positive:
`minkowskiBilin x y = x₃ y₃ - (x₀ y₀ + x₁ y₁ + x₂ y₂)`. Its quadratic form is the carried
`minkowskiSquare` (statement 3). The four proofs show additivity and homogeneity in each
argument. -/
def minkowskiBilin : LinearMap.BilinForm ℝ Spacetime :=
  LinearMap.mk₂ ℝ (fun x y => x 3 * y 3 - (x 0 * y 0 + x 1 * y 1 + x 2 * y 2))
    (fun x₁ x₂ y => by simp only [PiLp.add_apply]; ring)
    (fun c x y => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)
    (fun x y₁ y₂ => by simp only [PiLp.add_apply]; ring)
    (fun c x y => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)

/-- The Lorentz Lie algebra `L`: the Lie subalgebra of the linear endomorphisms `A` of
`Spacetime` that are skew-adjoint for the Minkowski form,
`minkowskiBilin (A x) y = -minkowskiBilin x (A y)` for all `x`, `y`, with the commutator
bracket `⁅A, B⁆ = A ∘ B - B ∘ A`. This is Mathlib's `skewAdjointLieSubalgebra`. -/
def lorentzAlgebra : LieSubalgebra ℝ (Module.End ℝ Spacetime) :=
  skewAdjointLieSubalgebra minkowskiBilin

/-- The boost generator along the space axis `k`: the endomorphism `x ↦ x₃ e_k + x_k e₃` of
`Spacetime`, with matrix `E k 3 + E 3 k` in the standard coordinates (`3` is the time axis). -/
def boostEnd (k : Fin 3) : Module.End ℝ Spacetime :=
  Matrix.toEuclideanLin (Matrix.single k.castSucc timeAxis (1 : ℝ) +
    Matrix.single timeAxis k.castSucc (1 : ℝ))

/-- The rotation generator in the plane of the space axes `i` and `j`: the endomorphism
`x ↦ x_i e_j - x_j e_i` of `Spacetime` (`e_i ↦ e_j`, `e_j ↦ -e_i`), with matrix `E j i - E i j`
in the standard coordinates. It is `0` for `i = j`. -/
def rotEnd (i j : Fin 3) : Module.End ℝ Spacetime :=
  Matrix.toEuclideanLin (Matrix.single j.castSucc i.castSucc (1 : ℝ) -
    Matrix.single i.castSucc j.castSucc (1 : ℝ))

/-- The operator `H` on `4 × 4` real matrices, entry by entry: `hodgeMatrix X = ⋆(η X) η`, where
`η = diag(1, 1, 1, -1)` (the negative of the matrix of `minkowskiBilin`; the operator is the same
for `-η`; time at index `3`) and, for a matrix `F`, `⋆F` is the antisymmetric
matrix with `(⋆F) i j = ε · F k l` for `i < j`, where `k < l` are the two other indices and `ε`
is the sign of the permutation `(i, j, k, l)` of `(0, 1, 2, 3)` (so `ε₀₁₂₃ = +1`; no index is
raised inside `⋆`). Only the entries of `X` above the diagonal are used. On a matrix `X` with
`X 3 k = X k 3` and `X i j = -X j i` for space indices `i`, `j` (the matrices of
`lorentzAlgebra`), with `β_k = X k 3` and `θ_k = X (k + 2) (k + 1)`, it is
`(β, θ) ↦ (θ, -β)`; statement 4 gives the values on the six generators.
Relation to the Hodge dual of two-forms, for `X` in `lorentzAlgebra` and `F = η X`:
`η · hodgeMatrix X` is the matrix `½ ε_{μνρσ} F^{ρσ}`, indices raised with `η`, for the
alternating symbol with lower indices normalised by `ε = +1` on the index order `(3, 0, 1, 2)`
(time first); for the symbol with upper indices normalised by `ε = +1` on that order it is the
negative of that matrix. -/
def hodgeMatrix (X : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, X 2 3, -X 1 3, -X 1 2;
     -X 2 3, 0, X 0 3, X 0 2;
     X 1 3, -X 0 3, 0, -X 0 1;
     -X 1 2, X 0 2, -X 0 1, 0]

/-- The operator `H` on endomorphisms of `Spacetime`: `hodgeEnd A` is the endomorphism whose
matrix in the standard coordinates is `hodgeMatrix` of the matrix of `A`. It is defined on all
endomorphisms; statement 4 is about its restriction to `lorentzAlgebra`. -/
def hodgeEnd (A : Module.End ℝ Spacetime) : Module.End ℝ Spacetime :=
  Matrix.toEuclideanLin (hodgeMatrix (Matrix.toEuclideanLin.symm A))

/-- `sl(2, ℂ)` regarded as a real Lie algebra: Mathlib's `sl (Fin 2) ℂ`, the complex `2 × 2`
matrices of trace zero with the commutator bracket, with scalars restricted to `ℝ`. -/
abbrev sl2CReal := RestrictScalars ℝ ℂ (LieAlgebra.SpecialLinear.sl (Fin 2) ℂ)

/-- The underlying complex `2 × 2` matrix of an element of `sl2CReal`. -/
def sl2CRealMat (x : sl2CReal) : Matrix (Fin 2) (Fin 2) ℂ :=
  (RestrictScalars.addEquiv ℝ ℂ (LieAlgebra.SpecialLinear.sl (Fin 2) ℂ) x).1

/-- The Pauli matrices: `pauli 0 = σ₁ = !![0, 1; 1, 0]`, `pauli 1 = σ₂ = !![0, -i; i, 0]`,
`pauli 2 = σ₃ = !![1, 0; 0, -1]`. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- The complex `2 × 2` matrix `-½ Σ_k (β_k + i θ_k) σ_k` for real triples `β`, `θ`, with
`σ_k = pauli k`. The factor `½` is written `1 / ((2 : ℕ) : ℂ)`, the natural number `2` read in
`ℂ`; its value is `1 / 2`. -/
def spinOf (β θ : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ k : Fin 3, (-(1 / ((2 : ℕ) : ℂ)) * ((β k : ℂ) + (θ k : ℂ) * Complex.I)) • pauli k

/-- The complex `2 × 2` matrix of an endomorphism `A` of `Spacetime`:
`spinMatrix A = -½ Σ_k (β_k + i θ_k) σ_k`, where, with `M` the matrix of `A` in the standard
coordinates, `β_k = M k 3` (row the space axis `k`, column the time axis) and
`θ_k = M (k + 2) (k + 1)` (space axes, the sums in `Fin 3`). It is defined on all endomorphisms;
statements 2 and 4 are about its restriction to `lorentzAlgebra`. -/
def spinMatrix (A : Module.End ℝ Spacetime) : Matrix (Fin 2) (Fin 2) ℂ :=
  spinOf (fun k => Matrix.toEuclideanLin.symm A k.castSucc timeAxis)
    (fun k => Matrix.toEuclideanLin.symm A (k + 2).castSucc (k + 1).castSucc)

/-! ### Bridge helpers: the entry's definitions are the library's -/

namespace Bridge

/-- The entry's Lie algebra is the library's (identical definitions). -/
theorem lorentzAlgebra_eq : lorentzAlgebra = ReleaseAdapter.lorentzAlgebra := rfl

/-- The entry's `sl2CRealMat` is the library's. -/
theorem sl2CRealMat_eq (x : sl2CReal) : sl2CRealMat x = LorentzLie.sl2CRealMat x := rfl

/-- The explicit matrix formula is the library's `hodgeMat` at `![1, 1, 1, -1]`. -/
theorem hodgeMatrix_eq (X : Matrix (Fin 4) (Fin 4) ℝ) :
    hodgeMatrix X = LorentzLie.hodgeMat (![1, 1, 1, -1] : Fin 4 → ℝ) X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hodgeMatrix, LorentzLie.hodgeMat, LorentzLie.star0, Matrix.mul_apply,
      Matrix.diagonal_apply]

/-- The underlying endomorphism of the library's `lorentzHodge X` is `hodgeEnd X`. -/
theorem lorentzHodge_coe (X : ReleaseAdapter.lorentzAlgebra) :
    ((ReleaseAdapter.lorentzHodge X : ReleaseAdapter.lorentzAlgebra) :
      Module.End ℝ Spacetime) = hodgeEnd X := by
  rw [ReleaseAdapter.lorentzHodge_coe, hodgeEnd, hodgeMatrix_eq]

/-- The two forms of statement 6 are the library's `lorentzTraceForm` and
`lorentzTraceForm (lorentzHodge ·) ·`. -/
theorem form_eq (a b : ℝ) (X Y : ReleaseAdapter.lorentzAlgebra) :
    a * LieModule.traceForm ℝ ReleaseAdapter.lorentzAlgebra Spacetime X Y +
        b * LinearMap.trace ℝ Spacetime
          (hodgeEnd (X : Module.End ℝ Spacetime) * (Y : Module.End ℝ Spacetime)) =
      a * ReleaseAdapter.lorentzTraceForm X Y +
        b * ReleaseAdapter.lorentzTraceForm (ReleaseAdapter.lorentzHodge X) Y := by
  rw [← lorentzHodge_coe X, ReleaseAdapter.lorentzTraceForm_eq_traceForm]
  rfl

/-- Statement 6 on the library's objects. -/
theorem s6 (B : LinearMap.BilinForm ℝ ReleaseAdapter.lorentzAlgebra) :
    ((∀ X Y Z : ReleaseAdapter.lorentzAlgebra, B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0) ↔
      ∃! ab : ℝ × ℝ, ∀ X Y : ReleaseAdapter.lorentzAlgebra,
        B X Y = ab.1 * LieModule.traceForm ℝ ReleaseAdapter.lorentzAlgebra Spacetime X Y +
          ab.2 * LinearMap.trace ℝ Spacetime
            (hodgeEnd (X : Module.End ℝ Spacetime) * (Y : Module.End ℝ Spacetime))) ∧
    ((∀ X Y Z : ReleaseAdapter.lorentzAlgebra, B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0) →
      ∀ X Y : ReleaseAdapter.lorentzAlgebra, B X Y = B Y X) := by
  have hiff : ∀ ab : ℝ × ℝ,
      (∀ X Y : ReleaseAdapter.lorentzAlgebra,
        B X Y = ab.1 * LieModule.traceForm ℝ ReleaseAdapter.lorentzAlgebra Spacetime X Y +
          ab.2 * LinearMap.trace ℝ Spacetime
            (hodgeEnd (X : Module.End ℝ Spacetime) * (Y : Module.End ℝ Spacetime))) ↔
      (∀ X Y : ReleaseAdapter.lorentzAlgebra,
        B X Y = ab.1 * ReleaseAdapter.lorentzTraceForm X Y +
          ab.2 * ReleaseAdapter.lorentzTraceForm (ReleaseAdapter.lorentzHodge X) Y) := by
    intro ab
    constructor
    · intro h X Y
      rw [← form_eq]
      exact h X Y
    · intro h X Y
      rw [form_eq]
      exact h X Y
  refine ⟨⟨fun hB => ?_, fun hex => ?_⟩,
    fun hB => ReleaseAdapter.lorentzAlgebra_invariant_form_symm B hB⟩
  · exact (existsUnique_congr hiff).mpr (ReleaseAdapter.lorentzAlgebra_invariant_form B hB)
  · obtain ⟨ab, hab, -⟩ := hex
    have h := (hiff ab).mp hab
    intro X Y Z
    rw [h, h]
    linear_combination ab.1 * ReleaseAdapter.lorentzTraceForm_invariant X Y Z +
      ab.2 * ReleaseAdapter.lorentzTraceForm_lorentzHodge_invariant X Y Z

/-- Statement 8 on the library's objects. -/
theorem s8 :
    ∃ B : LinearMap.BilinForm ℝ ReleaseAdapter.lorentzAlgebra, ¬ ∃ ab : ℝ × ℝ,
      ∀ X Y : ReleaseAdapter.lorentzAlgebra,
        B X Y = ab.1 * LieModule.traceForm ℝ ReleaseAdapter.lorentzAlgebra Spacetime X Y +
          ab.2 * LinearMap.trace ℝ Spacetime
            (hodgeEnd (X : Module.End ℝ Spacetime) * (Y : Module.End ℝ Spacetime)) := by
  obtain ⟨B, hB⟩ := ReleaseAdapter.exists_bilinForm_ne_smul_lorentzTraceForm
  refine ⟨B, ?_⟩
  rintro ⟨ab, hab⟩
  refine hB ab.1 ab.2 fun X Y => ?_
  rw [← form_eq]
  exact hab X Y

/-! #### Statements 2 and 4: the explicit formula -/

section Spin

open LorentzLie.RealForms

theorem cs0 : (0 : Fin 3).castSucc = (0 : Fin 4) := rfl
theorem cs1 : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
theorem cs2 : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
theorem tA : timeAxis = (3 : Fin 4) := rfl

/-- `spinOf` written out as a `2 × 2` matrix. -/
theorem spinOf_eq (β θ : Fin 3 → ℝ) :
    spinOf β θ =
      !![-(1 / 2 : ℂ) * ((β 2 : ℂ) + (θ 2 : ℂ) * Complex.I),
          -(1 / 2 : ℂ) * ((β 0 : ℂ) + (θ 0 : ℂ) * Complex.I) +
            (1 / 2 : ℂ) * Complex.I * ((β 1 : ℂ) + (θ 1 : ℂ) * Complex.I);
        -(1 / 2 : ℂ) * ((β 0 : ℂ) + (θ 0 : ℂ) * Complex.I) -
            (1 / 2 : ℂ) * Complex.I * ((β 1 : ℂ) + (θ 1 : ℂ) * Complex.I),
          (1 / 2 : ℂ) * ((β 2 : ℂ) + (θ 2 : ℂ) * Complex.I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinOf, pauli, Fin.sum_univ_three] <;> ring

/-- `spinMatrix` of the endomorphism with matrix `M`. -/
theorem spinMatrix_toEuclideanLin (M : Matrix (Fin 4) (Fin 4) ℝ) :
    spinMatrix (Matrix.toEuclideanLin M) =
      spinOf (fun k => M k.castSucc timeAxis) (fun k => M (k + 2).castSucc (k + 1).castSucc) := by
  unfold spinMatrix
  rw [LinearEquiv.symm_apply_apply]

/-- Entry relations of a `![1, 1, 1, -1]`-skew matrix used below. -/
theorem skew_entries {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M ∈ LorentzLie.etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ)) :
    M 1 0 = -M 0 1 ∧ M 2 1 = -M 1 2 := by
  have h := (LorentzLie.mem_etaSkew_iff _ M).mp hM
  exact ⟨by simpa using h 0 1, by simpa using h 1 2⟩

/-- On a `![1, 1, 1, -1]`-skew matrix, `hodgeMatrix` is multiplication by `-i` under `spinOf`. -/
theorem spinOf_hodgeMatrix (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : M ∈ LorentzLie.etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ)) :
    spinOf (fun k => hodgeMatrix M k.castSucc timeAxis)
        (fun k => hodgeMatrix M (k + 2).castSucc (k + 1).castSucc) =
      (-Complex.I) • spinOf (fun k => M k.castSucc timeAxis)
        (fun k => M (k + 2).castSucc (k + 1).castSucc) := by
  obtain ⟨h10, h21⟩ := skew_entries hM
  rw [spinOf_eq, spinOf_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (apply Complex.ext <;> simp [hodgeMatrix, h10, h21, cs2, tA] <;> ring)

/-- Statement 4(a) on the library's objects. -/
theorem s4a :
    ∃ H : ReleaseAdapter.lorentzAlgebra →ₗ[ℝ] ReleaseAdapter.lorentzAlgebra,
      (∀ X : ReleaseAdapter.lorentzAlgebra,
        ((H X : ReleaseAdapter.lorentzAlgebra) : Module.End ℝ Spacetime) = hodgeEnd X) ∧
      (∀ X Y : ReleaseAdapter.lorentzAlgebra, H ⁅X, Y⁆ = ⁅X, H Y⁆) ∧
      (∀ X : ReleaseAdapter.lorentzAlgebra, H (H X) = -X) ∧
      (∀ X : ReleaseAdapter.lorentzAlgebra,
        spinMatrix ((H X : ReleaseAdapter.lorentzAlgebra) : Module.End ℝ Spacetime) =
          (-Complex.I) • spinMatrix (X : Module.End ℝ Spacetime)) := by
  refine ⟨ReleaseAdapter.lorentzHodge, lorentzHodge_coe,
    ReleaseAdapter.lorentzHodge_isBracketCommuting, ReleaseAdapter.lorentzHodge_lorentzHodge,
    fun X => ?_⟩
  rw [lorentzHodge_coe, hodgeEnd, spinMatrix_toEuclideanLin]
  exact spinOf_hodgeMatrix _ ((LorentzLie.Landings.toEuclideanLin_symm_mem_etaSkew_iff X).mpr X.2)

/-- Statement 4(b). -/
theorem s4b (k : Fin 3) :
    hodgeEnd (boostEnd k) = -rotEnd (k + 1) (k + 2) ∧
      hodgeEnd (rotEnd (k + 1) (k + 2)) = boostEnd k := by
  constructor
  · have h := congrArg Subtype.val (ReleaseAdapter.lorentzHodge_lorentzBoost k)
    rw [lorentzHodge_coe] at h
    exact h
  · have h := congrArg Subtype.val (ReleaseAdapter.lorentzHodge_lorentzRot k)
    rw [lorentzHodge_coe] at h
    exact h

/-! The conjugation `x ↦ g x g⁻¹` of `sl(2, ℂ)` with `g = 1 - i σ₂ = !![1, -1; 1, 1]`: it sends
`σ₃ ↦ σ₁`, `σ₂ ↦ σ₂`, `σ₁ ↦ -σ₃`. -/

def gmat : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; 1, 1]

def gimat : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; -(1 / 2), 1 / 2]

theorem gmat_mul_gimat : gmat * gimat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gmat, gimat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

theorem gimat_mul_gmat : gimat * gmat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gmat, gimat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

theorem conj_trace (m : Matrix (Fin 2) (Fin 2) ℂ) (h : m.trace = 0) :
    (gmat * m * gimat).trace = 0 := by
  rw [Matrix.trace_mul_cycle, gimat_mul_gmat, one_mul, h]

theorem conj_trace' (m : Matrix (Fin 2) (Fin 2) ℂ) (h : m.trace = 0) :
    (gimat * m * gmat).trace = 0 := by
  rw [Matrix.trace_mul_cycle, gmat_mul_gimat, one_mul, h]

theorem conj_mul (x y : Matrix (Fin 2) (Fin 2) ℂ) :
    gmat * x * gimat * (gmat * y * gimat) = gmat * (x * y) * gimat := by
  rw [show gmat * x * gimat * (gmat * y * gimat) = gmat * x * (gimat * gmat) * y * gimat by
    simp only [Matrix.mul_assoc], gimat_mul_gmat, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem conj_inv_left (m : Matrix (Fin 2) (Fin 2) ℂ) : gimat * (gmat * m * gimat) * gmat = m := by
  rw [show gimat * (gmat * m * gimat) * gmat = (gimat * gmat) * m * (gimat * gmat) by
    simp only [Matrix.mul_assoc], gimat_mul_gmat, Matrix.one_mul, Matrix.mul_one]

theorem conj_inv_right (m : Matrix (Fin 2) (Fin 2) ℂ) : gmat * (gimat * m * gmat) * gimat = m := by
  rw [show gmat * (gimat * m * gmat) * gimat = (gmat * gimat) * m * (gmat * gimat) by
    simp only [Matrix.mul_assoc], gmat_mul_gimat, Matrix.one_mul, Matrix.mul_one]

/-- Conjugation by `g`, as an automorphism of the real Lie algebra `sl(2, ℂ)`. -/
def conjG : LorentzLie.sl2CReal ≃ₗ⁅ℝ⁆ LorentzLie.sl2CReal :=
  { toFun := fun x => toSl2CReal (gmat * LorentzLie.sl2CRealMat x * gimat)
      (conj_trace _ (sl2CRealMat_trace x))
    map_add' := fun x y => sl2CRealMat_injective (by
      simp only [sl2CRealMat_toSl2CReal, sl2CRealMat_add, Matrix.mul_add, Matrix.add_mul])
    map_smul' := fun r x => sl2CRealMat_injective (by
      simp only [RingHom.id_apply, sl2CRealMat_toSl2CReal, sl2CRealMat_smul, Matrix.mul_smul,
        Matrix.smul_mul])
    map_lie' := fun {x y} => sl2CRealMat_injective (by
      simp only [sl2CRealMat_toSl2CReal, sl2CRealMat_lie]
      rw [conj_mul, conj_mul]
      simp only [Matrix.mul_sub, Matrix.sub_mul])
    invFun := fun x => toSl2CReal (gimat * LorentzLie.sl2CRealMat x * gmat)
      (conj_trace' _ (sl2CRealMat_trace x))
    left_inv := fun x => sl2CRealMat_injective (by
      simp only [sl2CRealMat_toSl2CReal]
      exact conj_inv_left _)
    right_inv := fun x => sl2CRealMat_injective (by
      simp only [sl2CRealMat_toSl2CReal]
      exact conj_inv_right _) }

/-- The library's `spinMat` at `![1, 1, 1, -1]`, conjugated by `g`, is the formula `spinOf`. -/
theorem conj_spinMat (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : M ∈ LorentzLie.etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ)) :
    gmat * spinMat (![1, 1, 1, -1] : Fin 4 → ℝ) M * gimat =
      spinOf (fun k => M k.castSucc timeAxis) (fun k => M (k + 2).castSucc (k + 1).castSucc) := by
  obtain ⟨h10, h21⟩ := skew_entries hM
  rw [spinOf_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (apply Complex.ext <;>
      simp [spinMat, spinCoords, pauliR, lamRe, lamIm, gmat, gimat, Matrix.mul_apply,
        Fin.sum_univ_two, h10, h21, cs2, tA] <;> ring)

/-- The equivalence of statement 2: the library's `lorentzAlgebraEquivSl2C` followed by the
conjugation by `g`. -/
def e2 : ReleaseAdapter.lorentzAlgebra ≃ₗ⁅ℝ⁆ LorentzLie.sl2CReal :=
  LorentzLie.lorentzAlgebraEquivSl2C.trans conjG

theorem e2_apply (X : ReleaseAdapter.lorentzAlgebra) :
    LorentzLie.sl2CRealMat (e2 X) = spinMatrix (X : Module.End ℝ Spacetime) := by
  have h1 : LorentzLie.sl2CRealMat (e2 X) =
      gmat * spinMat (![1, 1, 1, -1] : Fin 4 → ℝ)
        (Matrix.toEuclideanLin.symm (X : Module.End ℝ Spacetime)) * gimat := rfl
  rw [h1, conj_spinMat _ ((LorentzLie.Landings.toEuclideanLin_symm_mem_etaSkew_iff X).mpr X.2)]
  rfl

theorem spinMatrix_boostEnd (k : Fin 3) :
    spinMatrix (boostEnd k) = (-(1 / 2 : ℂ)) • pauli k := by
  rw [boostEnd, spinMatrix_toEuclideanLin, spinOf_eq]
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, cs2, tA]

theorem spinMatrix_rotEnd (k : Fin 3) :
    spinMatrix (rotEnd (k + 1) (k + 2)) = (-(Complex.I / 2)) • pauli k := by
  rw [rotEnd, spinMatrix_toEuclideanLin, spinOf_eq]
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, cs2, tA] <;> ring

end Spin

/-! #### Statement 1: Mathlib's `so' (Fin 1) (Fin 3) ℝ` -/

section SoPrime

open LorentzLie.RealForms

theorem s1_apply (X : LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ) :
    LorentzLie.sl2CRealMat (LorentzLie.so'OneThreeEquivSl2C X) =
      spinOf (fun k => (X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) (Sum.inr k) (Sum.inl 0))
        (fun k => (X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
          (Sum.inr (k + 2)) (Sum.inr (k + 1))) := by
  have h1 : LorentzLie.sl2CRealMat (LorentzLie.so'OneThreeEquivSl2C X) =
      spinMat (LorentzLie.indefEta (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4))
        (Matrix.reindex (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4)
          (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) X.1) := rfl
  have hN := (LorentzLie.mem_etaSkew_iff _ _).mp
    ((LorentzLie.Landings.reindex_mem_etaSkew_iff
      (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) X.1).mpr X.2)
  rw [h1]
  rw [LorentzLie.Landings.indefEta_finSumFinEquiv] at hN ⊢
  have e : ∀ i j : Fin 1 ⊕ Fin 3, X.1 i j =
      Matrix.reindex (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4)
        (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) X.1
        ((finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) i) ((finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) j) := by
    intro i j
    simp [Matrix.reindex_apply]
  have f0 : (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) (Sum.inl 0) = 0 := rfl
  have f1 : (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) (Sum.inr 0) = 1 := rfl
  have f2 : (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) (Sum.inr 1) = 2 := rfl
  have f3 : (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) (Sum.inr 2) = 3 := rfl
  have a02 : (0 : Fin 3) + 2 = 2 := rfl
  have a01 : (0 : Fin 3) + 1 = 1 := rfl
  have a12 : (1 : Fin 3) + 2 = 0 := rfl
  have a11 : (1 : Fin 3) + 1 = 2 := rfl
  have a22 : (2 : Fin 3) + 2 = 1 := rfl
  have a21 : (2 : Fin 3) + 1 = 0 := rfl
  rw [spinOf_eq]
  simp only [a02, a01, a12, a11, a22, a21]
  rw [e (Sum.inr 2) (Sum.inl 0), e (Sum.inr 0) (Sum.inl 0), e (Sum.inr 1) (Sum.inl 0),
    e (Sum.inr 2) (Sum.inr 1), e (Sum.inr 0) (Sum.inr 2), e (Sum.inr 1) (Sum.inr 0),
    f0, f1, f2, f3]
  generalize Matrix.reindex (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4)
    (finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4) X.1 = N at hN ⊢
  have h10 : N 1 0 = N 0 1 := by have h := hN 0 1; simp at h; linarith
  have h20 : N 2 0 = N 0 2 := by have h := hN 0 2; simp at h; linarith
  have h30 : N 3 0 = N 0 3 := by have h := hN 0 3; simp at h; linarith
  have h32 : N 3 2 = -N 2 3 := by have h := hN 2 3; simp at h; linarith
  have h21 : N 2 1 = -N 1 2 := by have h := hN 1 2; simp at h; linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    (apply Complex.ext <;>
      simp [spinMat, spinCoords, pauliR, lamRe, lamIm, h10, h20, h30, h32, h21] <;> ring)

end SoPrime

/-! #### Statement 9: `exp A = 1` with `A` outside the Lie algebra -/

section ExpControl

/-- A complex structure on `ℝ⁴` that is not skew for the Minkowski form. -/
def jmat : Matrix (Fin 4) (Fin 4) ℝ := !![0, -2, 0, 0; 1 / 2, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

theorem jmat_mul_self : jmat * jmat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jmat, Matrix.mul_apply, Fin.sum_univ_four]

/-- The continuous linear endomorphism of `Spacetime` with matrix `jmat`. -/
def jclm : Spacetime →L[ℝ] Spacetime := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) jmat

theorem jclm_mul_self : jclm * jclm = -1 := by
  rw [jclm, ← map_mul, jmat_mul_self, map_neg, map_one]

theorem exp_two_pi_jclm : NormedSpace.exp ((2 * Real.pi) • jclm) = 1 := by
  have hφ : Continuous (Complex.liftAux jclm jclm_mul_self) :=
    (Complex.liftAux jclm jclm_mul_self).toLinearMap.continuous_of_finiteDimensional
  have h1 : Complex.liftAux jclm jclm_mul_self (((2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (2 * Real.pi) • jclm := by
    rw [Complex.liftAux_apply]
    simp
  have h2 := NormedSpace.map_exp (Complex.liftAux jclm jclm_mul_self) hφ
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I)
  rw [h1] at h2
  have h3 : NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_eq_exp_ℂ]
    push_cast
    exact Complex.exp_two_pi_mul_I
  rw [← h2, h3, map_one]

/-- Statement 9 on the library's objects. -/
theorem s9 :
    ∃ A : Spacetime →L[ℝ] Spacetime,
      (∃ g : ProperLorentz, g.val.val = NormedSpace.exp ((1 : ℝ) • A)) ∧
        A.toLinearMap ∉ ReleaseAdapter.lorentzAlgebra := by
  refine ⟨(2 * Real.pi) • jclm, ⟨⟨1, by simp, fun _ => rfl, fun _ => Iff.rfl⟩, ?_⟩, ?_⟩
  · rw [one_smul, exp_two_pi_jclm]
    rfl
  · intro hmem
    have hA : (((2 * Real.pi) • jclm : Spacetime →L[ℝ] Spacetime) : Spacetime →ₗ[ℝ] Spacetime) =
        Matrix.toEuclideanLin ((2 * Real.pi) • jmat) := by
      rw [map_smul]
      rfl
    rw [hA, LorentzLie.Landings.toEuclideanLin_mem_lorentzAlgebra_iff,
      LorentzLie.mem_etaSkew_iff] at hmem
    have h := hmem 0 1
    simp [jmat] at h
    linarith [Real.pi_pos]

end ExpControl

/-! #### Statement 5: the complexification -/

section Complexification

/-- The diagonal `(1, 1, 1, -1)`. -/
abbrev eta4 : Fin 4 → ℝ := ![1, 1, 1, -1]

theorem eta4_sign (i : Fin 4) : eta4 i = 1 ∨ eta4 i = -1 := LorentzLie.Landings.eta4_sign i

theorem lamProd_eta4 : LorentzLie.lamProd eta4 = Complex.I := by
  simp [LorentzLie.lamProd, Fin.prod_univ_four, LorentzLie.lam_one, LorentzLie.lam_neg_one]

/-- The base change of the matrix equivalence preserves brackets. -/
theorem baseChange_lie (s t : ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra) :
    LorentzLie.lorentzAlgebraEquivEtaSkew.toLinearEquiv.baseChange ℝ ℂ _ _ ⁅s, t⁆ =
      ⁅LorentzLie.lorentzAlgebraEquivEtaSkew.toLinearEquiv.baseChange ℝ ℂ _ _ s,
        LorentzLie.lorentzAlgebraEquivEtaSkew.toLinearEquiv.baseChange ℝ ℂ _ _ t⁆ := by
  induction s using TensorProduct.inductionOn with
  | tmul z X =>
    induction t using TensorProduct.inductionOn with
    | tmul w Y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, LinearEquiv.baseChange_tmul,
        LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul]
      congr 1
      exact LieEquiv.map_lie LorentzLie.lorentzAlgebraEquivEtaSkew X Y
    | add t1 t2 h1 h2 =>
      have e : ⁅(z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra), t1 + t2⁆ =
          ⁅(z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra), t1⁆ +
            ⁅(z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra), t2⁆ :=
        lie_add (z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra) t1 t2
      rw [e, map_add, map_add, lie_add, h1, h2]
  | add s1 s2 h1 h2 => rw [add_lie, map_add, map_add, add_lie, h1, h2]

/-- The base change `ℂ ⊗[ℝ] lorentzAlgebra ≃ ℂ ⊗[ℝ] etaSkew ![1, 1, 1, -1]`, as a Lie algebra
equivalence over `ℂ`. -/
def baseChangeEquiv :
    (ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] LorentzLie.etaSkew eta4) :=
  { LorentzLie.lorentzAlgebraEquivEtaSkew.toLinearEquiv.baseChange ℝ ℂ _ _ with
    map_lie' := fun {s t} => baseChange_lie s t }

/-- `ℂ ⊗[ℝ] lorentzAlgebra` as the complex `![1, 1, 1, -1]`-skew matrices. -/
def psi : (ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra) ≃ₗ⁅ℂ⁆ LorentzLie.etaSkew (LorentzLie.etaC eta4) :=
  baseChangeEquiv.trans (LorentzLie.Complexification.tensorEquivC eta4)

theorem psi_tmul (z : ℂ) (X : ReleaseAdapter.lorentzAlgebra) :
    psi (z ⊗ₜ[ℝ] X) =
      z • LorentzLie.Complexification.cplx eta4 (LorentzLie.lorentzAlgebraEquivEtaSkew X) :=
  LorentzLie.Complexification.tensorEquivC_tmul eta4 z (LorentzLie.lorentzAlgebraEquivEtaSkew X)

/-- Reading a real matrix over `ℂ` commutes with the Hodge operator. -/
theorem cplx_hodge (Y : LorentzLie.etaSkew eta4) :
    LorentzLie.Complexification.cplx eta4 (LorentzLie.hodge eta4 Y) =
      LorentzLie.hodge (LorentzLie.etaC eta4) (LorentzLie.Complexification.cplx eta4 Y) := by
  apply Subtype.ext
  ext i j
  rw [LorentzLie.Complexification.cplx_apply, LorentzLie.hodge_coe, LorentzLie.hodge_coe]
  fin_cases i <;> fin_cases j <;>
    simp [LorentzLie.hodgeMat, LorentzLie.star0, Matrix.mul_apply, Matrix.diagonal_apply,
      LorentzLie.Complexification.cplx_apply, LorentzLie.etaC, eta4]

/-- `psi` intertwines the `ℂ`-linear extension of `lorentzHodge` with the complex Hodge
operator. -/
theorem psi_hodge (t : ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra) :
    psi (ReleaseAdapter.lorentzHodge.baseChange ℂ t) =
      LorentzLie.hodge (LorentzLie.etaC eta4) (psi t) := by
  induction t using TensorProduct.inductionOn with
  | tmul z X =>
    rw [LinearMap.baseChange_tmul, psi_tmul, psi_tmul,
      ReleaseAdapter.lorentzAlgebraEquivEtaSkew_lorentzHodge, cplx_hodge, map_smul]
  | add s t hs ht => simp only [map_add, hs, ht]

theorem hodgeProjMinus_eta4 (Z : LorentzLie.etaSkew (LorentzLie.etaC eta4)) :
    LorentzLie.hodgeProjMinus eta4 Z =
      (1 / 2 : ℂ) • (Z + Complex.I • LorentzLie.hodge (LorentzLie.etaC eta4) Z) := by
  rw [LorentzLie.hodgeProjMinus, lamProd_eta4]
  simp [sub_eq_add_neg]

theorem hodgeProjPlus_eta4 (Z : LorentzLie.etaSkew (LorentzLie.etaC eta4)) :
    LorentzLie.hodgeProjPlus eta4 Z =
      (1 / 2 : ℂ) • (Z - Complex.I • LorentzLie.hodge (LorentzLie.etaC eta4) Z) := by
  rw [LorentzLie.hodgeProjPlus, lamProd_eta4]
  simp [sub_eq_add_neg]

/-- The equivalence of statement 5. -/
def bigE : (ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra) ≃ₗ⁅ℂ⁆ (LorentzLie.sl2C × LorentzLie.sl2C) :=
  psi.trans (LorentzLie.etaSkewCEquiv eta4 eta4_sign)

/-- Statement 5 on the library's objects. -/
theorem s5 :
    ∃ (H : ReleaseAdapter.lorentzAlgebra →ₗ[ℝ] ReleaseAdapter.lorentzAlgebra)
      (E : (ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra) ≃ₗ⁅ℂ⁆
        (LieAlgebra.SpecialLinear.sl (Fin 2) ℂ × LieAlgebra.SpecialLinear.sl (Fin 2) ℂ)),
      (∀ X : ReleaseAdapter.lorentzAlgebra,
        ((H X : ReleaseAdapter.lorentzAlgebra) : Module.End ℝ Spacetime) = hodgeEnd X) ∧
      ∀ t : ℂ ⊗[ℝ] ReleaseAdapter.lorentzAlgebra,
        E ((1 / 2 : ℂ) • (t + Complex.I • H.baseChange ℂ t)) = ((E t).1, 0) ∧
        E ((1 / 2 : ℂ) • (t - Complex.I • H.baseChange ℂ t)) = (0, (E t).2) := by
  refine ⟨ReleaseAdapter.lorentzHodge, bigE, lorentzHodge_coe, fun t => ?_⟩
  have hm : psi ((1 / 2 : ℂ) • (t + Complex.I • ReleaseAdapter.lorentzHodge.baseChange ℂ t)) =
      LorentzLie.hodgeProjMinus eta4 (psi t) := by
    rw [hodgeProjMinus_eta4, map_smul, map_add, map_smul, psi_hodge]
  have hp : psi ((1 / 2 : ℂ) • (t - Complex.I • ReleaseAdapter.lorentzHodge.baseChange ℂ t)) =
      LorentzLie.hodgeProjPlus eta4 (psi t) := by
    rw [hodgeProjPlus_eta4, map_smul, map_sub, map_smul, psi_hodge]
  obtain ⟨k1, k2⟩ := LorentzLie.etaSkewCEquiv_hodgeProj eta4 eta4_sign (psi t)
  constructor
  · change LorentzLie.etaSkewCEquiv eta4 eta4_sign
      (psi ((1 / 2 : ℂ) • (t + Complex.I • ReleaseAdapter.lorentzHodge.baseChange ℂ t))) = _
    rw [hm]
    exact k1
  · change LorentzLie.etaSkewCEquiv eta4 eta4_sign
      (psi ((1 / 2 : ℂ) • (t - Complex.I • ReleaseAdapter.lorentzHodge.baseChange ℂ t))) = _
    rw [hp]
    exact k2

end Complexification

/-! #### Statement 7: the two other signatures are not `sl(2, ℂ)` -/

section Simple

/-- Simplicity passes along a Lie algebra equivalence. -/
theorem isSimple_of_lieEquiv {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra ℝ L₁] [LieRing L₂]
    [LieAlgebra ℝ L₂] (e : L₁ ≃ₗ⁅ℝ⁆ L₂) (h : LieAlgebra.IsSimple ℝ L₂) :
    LieAlgebra.IsSimple ℝ L₁ := by
  refine ⟨fun I => ?_, fun hab => ?_⟩
  · rcases h.eq_bot_or_eq_top (LieIdeal.comap (e.symm : L₂ →ₗ⁅ℝ⁆ L₁) I) with h0 | h1
    · left
      rw [LieSubmodule.eq_bot_iff]
      intro x hx
      have hx' : e x ∈ LieIdeal.comap (e.symm : L₂ →ₗ⁅ℝ⁆ L₁) I := by
        rw [LieIdeal.mem_comap]
        simpa using hx
      rw [h0, LieSubmodule.mem_bot] at hx'
      exact e.injective (hx'.trans (map_zero e).symm)
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : e x ∈ LieIdeal.comap (e.symm : L₂ →ₗ⁅ℝ⁆ L₁) I := by
        rw [h1]
        exact LieSubmodule.mem_top _
      rw [LieIdeal.mem_comap] at hx'
      simpa using hx'
  · exact h.non_abelian ((lie_abelian_iff_equiv_lie_abelian e).mp hab)

/-- For entries `±1` with product `1`, `etaSkew η` is not isomorphic to `sl(2, ℂ)` over `ℝ`. -/
theorem not_lieEquiv_sl2C (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) (h : ∏ i, η i = 1) :
    ¬ Nonempty (LorentzLie.etaSkew η ≃ₗ⁅ℝ⁆ LorentzLie.sl2CReal) := by
  rintro ⟨e⟩
  have hs : LieAlgebra.IsSimple ℝ (LorentzLie.etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ)) :=
    LorentzLie.etaSkew_isSimple _ LorentzLie.Landings.eta4_sign LorentzLie.Landings.eta4_prod
  exact LorentzLie.Controls.not_isSimple_of_prod_eq_one η hη h
    (isSimple_of_lieEquiv
      (e.trans (LorentzLie.etaSkewEquivSl2C _ LorentzLie.Landings.eta4_sign
        LorentzLie.Landings.eta4_prod).symm) hs)

end Simple

end Bridge

/-! ### `sl(2, ℂ)` -/

/-- **1. `so(1, 3)` is `sl(2, ℂ)`, on Mathlib's `so'`.** There is an isomorphism `e` of real Lie
algebras from Mathlib's `so' (Fin 1) (Fin 3) ℝ` (the real matrices indexed by `Fin 1 ⊕ Fin 3` that
are skew-adjoint for `diag(1, -1, -1, -1)`) onto `sl(2, ℂ)` regarded as a real Lie algebra, such
that for every `X` the complex matrix of `e X` is `-½ Σ_k (β_k + i θ_k) σ_k`, where
`β_k = X (inr k) (inl 0)` is the entry of `X` in the row of the space index `k` and the column
of the time index, `θ_k = X (inr (k + 2)) (inr (k + 1))` (the sums in `Fin 3`; the coefficient of the rotation about
the space axis `k`, from axis `k + 1` towards axis `k + 2`), and `σ_k` is `pauli k`. No definition
copied from the Yang–Mills release is used. -/
theorem so'_one_three_lieEquiv_sl2C :
    ∃ e : LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ ≃ₗ⁅ℝ⁆ sl2CReal,
      ∀ X : LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ,
        sl2CRealMat (e X) =
          spinOf (fun k => (X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) (Sum.inr k) (Sum.inl 0))
            (fun k => (X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
              (Sum.inr (k + 2)) (Sum.inr (k + 1))) := by
  exact ⟨LorentzLie.so'OneThreeEquivSl2C, Bridge.s1_apply⟩

/-- **2. The Lorentz Lie algebra of the carried Minkowski space is `sl(2, ℂ)`.** For the Lie
algebra `lorentzAlgebra` of the endomorphisms of `Spacetime` skew-adjoint for `minkowskiBilin`
(`Spacetime` is a copy carried from the public statement of the Yang–Mills release):
(a) its dimension over `ℝ` is `6`;
(b) there is an isomorphism `e` of real Lie algebras from `lorentzAlgebra` onto `sl(2, ℂ)`
regarded as a real Lie algebra such that for every `X` the complex matrix of `e X` is
`spinMatrix X = -½ Σ_k (β_k + i θ_k) σ_k`;
(c) for every space axis `k`, the boost generator `boostEnd k` and the rotation generator
`rotEnd (k + 1) (k + 2)` (the sums in `Fin 3`) are in `lorentzAlgebra`,
`spinMatrix (boostEnd k) = -½ σ_k` and `spinMatrix (rotEnd (k + 1) (k + 2)) = -(i/2) σ_k`, where
`σ_k` is `pauli k`. -/
theorem lorentzAlgebra_lieEquiv_sl2C :
    Module.finrank ℝ lorentzAlgebra = 6 ∧
    (∃ e : lorentzAlgebra ≃ₗ⁅ℝ⁆ sl2CReal, ∀ X : lorentzAlgebra,
      sl2CRealMat (e X) = spinMatrix (X : Module.End ℝ Spacetime)) ∧
    ∀ k : Fin 3, boostEnd k ∈ lorentzAlgebra ∧ rotEnd (k + 1) (k + 2) ∈ lorentzAlgebra ∧
      spinMatrix (boostEnd k) = (-(1 / 2 : ℂ)) • pauli k ∧
      spinMatrix (rotEnd (k + 1) (k + 2)) = (-(Complex.I / 2)) • pauli k := by
  exact ⟨LorentzLie.finrank_lorentzAlgebra, ⟨Bridge.e2, Bridge.e2_apply⟩, fun k =>
    ⟨(ReleaseAdapter.lorentzBoost k).2, (ReleaseAdapter.lorentzRot (k + 1) (k + 2)).2,
      Bridge.spinMatrix_boostEnd k, Bridge.spinMatrix_rotEnd k⟩⟩

/-! ### The exponential criterion -/

/-- **3. The exponential criterion.** (a) The quadratic form of `minkowskiBilin` is the carried
`minkowskiSquare`: `minkowskiBilin x x = minkowskiSquare x` for every `x`. (b) For every
linear endomorphism `A` of `Spacetime` (typed as a continuous linear map, where `exp` is taken;
every linear endomorphism of this finite-dimensional space is continuous): `A` is in `lorentzAlgebra` if and only if for
every real `t` the exponential `exp (t • A)` is the underlying map of an element of the carried
type `ProperLorentz` (the invertible continuous linear maps of determinant `1` that preserve
`minkowskiSquare` and map the forward cone onto itself). -/
theorem mem_lorentzAlgebra_iff_exp :
    (∀ x : Spacetime, minkowskiBilin x x = minkowskiSquare x) ∧
    ∀ A : Spacetime →L[ℝ] Spacetime,
      A.toLinearMap ∈ lorentzAlgebra ↔
        ∀ t : ℝ, ∃ g : ProperLorentz, g.val.val = NormedSpace.exp (t • A) := by
  exact ⟨ReleaseAdapter.minkowskiBilin_self, LorentzLie.mem_lorentzAlgebra_iff_exp⟩

/-! ### The operator `H` -/

/-- **4. The operator `H` is a complex structure, and it is multiplication by `-i`.**
(a) There is a real-linear endomorphism `H` of `lorentzAlgebra` whose value at every `X` is the
endomorphism `hodgeEnd X` of `Spacetime` (so `hodgeEnd` maps `lorentzAlgebra` into itself and is
real-linear there), and it satisfies: `H ⁅X, Y⁆ = ⁅X, H Y⁆` for all `X`, `Y`; `H (H X) = -X` for
all `X`; and `spinMatrix (H X) = -i · spinMatrix X` for all `X`, that is, the isomorphism of
statement 2 carries `H` to multiplication by the complex number `-i` on `sl(2, ℂ)`.
(b) For every space axis `k`, `hodgeEnd (boostEnd k) = -rotEnd (k + 1) (k + 2)` and
`hodgeEnd (rotEnd (k + 1) (k + 2)) = boostEnd k`, the sums in `Fin 3`. -/
theorem hodgeEnd_complexStructure :
    (∃ H : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra,
      (∀ X : lorentzAlgebra, ((H X : lorentzAlgebra) : Module.End ℝ Spacetime) = hodgeEnd X) ∧
      (∀ X Y : lorentzAlgebra, H ⁅X, Y⁆ = ⁅X, H Y⁆) ∧
      (∀ X : lorentzAlgebra, H (H X) = -X) ∧
      (∀ X : lorentzAlgebra,
        spinMatrix ((H X : lorentzAlgebra) : Module.End ℝ Spacetime) =
          (-Complex.I) • spinMatrix (X : Module.End ℝ Spacetime))) ∧
    ∀ k : Fin 3, hodgeEnd (boostEnd k) = -rotEnd (k + 1) (k + 2) ∧
      hodgeEnd (rotEnd (k + 1) (k + 2)) = boostEnd k := by
  exact ⟨Bridge.s4a, Bridge.s4b⟩

/-! ### The complexification -/

/-- **5. The complexification is `sl(2, ℂ) × sl(2, ℂ)`.** There are a real-linear endomorphism
`H` of `lorentzAlgebra` whose value at every `X` is `hodgeEnd X`, and an isomorphism `E` of
complex Lie algebras from the base change `ℂ ⊗[ℝ] lorentzAlgebra` onto `sl(2, ℂ) × sl(2, ℂ)`,
such that for every `t` in `ℂ ⊗[ℝ] lorentzAlgebra`, with `H_ℂ` the `ℂ`-linear extension of `H`
(`H.baseChange ℂ`): `E (½ (t + i H_ℂ t)) = ((E t).1, 0)` and
`E (½ (t - i H_ℂ t)) = (0, (E t).2)`. So `½ (1 + i H_ℂ)` and `½ (1 - i H_ℂ)` are the projections
onto the two factors. -/
theorem complexification_lieEquiv :
    ∃ (H : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra)
      (E : (ℂ ⊗[ℝ] lorentzAlgebra) ≃ₗ⁅ℂ⁆
        (LieAlgebra.SpecialLinear.sl (Fin 2) ℂ × LieAlgebra.SpecialLinear.sl (Fin 2) ℂ)),
      (∀ X : lorentzAlgebra, ((H X : lorentzAlgebra) : Module.End ℝ Spacetime) = hodgeEnd X) ∧
      ∀ t : ℂ ⊗[ℝ] lorentzAlgebra,
        E ((1 / 2 : ℂ) • (t + Complex.I • H.baseChange ℂ t)) = ((E t).1, 0) ∧
        E ((1 / 2 : ℂ) • (t - Complex.I • H.baseChange ℂ t)) = (0, (E t).2) := by
  exact Bridge.s5

/-! ### The invariant bilinear forms -/

/-- **6. The invariant bilinear forms.** Let `B` be a real bilinear form on `lorentzAlgebra`; no
symmetry of `B` is assumed. (a) `B` is invariant, `B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0` for all `X`, `Y`,
`Z`, if and only if there is exactly one pair `(a, b)` of real numbers such that
`B X Y = a · tr (X Y) + b · tr (H(X) Y)` for all `X`, `Y`. Here `tr (X Y)` is Mathlib's
`LieModule.traceForm` of `lorentzAlgebra` acting on `Spacetime` (the trace of the composition
`X ∘ Y`), and `tr (H(X) Y)` is the trace of the composition `hodgeEnd X ∘ Y`. (b) If `B` is
invariant then it is symmetric: `B X Y = B Y X` for all `X`, `Y`. (For `X` in `L` and the
antisymmetric matrix `F = η X`, `tr (X X) = -F_{μν} F^{μν}` and `tr (H(X) X)` is, up to the sign
fixed by the normalisation of the alternating symbol, `F_{μν}` contracted with its dual; the
physics literature calls these two expressions, up to normalisation, the kinetic term and the
theta term. The reading of `X` as a two-form is not formalized.) -/
theorem invariant_bilinForm_iff (B : LinearMap.BilinForm ℝ lorentzAlgebra) :
    ((∀ X Y Z : lorentzAlgebra, B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0) ↔
      ∃! ab : ℝ × ℝ, ∀ X Y : lorentzAlgebra,
        B X Y = ab.1 * LieModule.traceForm ℝ lorentzAlgebra Spacetime X Y +
          ab.2 * LinearMap.trace ℝ Spacetime
            (hodgeEnd (X : Module.End ℝ Spacetime) * (Y : Module.End ℝ Spacetime))) ∧
    ((∀ X Y Z : lorentzAlgebra, B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0) →
      ∀ X Y : lorentzAlgebra, B X Y = B Y X) := by
  exact Bridge.s6 B

/-! ### Controls -/

/-- **7. Control: the definite and the split signature.** On Mathlib's
`skewAdjointMatricesLieSubalgebra`: (a) the Lie algebra of the real `4 × 4` matrices skew-adjoint
for `diag(1, 1, 1, 1)` is isomorphic, as a real Lie algebra, to `so(3) × so(3)` (`so (Fin 3) ℝ`,
the skew-symmetric real `3 × 3` matrices); (b) the Lie algebra of the real `4 × 4` matrices
skew-adjoint for `diag(1, 1, -1, -1)` is isomorphic to `sl(2, ℝ) × sl(2, ℝ)`; (c) there is no
isomorphism of real Lie algebras from the algebra of (a) onto `sl(2, ℂ)`; (d) there is none from
the algebra of (b) onto `sl(2, ℂ)`. So the conclusion of statements 1 and 2 does not hold in the
two other signatures. -/
theorem definite_split_signature :
    Nonempty (skewAdjointMatricesLieSubalgebra (Matrix.diagonal (![1, 1, 1, 1] : Fin 4 → ℝ)) ≃ₗ⁅ℝ⁆
      (LieAlgebra.Orthogonal.so (Fin 3) ℝ × LieAlgebra.Orthogonal.so (Fin 3) ℝ)) ∧
    Nonempty (skewAdjointMatricesLieSubalgebra (Matrix.diagonal (![1, 1, -1, -1] : Fin 4 → ℝ)) ≃ₗ⁅ℝ⁆
      (LieAlgebra.SpecialLinear.sl (Fin 2) ℝ × LieAlgebra.SpecialLinear.sl (Fin 2) ℝ)) ∧
    ¬ Nonempty (skewAdjointMatricesLieSubalgebra (Matrix.diagonal (![1, 1, 1, 1] : Fin 4 → ℝ)) ≃ₗ⁅ℝ⁆
      sl2CReal) ∧
    ¬ Nonempty (skewAdjointMatricesLieSubalgebra (Matrix.diagonal (![1, 1, -1, -1] : Fin 4 → ℝ)) ≃ₗ⁅ℝ⁆
      sl2CReal) := by
  refine ⟨⟨LorentzLie.etaSkewEquivSo3Prod (![1, 1, 1, 1] : Fin 4 → ℝ)
      (fun i => by fin_cases i <;> simp) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)⟩,
    ⟨LorentzLie.etaSkewEquivSl2RProd (![1, 1, -1, -1] : Fin 4 → ℝ)
      (fun i => by fin_cases i <;> simp) (by simp [Fin.sum_univ_four])⟩,
    Bridge.not_lieEquiv_sl2C _ (fun i => by fin_cases i <;> simp) (by simp [Fin.prod_univ_four]),
    Bridge.not_lieEquiv_sl2C _ (fun i => by fin_cases i <;> simp) (by simp [Fin.prod_univ_four])⟩

/-- **8. Control: not every bilinear form is invariant.** There is a real bilinear form `B` on
`lorentzAlgebra` such that for no pair `(a, b)` of real numbers does
`B X Y = a · tr (X Y) + b · tr (H(X) Y)` hold for all `X`, `Y` (notation of statement 6). By
statement 6 this `B` is not invariant, so the two sides of the equivalence in statement 6 do not
hold for every bilinear form. -/
theorem exists_bilinForm_not_trace_form :
    ∃ B : LinearMap.BilinForm ℝ lorentzAlgebra, ¬ ∃ ab : ℝ × ℝ, ∀ X Y : lorentzAlgebra,
      B X Y = ab.1 * LieModule.traceForm ℝ lorentzAlgebra Spacetime X Y +
        ab.2 * LinearMap.trace ℝ Spacetime
          (hodgeEnd (X : Module.End ℝ Spacetime) * (Y : Module.End ℝ Spacetime)) := by
  exact Bridge.s8

/-- **9. Control: one value of `t` is not enough.** There is a continuous linear endomorphism `A`
of `Spacetime` such that `exp A` (`exp (t • A)` at `t = 1`) is the underlying map of an element
of the carried type `ProperLorentz`, and `A` is not in `lorentzAlgebra`. So in statement 3 the
condition for every real `t` cannot be replaced by the condition at `t = 1`. -/
theorem exists_exp_mem_not_mem_lorentzAlgebra :
    ∃ A : Spacetime →L[ℝ] Spacetime,
      (∃ g : ProperLorentz, g.val.val = NormedSpace.exp ((1 : ℝ) • A)) ∧
        A.toLinearMap ∉ lorentzAlgebra := by
  exact Bridge.s9

end MinkowskiLorentz
