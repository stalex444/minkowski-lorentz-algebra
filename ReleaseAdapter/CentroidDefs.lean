module
public import Mathlib
public import LorentzLie.Defs
public import LorentzLie.Landings
public import ReleaseAdapter.Carried

@[expose] public section

/-!
# Definitions for the bracket-commuting maps of `lorentzAlgebra`

`Spacetime`, `time`, `spatial`, `minkowskiSquare` are copies carried from the public statement of
the Yang–Mills release (`ReleaseAdapter/Carried.lean`, Part 1); `minkowskiBilin` and
`lorentzAlgebra` are this package's (Part 2). This file adds, on `lorentzAlgebra`:

* `lorentzHodge` — the Hodge operator `LorentzLie.hodge ![1, 1, 1, -1]` read on `lorentzAlgebra`
  along `LorentzLie.lorentzAlgebraEquivEtaSkew` (the matrix in the standard coordinates);
  `lorentzAlgebraEquivEtaSkew_lorentzHodge` and `lorentzHodge_coe` pin it down.
* `lorentzBoost k` (`k : Fin 3`) — the endomorphism `x ↦ x 3 • e_k + x k • e_3` of `Spacetime`,
  which mixes the space axis `k` with the time axis `timeAxis = 3`.
* `lorentzRot i j` (`i j : Fin 3`) — the endomorphism `x ↦ x i • e_j - x j • e_i` of `Spacetime`
  (`e_i ↦ e_j`, `e_j ↦ -e_i`), in the plane of the space axes `i` and `j`. It is `0` for `i = j`
  and `lorentzRot j i = -lorentzRot i j`.
* `lorentzTraceForm` — the bilinear form `(X, Y) ↦ trace (X ∘ Y)` on `lorentzAlgebra`, the trace
  being that of endomorphisms of `Spacetime`.

The six sanity statements `lorentzBoost_zero_apply`, …, `lorentzRot_zero_one_apply` give the
coordinate formulas of the six generators; `lorentzAlgebraEquivEtaSkew_lorentzBoost` and
`lorentzAlgebraEquivEtaSkew_lorentzRot` give their matrices.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

namespace ReleaseAdapter

open YangMills

/-! ### The Hodge operator on `lorentzAlgebra` -/

/-- The Hodge operator on `lorentzAlgebra`: an endomorphism `X` of `Spacetime` in `lorentzAlgebra`
is sent to the endomorphism whose matrix in the standard coordinates is
`LorentzLie.hodgeMat ![1, 1, 1, -1]` of the matrix of `X`. In symbols,
`lorentzHodge = φ⁻¹ ∘ LorentzLie.hodge ![1, 1, 1, -1] ∘ φ` with
`φ = LorentzLie.lorentzAlgebraEquivEtaSkew`. -/
def lorentzHodge : lorentzAlgebra →ₗ[ℝ] lorentzAlgebra :=
  (LorentzLie.lorentzAlgebraEquivEtaSkew.symm.toLinearEquiv :
      LorentzLie.etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ) →ₗ[ℝ] lorentzAlgebra) ∘ₗ
    LorentzLie.hodge (![1, 1, 1, -1] : Fin 4 → ℝ) ∘ₗ
    (LorentzLie.lorentzAlgebraEquivEtaSkew.toLinearEquiv :
      lorentzAlgebra →ₗ[ℝ] LorentzLie.etaSkew (![1, 1, 1, -1] : Fin 4 → ℝ))

/-- Sanity: under `LorentzLie.lorentzAlgebraEquivEtaSkew`, `lorentzHodge` is
`LorentzLie.hodge ![1, 1, 1, -1]`. -/
theorem lorentzAlgebraEquivEtaSkew_lorentzHodge (X : lorentzAlgebra) :
    LorentzLie.lorentzAlgebraEquivEtaSkew (lorentzHodge X) =
      LorentzLie.hodge (![1, 1, 1, -1] : Fin 4 → ℝ) (LorentzLie.lorentzAlgebraEquivEtaSkew X) :=
  LieEquiv.apply_symm_apply _ _

/-- Sanity: the endomorphism `lorentzHodge X` of `Spacetime` is the one with matrix
`LorentzLie.hodgeMat ![1, 1, 1, -1] M`, where `M` is the matrix of `X` in the standard
coordinates. -/
theorem lorentzHodge_coe (X : lorentzAlgebra) :
    ((lorentzHodge X : lorentzAlgebra) : Module.End ℝ Spacetime) =
      Matrix.toEuclideanLin (LorentzLie.hodgeMat (![1, 1, 1, -1] : Fin 4 → ℝ)
        (Matrix.toEuclideanLin.symm (X : Module.End ℝ Spacetime))) := by
  have h := congrArg Subtype.val (lorentzAlgebraEquivEtaSkew_lorentzHodge X)
  rw [LorentzLie.lorentzAlgebraEquivEtaSkew_apply, LorentzLie.hodge_coe,
    LorentzLie.lorentzAlgebraEquivEtaSkew_apply] at h
  rw [← h, LinearEquiv.apply_symm_apply]

/-! ### The six generators -/

/-- The endomorphism with matrix `E k 3 + E 3 k` is in `lorentzAlgebra`. -/
theorem lorentzBoost_mem (k : Fin 3) :
    (Matrix.toEuclideanLin (Matrix.single k.castSucc timeAxis (1 : ℝ) +
        Matrix.single timeAxis k.castSucc (1 : ℝ)) : Module.End ℝ Spacetime) ∈ lorentzAlgebra := by
  rw [LorentzLie.Landings.toEuclideanLin_mem_lorentzAlgebra_iff, LorentzLie.mem_etaSkew_iff]
  intro i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [timeAxis]

/-- The boost generator along the space axis `k`: the endomorphism `x ↦ x 3 • e_k + x k • e_3` of
`Spacetime`, with matrix `E k 3 + E 3 k` in the standard coordinates (`3 = timeAxis`). -/
def lorentzBoost (k : Fin 3) : lorentzAlgebra :=
  ⟨Matrix.toEuclideanLin (Matrix.single k.castSucc timeAxis (1 : ℝ) +
      Matrix.single timeAxis k.castSucc (1 : ℝ)), lorentzBoost_mem k⟩

/-- The endomorphism with matrix `E j i - E i j` (`i`, `j` space axes) is in `lorentzAlgebra`. -/
theorem lorentzRot_mem (i j : Fin 3) :
    (Matrix.toEuclideanLin (Matrix.single j.castSucc i.castSucc (1 : ℝ) -
        Matrix.single i.castSucc j.castSucc (1 : ℝ)) : Module.End ℝ Spacetime) ∈ lorentzAlgebra := by
  rw [LorentzLie.Landings.toEuclideanLin_mem_lorentzAlgebra_iff, LorentzLie.mem_etaSkew_iff]
  intro a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> simp

/-- The rotation generator in the plane of the space axes `i` and `j`: the endomorphism
`x ↦ x i • e_j - x j • e_i` of `Spacetime` (`e_i ↦ e_j`, `e_j ↦ -e_i`), with matrix
`E j i - E i j` in the standard coordinates. It is `0` for `i = j`. -/
def lorentzRot (i j : Fin 3) : lorentzAlgebra :=
  ⟨Matrix.toEuclideanLin (Matrix.single j.castSucc i.castSucc (1 : ℝ) -
      Matrix.single i.castSucc j.castSucc (1 : ℝ)), lorentzRot_mem i j⟩

/-- Sanity: the matrix of `lorentzBoost k` in the standard coordinates is `E k 3 + E 3 k`. -/
theorem lorentzAlgebraEquivEtaSkew_lorentzBoost (k : Fin 3) :
    (LorentzLie.lorentzAlgebraEquivEtaSkew (lorentzBoost k) : Matrix (Fin 4) (Fin 4) ℝ) =
      Matrix.single k.castSucc timeAxis (1 : ℝ) + Matrix.single timeAxis k.castSucc (1 : ℝ) := by
  rw [LorentzLie.lorentzAlgebraEquivEtaSkew_apply]
  exact LinearEquiv.symm_apply_apply _ _

/-- Sanity: the matrix of `lorentzRot i j` in the standard coordinates is `E j i - E i j`. -/
theorem lorentzAlgebraEquivEtaSkew_lorentzRot (i j : Fin 3) :
    (LorentzLie.lorentzAlgebraEquivEtaSkew (lorentzRot i j) : Matrix (Fin 4) (Fin 4) ℝ) =
      Matrix.single j.castSucc i.castSucc (1 : ℝ) - Matrix.single i.castSucc j.castSucc (1 : ℝ) := by
  rw [LorentzLie.lorentzAlgebraEquivEtaSkew_apply]
  exact LinearEquiv.symm_apply_apply _ _

/-- Sanity: `lorentzBoost 0` is `x ↦ (x 3, 0, 0, x 0)`. -/
theorem lorentzBoost_zero_apply (x : Spacetime) :
    (lorentzBoost 0 : Module.End ℝ Spacetime) x = WithLp.toLp 2 ![x 3, 0, 0, x 0] := by
  ext a
  fin_cases a <;>
    simp [lorentzBoost, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.single_apply,
      timeAxis]

/-- Sanity: `lorentzBoost 1` is `x ↦ (0, x 3, 0, x 1)`. -/
theorem lorentzBoost_one_apply (x : Spacetime) :
    (lorentzBoost 1 : Module.End ℝ Spacetime) x = WithLp.toLp 2 ![0, x 3, 0, x 1] := by
  ext a
  fin_cases a <;>
    simp [lorentzBoost, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.single_apply,
      timeAxis]

/-- Sanity: `lorentzBoost 2` is `x ↦ (0, 0, x 3, x 2)`. -/
theorem lorentzBoost_two_apply (x : Spacetime) :
    (lorentzBoost 2 : Module.End ℝ Spacetime) x = WithLp.toLp 2 ![0, 0, x 3, x 2] := by
  ext a
  fin_cases a <;>
    simp [lorentzBoost, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.single_apply,
      timeAxis]

/-- Sanity: `lorentzRot 1 2` is `x ↦ (0, -x 2, x 1, 0)`. -/
theorem lorentzRot_one_two_apply (x : Spacetime) :
    (lorentzRot 1 2 : Module.End ℝ Spacetime) x = WithLp.toLp 2 ![0, -x 2, x 1, 0] := by
  ext a
  fin_cases a <;>
    simp [lorentzRot, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.single_apply]

/-- Sanity: `lorentzRot 2 0` is `x ↦ (x 2, 0, -x 0, 0)`. -/
theorem lorentzRot_two_zero_apply (x : Spacetime) :
    (lorentzRot 2 0 : Module.End ℝ Spacetime) x = WithLp.toLp 2 ![x 2, 0, -x 0, 0] := by
  ext a
  fin_cases a <;>
    simp [lorentzRot, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.single_apply]

/-- Sanity: `lorentzRot 0 1` is `x ↦ (-x 1, x 0, 0, 0)`. -/
theorem lorentzRot_zero_one_apply (x : Spacetime) :
    (lorentzRot 0 1 : Module.End ℝ Spacetime) x = WithLp.toLp 2 ![-x 1, x 0, 0, 0] := by
  ext a
  fin_cases a <;>
    simp [lorentzRot, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.single_apply]

/-- Sanity: exchanging the two axes changes the sign, `lorentzRot j i = -lorentzRot i j`. -/
theorem lorentzRot_swap (i j : Fin 3) : lorentzRot j i = -lorentzRot i j := by
  apply Subtype.ext
  simp [lorentzRot]

/-! ### The trace form -/

/-- The trace form of `lorentzAlgebra` on `Spacetime`: `(X, Y) ↦ trace (X ∘ Y)`, the trace of the
composition of the two endomorphisms of `Spacetime`. -/
def lorentzTraceForm : LinearMap.BilinForm ℝ lorentzAlgebra :=
  LinearMap.mk₂ ℝ
    (fun X Y => LinearMap.trace ℝ Spacetime
      ((X : Module.End ℝ Spacetime) * (Y : Module.End ℝ Spacetime)))
    (fun X₁ X₂ Y => by simp [add_mul])
    (fun c X Y => by simp)
    (fun X Y₁ Y₂ => by simp [mul_add])
    (fun c X Y => by simp)

/-- Sanity: `lorentzTraceForm X Y` unfolds to the trace of the product `X * Y` in the endomorphisms
of `Spacetime`, that is, of the composition `X ∘ Y`. -/
theorem lorentzTraceForm_apply (X Y : lorentzAlgebra) :
    lorentzTraceForm X Y = LinearMap.trace ℝ Spacetime
      ((X : Module.End ℝ Spacetime) * (Y : Module.End ℝ Spacetime)) :=
  rfl

/-- Sanity: the trace form is the trace of the product of the two matrices in the standard
coordinates. -/
theorem lorentzTraceForm_eq_matrix_trace (X Y : lorentzAlgebra) :
    lorentzTraceForm X Y =
      Matrix.trace ((LorentzLie.lorentzAlgebraEquivEtaSkew X : Matrix (Fin 4) (Fin 4) ℝ) *
        (LorentzLie.lorentzAlgebraEquivEtaSkew Y : Matrix (Fin 4) (Fin 4) ℝ)) := by
  rw [lorentzTraceForm_apply, LinearMap.trace_eq_matrix_trace ℝ (PiLp.basisFun 2 ℝ (Fin 4)),
    LinearMap.toMatrix_mul]
  rfl

/-- Sanity: `lorentzTraceForm` is Mathlib's trace form `LieModule.traceForm` of `lorentzAlgebra`
acting on `Spacetime`. -/
theorem lorentzTraceForm_eq_traceForm :
    lorentzTraceForm = LieModule.traceForm ℝ lorentzAlgebra Spacetime := by
  ext X Y
  rfl

end ReleaseAdapter
