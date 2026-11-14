module
public import Mathlib
public import ArithmeticLorentz.Defs
public import ArithmeticLorentz.Counting
public import ArithmeticLorentz.PlaceLink
public import ArithmeticLorentz.Boost
public import ArithmeticLorentz.RegisterBridge

@[expose] public section

/-!
# Carried definitions of the adapter

## Part 1 — carried text (namespace `YangMills`)

The declarations between the `BEGIN CARRIED` / `END CARRIED` markers are carried textually.

* Source file: `PublicTheory.lean` of the source distribution `OpenAI-YM-20261028`.
* Lines carried: 11 (`namespace YangMills`), 13–14 (the two `open` lines), 51–55 (`Axis`,
  `SpaceAxis`, `timeAxis`, `Spacetime`, `Space`), 57 (`time`), 59–60 (`spatial`),
  64 (`forwardCone`), 66 (`minkowskiSquare`), 209–212 (`ProperLorentz`),
  215 (`PoincareCoordinates`). Not carried from lines 51–68 and 208–215: the docstrings at lines
  62–63, 208 and 214, and the declaration `spacelike` (line 68).
* Commit: 3456e5e75cf8d4cd558955a5c7638fba2d68f464 (short 3456e5e7).
* Licence of the source: Apache License, Version 2.0 (its `LICENSE` and `NOTICE` files).
* The source's `lean-toolchain` is Lean 4.32.0; the carried text is elaborated here at
  Lean 4.35.0-rc2 with Mathlib 065356127b1d. The source file itself is not imported.

## Part 2 — the adapter's own definitions (namespace `ReleaseAdapter`)

* `minkowskiBilin`, `lorentzAlgebra` — the bilinear form with `minkowskiBilin x x =
  minkowskiSquare x` and the Lie subalgebra of its skew-adjoint endomorphisms of `Spacetime`.
* `placeLin` — the coordinate formula `(a, b, z) ↦ (a, b, √2 Re z, √2 Im z)` from
  `HermitianExclusion.PlaceSpace 2` to `Spacetime`; `timeReflection`.
* `diagSign`, `fourSign` — the four sign maps of the place space; `swapConj`.
* `IsBlockPreserving` — place-preserving on a space `(ι₁ → ℝ) × (ι₂ → ℂ)`: each real coordinate
  line and each complex coordinate block is mapped into itself.
* `placeBoost` — `boostC β` on every complex coordinate, identity on the real coordinates.
* `placeSkew`, `traceSkew` — the Lie subalgebra of endomorphisms skew-adjoint for the polar form
  of `HermitianExclusion.placeForm`; on `mixedSpace K` this is the trace-form-skew Lie algebra.
* `relabel` — the relabelling `mixedSpace K ≃ₗ[ℝ] PlaceSpace 2` of a field with two real places
  and one complex place.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

-- BEGIN CARRIED
namespace YangMills

open MeasureTheory Set Function
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius

abbrev Axis := Fin 4
abbrev SpaceAxis := Fin 3
abbrev timeAxis : Axis := Fin.last 3
abbrev Spacetime := EuclideanSpace ℝ Axis
abbrev Space := EuclideanSpace ℝ SpaceAxis

def time (x : Spacetime) : ℝ := x timeAxis

def spatial (x : Spacetime) : Space :=
  WithLp.toLp 2 fun i ↦ x i.castSucc

def forwardCone : Set Spacetime := {x | ‖spatial x‖ ≤ time x}

def minkowskiSquare (x : Spacetime) : ℝ := time x ^ 2 - ‖spatial x‖ ^ 2

abbrev ProperLorentz := {g : (Spacetime →L[ℝ] Spacetime)ˣ //
  LinearMap.det g.val.toLinearMap = 1 ∧
  (∀ x, minkowskiSquare (g.val x) = minkowskiSquare x) ∧
  (∀ x, g.val x ∈ forwardCone ↔ x ∈ forwardCone)}

abbrev PoincareCoordinates := ProperLorentz × Spacetime

end YangMills
-- END CARRIED

namespace ReleaseAdapter

open YangMills HermitianExclusion
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

/-! ### The form and its Lie algebra on `Spacetime` -/

/-- Sanity: the carried form in coordinates, time last and positive. -/
theorem minkowskiSquare_coords (x : Spacetime) :
    minkowskiSquare x = x 3 ^ 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  have h : ‖spatial x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [spatial, Fin.sum_univ_three]
  rw [minkowskiSquare, h]; rfl

/-- Sanity: the identity is in the carried set `ProperLorentz`. -/
example : ProperLorentz := ⟨1, by simp, fun _ => rfl, fun _ => Iff.rfl⟩

/-- The symmetric bilinear form `x 3 * y 3 - (x 0 * y 0 + x 1 * y 1 + x 2 * y 2)` on
`Spacetime`. -/
def minkowskiBilin : LinearMap.BilinForm ℝ Spacetime :=
  LinearMap.mk₂ ℝ (fun x y => x 3 * y 3 - (x 0 * y 0 + x 1 * y 1 + x 2 * y 2))
    (fun x₁ x₂ y => by simp only [PiLp.add_apply]; ring)
    (fun c x y => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)
    (fun x y₁ y₂ => by simp only [PiLp.add_apply]; ring)
    (fun c x y => by simp only [PiLp.smul_apply, smul_eq_mul]; ring)

theorem minkowskiBilin_apply (x y : Spacetime) :
    minkowskiBilin x y = x 3 * y 3 - (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) :=
  rfl

/-- Sanity: the quadratic form of `minkowskiBilin` is the carried `minkowskiSquare`. -/
theorem minkowskiBilin_self (x : Spacetime) : minkowskiBilin x x = minkowskiSquare x := by
  rw [minkowskiBilin_apply, minkowskiSquare_coords]; ring

/-- The Lie subalgebra of the endomorphisms `A` of `Spacetime` that are skew-adjoint for
`minkowskiBilin`: `minkowskiBilin (A x) y = minkowskiBilin x (-A y)`. -/
def lorentzAlgebra : LieSubalgebra ℝ (Module.End ℝ Spacetime) :=
  skewAdjointLieSubalgebra minkowskiBilin

/-- The time reflection `(x 0, x 1, x 2, x 3) ↦ (x 0, x 1, x 2, -x 3)` of `Spacetime`. -/
def timeReflection : Spacetime →ₗ[ℝ] Spacetime where
  toFun x := WithLp.toLp 2 ![x 0, x 1, x 2, -x 3]
  map_add' x y := by
    ext i; fin_cases i <;> simp; ring
  map_smul' c x := by
    ext i; fin_cases i <;> simp

/-! ### The place space `ℝ² × ℂ` and `Spacetime` -/

/-- The coordinate formula of the explicit isometry: `(a, b, z) ↦ (a, b, √2 Re z, √2 Im z)`,
with the time axis (index `3`) carrying `√2 Im z`. -/
def placeLin : PlaceSpace 2 →ₗ[ℝ] Spacetime where
  toFun p := WithLp.toLp 2 ![p.1 0, p.1 1, √2 * (p.2 0).re, √2 * (p.2 0).im]
  map_add' p q := by
    ext i; fin_cases i <;> simp <;> ring
  map_smul' c p := by
    ext i; fin_cases i <;> simp <;> ring

theorem placeLin_apply (p : PlaceSpace 2) :
    placeLin p = WithLp.toLp 2 ![p.1 0, p.1 1, √2 * (p.2 0).re, √2 * (p.2 0).im] :=
  rfl

/-- The sign map with matrix `diag(ε₀, ε₁, ε₂, 1)` in the coordinates `(a, b, Re z, Im z)`:
`(a, b, z) ↦ (ε₀ a, ε₁ b, ε₂ Re z + i Im z)`. -/
def diagSign (ε₀ ε₁ ε₂ : ℝ) : PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2 where
  toFun p := (![ε₀ * p.1 0, ε₁ * p.1 1], fun j => ⟨ε₂ * (p.2 j).re, (p.2 j).im⟩)
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · funext i; fin_cases i <;> simp <;> ring
    · funext j; apply Complex.ext <;> simp; ring
  map_smul' c p := by
    refine Prod.ext ?_ ?_
    · funext i; fin_cases i <;> simp <;> ring
    · funext j; apply Complex.ext <;> simp; ring

/-- The four sign maps `diag(1, 1, 1, 1)`, `diag(-1, -1, 1, 1)`, `diag(1, -1, -1, 1)`,
`diag(-1, 1, -1, 1)` in the coordinates `(a, b, Re z, Im z)`. -/
def fourSign : Fin 4 → (PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2) :=
  ![diagSign 1 1 1, diagSign (-1) (-1) 1, diagSign 1 (-1) (-1), diagSign (-1) 1 (-1)]

/-- The map `(a, b, z) ↦ (b, a, conj z)`: it exchanges the two real coordinates and conjugates the
complex coordinate. -/
def swapConj : PlaceSpace 2 →ₗ[ℝ] PlaceSpace 2 where
  toFun p := (![p.1 1, p.1 0], fun j => (starRingEnd ℂ) (p.2 j))
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · funext i; fin_cases i <;> simp
    · funext j; simp
  map_smul' c p := by
    refine Prod.ext ?_ ?_
    · funext i; fin_cases i <;> simp
    · funext j; simp [Complex.real_smul]

/-! ### Spaces `(ι₁ → ℝ) × (ι₂ → ℂ)`: block-preserving maps, the boost, the trace-form-skew
Lie algebra -/

section Places

variable {ι₁ ι₂ : Type*}

/-- `T` is place-preserving (block-preserving) on `(ι₁ → ℝ) × (ι₂ → ℂ)`: for every real index
`i`, the vectors supported on the real coordinate `i` are mapped to vectors supported on the real
coordinate `i`; for every complex index `j`, the vectors supported on the complex coordinate `j`
are mapped to vectors supported on the complex coordinate `j`. No permutation of coordinates is
allowed. -/
def IsBlockPreserving
    (T : ((ι₁ → ℝ) × (ι₂ → ℂ)) →ₗ[ℝ] ((ι₁ → ℝ) × (ι₂ → ℂ))) : Prop :=
  (∀ (i : ι₁) (v : (ι₁ → ℝ) × (ι₂ → ℂ)), (∀ i', i' ≠ i → v.1 i' = 0) → v.2 = 0 →
      (∀ i', i' ≠ i → (T v).1 i' = 0) ∧ (T v).2 = 0) ∧
  (∀ (j : ι₂) (v : (ι₁ → ℝ) × (ι₂ → ℂ)), v.1 = 0 → (∀ j', j' ≠ j → v.2 j' = 0) →
      (T v).1 = 0 ∧ ∀ j', j' ≠ j → (T v).2 j' = 0)

/-- The boost on `(ι₁ → ℝ) × (ι₂ → ℂ)`: the identity on the real coordinates and
`boostC β : z ↦ cosh β · z + i sinh β · conj z` on every complex coordinate. For `ι₁ = Fin r₁`,
`ι₂ = Fin 1` it is `HermitianExclusion.boost r₁ β`. -/
def placeBoost (β : ℝ) : ((ι₁ → ℝ) × (ι₂ → ℂ)) →ₗ[ℝ] ((ι₁ → ℝ) × (ι₂ → ℂ)) where
  toFun p := (p.1, fun j => boostC β (p.2 j))
  map_add' p q := Prod.ext rfl (funext fun j => boostC_add β (p.2 j) (q.2 j))
  map_smul' c p := Prod.ext rfl (funext fun j => boostC_smul β c (p.2 j))

theorem placeBoost_apply (β : ℝ) (p : (ι₁ → ℝ) × (ι₂ → ℂ)) :
    placeBoost β p = (p.1, fun j => boostC β (p.2 j)) :=
  rfl

/-- Sanity: on `PlaceSpace r₁` the boost `placeBoost β` is `HermitianExclusion.boost r₁ β`. -/
theorem placeBoost_eq_boost (r₁ : ℕ) (β : ℝ) :
    (placeBoost β : PlaceSpace r₁ →ₗ[ℝ] PlaceSpace r₁) = boost r₁ β :=
  rfl

variable (ι₁ ι₂) in
/-- The Lie subalgebra of the endomorphisms of `(ι₁ → ℝ) × (ι₂ → ℂ)` that are skew-adjoint for
the polar form of `HermitianExclusion.placeForm ι₁ ι₂`, the form
`(x, z) ↦ Σ x_i² + Σ 2 Re(z_j²)`. -/
def placeSkew [Fintype ι₁] [Fintype ι₂] :
    LieSubalgebra ℝ (Module.End ℝ ((ι₁ → ℝ) × (ι₂ → ℂ))) :=
  skewAdjointLieSubalgebra (QuadraticMap.polarBilin (placeForm ι₁ ι₂))

end Places

section NumberField

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The trace-form-skew Lie algebra of `mixedSpace K`: the endomorphisms skew-adjoint for the
polar form of the place form, which is `x ↦ Tr_{K/ℚ}(x²)` on the image of `K`
(`HermitianExclusion.trace_sq_eq_placeForm`). The `Fintype` instances on the two sets of places
are the classical ones, as in `ArithmeticLorentz.PlaceLink`. -/
abbrev traceSkew : LieSubalgebra ℝ (Module.End ℝ (mixedSpace K)) :=
  placeSkew {w : InfinitePlace K // IsReal w} {w : InfinitePlace K // IsComplex w}

variable {K}

/-- The relabelling of the mixed space of a field with two real places and one complex place,
for a labelling `e₁` of the real places and `e₂` of the complex place:
`(x, z) ↦ (x ∘ e₁.symm, z ∘ e₂.symm)`. -/
def relabel (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) : mixedSpace K ≃ₗ[ℝ] PlaceSpace 2 :=
  LinearEquiv.prodCongr (LinearEquiv.funCongrLeft ℝ ℝ e₁.symm)
    (LinearEquiv.funCongrLeft ℝ ℂ e₂.symm)

omit [NumberField K] in
theorem relabel_apply (e₁ : {w : InfinitePlace K // IsReal w} ≃ Fin 2)
    (e₂ : {w : InfinitePlace K // IsComplex w} ≃ Fin 1) (v : mixedSpace K) :
    relabel e₁ e₂ v = (fun i => v.1 (e₁.symm i), fun j => v.2 (e₂.symm j)) :=
  rfl

end NumberField

end ReleaseAdapter
