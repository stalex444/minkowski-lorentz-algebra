module
public import Mathlib

@[expose] public section
/-!
# Invariant bilinear forms on the Lorentz Lie algebra `so(3, 1)`: the two-parameter family, with `sl(2, ℂ)`, the exponential criterion and the complexification

Let `L` be the Lie algebra of the linear endomorphisms of four-dimensional Minkowski space that
are skew-adjoint for the Minkowski form. This entry compares exactly nine statements.
The main theorem is statement 6: the invariant bilinear forms on `L` are exactly
`a · tr (X Y) + b · tr (H(X) Y)`, with `(a, b)` unique, and all of them are symmetric. Statements 1–5
are the identification with `sl(2, ℂ)`, the exponential criterion, the operator `H` and the
complexification. By statements 2 and 4, `L` is `sl(2, ℂ)` regarded as a real Lie algebra and `H` is
multiplication by `-i` under that isomorphism. `sl(2, ℂ)` is a complex simple Lie algebra (a classical
fact, not one of the compared statements), and by the uniqueness of `(a, b)` the forms with `b ≠ 0`
are the invariant forms that are not multiples of the trace form. Statements 7–9 are controls. They
are listed below by role; `comparator.json` and the theorems of this file keep the order 1–9.

The main theorem, the invariant bilinear forms (statement 6):

6. `invariant_bilinForm_iff` — a real bilinear form `B` on `L` satisfies
   `B ⁅Z, X⁆ Y + B X ⁅Z, Y⁆ = 0` for all `X`, `Y`, `Z` if and only if
   `B X Y = a · tr (X Y) + b · tr (H(X) Y)` for exactly one pair of real numbers `(a, b)`; every
   such form is symmetric. Here `tr (X Y)` is Mathlib's `LieModule.traceForm` of `L` acting on
   Minkowski space.

`sl(2, ℂ)` and the exponential criterion (statements 1–3):

1. `so'_one_three_lieEquiv_sl2C` — on Mathlib's own objects, with nothing carried: Mathlib's
   `LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ` is isomorphic, as a real Lie algebra, to
   `sl(2, ℂ)` (Mathlib's `sl (Fin 2) ℂ` with scalars restricted to `ℝ`), by the explicit map
   `X ↦ -½ Σ_k (β_k + i θ_k) σ_k`, where `β_k` and `θ_k` are the boost and rotation entries of
   `X` and `σ_k` are the Pauli matrices.
2. `lorentzAlgebra_lieEquiv_sl2C` — on the carried copy of Minkowski space: `L` has dimension
   `6`; the map `X ↦ -½ Σ_k (β_k + i θ_k) σ_k` (`spinMatrix`) is an isomorphism of real Lie
   algebras from `L` onto `sl(2, ℂ)`; the three boost generators and the three rotation
   generators are in `L`, the boost along the axis `k` goes to `-½ σ_k` and the rotation in the
   plane of the two other axes goes to `-(i/2) σ_k`.
3. `mem_lorentzAlgebra_iff_exp` — the exponential criterion: a continuous linear endomorphism `A`
   is in `L` if and only if `exp (t A)` is in the carried type `ProperLorentz` for every real `t`.
   The statement also records that the Minkowski form used for `L` has the carried
   `minkowskiSquare` as its quadratic form.

The operator `H` and the complexification (statements 4–5):

4. `hodgeEnd_complexStructure` — the explicit operator `H` (`hodgeEnd`: the boost along the axis
   `k` goes to minus the rotation in the plane of the two other axes, and that rotation goes to
   the boost) maps `L` into `L`, is real-linear there, satisfies `H ⁅X, Y⁆ = ⁅X, H Y⁆` and
   `H (H X) = -X`, and the isomorphism of statement 2 carries it to multiplication by `-i` on
   `sl(2, ℂ)`.
5. `complexification_lieEquiv` — the complexification `ℂ ⊗_ℝ L` is isomorphic, as a complex Lie
   algebra, to `sl(2, ℂ) × sl(2, ℂ)`, and the two maps `½ (1 + i H)` and `½ (1 - i H)` are the
   projections onto the two factors, `H` being the operator of statement 4 extended
   `ℂ`-linearly.

Controls (statements 7–9):

7. `definite_split_signature` — for the definite diagonal form `diag(1, 1, 1, 1)` the Lie algebra
   of skew matrices is isomorphic to `so(3) × so(3)`, for the split form `diag(1, 1, -1, -1)` it
   is isomorphic to `sl(2, ℝ) × sl(2, ℝ)`, and neither of the two is isomorphic to `sl(2, ℂ)` as
   a real Lie algebra (all on Mathlib's `skewAdjointMatricesLieSubalgebra`).
8. `exists_bilinForm_not_trace_form` — there is a bilinear form on `L` that is not
   `a · tr (X Y) + b · tr (H(X) Y)` for any real `a`, `b`: so not every bilinear form on `L` is
   invariant.
9. `exists_exp_mem_not_mem_lorentzAlgebra` — there is a continuous linear endomorphism `A` with
   `exp A` in `ProperLorentz` and `A` not in `L`: in statement 3, "for every real `t`" cannot be
   replaced by "for `t = 1`".

Carried definitions. The declarations between the markers `BEGIN CARRIED` and `END CARRIED`
(`Axis`, `SpaceAxis`, `timeAxis`, `Spacetime`, `Space`, `time`, `spatial`, `forwardCone`,
`minkowskiSquare`, `ProperLorentz`, `PoincareCoordinates`) are copies carried textually from the
public statement of the Yang–Mills release: repository
`github.com/yang-mills-group/OpenAI-YM-20261028`, commit
`3456e5e75cf8d4cd558955a5c7638fba2d68f464`, file `PublicTheory.lean`, lines 11, 13–14, 51–55, 57,
59–60, 64, 66, 209–212 and 215, under the Apache License, Version 2.0. The source file is not
imported; the copies are elaborated here at this entry's Lean and Mathlib versions. The block
consists of exactly those lines, blank lines and the closing line `end YangMills`. The copy
`PoincareCoordinates` is carried with the block and is not used by any statement.

Conventions.
* `Spacetime` is `EuclideanSpace ℝ (Fin 4)`; the space axes are the indices `0, 1, 2` and the time
  axis is the index `3` (`timeAxis`). The copies carry no docstrings (the carried lines are
  unaltered; the three docstrings of the source, at its lines 62–63, 208 and 214, are among the
  lines not carried); their meaning is: `time x = x₃`; `spatial x = (x₀, x₁, x₂)` in
  `EuclideanSpace ℝ (Fin 3)`; `forwardCone = {x | ‖spatial x‖ ≤ time x}`, the closed forward
  cone; `minkowskiSquare x = time x ^ 2 - ‖spatial x‖ ^ 2`, that is,
  `x₃² - (x₀² + x₁² + x₂²)`; `ProperLorentz` is the type of the invertible continuous linear
  maps `g` of `Spacetime` with `det g = 1`, `minkowskiSquare (g x) = minkowskiSquare x` for all
  `x`, and `g x ∈ forwardCone ↔ x ∈ forwardCone` for all `x`.
* `minkowskiBilin x y = x₃ y₃ - (x₀ y₀ + x₁ y₁ + x₂ y₂)`, the symmetric bilinear form whose
  quadratic form is `minkowskiSquare` (statement 3); `lorentzAlgebra` (`L`) is Mathlib's
  `skewAdjointLieSubalgebra minkowskiBilin`: the endomorphisms `A` with
  `minkowskiBilin (A x) y = -minkowskiBilin x (A y)`, with the commutator bracket.
* `boostEnd k` is `x ↦ x₃ e_k + x_k e₃`; `rotEnd i j` is `x ↦ x_i e_j - x_j e_i`. Sums of indices
  such as `k + 1`, `k + 2` are taken in `Fin 3`, so `rotEnd (k + 1) (k + 2)` is the rotation in
  the plane of the two space axes other than `k`, in cyclic order.
* `hodgeMatrix` is the operator `X ↦ ⋆(η X) η` on `4 × 4` matrices, with `η = diag(1, 1, 1, -1)`
  (the negative of the matrix of `minkowskiBilin`; the operator is the same for `-η`) and `⋆`
  the complement of index pairs with sign `ε₀₁₂₃ = +1` (no index is raised inside `⋆`),
  written out entry by entry; `hodgeEnd` is the same operator on endomorphisms of `Spacetime`,
  through the matrix in the standard coordinates. The docstring of `hodgeMatrix` states its
  relation to the Hodge dual of two-forms for the two normalisations of the alternating symbol.
* `pauli 0, pauli 1, pauli 2` are the Pauli matrices `σ₁, σ₂, σ₃`; in the formulas of this file
  the index runs over `k = 0, 1, 2` and `σ_k` stands for `pauli k`. `sl2CReal` is `sl(2, ℂ)` as a
  real Lie algebra and `sl2CRealMat` reads off the complex `2 × 2` matrix of an element.
  `spinOf β θ = -½ Σ_k (β_k + i θ_k) σ_k`.
* The line `attribute [local instance] LieRing.ofAssociativeRing` makes Mathlib's commutator
  bracket `⁅A, B⁆ = A * B - B * A` of an associative ring available in this file. It is the
  bracket of the endomorphisms of `Spacetime` and of the matrix algebras in every statement.
* In statement 1 the time index of Mathlib's `so' (Fin 1) (Fin 3) ℝ` is `Sum.inl 0` and the
  space indices are `Sum.inr k`; its form is `diag(1, -1, -1, -1)`.

Scope.
* Statements 2–6, 8 and 9 are about the copy of Minkowski space carried from the public statement
  of the Yang–Mills release, in its coordinates. Statements 1 and 7 use none of the carried definitions:
  their Lie algebras are Mathlib's, and the formula of statement 1 uses this entry's `spinOf` and
  `pauli`.
  Statement 1 and part (b) of statement 2 are one isomorphism on two presentations (Mathlib's
  matrices indexed by `Fin 1 ⊕ Fin 3`; the endomorphisms of the carried `Spacetime`): the formula
  is the same under `Sum.inl 0 ↦ 3`, `Sum.inr k ↦ k`. They are not two results.
* The sign in statement 4 depends on the conventions: with the isomorphism of statement 2
  (boost along `k` to `-½ σ_k`, rotation to `-(i/2) σ_k`) and `ε₀₁₂₃ = +1`, time at index `3`,
  the operator `H` is multiplication by `-i`, so `-H` is multiplication by `i`.
* Statement 5 does not give the isomorphism on generators; it states the property that
  identifies the two factors with the two maps `½ (1 ± i H)`.
* Nothing is stated about the Lie group beyond statement 3: no covering map from `SL(2, ℂ)` is
  constructed, and the Lie algebra of `ProperLorentz` is not defined other than through the
  one-parameter groups of statement 3.
* The classification of all linear maps `R` of `L` with `R ⁅X, Y⁆ = ⁅X, R Y⁆` is not a compared
  statement of this entry.

Statements 1–7 and 9 are classical, and statement 8 holds by a count of dimensions (the bilinear
forms on `L` have dimension 36 and the forms of statement 6 are a plane). Statements 1 and 2 are
the Lie-algebra form of `Spin(3, 1) = SL(2, ℂ)` (P. Woit, *Quantum Theory, Groups and
Representations*, the author's draft of 20 October 2025, §40.4, where `SL(2, ℂ)` is said to have the same
Lie algebra as `SO(3, 1)`; the six generators and the dimension are in §40.2); the formula of
statement 2 is the derivative of the action of `SL(2, ℂ)` on Hermitian matrices given there,
with the opposite sign for the boosts. Statement 3 is the description of the Lie algebra of a
matrix group by its one-parameter subgroups, for the subgroup of `O(3; 1)` of determinant one
that preserves the forward cone (B. C. Hall, *An Elementary Introduction to Groups and
Representations*, arXiv:math-ph/0005032, Definition 3.13 and Chapter 3, §5.6, where the
criterion is proved for `O(n; k)` and the Lie algebra of the identity component is said, without
proof in that passage, to be the same; connectedness is not formalized here), and statement 9 is
Exercise 5 of that chapter for this group. Statement 4 is the Hodge operator on
`so(3, 1)` with `⋆⋆X = -X` and `⋆[X, X'] = [X, ⋆X']` (D. K. Wise, Class. Quantum Grav. 27 (2010)
155010, Appendix); `hodgeMatrix` is the matrix printed there, with the time index moved from
the beginning to the end. Statement 5 is the splitting of the complexified Lorentz algebra into
two copies of `sl(2, ℂ)` with the projections `½ (1 ∓ i⋆)` (Woit, §40.2; H. Sahlmann and
R. Seeger, Class. Quantum Grav. 41 (2024) 075010, §2.2.1). Statement 6 is the description of the
invariant bilinear forms of a complex simple Lie algebra regarded as a real one,
`a K + b K(·, J ·)` with `K` the Killing form and `J` the complex structure (G. Ólafsson and
R. Quiroga-Barranco, Transform. Groups 17 (2012) 835–860, Remark A.10; K. Francis-Staite and
T. Leistner, Transform. Groups 26 (2021) 859–892, Proposition 4.1), for `sl(2, ℂ)` and written
with the trace form of Minkowski space. Parts (a) and (b) of statement 7 are the companion
isomorphisms in the two other signatures: `so(4) = so(3) × so(3)` (Woit, §21.2) and
`so(2, 2) ≃ sl(2, ℝ) × sl(2, ℝ)` (Ólafsson and Quiroga-Barranco, Remark A.2; their Remark A.10
has `so(2, 2) ≃ so(2, 1) × so(2, 1)`), with `Spin(2, 2) = SL(2, ℝ) × SL(2, ℝ)` for the groups
(Woit, §40.4). The formula of statements 1 and 2 is printed in Woit, §41.2 (p. 441), on
generators, as the upper block of the representation `π′` of `so(3, 1)`: `π′(k_j)` has upper
block `-½ σ_j` and `π′(l_j)` has `-(i/2) σ_j`, and Woit's `k_j`, `l_j` (§40.2) are this entry's
boosts and rotations with the time index moved from the beginning to the end; Ólafsson and
Quiroga-Barranco state `so(3, 1) ≃ sl(2, ℂ)_ℝ` (Lemma A.1). Two things were not found printed in
the sources read for this entry: the clause of statement 4 on multiplication by `-i`, and parts
(c) and (d) of statement 7. The clause on `-i` follows from the values on the six generators in
statements 2 and 4, by linearity (compare Woit, §41.2, where `π′(B_j)` has upper block `0`).
Parts (c) and (d) follow from parts (a) and (b), the simplicity of `so(3, 1) ≃ sl(2, ℂ)_ℝ`
(Ólafsson and Quiroga-Barranco, p. 9 and Lemma A.1) and the non-simplicity of `so(2, 2)` (ibid.,
Remark A.2) and of `so(4) = so(3) × so(3)`. This entry formalizes known mathematics; the clauses
listed here are the ones not found printed.

Prior formalization (search of 2026-11-13). The group-level counterpart of statements 1 and 2,
`Spin(3, 1) ≃* SL(2, ℂ)`, is in TauCeti, and the homomorphism from `SL(2, ℂ)` onto the restricted
Lorentz group with its kernel is in physlib. TauCeti also has the Lie algebra of `SL(n, ℂ)` as
`sl(n, ℂ)` with scalars restricted to `ℝ`, the Lie algebra of the Spin group of every real
signature as the quadratic elements of the Clifford algebra, the isomorphism of those elements
with the skew-adjoint endomorphisms, and the isomorphism `𝔰𝔲(2) ≅ so(3)`; these were not found
combined there into the isomorphism of statement 1. The equivalence of statement 3 is proved in
TauCeti for the unitary group of a complete normed real algebra with a continuous involution,
for the matrix groups `O(n)`, `SO(n)`, `SL(n)`, `SU(n)` and the symplectic group, and for the
Spin group of every real signature inside the Clifford algebra; by a reading that was not
compiled (the Minkowski adjoint as the involution), the part of statement 3 on the preservation
of the form is a case of the first of these; the direction from the Lie
algebra to the group is proved for Lorentz matrices in physlib and in OSreconstruction; TauCeti
and physlib each define the Lie algebra of a closed subgroup by this criterion. For statement
6, TauCeti proves that over an algebraically closed field every invariant bilinear form on a
Lie algebra with irreducible adjoint module and nondegenerate Killing form is a multiple of the
Killing form; physlib proves that a complex coefficient tensor with four vector indices that is
invariant under `SL(2, ℂ)` acting through the Lorentz group is a combination of the three
pairings of the metric and the alternating symbol, and applies this to products of two field
strengths. The group isomorphisms `Spin(4) ≃* SU(2) × SU(2)` and
`Spin(2, 2) ≃* SL(2, ℝ) × SL(2, ℝ)`, the counterparts for groups of parts (a) and (b) of
statement 7, are in TauCeti. For statement 5, TauCeti proves that extension of scalars carries
the skew-adjoint matrices of a Gram matrix to those of the same matrix over the larger ring, and
the complexifications of `so(n)` and `su(n)`; the splitting into two copies of `sl(2, ℂ)` was not
found there. The Hodge operator of four-dimensional Euclidean space on `4 × 4`
matrices, with its values `+1` and `-1` on two commuting triples of matrices, is in
`github.com/openai/math`. In the places searched, no formalization was found of the isomorphisms
of statements 1, 2, 5 and 7 as isomorphisms of Lie algebras, of statement 3 with both
directions for the Lorentz group or another indefinite orthogonal group of linear maps, of
statement 4, or of statement 6 over `ℝ`. This is a dated search; `README.md`, section "Prior
formalization", names the files and commits, where the search looked and what it could not
search.

Not formalized, beyond the scope items above: no Lie group structure on `ProperLorentz` and no
connectedness statement; no statement that every element of `ProperLorentz` is an exponential;
other dimensions and signatures beyond statement 7; the identification of `L` with two-forms
(Mathlib's `exteriorPower.hodgeStar` is not used); the invariant forms of the complexification.
The list is continued in `README.md`, section "Not formalized".

Sources and proof. The proofs were written before the sources were read and are not adapted
from any of them; `README.md` and `formalization.yaml` record how each source was read. The
isomorphisms are explicit linear maps of skew matrices, and their bracket identities are checked
by computation on the matrix entries; statement 3 is proved by differentiating `t ↦ exp (t A)`
and by writing `exp (t A)` as the square of `exp ((t / 2) A)`; the two non-isomorphisms of
statement 7 are proved by simplicity. Statement 6 is proved in the library from the description
of the linear maps `R` of `L` with `R ⁅X, Y⁆ = ⁅X, R Y⁆` as `a • id + b • H`, which is not
compared here (it is the subject of a separate entry in preparation) and is the same fact read
through the nondegenerate form `tr (X Y)`.

Also proved in the library, not compared: Minkowski space from a number field. For a number field `K` with exactly two
real places and exactly one complex place there is a real-linear equivalence `e` from Mathlib's
`mixedSpace K` onto `Spacetime` with `minkowskiSquare (e x) = -Tr_{K/ℚ}(x²)` for every `x` in
`K`, and conjugation by `e` is an isomorphism of real Lie algebras onto `L` from the Lie algebra
of the endomorphisms of `mixedSpace K` that are skew-adjoint for the form
`Σ x_w² + Σ 2 Re(z_w²)`, the form that restricts to `Tr_{K/ℚ}(x²)` on `K`. This is proved in
the library of this entry and is not compared.

Every statement here is left unproved as a placeholder; `Solution.lean` proves each, with the
identical statement and the identical definitions.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

-- Copies carried textually from the public statement of the Yang–Mills release.
-- Repository: github.com/yang-mills-group/OpenAI-YM-20261028
-- Commit: 3456e5e75cf8d4cd558955a5c7638fba2d68f464 (short 3456e5e7)
-- File: PublicTheory.lean; lines 11, 13–14, 51–55, 57, 59–60, 64, 66, 209–212, 215.
-- Licence of the source: Apache License, Version 2.0 (its LICENSE and NOTICE files).
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **9. Control: one value of `t` is not enough.** There is a continuous linear endomorphism `A`
of `Spacetime` such that `exp A` (`exp (t • A)` at `t = 1`) is the underlying map of an element
of the carried type `ProperLorentz`, and `A` is not in `lorentzAlgebra`. So in statement 3 the
condition for every real `t` cannot be replaced by the condition at `t = 1`. -/
theorem exists_exp_mem_not_mem_lorentzAlgebra :
    ∃ A : Spacetime →L[ℝ] Spacetime,
      (∃ g : ProperLorentz, g.val.val = NormedSpace.exp ((1 : ℝ) • A)) ∧
        A.toLinearMap ∉ lorentzAlgebra := by
  sorry

end MinkowskiLorentz
