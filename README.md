# The Lorentz Lie algebra of four-dimensional Minkowski space: `sl(2, ℂ)`, the exponential criterion, the complexification and the invariant bilinear forms

Author: Stephanie Alexander (ORCID [0009-0003-7727-2565](https://orcid.org/0009-0003-7727-2565)).

Kernel-checked, in Lean 4 + Mathlib. Let `L = so(3, 1)` be the Lorentz Lie algebra: the linear
endomorphisms of four-dimensional Minkowski space that are skew-adjoint for the Minkowski form.
This entry proves nine statements about `L`. (They are the statements the registry's Comparator
checks; "compared" below means one of these nine.)

- **1–2.** `L` is isomorphic to `sl(2, ℂ)` as a real Lie algebra, by the explicit map
  `X ↦ −½ Σ_k (β_k + iθ_k) σ_k` (`β`, `θ` the boost and rotation entries of `X`); `dim L = 6`.
- **3.** A linear endomorphism `A` is in `L` if and only if `exp (t A)` is a proper orthochronous
  Lorentz transformation for every real `t`.
- **4.** The Hodge operator `H` on `L`, defined here entry by entry on matrices, satisfies
  `H[X, Y] = [X, HY]` and `H² = −1`, and the isomorphism carries it to multiplication by `−i`.
- **5.** `ℂ ⊗_ℝ L ≅ sl(2, ℂ) × sl(2, ℂ)`, with `½ (1 ± i H)` the two projections.
- **6.** The invariant bilinear forms on `L` are exactly `a · tr (X Y) + b · tr (H(X) Y)`, with
  `(a, b)` unique; all of them are symmetric.
- **7–9.** Three checks that the hypotheses matter ("controls" below): `so(4) ≅ so(3) × so(3)`
  and `so(2, 2) ≅ sl(2, ℝ) × sl(2, ℝ)`, and neither is `sl(2, ℂ)`; some bilinear form on `L` is
  not of the shape in statement 6; and `exp A` can be in `ProperLorentz` with `A` not in `L`.

Minkowski space is the type `Spacetime` with the quadratic form `minkowskiSquare`, and the proper
orthochronous Lorentz transformations are the type `ProperLorentz` (determinant `1`, the form
preserved, the forward cone preserved). These definitions are copied unaltered ("carried"
below) from the file `PublicTheory.lean` of the public Lean repository
`yang-mills-group/OpenAI-YM-20261028` ("the Yang–Mills release"; see "Definitions"). Statements
1 and 7 use none of the carried definitions: their Lie algebras are Mathlib's, and the formula of
statement 1 uses this entry's `spinOf` and `pauli`.

This entry formalizes known mathematics; the clauses not found printed are listed below. What
this entry adds is the nine statements as kernel-checked theorems on Mathlib's `so'` and on the
carried copy of Minkowski space, with explicit formulas. Statements 1, 2 and 5: Woit, §40.2 and
§40.4; for statement 5 also Sahlmann and Seeger, §2.2.1. Statements 3 and 9: Hall, Definition
3.13, Chapter 3, §5.6 (proved there for `O(3; 1)`) and Exercise 5. Statement 4: Wise, Appendix.
Statement 6: Ólafsson and Quiroga-Barranco, Remark A.10; Francis-Staite and Leistner,
Proposition 4.1. Statement 7(a), (b): the companion isomorphisms in the two other signatures.
Statement 8 is a count of dimensions. "Relation to the literature" gives the pages, and says how
the statement follows from the printed sentence for the four clauses that were not found printed
(the explicit formula of statements 1 and 2, the `-i` clause of statement 4, statement 7(b) with
`sl(2, ℝ)`, and statement 7(c), (d)).

Prior formalization (search of 2026-11-13): none of the nine statements was found. The nearest
work is: the group-level counterparts of statements 1, 2, 5, 7(a) and 7(b) and every ingredient
of statements 1 and 2, in TauCeti, not found combined there, with the homomorphism from
`SL(2, ℂ)` onto the restricted Lorentz group in physlib; the criterion of statement 3 as a
general theorem (TauCeti; the form-preservation part of statement 3 is a case of it, by a reading
that was not compiled) and for other groups, and its direction from the algebra to the group for
Lorentz matrices (physlib, OSreconstruction); two neighbours of statement 6 (TauCeti, physlib);
the extension of scalars for skew-adjoint matrices, the first step of statement 5 (TauCeti);
and the operator of statement 4 in definite signature (`openai/math`). "Prior formalization"
gives the files and commits, where the search looked and what it could not search.

## Who this is for

Formal developments that use the Lorentz group of Minkowski space and need its Lie algebra as an
object: its identification with `sl(2, ℂ)`, the passage between the algebra and the
one-parameter groups, and its invariant bilinear forms.

The objects of this entry are in use in the following public places. They were read on
2026-11-13 at the commits listed under "Prior formalization"; no one at these projects was
contacted, and none of them has asked for or endorsed this entry.

- **physlib.** Its `lorentzAlgebra` is Mathlib's `so' (Fin 1) (Fin 3) ℝ`, the object statement 1
  is stated on. It has the six generators (their linear independence and spanning are marked
  there as not yet proved), and since 2026-11-12 it defines the Lie algebra of a closed matrix
  group by the criterion of statement 3.
- **TauCeti.** The Lie algebras of the real Spin groups by exponential lines, invariant forms on
  simple Lie algebras, and `Spin(3, 1)`, `Spin(4)`, `Spin(2, 2)` as groups.
- **The Yang–Mills release** and the monograph project
  [`hairer/humanise-yang-mills`](https://github.com/hairer/humanise-yang-mills/tree/ba4528fdd98ed0735d498c0ec26e28c8093811f6),
  a crowd-sourced effort to turn that release into a human-readable proof in which existing
  mathematical results are to be found and cited. The file `PublicTheory.lean` of the release
  defines `ProperLorentz` and the covariance of its fields under the Poincaré group built on it; no
  `LieAlgebra`, `LieSubalgebra` or `LieRing` occurs in the repository. Statements 2–6, 8 and 9
  here are stated on copies of that text for Minkowski space, and statements 3 and 9 also on the
  copy of the type `ProperLorentz`.
- **Teaching and papers.** A graduate problem set of 2026 poses statements 1 and 7(a) as
  exercises, and statement 5 without its projections (source S9 below). The self-dual splitting of the complexified Lorentz algebra and
  the invariant forms of a simple real Lie algebra are used in Sahlmann and Seeger (2024) and in
  Francis-Staite and Leistner (2021), and the Hodge operator on `so(3, 1)` in Wise (2010).

## The compared statements (namespace `MinkowskiLorentz`)

`Challenge.lean` states them, with `sorry` placeholders; `Solution.lean` proves them;
`comparator.json` lists them in this order.

`sl(2, ℂ)` and the exponential criterion (statements 1–3):

1. `so'_one_three_lieEquiv_sl2C` — Mathlib's `so' (Fin 1) (Fin 3) ℝ` (real matrices on
   `Fin 1 ⊕ Fin 3` skew-adjoint for `diag(1, −1, −1, −1)`) is isomorphic over `ℝ` to `sl(2, ℂ)`,
   and the isomorphism is the explicit map `X ↦ −½ Σ_k (β_k + iθ_k) σ_k` with
   `β_k = X (inr k) (inl 0)` (boost entries) and `θ_k = X (inr (k+2)) (inr (k+1))` (rotation
   entries). No definition copied from the Yang–Mills release is used.
2. `lorentzAlgebra_lieEquiv_sl2C` — on the carried copy: (a) `L` has real dimension 6;
   (b) `spinMatrix` restricted to `L` is (the matrix of) an isomorphism of real Lie algebras
   `L → sl(2, ℂ)`; (c) the three boosts and three rotations are in `L` and go to `−½σ_k` and
   `−(i/2)σ_k`.
3. `mem_lorentzAlgebra_iff_exp` — (a) `minkowskiBilin x x = minkowskiSquare x` (the carried quadratic form is the quadratic form of the entry's bilinear form). (b) A continuous linear `A` is in `L` iff
   every `exp(tA)`, `t` real, is in the carried `ProperLorentz`.

The operator `H` and the complexification (statements 4–5):

4. `hodgeEnd_complexStructure` — (a) `hodgeEnd` restricts to a real-linear `H : L → L` with
   `H[X,Y] = [X,HY]`, `H² = −1`, and `spinMatrix (H X) = −i · spinMatrix X`: under the isomorphism
   of statement 2, `H` is multiplication by `−i`. (b) `H(boost k) = −rot(k+1,k+2)`,
   `H(rot(k+1,k+2)) = boost k`.
5. `complexification_lieEquiv` — `ℂ ⊗_ℝ L ≅ sl(2,ℂ) × sl(2,ℂ)` as complex Lie algebras, by an
   isomorphism `E` under which `½(1 + iH_ℂ)` is the projection onto the factor `(·, 0)` and
   `½(1 − iH_ℂ)` the projection onto `(0, ·)`; `H` is the linear map of statement 4 (`H X = hodgeEnd X` is part of the statement).

The invariant bilinear forms (statement 6):

6. `invariant_bilinForm_iff` — a bilinear form on `L` is invariant iff it is
   `a·tr(XY) + b·tr(H(X)Y)` for exactly one real pair; invariant forms are symmetric. `tr(XY)` is
   Mathlib's `LieModule.traceForm ℝ L Spacetime`.

Controls (statements 7–9):

7. `definite_split_signature` — `so(4) ≅ so(3) × so(3)`, `so(2,2) ≅ sl(2,ℝ) × sl(2,ℝ)` (as
   Mathlib's `skewAdjointMatricesLieSubalgebra` of `diag(1,1,1,1)`, `diag(1,1,−1,−1)`), and
   neither is isomorphic to `sl(2,ℂ)` over `ℝ`.
8. `exists_bilinForm_not_trace_form` — some bilinear form on `L` is not in the two-parameter
   family of statement 6 (so it is not invariant).
9. `exists_exp_mem_not_mem_lorentzAlgebra` — there is `A` with `exp A ∈ ProperLorentz` and
   `A ∉ L`.

Sums of indices such as `k + 1`, `k + 2` are taken in `Fin 3`, and `σ_k` stands for `pauli k`,
`k = 0, 1, 2` (the Pauli matrices `σ₁, σ₂, σ₃`). The Lorentz algebra is written `so(3, 1)`
throughout; `so(1, 3)` and Mathlib's `so' (Fin 1) (Fin 3) ℝ` put time first, and `so(3; 1)`,
`O(3; 1)` are Hall's notation.

## How the statements relate, and what is proved elsewhere

- **Statements 1 and 2(b) are one isomorphism on two presentations** (Mathlib's matrices indexed
  by `Fin 1 ⊕ Fin 3`; the endomorphisms of the carried `Spacetime`): the formula is the same
  under `Sum.inl 0 ↦ 3`, `Sum.inr k ↦ k`. They are not two results.
- **Statement 6 is proved from the centroid of `L`** (the linear maps `R` with
  `R ⁅X, Y⁆ = ⁅X, R Y⁆`; "bracket-commuting maps" below). Its proof in the library
  (`ReleaseAdapter.lorentzAlgebra_invariant_form`, `ReleaseAdapter/Centroid.lean`) uses
  `ReleaseAdapter.lorentzAlgebra_centroid_lorentzHodge`: every linear map `R` of `L` with
  `R ⁅X, Y⁆ = ⁅X, R Y⁆` is `a • id + b • H` for exactly one pair `(a, b)`. That classification is
  not a compared statement here; it is used here in a proof. Through the nondegenerate form
  `tr (X Y)`, "every invariant form is `a·tr(XY) + b·tr(H(X)Y)`" is equivalent to "every
  bracket-commuting map is `a • id + b • H`" at this form. The classification is the subject of a
  separate entry in preparation, which compares the bracket-commuting maps of the orthogonal Lie
  algebra of a quaternary form; it has no identifier yet.
- **Statement 8 is a control of statement 6.** The bilinear forms on `L` have dimension 36 and
  the forms of statement 6 are a plane; the proof exhibits one form outside the plane.
- **Statement 7** is on `skewAdjointMatricesLieSubalgebra (Matrix.diagonal …)`, not on Mathlib's
  named `so (Fin 4) ℝ` and `so' (Fin 2) (Fin 2) ℝ`.
- **`ArithmeticLorentz` and `GravityScreening` are modules of the author's earlier
  repositories**, on the Solution side only: no file of them is imported by `Challenge.lean`.
  See "Files".

## Definitions

`Challenge.lean` imports Mathlib only and carries every definition its statements use.

**Copies carried from the public statement of the Yang–Mills release** (namespace `YangMills`;
between the markers `BEGIN CARRIED` / `END CARRIED`): `Axis`, `SpaceAxis`, `timeAxis`,
`Spacetime`, `Space`, `time`, `spatial`, `forwardCone`, `minkowskiSquare`, `ProperLorentz`,
`PoincareCoordinates`. Source: repository
[`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e75cf8d4cd558955a5c7638fba2d68f464),
commit `3456e5e75cf8d4cd558955a5c7638fba2d68f464`, file `PublicTheory.lean`, lines 11, 13–14,
51–55, 57, 59–60, 64, 66, 209–212 and 215, under the Apache License, Version 2.0. The source file
is not imported; the copies are elaborated here at this entry's Lean and Mathlib versions. The
copy `PoincareCoordinates` is carried with the block and is not used by any statement. The copies
carry no docstrings (the carried lines are unaltered; the three docstrings of the source, at its lines 62–63, 208 and 214, are among the lines not carried); their meaning is: `time x = x₃`;
`spatial x = (x₀, x₁, x₂)`; `forwardCone = {x | ‖spatial x‖ ≤ time x}`, the closed forward cone;
`minkowskiSquare x = x₃² − (x₀² + x₁² + x₂²)`; `ProperLorentz` is the type of the invertible
continuous linear maps `g` of `Spacetime` with `det g = 1`,
`minkowskiSquare (g x) = minkowskiSquare x` for all `x`, and `g x ∈ forwardCone ↔ x ∈ forwardCone`
for all `x`.

**This entry's** (namespace `MinkowskiLorentz`; each with a docstring stating its convention):

| Definition | Meaning |
|---|---|
| `minkowskiBilin` | `x₃y₃ − (x₀y₀ + x₁y₁ + x₂y₂)` |
| `lorentzAlgebra` | Mathlib's `skewAdjointLieSubalgebra minkowskiBilin` |
| `boostEnd k`, `rotEnd i j` | `x ↦ x₃ e_k + x_k e₃`; `x ↦ x_i e_j − x_j e_i` |
| `hodgeMatrix`, `hodgeEnd` | the operator `X ↦ ⋆(η X) η` on `4 × 4` matrices, `η = diag(1, 1, 1, −1)` (the negative of the matrix of `minkowskiBilin`; the operator is the same for `-η`), time at index `3`, `ε₀₁₂₃ = +1`, written out entry by entry; the same operator on endomorphisms of `Spacetime` |
| `sl2CReal`, `sl2CRealMat` | `sl(2, ℂ)` over `ℝ` and its matrix |
| `pauli` | `σ₁, σ₂, σ₃` |
| `spinOf β θ` | `−½ Σ_k (β_k + iθ_k) σ_k` |
| `spinMatrix A` | `spinOf` of the entries `M k 3` and `M (k+2) (k+1)` of the matrix `M` of `A` |

`spinMatrix` and `hodgeEnd` are total functions on all endomorphisms; every statement uses them
on `L` only (the docstrings say so). The docstring of `hodgeMatrix` states its relation to the
Hodge dual of two-forms for the two normalisations of the alternating symbol. The sign in statement 4 depends on these conventions: with the isomorphism of statement 2, `ε₀₁₂₃ = +1` and time at index `3`, `H` is multiplication by `-i`, so `-H` is multiplication by `i`. The scope account is the section "Scope" of the opening docstring of `Challenge.lean`; "Not formalized" below continues it.

## Also proved in the library, not compared: Minkowski space from a number field

For a number field `K` with exactly two real places and exactly one complex place there is a
real-linear equivalence `e` from Mathlib's `mixedSpace K` onto `Spacetime` with
`minkowskiSquare (e x) = -Tr_{K/ℚ}(x²)` for every `x` in `K`, and conjugation by `e` is an
isomorphism of real Lie algebras onto `L` from the Lie algebra of the endomorphisms of
`mixedSpace K` that are skew-adjoint for the form `Σ x_w² + Σ 2 Re(z_w²)`, the form that
restricts to `Tr_{K/ℚ}(x²)` on `K`. This is proved in the library of this entry and is **not
compared**. The theorems:

- `ReleaseAdapter.mixedIso`, `ReleaseAdapter.minkowskiSquare_mixedIso`,
  `ReleaseAdapter.minkowskiSquare_mixedIso_mixedEmbedding`,
  `ReleaseAdapter.exists_mixedSpace_isometry` (`ReleaseAdapter/Landing.lean`): the equivalence
  for a labelling of the places, the form on the whole mixed space and on the field, and the
  existential form for a field with two real places and one complex place.
- `LorentzLie.NumberFieldAux.traceSkewEquivLorentzAlgebra`,
  `LorentzLie.NumberFieldAux.traceSkewEquivLorentzAlgebra_apply`,
  `LorentzLie.NumberFieldAux.finrank_traceSkew` (`LorentzLie/NumberField.lean`): conjugation by
  that equivalence is a Lie algebra equivalence from `ReleaseAdapter.traceSkew K` to the library's
  `lorentzAlgebra`, and `traceSkew K` has dimension 6.

`Axioms.lean` prints the axioms of these seven declarations with those of the compared ones.

## The proofs

The opening docstring of `Solution.lean` names, statement by statement, the library declarations
that prove each compared statement and what is computed in `Solution.lean` itself. In plain
words:

- **Statements 1 and 2.** A matrix that is skew for a diagonal form `η` with entries `±1` has six
  free entries. For `η` with product of entries `-1` the library writes down a linear map from
  these six coordinates to the trace-zero complex `2 × 2` matrices, with an explicit inverse, and
  checks the bracket identity entry by entry (`LorentzLie/RealForms.lean`). Mathlib's
  `so' (Fin 1) (Fin 3) ℝ` and the algebra `L` of the carried `Spacetime` are each identified with
  such skew matrices (`LorentzLie/Landings.lean`), which also gives the dimension `6`. For
  statement 2(b), `Solution.lean` composes with a fixed conjugation of `sl(2, ℂ)` so that the
  isomorphism has the stated formula, and it computes the values on the six generators.
- **Statement 3.** If `A` is in `L`, the function `t ↦ ⟨exp (t A) x, exp (t A) y⟩` has derivative
  zero, so every `exp (t A)` preserves the form. A linear map that preserves the form has
  determinant of square `1` and maps the forward cone into itself or into its negative; since
  `exp (t A)` is the square of `exp ((t / 2) A)`, its determinant is `1` and it maps the forward
  cone into itself, and onto it because `exp (-t A)` is its inverse. Conversely, if every
  `exp (t A)` preserves the quadratic form, differentiating at `t = 0` gives the skew-adjointness
  of `A`. In that direction only the preservation of `minkowskiSquare` is used.
- **Statement 4.** The operator is given entry by entry. That it commutes with brackets in the
  stated sense and squares to `-1` is proved in the library for the skew matrices of a diagonal
  form (`LorentzLie/Centroid.lean`) and carried to `L` (`ReleaseAdapter/Centroid.lean`); the
  clause on multiplication by `-i` is computed in `Solution.lean`.
- **Statement 5.** Over `ℂ`, conjugation by a diagonal matrix carries the skew matrices of the
  form to the antisymmetric ones; an antisymmetric `4 × 4` matrix determines two trace-zero
  `2 × 2` matrices, and the bracket identity for them is a polynomial identity
  (`LorentzLie/Complexification.lean`). `Solution.lean` carries this to the base change
  `ℂ ⊗[ℝ] L`.
- **Statement 6.** The form `tr (X Y)` on `L` is nondegenerate, so a bilinear form `B` is
  `B X Y = tr (T(X) Y)` for one linear map `T`. If `B` is invariant then `T ⁅X, Y⁆ = ⁅X, T Y⁆`,
  and such a map is `a • id + b • H` for exactly one pair `(a, b)`
  (`ReleaseAdapter.lorentzAlgebra_centroid_lorentzHodge`). The other direction and the symmetry
  are the invariance and the symmetry of the two forms `tr (X Y)` and `tr (H(X) Y)`. The
  classification of the maps `T` is proved in `LorentzLie/Centroid.lean`: the image of a
  generator commutes with everything that commutes with the generator, which confines its
  entries; the elements on which two bracket-commuting maps agree are stable under every
  `⁅X, ·⁆`; and one generator generates everything under these operations.
- **Statement 7.** Parts (a) and (b) are explicit maps as in statements 1 and 2, for the two other
  sign patterns. For (c) and (d): the algebra of skew matrices is simple when the product of the
  signs is `-1`, so `sl(2, ℂ)` is simple as a real Lie algebra, and it is not simple when the
  product is `1` (`LorentzLie/Controls.lean`); an isomorphism would carry simplicity across.
- **Statement 8.** An explicit bilinear form that is antisymmetric and nonzero on a boost and a
  rotation; the forms of statement 6 are symmetric.
- **Statement 9.** `A = 2π J` for an endomorphism `J` with `J ∘ J = -1`, so that `exp A = 1`, and
  `A` is not skew-adjoint for the Minkowski form.

## Not formalized

- **The Lie group.** No covering map from `SL(2, ℂ)` to the carried `ProperLorentz`, no Lie group
  structure on `ProperLorentz`, no connectedness statement (in particular, that `ProperLorentz` is
  the identity component of `O(3; 1)` is not stated), and no statement that every element of
  `ProperLorentz` is an exponential. The Lie algebra of `ProperLorentz` is not defined other than
  through the one-parameter groups of statement 3.
- **Other dimensions and signatures**, beyond the two signatures of statement 7. Statement 7 is
  stated on `skewAdjointMatricesLieSubalgebra` of a diagonal matrix, not on Mathlib's
  `so (Fin 4) ℝ` and `so' (Fin 2) (Fin 2) ℝ`.
- **Two-forms.** The identification of `L` with the two-forms of Minkowski space is not
  formalized, and Mathlib's `exteriorPower.hodgeStar` is not used: `H` is defined on matrices,
  entry by entry. The docstring of `hodgeMatrix` states its relation to the Hodge dual of
  two-forms in words. The remark in the docstring of statement 6 on the two expressions in
  `F = η X` rests on that reading and is not a theorem of this entry.
- **The Killing form.** Statement 6 is stated with the trace form of `L` acting on Minkowski
  space. The Killing form of `L` is `2 · tr (X Y)`; this is not formalized.
- **The complexification.** The invariant bilinear forms of `ℂ ⊗_ℝ L` are not described.
  Statement 5 does not give its isomorphism on generators; it states the property that identifies
  the two factors with the two maps `½ (1 ± i H)`.
- **The centroid of `L`** (see "How the statements relate") and the simplicity of `L` (`LorentzLie.etaSkew_isSimple`) are proved in the library and are not compared; simplicity enters the compared statements only through parts (c) and (d) of statement 7.
- **Spin groups, Clifford algebras and representations** do not appear.
- **Physics.** No field, action or equation of motion is defined, and no compared statement is a
  physical claim.

## Relation to the literature

Every source below was read in the version named; where a published edition was not opened, that
is said. Section numbers of Woit's book are those of the author's draft that was read. The proofs were written before these sources were read and are not adapted from any of them.

- **S1. B. C. Hall, *An Elementary Introduction to Groups and Representations*,
  [arXiv:math-ph/0005032v1](https://arxiv.org/abs/math-ph/0005032)** (128 pp.), read in the arXiv
  PDF. Definition 3.13 (p. 36) defines the Lie algebra of a matrix Lie group `G` as the set of
  matrices `X` with `e^{tX}` in `G` for all real `t`, and the text after it (p. 37) says that
  `e^X` in `G` alone is not enough. Chapter 3, §5.6 (p. 38) shows for the generalized orthogonal
  group `O(n; k)` with its diagonal matrix `g` that `e^{tX}` is in `O(n; k)` for all real `t`
  exactly when `g X^{tr} g = -X`, and says that `SO(n; k)` and its identity component have the
  same Lie algebra `so(n; k)`; the sentence on the identity component is stated without proof in
  that passage. Exercise 5 of that chapter (p. 51) asks for a matrix Lie group `G` and a matrix
  `X` with `e^X` in `G` and `X` not in its Lie algebra; Exercise 7 asks for the general matrix of
  `so(3; 1)`. The isomorphism of `so(3; 1)` with `sl(2; ℂ)` is not stated in these notes. The
  arXiv record names an expanded version published as Graduate Texts in Mathematics 222
  (Springer); that book was not opened. **Statements 3 and 9.**
- **S2. P. Woit, *Quantum Theory, Groups and Representations: An Introduction*** (Springer, 2017,
  [DOI 10.1007/978-3-319-64612-1](https://doi.org/10.1007/978-3-319-64612-1)), read in the
  author's revised and expanded draft dated 20 October 2025 (580 pp.,
  `math.columbia.edu/~woit/QM/qmbook.pdf`); the Springer printing was not opened. §40.2
  (pp. 429–430): the Lorentz group has dimension six; generators `l_j`, `k_j` with their brackets
  (40.1), (40.2); the complex combinations `A_j = ½ (l_j + i k_j)`, `B_j = ½ (l_j - i k_j)` give
  `so(3, 1) ⊗ ℂ = sl(2, ℂ) ⊕ sl(2, ℂ)`. §40.4 (pp. 431–434): `Spin(3, 1)` is identified with
  `SL(2, ℂ)`, which is said to have the same Lie algebra as `SO(3, 1)`; the action (40.4) of
  `SL(2, ℂ)` on Hermitian matrices; `Spin(4) = SU(2) × SU(2)` and `Spin(2, 2) = SL(2, ℝ) × SL(2, ℝ)`
  for the groups. §21.2 (p. 241): `so(4) = su(2) × su(2) = so(3) × so(3)`. Problem 2 of
  section B.18 (p. 553) poses `so(4, ℂ) = sl(2, ℂ) ⊕ sl(2, ℂ)` and its real subalgebras as a
  problem. **Statements 1, 2, 5 and 7(a).**
- **S3. D. K. Wise, "MacDowell–Mansouri gravity and Cartan geometry", Class. Quantum Grav. 27
  (2010) 155010, [DOI 10.1088/0264-9381/27/15/155010](https://doi.org/10.1088/0264-9381/27/15/155010)**,
  read as arXiv:gr-qc/0611154v2. The Appendix (pp. 32–33 of the arXiv version) prints the
  matrix of the Hodge operator on `so(3, 1)` in the fundamental representation and states
  `⋆⋆X = -X` and `⋆[X, X'] = [X, ⋆X']`, with `⋆⋆ = +1` in the `so(4)` case. `hodgeMatrix` is that
  printed matrix with the time index moved from the beginning to the end (compared by an exact
  script on integer coefficients). **Statement 4**, without its clause on multiplication by `-i`.
- **S4. H. Sahlmann and R. Seeger, "Revisiting loop quantum gravity with selfdual variables:
  classical theory", Class. Quantum Grav. 41 (2024) 075010,
  [DOI 10.1088/1361-6382/ad2cec](https://doi.org/10.1088/1361-6382/ad2cec)**, read as
  arXiv:2310.19729. §2.2.1 (pp. 5–8): in signature `(-+++)` the Hodge operator squares to `-1`;
  the projectors `(1 ∓ i⋆)/2` (7); the decomposition of the complexified algebra into self-dual
  and anti-self-dual parts (18); the bracket splits (26), (27), and the projectors are Lie
  algebra homomorphisms; the Cartan–Killing metric as twice a trace (35). **Statement 5**, and
  `⋆⋆ = -1` of statement 4.
- **S5. K. Krasnov, "Plebański formulation of general relativity: a practical introduction",
  Gen. Relativ. Gravit. 43 (2011) 1–15,
  [DOI 10.1007/s10714-010-1061-x](https://doi.org/10.1007/s10714-010-1061-x)**, read as
  arXiv:0904.0423v2 (p. 4, equations (1), (4), (5)): the Hodge dual on bivectors, its square
  `-1`, self-dual and anti-self-dual bivectors and their projectors. Background for statements 4
  and 5.
- **S6. G. Ólafsson and R. Quiroga-Barranco, "On low-dimensional manifolds with isometric
  SO₀(p, q)-actions", Transform. Groups 17 (2012) 835–860,
  [DOI 10.1007/s00031-012-9194-5](https://doi.org/10.1007/s00031-012-9194-5)**, read as
  arXiv:1003.0704v2. Remark A.10 (p. 21 of the arXiv version): the invariant bilinear forms on
  `so(2, 2) ≃ so(2, 1) × so(2, 1)` are the combinations of the Killing forms of the factors; for
  the realification of a simple complex Lie algebra with Killing form `K` and complex structure
  `J`, the form `K(X, J Y)` is invariant and is not a multiple of `K`, and by Schur's lemma the
  invariant bilinear forms are the combinations `a K + b K(·, J ·)`. **Statement 6**, and
  statement 7(b) in the form `so(2, 1) × so(2, 1)`.
- **S7. K. Francis-Staite and T. Leistner, "Conformal properties of indefinite bi-invariant
  metrics", Transform. Groups 26 (2021) 859–892,
  [DOI 10.1007/s00031-020-09561-9](https://doi.org/10.1007/s00031-020-09561-9)**, read as
  arXiv:1901.04682v2. Proposition 4.1 (pp. 11–12 of the arXiv version): for a real simple Lie
  algebra, either its complexification is simple and the invariant symmetric bilinear forms are
  the multiples of the Killing form, or it is a complex simple Lie algebra regarded as real and
  they form a plane spanned by the real and the imaginary part of the complex Killing form. The
  sentence after the proposition adds that simple Lie algebras admit no invariant skew-symmetric
  bilinear form. The four references that sentence cites were not read. **Statement 6**, for
  symmetric forms.
- **S8. D. Tong, lecture notes (University of Cambridge)**: *Electromagnetism* (Lent 2015),
  p. 113, equation (5.25), and p. 127; *Gauge Theory* (2018), §1.2, p. 10, equation (1.11). The
  two Lorentz-invariant quadratic expressions in a field strength and its dual, and the names
  kinetic (Maxwell) term and theta term. Source of the naming remark in the docstring of
  statement 6 only.
- **S9. Physics 251, Problem Set 4, Spring 2026** (University of California, Santa Cruz; 4 pp.,
  `scipp-legacy.pbsci.ucsc.edu/~haber/ph251/groups26_4.pdf`; the file does not name its author).
  Problem 1 asks in part (a) to work out `so(4)` and verify `so(4) ≅ so(3) ⊕ so(3)`, and in part
  (e) to show `so(3, 1) ≅ sl(2, ℂ)_ℝ`, the realification of `sl(2, ℂ)`. **Statements 1 and 7(a)**, posed as exercises, and statement 5 without its projections, in the form `so(4, ℂ) ≅ so(3, ℂ) ⊕ so(3, ℂ)` with `so(3, ℂ) ≅ sl(2, ℂ)` (parts (d) and (e) and the remark); background.

How the statements follow where the printed sentence is not the statement:

- **The formula of statements 1 and 2.** No source that was opened prints the map
  `X ↦ -½ Σ_k (β_k + i θ_k) σ_k`. It is the derivative of Woit's action (40.4) of `SL(2, ℂ)` on
  Hermitian matrices, with the opposite sign for the boosts: differentiating (40.4) sends a boost
  to `+½ σ` and a rotation to `-(i/2) σ` (a computation made for this entry, not a printed
  sentence), and this entry sends a boost to `-½ σ_k`. The two isomorphisms differ by the automorphism `X ↦ −X*` of `sl(2, ℂ)` over `ℝ`, which is conjugate-linear; with Woit's sign `H` would be multiplication by `i` (a computation made for this entry, not formalized).
- **Statement 3.** Hall's statement is for `O(n; k)`; `ProperLorentz` adds determinant `1` and the
  forward cone. In the statement here these two clauses are conclusions in the direction from
  the algebra to the group, and are not used in the other direction.
- **Statement 6.** The sources state the result with the Killing form; here it is written with
  the trace form of the action on Minkowski space, which is half the Killing form (compare S4,
  equation (35)). That step is not formalized. Uniqueness of the pair `(a, b)` is the remark
  in S6 that the second form is not a multiple of the Killing form.
- **Statement 8** was not located in a source; it holds by a count of dimensions (the bilinear forms on `L` have dimension 36 and the forms of statement 6 are a plane). **Statement 9**: the exercise is Hall's, the example is this entry's.

Besides the formula of statements 1 and 2 (the bullet above), three things were not found printed in the sources read:

1. the clause of statement 4 that the isomorphism of statement 2 carries `H` to multiplication by
   `-i` (it follows from the values on the six generators in statements 2(c) and 4(b), by
   linearity);
2. part (b) of statement 7 with `sl(2, ℝ)` in place of `so(2, 1)` (S6 has
   `so(2, 2) ≃ so(2, 1) × so(2, 1)` and S2 has `Spin(2, 2) = SL(2, ℝ) × SL(2, ℝ)` for the groups;
   the classical isomorphism of `so(2, 1)` with `sl(2, ℝ)` is not in the pages read);
3. parts (c) and (d) of statement 7 (`sl(2, ℂ)` is simple as a real Lie algebra, case (2) of the
   proposition in S7, and the two other algebras are products).

Not opened: the Springer editions of S1 and S2; the references [1], [8], [21], [23] of S7 (among
them Milnor 1976 and Medina 1985); Sexl and Urbantke; Penrose and Rindler; Landau and Lifshitz;
Wald; Knapp; Helgason; Jackson; Lawson and Michelsohn; Kirillov. Opened and not used:
F. Klinker, Int. Electron. J. Geom. 8 (2015) 94–104 (arXiv:1712.02168), which gives formulas for
the groups and prints no map of Lie algebras.

## Prior formalization

This section reports a search made on 2026-11-13 (the heads of the repositories were re-read
that day at 14:08 UTC). "Not found" below means not found in the places and at the commits
listed under "Where the search looked"; the limits of the search are listed after that. Nothing
from the libraries named here was compiled for this entry, and nothing of them is imported or
reproduced, except Mathlib (the dependency) and the carried copies.

### By statement

| # | Nearest prior formalization | Relation |
|---|---|---|
| 1 | TauCeti `realSpinThreeOneEquivSpecialLinear`, `Matrix.SpecialLinearGroup.lieAlgebraLieEquiv`, the Lie algebra of the Spin groups, `soEquivQuadratic`; physlib `toRestrictedLorentzGroup_surjective`, `toLorentzGroup_eq_one_iff`; TauCeti `suTwoLieEquivSoThree`; Mathlib `soIndefiniteEquiv` (needs `i * i = -1`, so not over `ℝ`) | The counterpart for groups, in two places. Every ingredient is in one library (TauCeti), not found combined there. The compact subalgebra. The isomorphism of Lie algebras: not found. |
| 2 | As 1; physlib `boostGenerator_mem`, `rotationGenerator_mem` (the basis property is marked as not yet proved there); the Yang–Mills release `tangent_parts`, `boost_bracket` | Ingredients on other carriers. The dimension `6` as a `finrank`: not found. |
| 3 | TauCeti `forall_exp_smul_mem_unitary_iff_mem_skewAdjoint`; `forall_exp_smul_mem_specialOrthogonalGroup_iff_mem_so` (and `O(n)`, `SL`, `SU`, `Sp`); `forall_expUnit_smul_mem_realCliffordSpinGroup_iff_mem_quadraticLieSubalgebra`; physlib `exp_mem_restricted_lorentzGroup`; OSreconstruction `exp_isLorentz`, `exp_det_one`, `exp_orthochronous`; as definitions: TauCeti `mem_lieSubalgebraOfSubgroup`, physlib `lieAlgebraOfIsClosed`, the Yang–Mills release `GaugeGroup.generates` | A general theorem with both directions; no instance at an indefinite form was found. The same criterion on definite and symplectic matrix groups. A counterpart on the Spin group. One direction on two carriers of Lorentz matrices. The criterion as a definition, in three places. Both directions for the Lorentz group or another indefinite orthogonal group of linear maps: not found. |
| 4 | `openai/math` `hodgeStarFour`, `hodgeStarFour_quaternion`, `hodgeStarFour_opposite`; TauCeti `bivectorExterior_hodgeStar`, `hodgeStar_hodgeStar`; Mathlib `exteriorPower.hodgeStar` (its square is left as a to-do note there) | The operator in definite signature; a general construction. The Lorentzian operator on the Lie algebra: not found outside the author's repositories. |
| 5 | TauCeti `skewAdjointMatricesLieSubalgebraBaseChangeEquiv` (`Algebra/Lie/SkewAdjoint/BaseChange.lean:162`), `specialOrthogonalBaseChangeLieEquiv` (`Geometry/Lie/Subgroup/Complexification.lean:272`), `specialUnitaryComplexificationLieEquiv`; TauCeti `Spin/LowRank/HyperbolicFour.lean` (the Spin group of the hyperbolic four-space is `SL₂(K) × SL₂(K)`); `realSpinFourEquivSpecialUnitaryProd` | A general theorem for the first step: extension of scalars carries the skew-adjoint matrices of a Gram matrix `J` to those of `J` over the larger ring; no instance at the Minkowski form was found. The complexifications of `so(n)` and `su(n)`. A counterpart for groups over a field. The splitting into `sl(2, ℂ) × sl(2, ℂ)` with its projections: not found. |
| 6 | TauCeti `exists_eq_smul_killingForm`, `isSymm_of_lieInvariant`, `finrank_invariantForms_pi_eq_card`; physlib `Lorentz.RankFour.exists_eq_sum`, `span_range_contractionTensor_of_antisymm`, and its use `lorentzContractionEightSpan_eq`; Mathlib `traceForm_lieInvariant` | A general theorem under another hypothesis (an algebraically closed field). The same classical fact as group-invariant complex coefficient tensors, where independence is not proved. A use of it on two field strengths. An ingredient of one direction. Over `ℝ`, on the Lie algebra, with uniqueness: not found. |
| 7 | TauCeti `realSpinFourEquivSpecialUnitaryProd`, `realSpinTwoTwoEquivSpecialLinearProd`, `hasTrivialRadical_so'` (`Algebra/Lie/Orthogonal/Killing.lean:230`) and a docstring (`:38-39`); `openai/math` `hodgeStarFour_quaternion`, `hodgeStarFour_opposite`, `oppositeMatrix_commute` | Counterparts for groups of (a) and (b); the semisimplicity of `so(p, q)` on Mathlib's `so'` (`hasTrivialRadical_so'`), in a file that says simplicity is not asserted there and fails for `so(2, 2)`; an ingredient. The equivalences of Lie algebras and the two non-isomorphisms: not found. |
| 8 | — | No neighbour recorded; the statement holds by a count of dimensions. |
| 9 | — | Not found. |

Three remarks on this table.

- **Statement 3.** TauCeti's general theorem is for the unitary group of a complete normed real
  algebra with a continuous involution. By a reading that was not compiled (the Minkowski adjoint
  `A ↦ η Aᵀ η` as the involution of the algebra of endomorphisms), the part of statement 3 on the
  preservation of the form is a case of that theorem; the determinant and cone clauses, and the
  statement on the carried type `ProperLorentz`, are what this entry states beyond it.
- **Statements 1 and 2.** One of the four TauCeti ingredients, the Lie algebra of `SL(n, 𝕜)` as
  `sl(n, 𝕜)` with scalars restricted to `ℝ`, is in TauCeti at the head commit read and not at the
  earlier commit `3602eb5f` that was also read.
- **Statement 6.** physlib's file on the invariants with four indices says in its header that
  independence is not proved there. Its use in the Standard Model files is a spanning statement
  for the metric contraction and the alternating contraction of two field strengths.

### Declarations, by place (file and line at the commit named)

**Mathlib**, the pin of this entry,
[`065356127b1dc0016f66b7283ce0ce2c4055aa55`](https://github.com/leanprover-community/mathlib4/tree/065356127b1dc0016f66b7283ce0ce2c4055aa55).
`Mathlib/Algebra/Lie/Classical.lean`: `sl` (`:94`), `so` (`:168`), `so'` (`:182`),
`soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (p ⊕ q) R` (`:226`),
`typeDEquivSo'` (`:292`), `typeBEquivSo'` (`:375`); a search of the tree for the notation `≃ₗ⁅` with `sl` or `so'` returned these three only. `Mathlib/Algebra/Lie/SkewAdjoint.lean`: `skewAdjointLieSubalgebra`
(`:60`), `skewAdjointMatricesLieSubalgebra` (`:114`). `Mathlib/Algebra/Lie/TraceForm.lean`:
`traceForm` (`:54`), `traceForm_comm` (`:61`), `traceForm_lieInvariant` (`:94`);
`Mathlib/Algebra/Lie/InvariantForm.lean:54`; no uniqueness statement for invariant forms in
either file. `Mathlib/Analysis/Normed/Algebra/Exponential.lean:539`,
`exp_mem_unitary_of_mem_skewAdjoint` (one direction, in a star algebra).
`Mathlib/Geometry/Manifold/GroupLieAlgebra.lean:56`. `Mathlib/Algebra/Lie/Sl2.lean:41`.
`Mathlib/LinearAlgebra/ExteriorPower/HodgeStar.lean:48` (the square of the operator is a to-do note,
`:20-27`). No hit at the pin for: a statement of the form `∀ t : ℝ, … exp (t • …)`; a `finrank`
of `so`, `sl` or a skew-adjoint algebra; a uniqueness statement for invariant forms; a file named
for Lorentz or Minkowski space. Mathlib master `7bcc5e95ffc0d80d94adc6f17715f224d59d209b` was
read by file names and in three files.

**physlib**,
[`adccea9195c7c347a5f8cde1ddf6874f89ea6a9a`](https://github.com/leanprover-community/physlib/tree/adccea9195c7c347a5f8cde1ddf6874f89ea6a9a)
(Lean 4.35.0). Under `Physlib/Relativity/`: `LorentzAlgebra/Basic.lean:29-30` (`lorentzAlgebra`
is `so' (Fin 1) (Fin 3) ℝ`); `LorentzAlgebra/Basis.lean:82`, `:106`, `:122`, `:129` (the
generators and their membership; `:26`, `:39` on the basis property);
`LorentzAlgebra/ExponentialMap.lean:70` `exp_mem_lorentzGroup`, `:131` `exp_isProper`, `:141`
`exp_isOrthochronous`, `:175` `exp_mem_restricted_lorentzGroup` (no converse was found);
`SL2C/Basic.lean:169` `toLorentzGroup`, `:273` `toLorentzGroup_eq_one_iff`, `:338`
`toRestrictedLorentzGroup`; `SL2C/Cover.lean:139` `toRestrictedLorentzGroup_surjective`;
`LorentzGroup/Restricted/Basic.lean:62` (connectedness of the restricted group is recorded there
as a semiformal result).
`PhyslibAlpha/Mathematics/ForMathlib/Analysis/Normed/Algebra/MatrixLieAlgebra.lean:117-119`
`lieAlgebraOfIsClosed`, `:132`, `:163` (added by commit `c1c822b8ee`, 2026-11-12; it cites Hall's
book). `PhyslibAlpha/Relativity/LorentzGroup/Invariants/RankFour.lean:28`, `:119`, `:309`, `:771`,
`:814` (one commit, `1a7d73188a`, 2026-10-19) and `PhyslibAlpha/Relativity/LorentzGroup/Invariants/Basic.lean:140-141`.
`PhyslibAlpha/Particles/StandardModel/IsGaugeSector/MassWeight/MassDimEight.lean:1204`;
`PhyslibAlpha/Particles/StandardModel/CovRealization/MassWeight/Invariants.lean:26-41`;
`PhyslibAlpha/Particles/QED/Lagrangian.lean:124-125`.
`Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Contractions.lean:298-299`.
`Physlib/Electromagnetism/Dynamics/KineticTerm.lean:87`, `:100`. No hit for: a Lie equivalence
out of `lorentzAlgebra` (the hits for a Lie equivalence are all on `sl₂`-modules); a
`finrank` in `Relativity` other than for the Clifford algebra; `so(4)` or `so(2,2)`; a dual field
strength; `sl` as a Lie algebra.

**TauCeti**,
[`da527980caecf7e72838e069c01f4a7e7633eca3`](https://github.com/TauCetiProject/TauCeti/tree/da527980caecf7e72838e069c01f4a7e7633eca3)
(Lean 4.36.0-rc2). Under `TauCeti/`:
`Topology/Algebra/CliffordAlgebra/Spin/LieAlgebra.lean:95-99` (the Spin group of every real
signature; the same file at `1e668f5e` and `3602eb5f`);
`Geometry/Lie/Subgroup/LieAlgebra.lean:369-371` `mem_lieSubalgebraOfSubgroup`;
`Geometry/Lie/Exponential/Unitary.lean:74`;
`Geometry/Lie/Exponential/Matrix/SpecialOrthogonal.lean:96`, `:107`;
`Geometry/Lie/Exponential/Matrix/Symplectic.lean:80`;
`Geometry/Lie/Exponential/Matrix/SpecialUnitary.lean:77`;
`Geometry/Lie/Subgroup/SpecialLinear.lean:85`; `Geometry/Lie/SpecialLinear.lean:136`;
`LinearAlgebra/CliffordAlgebra/Spin/Real/ThreeOne.lean:79`, `:264`;
`LinearAlgebra/CliffordAlgebra/Spin/Real/Four.lean:383`;
`LinearAlgebra/CliffordAlgebra/Spin/Real/TwoTwo.lean:99`;
`LinearAlgebra/CliffordAlgebra/Spin/Real/TwoOne.lean:86`;
`LinearAlgebra/CliffordAlgebra/Spin/LowRank/HyperbolicFour.lean` (header);
`LinearAlgebra/CliffordAlgebra/RealForm/ThreeOne.lean:295`;
`RepresentationTheory/SU2/StandardBasis.lean:204` `suTwoLieEquivSoThree`;
`Algebra/Lie/SkewAdjoint/BaseChange.lean:162`;
`Geometry/Lie/Subgroup/Complexification.lean:193-196`, `:272`;
`Algebra/Lie/Killing/InvariantForm.lean:55-56`, `:62-63`, `:71`, `:90`, `:105`;
`Algebra/Lie/InvariantForm/Basic.lean:191`; `Algebra/Lie/Orthogonal/Killing.lean:219` `isIrreducible_so'_standard`, `:230` `hasTrivialRadical_so'` (for `p + q ≥ 3`; over `ℝ`, the semisimplicity of `so(p, q)`), `:38-39` (simplicity is not asserted there); `LinearAlgebra/CliffordAlgebra/Chirality.lean:304`;
`Analysis/InnerProductSpace/HodgeStar/Basic.lean:217`;
`LinearAlgebra/CliffordAlgebra/Quadratic/Realization.lean:164-165`, `:187-190`;
`LinearAlgebra/CliffordAlgebra/StandardBivector.lean:401-403`, `:415-419`;
`Geometry/Lie/CliffordAlgebra/Spin/Differential.lean` (header). No hit for: a Lie equivalence
over `ℝ` onto `sl (Fin 2) ℂ` from an orthogonal algebra (22 Lie equivalences over `ℝ` were
listed); a file named for Lorentz, Minkowski, an indefinite form or a centroid in a Lie folder;
an instance of the exponential criterion at an indefinite form in `TauCeti/Geometry/Lie`. The
word Lorentz occurs in six files (four on `Spin(3, 1)` and the Dirac algebra, two on the
hyperboloid).

**OSreconstruction**,
[`cf0904e34a7c146a9f312f601e3707dca4a87697`](https://github.com/xiyin137/OSreconstruction/blob/cf0904e34a7c146a9f312f601e3707dca4a87697/os-reconstruction/OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean).
`os-reconstruction/OSReconstruction/ComplexLieGroups/LorentzLieGroup.lean:211`
`IsInLorentzAlgebra` (a predicate on matrices, signature `(-,+,…,+)`, every dimension), `:221`
`exp_isLorentz`, `:250` `exp_det_one`, `:306` `exp_orthochronous`, `:334` `expLorentz`, `:1686`
(path-connectedness of the restricted group). No converse was found: the predicate occurs as a
conclusion only for the real and imaginary parts of a complex element
(`os-reconstruction/OSReconstruction/ComplexLieGroups/Connectedness/ComplexInvariance/Core.lean:112`, `:142`); `os-reconstruction/OSReconstruction/ComplexLieGroups/Complexification.lean:424` defines the
complex predicate.

**`openai/math`**,
[`4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean).
`lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean:9807-9814` `hodgeStarFour` (the Hodge
operator on two-forms of Euclidean four-space, as a linear map on `4 × 4` matrices), `:9835`
`hodgeStarFour_quaternion`, `:9840` `hodgeStarFour_opposite`, `:10972`, `:10977`;
`lean/OAI/Geometry/EinsteinFour/AngularClifford.lean:66` `oppositeMatrix_commute`. `hodgeMatrix` here has the same shape with
the three signs in the last column changed; the last rows are identical. No lemma on the square
of `hodgeStarFour` or on brackets was found there, and no Lie-algebra statement. This file was
opened on 2026-11-13, after the statements of this entry were fixed.

**The Yang–Mills release**,
[`3456e5e75cf8d4cd558955a5c7638fba2d68f464`](https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e75cf8d4cd558955a5c7638fba2d68f464).
`PublicTheory.lean:22-33` (the gauge group with its Lie algebra, defined by the criterion of
statement 3), `:208-212`, `:214-215`, `:286`, `:300`; `YM/Gauge/Lie.lean:26`, `:42`, `:114`,
`:126`, `:159`; `YM/Next/BOUNDARY/Derived.lean:21` (`tangent`), `:23`, `:25`, `:43`
(`tangent_parts`), `:154`, `:160` (`boost_bracket`); `YM/Space/Orthogonal.lean:131-132`, `:146`
(one-parameter groups of rotations of Euclidean four-space, one direction). Read on
2026-11-11 and 2026-11-13 at that commit: `ProperLorentz` occurs in `PublicTheory.lean` only
(lines 209, 215, and through `PoincareCoordinates` line 235); no `LieSubalgebra`, `LieAlgebra`
or `LieRing` occurs in the repository; the infinitesimal Lorentz elements used internally are
the predicate `tangent` (`YM/Next/BOUNDARY/Derived.lean:21`), and no declaration relating it to
exponentials was found.

**The monograph project**
[`hairer/humanise-yang-mills`](https://github.com/hairer/humanise-yang-mills/tree/ba4528fdd98ed0735d498c0ec26e28c8093811f6)
(commit `ba4528fdd98ed0735d498c0ec26e28c8093811f6`; its `README.md` and `blueprint/outline.md`
were the same files at `16b070a9f5ebf4c83c210d8ccffba3be2c711c48` on 2026-11-13). Its README
(lines 3–9) describes a crowd-sourced effort to turn that release into a human-readable proof,
a research monograph in which existing mathematical results are to be found and cited where
applicable, and it pins its source to revision `3456e5e75cf8d4cd558955a5c7638fba2d68f464`
(lines 11–12), the commit the copies here are carried from. Its outline lists the lattice,
symmetry and gauge-group setup and the Wightman reconstruction among its source clusters
(`blueprint/outline.md:83`, `:87`) and calls itself a planning document (`:7-8`).

**atlas-lean** ([`facebookresearch/atlas-lean`](https://github.com/facebookresearch/atlas-lean/tree/f83e3b9054234d1c0f6455272c774f4559b44522)), commit `f83e3b9054234d1c0f6455272c774f4559b44522` (a local copy of 2026-11-11; the
head, which moved during the search, was read by file names only).
`v1/Atlas/LieGroups/code/SL2CRepresentations.lean` (with two `sorry`); a predicate
`IsLorentzTransformation` on matrices in a file `v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM12/MinkowskiVectors.lean` (`:56`);
`WantedExt/Geometry/MostowRigidityWanted.lean`. No hit for a Lie equivalence with `so` or `sl`,
for a Lorentz Lie algebra, or for the exponential criterion in a Lie file.

**Other proof assistants.** Web searches only. They returned no formalization of
`so(3, 1) ≅ sl(2, ℂ)`, of a Lorentz Lie algebra, or of the Lorentz case of the exponential
criterion in Isabelle, Coq/Rocq, HOL Light or Metamath. The Archive of Formal Proofs has an
entry "Lie Groups and Algebras" (2024), which constructs the Lie algebra of a Lie group; the
content of its theory `Classical_Groups` was not read.

### Where the search looked

| Place | Commit | How |
|---|---|---|
| Mathlib (the pin) | `06535612` | whole tree (`Mathlib`, `Archive`, `Counterexamples`), by content |
| Mathlib master | `7bcc5e95` | file names; three files by content |
| physlib | `adccea91` | whole tree (1,629 files), by content |
| TauCeti | `da527980` | all 31,993 file names; 2,135 files by content (the folders for Lie algebras, Clifford algebras, Lie groups, the Hodge operator, quadratic forms, hyperbolic geometry, `SU(2)`, the special orthogonal group, examples); the whole tree by content at the earlier commit `3602eb5f` |
| OSreconstruction | `cf0904e3` | 42 files (`ComplexLieGroups/`, `Wightman/Groups/`, `Wightman/Spacetime/`), README |
| `openai/math` | `4eaee875` | file names; 3,384 files by content (`Geometry/EinsteinFour`, `Geometry/Relativity` and other named folders and files) |
| the Yang–Mills release | `3456e5e7` | whole tree, by content |
| atlas-lean | `f83e3b90` | whole tree by content at that commit; the head by file names |
| Isabelle AFP, Coq/Rocq, HOL Light, Metamath | — | web searches |

### Limits of the search

- Nothing was compiled against these libraries. Declarations are quoted from source text, and
  the reading of TauCeti's general theorem for statement 3 is mathematics, not a compiled
  instance.
- TauCeti at its head: content was read in 2,135 of 31,993 files, the rest by file name; the
  whole tree by content only at `3602eb5f`. A relevant file added later, outside the folders
  read and under a name the patterns miss, would not have been seen.
- `openai/math`: 3,384 files by content, names for the rest. OSreconstruction: 42 files.
  atlas-lean: the head by file names only.
- Other proof assistants: web searches only; no source of the Archive of Formal Proofs, Coq/Rocq,
  HOL Light or Metamath was read.
- These repositories change quickly (the head of TauCeti was 1,569 commits after the earlier
  commit `3602eb5f`). The search is of its date.

### The author's related entries and repositories

- [`stalex444/one-complex-place-lorentz-group-galois-boost`](https://github.com/stalex444/one-complex-place-lorentz-group-galois-boost/tree/ec70bded79e51b31f907b085f71756a79df0fe33)
  (not a registered entry on 2026-11-13): seven modules of its library `ArithmeticLorentz` are a
  Solution-side
  dependency here (see "Files"). Its statements on the Hodge images of generators are not
  compared here.
- PALOMAR-2026-09-30-000024 (`stalex444/pdt-hodge-lie-generation`, commit
  `e2d8dde6f076b730b9a718c95ff1664c6aa88b51`): the module `GravityScreening/SignedLieGeneration.lean` of this entry is an unchanged copy of the file of the same name at that commit (git blob id compared; the same blob is in `stalex444/pdt-em-source-selection`, see "Files"). Its compared statement is a different
  theorem on the same family of operators.
- PALOMAR-2026-11-12-000002
  ([`stalex444/conformal-killing-flat`](https://github.com/stalex444/conformal-killing-flat/tree/ef2fbb3488aef70b5e2fbd933c7e01cae6679e48)):
  its cited application names the dimension `10` of the infinitesimal isometries of Minkowski
  space; statement 2(a) here is the count `6` of their linear part, as a compared `finrank`. No
  statement in common.
- A separate entry in preparation (no identifier yet) compares the centroid of the orthogonal Lie algebra of a quaternary form; see "How the statements relate".

## Files

- `Challenge.lean` — the nine statements, with the carried block and the entry's definitions;
  imports Mathlib only.
- `Solution.lean` — the nine proofs. It repeats the entry's definitions verbatim and does not
  repeat the carried block, which reaches it through the import of `ReleaseAdapter/Carried.lean`
  (the same text). `BUILD.txt` records that the Comparator accepts this layout.
- `comparator.json` — the nine names, in order.
- `LorentzLie.lean`, `LorentzLie/` (`Defs`, `Centroid`, `RealForms`, `Complexification`,
  `Landings`, `Controls`, `NumberField`, `FormCentroid`) and `ReleaseAdapter.lean`,
  `ReleaseAdapter/` (`Carried`, `Landing`, `CentroidDefs`, `Centroid`) — the proof library of
  this entry. Their docstrings carry the working labels of the development (L1–L8, D0, D1, D5, A1–A6, T1–T5).
- `ArithmeticLorentz/` (`Defs`, `Counting`, `Arithmetic`, `Qubit`, `PlaceLink`, `Boost`,
  `RegisterBridge`) — seven modules of the author's earlier library, copied unchanged from
  [`stalex444/one-complex-place-lorentz-group-galois-boost`](https://github.com/stalex444/one-complex-place-lorentz-group-galois-boost/tree/ec70bded79e51b31f907b085f71756a79df0fe33)
  at commit `ec70bded79e51b31f907b085f71756a79df0fe33`. They are the modules of that library in
  the import closure of `Solution.lean`; its two other files are not included. Their docstrings
  describe the subject of that repository and use its working labels. This entry uses their
  definitions and lemmas on the skew matrices of a diagonal form, on the Hodge operator on those
  matrices and on the place space of a number field.
- `GravityScreening/SignedLieGeneration.lean` — copied unchanged from
  [`stalex444/pdt-em-source-selection`](https://github.com/stalex444/pdt-em-source-selection/tree/1c9ba637b5e664a88b6487d463515587616476e1)
  at commit `1c9ba637b5e664a88b6487d463515587616476e1`.
- `Axioms.lean` — `#print axioms` for the nine compared statements and for library declarations.
- `formalization.yaml` — metadata. `BUILD.txt` — the build record. `SHA256SUMS` — hashes.
- `LICENSE`, `NOTICE` — see "Licence".
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` — Lean `v4.35.0-rc2`, Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Build

```
lake exe cache get        # Mathlib's prebuilt files
lake build                # the libraries, Challenge and Solution
lake env lean Axioms.lean
lake comparator           # needs bubblewrap; see BUILD.txt for the local run
```

`BUILD.txt` records the commands that were run, their exit codes and job counts, and what was not
run.

## Production and review

- **AI assistance.** The library, the statements, the proofs and this documentation were
  developed with Anthropic Claude, in Claude Code, under the author's direction. The author
  decided the scope, the cut between this entry and the separate entry on bracket-commuting
  maps, the dependencies and the licence.
- **Statement review.** The nine statements were written in an AI-assisted statement stage (each
  with a plain reading and a bridging proof) and then reviewed by separate AI sessions, among
  them a hypothesis-deleting review with compiled probe files and an exact check script. That
  review found one blocking difference between `Challenge.lean` and `Solution.lean` (the
  definition `spinOf`), which was corrected, and gave replacement texts that were applied.
- **Literature and prior formalization.** The search reported above was made by an AI session
  and then checked by a separate AI session, which re-opened every declaration and every source
  and corrected five omissions, each in the direction of more prior work.
- **Builds.** All builds, the Comparator run (without its sandbox, which is not available on
  macOS), the axiom printout, the structural-hash comparison of the statements and the count
  check were run on the author's machine; `BUILD.txt` records them and what was not run.
- **The author's review.** The author's own review of the nine statements against their
  informal descriptions is hers to record and is **not yet recorded** in this file or in
  `formalization.yaml`.
- Not peer-reviewed.

## Licence

Apache License, Version 2.0 (`LICENSE`). `NOTICE` reproduces the NOTICE file carried from the
Yang–Mills release at the commit above and records what is carried from it. The files under
`ArithmeticLorentz/` and `GravityScreening/` are published in the author's two repositories named
under "Files" under the MIT License; `NOTICE` states that they are distributed here by their
author under the Apache License, Version 2.0.
