module
public import Mathlib
public import LorentzLie.Defs
public import LorentzLie.RealForms
public import LorentzLie.Centroid

@[expose] public section

/-!
# The `η`-skew `4 × 4` matrices over `ℂ`

For a diagonal `η : Fin 4 → ℝ` with entries `±1`, read over `ℂ` (`etaC η`):

* `etaSkewCEquiv` — a Lie algebra equivalence over `ℂ` from `etaSkew (etaC η)` to
  `sl(2, ℂ) × sl(2, ℂ)`, with `etaSkewCEquiv_gen` on generators;
* `etaSkewCEquiv_hodgeProj` — the two projectors `hodgeProjMinus η`, `hodgeProjPlus η` of the
  Hodge operator correspond to the two factors;
* `centroid_complex` — every bracket-commuting `ℂ`-linear endomorphism of `etaSkew (etaC η)` is
  uniquely `a • hodgeProjPlus η + b • hodgeProjMinus η`;
* `tensorEtaSkewEquiv` — the same equivalence on the base change `ℂ ⊗[ℝ] etaSkew η`, with
  `tensorEtaSkewEquiv_tmul_gen`.

Method. With `D = diagonal (lam (η i))` (so `D * D = diagonal (etaC η)`), `X ↦ D * X * D⁻¹` carries
the `etaC η`-skew matrices to the antisymmetric ones and preserves commutators; an antisymmetric
`4 × 4` matrix `S` has the two trace-zero `2 × 2` matrices `sdPlus S`, `sdMinus S`, and the bracket
identity for these is a polynomial identity with no case split. The helper declarations are in
the namespace `LorentzLie.Complexification`.
-/

set_option autoImplicit false

attribute [local instance] LieRing.ofAssociativeRing

namespace LorentzLie

open Matrix
open scoped TensorProduct

namespace Complexification

/-! ### Scalars -/

section Scalars

/-- An entry `±1`, read in `ℂ`, has square `1`. -/
theorem etaC_mul_self {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (i : Fin 4) :
    (η i : ℂ) * (η i : ℂ) = 1 := by
  rcases hη i with h | h <;> rw [h] <;> norm_num

/-- `lam (η i) * lam (η i) = η i` for an entry `±1`. -/
theorem lam_mul_self {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (i : Fin 4) :
    lam (η i) * lam (η i) = (η i : ℂ) := by
  rw [← pow_two]
  exact lam_sq (η i) (hη i)

/-- `lam (η i) ^ 4 = 1` for an entry `±1`. -/
theorem lam_pow_four {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (i : Fin 4) :
    lam (η i) ^ 4 = 1 := by
  have h1 := lam_mul_self hη i
  have h2 := etaC_mul_self hη i
  linear_combination (lam (η i) * lam (η i) + (η i : ℂ)) * h1 + h2

end Scalars

/-! ### Trace-zero complex `2 × 2` matrices in the basis `eₖ = -½ quat k` -/

section Pauli

/-- The trace-zero complex `2 × 2` matrix `a₁ • e₁ + a₂ • e₂ + a₃ • e₃`, where `eₖ = -½ quat k`
(`k = 1, 2, 3`) satisfy `⁅e₁, e₂⁆ = e₃` and cyclic. -/
noncomputable def pauliC (a1 a2 a3 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(Complex.I * a3) / 2, -(Complex.I * a1 + a2) / 2;
     (-(Complex.I * a1) + a2) / 2, Complex.I * a3 / 2]

/-- `pauliC` has trace zero. -/
theorem pauliC_trace (a1 a2 a3 : ℂ) : (pauliC a1 a2 a3).trace = 0 := by
  simp only [pauliC, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
  ring

/-- The commutator of two `pauliC` matrices is the `pauliC` matrix of the cross product. -/
theorem pauliC_bracket (a1 a2 a3 b1 b2 b3 : ℂ) :
    pauliC a1 a2 a3 * pauliC b1 b2 b3 - pauliC b1 b2 b3 * pauliC a1 a2 a3 =
      pauliC (a2 * b3 - a3 * b2) (a3 * b1 - a1 * b3) (a1 * b2 - a2 * b1) := by
  have hI := Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliC, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · ring
  · linear_combination ((a3 * b1 - a1 * b3) / 2) * hI
  · linear_combination ((a1 * b3 - a3 * b1) / 2) * hI
  · ring

/-- `pauliC` is additive. -/
theorem pauliC_add (a1 a2 a3 b1 b2 b3 : ℂ) :
    pauliC a1 a2 a3 + pauliC b1 b2 b3 = pauliC (a1 + b1) (a2 + b2) (a3 + b3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliC] <;> ring

/-- `pauliC` commutes with multiplication by a complex number. -/
theorem pauliC_smul (w a1 a2 a3 : ℂ) :
    w • pauliC a1 a2 a3 = pauliC (w * a1) (w * a2) (w * a3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliC] <;> ring

/-- `pauliC 0 0 0 = 0`. -/
theorem pauliC_zero : pauliC 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliC]

/-- Every trace-zero complex `2 × 2` matrix is a `pauliC` matrix. -/
theorem eq_pauliC (m : Matrix (Fin 2) (Fin 2) ℂ) (hm : m.trace = 0) :
    m = pauliC (Complex.I * (m 0 1 + m 1 0)) (m 1 0 - m 0 1) (2 * Complex.I * m 0 0) := by
  have hI := Complex.I_mul_I
  have h1 : m 0 0 + m 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using hm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliC, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (m 0 0) * hI
  · linear_combination ((m 0 1 + m 1 0) / 2) * hI
  · linear_combination ((m 0 1 + m 1 0) / 2) * hI
  · linear_combination h1 - (m 0 0) * hI

end Pauli

/-! ### Conjugation by `diagonal (lam (η i))` -/

section Conj

/-- The diagonal matrix `D` with entries `lam (η i)`; for entries `±1`,
`D * D = diagonal (etaC η)`. -/
noncomputable def dmat (η : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun i => lam (η i)

/-- The inverse of `dmat η` for entries `±1`: the diagonal matrix with entries
`η i * lam (η i)`. -/
noncomputable def dinv (η : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal fun i => (η i : ℂ) * lam (η i)

/-- `dmat η * dinv η = 1`. -/
theorem dmat_mul_dinv {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) : dmat η * dinv η = 1 := by
  rw [dmat, dinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h1 := etaC_mul_self hη i
  have h2 := lam_mul_self hη i
  linear_combination (η i : ℂ) * h2 + h1

/-- `dinv η * dmat η = 1`. -/
theorem dinv_mul_dmat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) : dinv η * dmat η = 1 := by
  rw [dmat, dinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h1 := etaC_mul_self hη i
  have h2 := lam_mul_self hη i
  linear_combination (η i : ℂ) * h2 + h1

/-- `conj η X = D * X * D⁻¹`. -/
noncomputable def conj (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  dmat η * X * dinv η

/-- The inverse conjugation `unconj η S = D⁻¹ * S * D`. -/
noncomputable def unconj (η : Fin 4 → ℝ) (S : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  dinv η * S * dmat η

/-- Entries of `conj η X`. -/
theorem conj_apply (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    conj η X a b = lam (η a) * X a b * ((η b : ℂ) * lam (η b)) := by
  rw [conj, dinv, Matrix.mul_diagonal, dmat, Matrix.diagonal_mul]

/-- Entries of `unconj η S`. -/
theorem unconj_apply (η : Fin 4 → ℝ) (S : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    unconj η S a b = (η a : ℂ) * lam (η a) * S a b * lam (η b) := by
  rw [unconj, dmat, Matrix.mul_diagonal, dinv, Matrix.diagonal_mul]

/-- `conj η` is additive. -/
theorem conj_add (η : Fin 4 → ℝ) (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    conj η (X + Y) = conj η X + conj η Y := by
  simp only [conj, Matrix.mul_add, Matrix.add_mul]

/-- `conj η` commutes with scalars. -/
theorem conj_smul (η : Fin 4 → ℝ) (w : ℂ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    conj η (w • X) = w • conj η X := by
  simp only [conj, Matrix.mul_smul, Matrix.smul_mul]

/-- `conj η` is multiplicative. -/
theorem conj_mul {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X Y : Matrix (Fin 4) (Fin 4) ℂ) : conj η (X * Y) = conj η X * conj η Y := by
  have h := dinv_mul_dmat hη
  symm
  calc dmat η * X * dinv η * (dmat η * Y * dinv η)
      = dmat η * X * (dinv η * dmat η) * Y * dinv η := by simp only [Matrix.mul_assoc]
    _ = dmat η * (X * Y) * dinv η := by rw [h, Matrix.mul_one, Matrix.mul_assoc (dmat η) X Y]

/-- `conj η` preserves commutators. -/
theorem conj_bracket {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    conj η (X * Y - Y * X) = conj η X * conj η Y - conj η Y * conj η X := by
  rw [← conj_mul hη, ← conj_mul hη]
  simp only [conj, Matrix.mul_sub, Matrix.sub_mul]

/-- `unconj η (conj η X) = X`. -/
theorem unconj_conj {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X : Matrix (Fin 4) (Fin 4) ℂ) : unconj η (conj η X) = X := by
  have h := dinv_mul_dmat hη
  calc dinv η * (dmat η * X * dinv η) * dmat η
      = (dinv η * dmat η) * X * (dinv η * dmat η) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [h, Matrix.one_mul, Matrix.mul_one]

/-- `conj η (unconj η S) = S`. -/
theorem conj_unconj {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (S : Matrix (Fin 4) (Fin 4) ℂ) : conj η (unconj η S) = S := by
  have h := dmat_mul_dinv hη
  calc dmat η * (dinv η * S * dmat η) * dinv η
      = (dmat η * dinv η) * S * (dmat η * dinv η) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h, Matrix.one_mul, Matrix.mul_one]

/-- `conj η X` is antisymmetric for an `etaC η`-skew `X`. -/
theorem conj_antisymm {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X : etaSkew (etaC η))
    (i j : Fin 4) : conj η X.1 j i = -conj η X.1 i j := by
  have h : X.1 j i * (η j : ℂ) = -((η i : ℂ) * X.1 i j) :=
    (mem_etaSkew_iff (etaC η) X.1).mp X.2 i j
  have hi := etaC_mul_self hη i
  have hj := etaC_mul_self hη j
  rw [conj_apply, conj_apply]
  linear_combination (lam (η i) * lam (η j) * (η i : ℂ) * (η j : ℂ)) * h -
    (lam (η i) * lam (η j) * (η i : ℂ) * X.1 j i) * hj -
    (lam (η i) * lam (η j) * (η j : ℂ) * X.1 i j) * hi

/-- `unconj η S` is `etaC η`-skew for an antisymmetric `S`. -/
theorem unconj_mem {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : ∀ i j, S j i = -S i j) :
    unconj η S ∈ etaSkew (etaC η) := by
  rw [mem_etaSkew_iff]
  intro i j
  have hi := etaC_mul_self hη i
  have hj := etaC_mul_self hη j
  rw [unconj_apply, unconj_apply, hS i j]
  change (η j : ℂ) * lam (η j) * -S i j * lam (η i) * (η j : ℂ) =
    -((η i : ℂ) * ((η i : ℂ) * lam (η i) * S i j * lam (η j)))
  linear_combination (-(lam (η j) * S i j * lam (η i))) * hj +
    (lam (η i) * S i j * lam (η j)) * hi

end Conj

/-! ### Antisymmetric `4 × 4` matrices and their two trace-zero `2 × 2` matrices -/

section SelfDual

/-- The first trace-zero `2 × 2` matrix of a `4 × 4` matrix; it reads the entries above the
diagonal. -/
noncomputable def sdPlus (S : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliC (S 0 1 - S 2 3) (S 0 2 + S 1 3) (S 0 3 - S 1 2)

/-- The second trace-zero `2 × 2` matrix of a `4 × 4` matrix; it reads the entries above the
diagonal. -/
noncomputable def sdMinus (S : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliC (-S 0 1 - S 2 3) (-S 0 2 + S 1 3) (-S 0 3 - S 1 2)

/-- `sdPlus` is additive. -/
theorem sdPlus_add (S T : Matrix (Fin 4) (Fin 4) ℂ) : sdPlus (S + T) = sdPlus S + sdPlus T := by
  simp only [sdPlus, pauliC_add, Matrix.add_apply]
  congr 1 <;> ring

/-- `sdMinus` is additive. -/
theorem sdMinus_add (S T : Matrix (Fin 4) (Fin 4) ℂ) :
    sdMinus (S + T) = sdMinus S + sdMinus T := by
  simp only [sdMinus, pauliC_add, Matrix.add_apply]
  congr 1 <;> ring

/-- `sdPlus` commutes with scalars. -/
theorem sdPlus_smul (w : ℂ) (S : Matrix (Fin 4) (Fin 4) ℂ) : sdPlus (w • S) = w • sdPlus S := by
  simp only [sdPlus, pauliC_smul, Matrix.smul_apply, smul_eq_mul]
  congr 1 <;> ring

/-- `sdMinus` commutes with scalars. -/
theorem sdMinus_smul (w : ℂ) (S : Matrix (Fin 4) (Fin 4) ℂ) :
    sdMinus (w • S) = w • sdMinus S := by
  simp only [sdMinus, pauliC_smul, Matrix.smul_apply, smul_eq_mul]
  congr 1 <;> ring

/-- The diagonal of an antisymmetric complex matrix vanishes. -/
theorem antisymm_diag {S : Matrix (Fin 4) (Fin 4) ℂ} (hS : ∀ i j, S j i = -S i j) (i : Fin 4) :
    S i i = 0 := by
  have h := hS i i
  linear_combination (1 / 2 : ℂ) * h

/-- `sdPlus` preserves the commutator of antisymmetric matrices. -/
theorem sdPlus_bracket (S T : Matrix (Fin 4) (Fin 4) ℂ) (hS : ∀ i j, S j i = -S i j)
    (hT : ∀ i j, T j i = -T i j) :
    sdPlus (S * T - T * S) = sdPlus S * sdPlus T - sdPlus T * sdPlus S := by
  rw [sdPlus, sdPlus, sdPlus, pauliC_bracket]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four, hS 0 1, hS 0 2,
    hS 1 2, hS 1 3, hS 2 3, hT 0 1, hT 0 2, hT 1 2, hT 1 3, hT 2 3,
    antisymm_diag hS, antisymm_diag hT]
  congr 1 <;> ring

/-- `sdMinus` preserves the commutator of antisymmetric matrices. -/
theorem sdMinus_bracket (S T : Matrix (Fin 4) (Fin 4) ℂ) (hS : ∀ i j, S j i = -S i j)
    (hT : ∀ i j, T j i = -T i j) :
    sdMinus (S * T - T * S) = sdMinus S * sdMinus T - sdMinus T * sdMinus S := by
  rw [sdMinus, sdMinus, sdMinus, pauliC_bracket]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four, hS 0 1, hS 0 2,
    hS 1 2, hS 1 3, hS 2 3, hT 0 1, hT 0 2, hT 1 2, hT 1 3, hT 2 3,
    antisymm_diag hS, antisymm_diag hT]
  congr 1 <;> ring

/-- The antisymmetric `4 × 4` matrix with entries `s i j` above the diagonal. -/
def asym (s01 s02 s03 s12 s13 s23 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, s01, s02, s03; -s01, 0, s12, s13; -s02, -s12, 0, s23; -s03, -s13, -s23, 0]

/-- `asym s` is antisymmetric. -/
theorem asym_antisymm (s01 s02 s03 s12 s13 s23 : ℂ) (i j : Fin 4) :
    asym s01 s02 s03 s12 s13 s23 j i = -asym s01 s02 s03 s12 s13 s23 i j := by
  fin_cases i <;> fin_cases j <;> simp [asym]

/-- Every antisymmetric matrix is `asym` of its entries above the diagonal. -/
theorem eq_asym (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : ∀ i j, S j i = -S i j) :
    S = asym (S 0 1) (S 0 2) (S 0 3) (S 1 2) (S 1 3) (S 2 3) := by
  have hd := antisymm_diag hS
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asym, hd, hS 0 1, hS 0 2, hS 0 3, hS 1 2, hS 1 3, hS 2 3]

/-- `sdPlus` of `asym s`. -/
theorem sdPlus_asym (s01 s02 s03 s12 s13 s23 : ℂ) :
    sdPlus (asym s01 s02 s03 s12 s13 s23) = pauliC (s01 - s23) (s02 + s13) (s03 - s12) :=
  rfl

/-- `sdMinus` of `asym s`. -/
theorem sdMinus_asym (s01 s02 s03 s12 s13 s23 : ℂ) :
    sdMinus (asym s01 s02 s03 s12 s13 s23) = pauliC (-s01 - s23) (-s02 + s13) (-s03 - s12) :=
  rfl

/-- The antisymmetric matrix with given images under `sdPlus` and `sdMinus`, in the coordinates
of `pauliC`. -/
noncomputable def unsdCoords (a1 a2 a3 b1 b2 b3 : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  asym ((a1 - b1) / 2) ((a2 - b2) / 2) ((a3 - b3) / 2) (-(a3 + b3) / 2) ((a2 + b2) / 2)
    (-(a1 + b1) / 2)

/-- The antisymmetric matrix with images `A` under `sdPlus` and `B` under `sdMinus` (for
trace-zero `A`, `B`). -/
noncomputable def unsd (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  unsdCoords (Complex.I * (A 0 1 + A 1 0)) (A 1 0 - A 0 1) (2 * Complex.I * A 0 0)
    (Complex.I * (B 0 1 + B 1 0)) (B 1 0 - B 0 1) (2 * Complex.I * B 0 0)

/-- `unsd A B` is antisymmetric. -/
theorem unsd_antisymm (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 4) :
    unsd A B j i = -unsd A B i j :=
  asym_antisymm _ _ _ _ _ _ i j

/-- `sdPlus (unsd A B) = A` for trace-zero `A`. -/
theorem sdPlus_unsd (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.trace = 0) :
    sdPlus (unsd A B) = A := by
  refine Eq.trans ?_ (eq_pauliC A hA).symm
  rw [unsd, unsdCoords, sdPlus_asym]
  congr 1 <;> ring

/-- `sdMinus (unsd A B) = B` for trace-zero `B`. -/
theorem sdMinus_unsd (A B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B.trace = 0) :
    sdMinus (unsd A B) = B := by
  refine Eq.trans ?_ (eq_pauliC B hB).symm
  rw [unsd, unsdCoords, sdMinus_asym]
  congr 1 <;> ring

/-- `unsd` on two `pauliC` matrices. -/
theorem unsd_pauliC (a1 a2 a3 b1 b2 b3 : ℂ) :
    unsd (pauliC a1 a2 a3) (pauliC b1 b2 b3) = unsdCoords a1 a2 a3 b1 b2 b3 := by
  have hI := Complex.I_mul_I
  have e1 : ∀ a1 a2 a3 : ℂ,
      Complex.I * (pauliC a1 a2 a3 0 1 + pauliC a1 a2 a3 1 0) = a1 := by
    intro a1 a2 a3
    change Complex.I * (-(Complex.I * a1 + a2) / 2 + (-(Complex.I * a1) + a2) / 2) = a1
    linear_combination (-a1) * hI
  have e2 : ∀ a1 a2 a3 : ℂ, pauliC a1 a2 a3 1 0 - pauliC a1 a2 a3 0 1 = a2 := by
    intro a1 a2 a3
    change (-(Complex.I * a1) + a2) / 2 - -(Complex.I * a1 + a2) / 2 = a2
    ring
  have e3 : ∀ a1 a2 a3 : ℂ, 2 * Complex.I * pauliC a1 a2 a3 0 0 = a3 := by
    intro a1 a2 a3
    change 2 * Complex.I * (-(Complex.I * a3) / 2) = a3
    linear_combination (-a3) * hI
  rw [unsd, e1, e2, e3, e1, e2, e3]

/-- `unsd (sdPlus S) (sdMinus S) = S` for an antisymmetric `S`. -/
theorem unsd_sd (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : ∀ i j, S j i = -S i j) :
    unsd (sdPlus S) (sdMinus S) = S := by
  refine Eq.trans ?_ (eq_asym S hS).symm
  rw [sdPlus, sdMinus, unsd_pauliC, unsdCoords]
  congr 1 <;> ring

end SelfDual

/-! ### The two maps to trace-zero `2 × 2` matrices -/

section Spin

/-- The first component of the equivalence, on all complex `4 × 4` matrices:
`X ↦ sdPlus (D * X * D⁻¹)`. -/
noncomputable def spinP (η : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := sdPlus (conj η X)
  map_add' X Y := by rw [conj_add, sdPlus_add]
  map_smul' w X := by rw [conj_smul, sdPlus_smul, RingHom.id_apply]

/-- The second component of the equivalence, on all complex `4 × 4` matrices:
`X ↦ sdMinus (D * X * D⁻¹)`. -/
noncomputable def spinM (η : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := sdMinus (conj η X)
  map_add' X Y := by rw [conj_add, sdMinus_add]
  map_smul' w X := by rw [conj_smul, sdMinus_smul, RingHom.id_apply]

theorem spinP_apply (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    spinP η X = sdPlus (conj η X) :=
  rfl

theorem spinM_apply (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    spinM η X = sdMinus (conj η X) :=
  rfl

/-- `spinP η X` has trace zero. -/
theorem spinP_trace (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) : (spinP η X).trace = 0 :=
  pauliC_trace _ _ _

/-- `spinM η X` has trace zero. -/
theorem spinM_trace (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) : (spinM η X).trace = 0 :=
  pauliC_trace _ _ _

/-- `spinP η` preserves the bracket of `etaC η`-skew matrices. -/
theorem spinP_bracket {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X Y : etaSkew (etaC η)) :
    spinP η (X.1 * Y.1 - Y.1 * X.1) = spinP η X.1 * spinP η Y.1 - spinP η Y.1 * spinP η X.1 := by
  rw [spinP_apply, conj_bracket hη]
  exact sdPlus_bracket _ _ (conj_antisymm hη X) (conj_antisymm hη Y)

/-- `spinM η` preserves the bracket of `etaC η`-skew matrices. -/
theorem spinM_bracket {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X Y : etaSkew (etaC η)) :
    spinM η (X.1 * Y.1 - Y.1 * X.1) = spinM η X.1 * spinM η Y.1 - spinM η Y.1 * spinM η X.1 := by
  rw [spinM_apply, conj_bracket hη]
  exact sdMinus_bracket _ _ (conj_antisymm hη X) (conj_antisymm hη Y)

/-- The inverse of `X ↦ (spinP η X, spinM η X)`. -/
noncomputable def unspin (η : Fin 4 → ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  unconj η (unsd A B)

/-- `unspin η A B` is `etaC η`-skew. -/
theorem unspin_mem {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) : unspin η A B ∈ etaSkew (etaC η) :=
  unconj_mem hη _ (unsd_antisymm A B)

/-- `unspin η` is a left inverse on `etaC η`-skew matrices. -/
theorem unspin_spin {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (X : etaSkew (etaC η)) :
    unspin η (spinP η X.1) (spinM η X.1) = X.1 := by
  rw [unspin, spinP_apply, spinM_apply, unsd_sd _ (conj_antisymm hη X), unconj_conj hη]

/-- `unspin η` is a right inverse, first component. -/
theorem spinP_unspin {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.trace = 0) : spinP η (unspin η A B) = A := by
  rw [unspin, spinP_apply, conj_unconj hη, sdPlus_unsd A B hA]

/-- `unspin η` is a right inverse, second component. -/
theorem spinM_unspin {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B.trace = 0) : spinM η (unspin η A B) = B := by
  rw [unspin, spinM_apply, conj_unconj hη, sdMinus_unsd A B hB]

end Spin

/-! ### Generators -/

section Gen

/-- `conj η` of a generator: `lam (η i) * lam (η j)` times `E i j - E j i`. -/
theorem conj_gen {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (i j : Fin 4) :
    conj η (gen (etaC η) i j).1 =
      (lam (η i) * lam (η j)) • (Matrix.single i j (1 : ℂ) - Matrix.single j i (1 : ℂ)) := by
  have hi := etaC_mul_self hη i
  have hj := etaC_mul_self hη j
  ext a b
  rw [conj_apply, gen_coe]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h1 : i = a ∧ j = b
  · by_cases h2 : j = a ∧ i = b
    · have hij : i = j := h1.1.trans h2.1.symm
      simp only [ite_eq_left h1, ite_eq_left h2]
      rw [hij]
      ring
    · simp only [ite_eq_left h1, ite_eq_right h2]
      rw [← h1.1, ← h1.2]
      change lam (η i) * ((η j : ℂ) - 0) * ((η j : ℂ) * lam (η j)) =
        lam (η i) * lam (η j) * (1 - 0)
      linear_combination (lam (η i) * lam (η j)) * hj
  · by_cases h2 : j = a ∧ i = b
    · simp only [ite_eq_right h1, ite_eq_left h2]
      rw [← h2.1, ← h2.2]
      change lam (η j) * (0 - (η i : ℂ)) * ((η i : ℂ) * lam (η i)) =
        lam (η i) * lam (η j) * (0 - 1)
      linear_combination (-(lam (η i) * lam (η j))) * hi
    · simp only [ite_eq_right h1, ite_eq_right h2]
      ring

/-- `sdPlus (E i j - E j i) = ½ • (quat i * quatBar j)` for `i ≠ j`. -/
theorem sdPlus_single (i j : Fin 4) (hij : i ≠ j) :
    sdPlus (Matrix.single i j (1 : ℂ) - Matrix.single j i (1 : ℂ)) =
      (1 / 2 : ℂ) • (quat i * quatBar j) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (ext a b
       fin_cases a <;> fin_cases b <;>
         simp [sdPlus, pauliC, quat, quatBar] <;> ring_nf)

/-- `sdMinus (E i j - E j i) = ½ • (quatBar i * quat j)` for `i ≠ j`. -/
theorem sdMinus_single (i j : Fin 4) (hij : i ≠ j) :
    sdMinus (Matrix.single i j (1 : ℂ) - Matrix.single j i (1 : ℂ)) =
      (1 / 2 : ℂ) • (quatBar i * quat j) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (ext a b
       fin_cases a <;> fin_cases b <;>
         simp [sdMinus, pauliC, quat, quatBar] <;> ring_nf)

/-- `spinP η` on a generator. -/
theorem spinP_gen {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (i j : Fin 4) (hij : i ≠ j) :
    spinP η (gen (etaC η) i j).1 = spinPlus η i j := by
  rw [spinP_apply, conj_gen hη, sdPlus_smul, sdPlus_single i j hij, spinPlus, smul_smul]
  congr 1
  ring

/-- `spinM η` on a generator. -/
theorem spinM_gen {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (i j : Fin 4) (hij : i ≠ j) :
    spinM η (gen (etaC η) i j).1 = spinMinus η i j := by
  rw [spinM_apply, conj_gen hη, sdMinus_smul, sdMinus_single i j hij, spinMinus, smul_smul]
  congr 1
  ring

end Gen

/-! ### The Hodge operator over `ℂ` -/

section HodgeC

/-- Entry `(0, 1)` of `hodgeMat (etaC η) X`. -/
theorem hodgeMatC_01 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    hodgeMat (etaC η) X 0 1 = (η 2 : ℂ) * X 2 3 * (η 1 : ℂ) := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change (Matrix.diagonal (etaC η) * X) 2 3 * (η 1 : ℂ) = _
  rw [Matrix.diagonal_mul]

/-- Entry `(0, 2)` of `hodgeMat (etaC η) X`. -/
theorem hodgeMatC_02 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    hodgeMat (etaC η) X 0 2 = -((η 1 : ℂ) * X 1 3) * (η 2 : ℂ) := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change -(Matrix.diagonal (etaC η) * X) 1 3 * (η 2 : ℂ) = _
  rw [Matrix.diagonal_mul]

/-- Entry `(0, 3)` of `hodgeMat (etaC η) X`. -/
theorem hodgeMatC_03 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    hodgeMat (etaC η) X 0 3 = (η 1 : ℂ) * X 1 2 * (η 3 : ℂ) := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change (Matrix.diagonal (etaC η) * X) 1 2 * (η 3 : ℂ) = _
  rw [Matrix.diagonal_mul]

/-- Entry `(1, 2)` of `hodgeMat (etaC η) X`. -/
theorem hodgeMatC_12 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    hodgeMat (etaC η) X 1 2 = (η 0 : ℂ) * X 0 3 * (η 2 : ℂ) := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change (Matrix.diagonal (etaC η) * X) 0 3 * (η 2 : ℂ) = _
  rw [Matrix.diagonal_mul]

/-- Entry `(1, 3)` of `hodgeMat (etaC η) X`. -/
theorem hodgeMatC_13 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    hodgeMat (etaC η) X 1 3 = -((η 0 : ℂ) * X 0 2) * (η 3 : ℂ) := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change -(Matrix.diagonal (etaC η) * X) 0 2 * (η 3 : ℂ) = _
  rw [Matrix.diagonal_mul]

/-- Entry `(2, 3)` of `hodgeMat (etaC η) X`. -/
theorem hodgeMatC_23 (η : Fin 4 → ℝ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    hodgeMat (etaC η) X 2 3 = (η 0 : ℂ) * X 0 1 * (η 3 : ℂ) := by
  rw [hodgeMat, Matrix.mul_diagonal]
  change (Matrix.diagonal (etaC η) * X) 0 1 * (η 3 : ℂ) = _
  rw [Matrix.diagonal_mul]

/-- `spinP η` carries `hodgeMat (etaC η)` to multiplication by `-lamProd η`. -/
theorem spinP_hodgeMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    spinP η (hodgeMat (etaC η) X) = (-lamProd η) • spinP η X := by
  have q1 := lam_pow_four hη 1
  have q2 := lam_pow_four hη 2
  have q3 := lam_pow_four hη 3
  rw [spinP_apply, spinP_apply, sdPlus, sdPlus, pauliC_smul, lamProd, Fin.prod_univ_four]
  simp only [conj_apply, hodgeMatC_01, hodgeMatC_02, hodgeMatC_03, hodgeMatC_12, hodgeMatC_13,
    hodgeMatC_23, ← lam_mul_self hη]
  set m0 := lam (η 0)
  set m1 := lam (η 1)
  set m2 := lam (η 2)
  set m3 := lam (η 3)
  congr 1
  · linear_combination (m0 * m1 * m2 ^ 2 * X 2 3 + m0 ^ 2 * m2 * m3 * X 0 1) * q1 -
      (m0 * m1 * m2 ^ 2 * X 2 3 + m0 ^ 2 * m2 * m3 * X 0 1) * q3
  · linear_combination (-(m0 * m1 ^ 2 * m2 * X 1 3) + m0 ^ 2 * m1 * m3 * X 0 2) * q2 -
      (-(m0 * m1 ^ 2 * m2 * X 1 3) + m0 ^ 2 * m1 * m3 * X 0 2) * q3
  · linear_combination (m0 * m1 ^ 2 * m3 * X 1 2 + m0 ^ 2 * m1 * m2 * X 0 3) * q3 -
      (m0 * m1 ^ 2 * m3 * X 1 2 + m0 ^ 2 * m1 * m2 * X 0 3) * q2

/-- `spinM η` carries `hodgeMat (etaC η)` to multiplication by `lamProd η`. -/
theorem spinM_hodgeMat {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    spinM η (hodgeMat (etaC η) X) = lamProd η • spinM η X := by
  have q1 := lam_pow_four hη 1
  have q2 := lam_pow_four hη 2
  have q3 := lam_pow_four hη 3
  rw [spinM_apply, spinM_apply, sdMinus, sdMinus, pauliC_smul, lamProd, Fin.prod_univ_four]
  simp only [conj_apply, hodgeMatC_01, hodgeMatC_02, hodgeMatC_03, hodgeMatC_12, hodgeMatC_13,
    hodgeMatC_23, ← lam_mul_self hη]
  set m0 := lam (η 0)
  set m1 := lam (η 1)
  set m2 := lam (η 2)
  set m3 := lam (η 3)
  congr 1
  · linear_combination (-(m0 * m1 * m2 ^ 2 * X 2 3) + m0 ^ 2 * m2 * m3 * X 0 1) * q1 -
      (-(m0 * m1 * m2 ^ 2 * X 2 3) + m0 ^ 2 * m2 * m3 * X 0 1) * q3
  · linear_combination (m0 * m1 ^ 2 * m2 * X 1 3 + m0 ^ 2 * m1 * m3 * X 0 2) * q2 -
      (m0 * m1 ^ 2 * m2 * X 1 3 + m0 ^ 2 * m1 * m3 * X 0 2) * q3
  · linear_combination (-(m0 * m1 ^ 2 * m3 * X 1 2) + m0 ^ 2 * m1 * m2 * X 0 3) * q3 -
      (-(m0 * m1 ^ 2 * m3 * X 1 2) + m0 ^ 2 * m1 * m2 * X 0 3) * q2

end HodgeC

/-! ### The two projectors of the Hodge operator -/

section Proj

/-- `lamProd η ^ 4 = 1` for entries `±1`. -/
theorem lamProd_pow_four {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) : lamProd η ^ 4 = 1 := by
  rw [lamProd, Fin.prod_univ_four, mul_pow, mul_pow, mul_pow, lam_pow_four hη 0,
    lam_pow_four hη 1, lam_pow_four hη 2, lam_pow_four hη 3]
  norm_num

/-- `lamProd η ≠ 0` for entries `±1`. -/
theorem lamProd_ne_zero {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) : lamProd η ≠ 0 := by
  intro h
  have h4 := lamProd_pow_four hη
  rw [h] at h4
  norm_num at h4

/-- The matrix of `hodgeProjMinus η X`. -/
theorem hodgeProjMinus_coe (η : Fin 4 → ℝ) (X : etaSkew (etaC η)) :
    ((hodgeProjMinus η X : etaSkew (etaC η)) : Matrix (Fin 4) (Fin 4) ℂ) =
      (1 / 2 : ℂ) • (X.1 - (lamProd η)⁻¹ • hodgeMat (etaC η) X.1) :=
  rfl

/-- The matrix of `hodgeProjPlus η X`. -/
theorem hodgeProjPlus_coe (η : Fin 4 → ℝ) (X : etaSkew (etaC η)) :
    ((hodgeProjPlus η X : etaSkew (etaC η)) : Matrix (Fin 4) (Fin 4) ℂ) =
      (1 / 2 : ℂ) • (X.1 + (lamProd η)⁻¹ • hodgeMat (etaC η) X.1) :=
  rfl

/-- `spinP η` does not see `hodgeProjMinus η`. -/
theorem spinP_hodgeProjMinus {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X : etaSkew (etaC η)) : spinP η (hodgeProjMinus η X).1 = spinP η X.1 := by
  have h : (lamProd η)⁻¹ * -lamProd η = -1 := by
    field_simp [lamProd_ne_zero hη]
  rw [hodgeProjMinus_coe, map_smul, map_sub, map_smul, spinP_hodgeMat hη, smul_smul, h]
  module

/-- `spinM η` vanishes on the image of `hodgeProjMinus η`. -/
theorem spinM_hodgeProjMinus {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X : etaSkew (etaC η)) : spinM η (hodgeProjMinus η X).1 = 0 := by
  have h : (lamProd η)⁻¹ * lamProd η = 1 := inv_mul_cancel₀ (lamProd_ne_zero hη)
  rw [hodgeProjMinus_coe, map_smul, map_sub, map_smul, spinM_hodgeMat hη, smul_smul, h]
  module

/-- `spinP η` vanishes on the image of `hodgeProjPlus η`. -/
theorem spinP_hodgeProjPlus {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X : etaSkew (etaC η)) : spinP η (hodgeProjPlus η X).1 = 0 := by
  have h : (lamProd η)⁻¹ * -lamProd η = -1 := by
    field_simp [lamProd_ne_zero hη]
  rw [hodgeProjPlus_coe, map_smul, map_add, map_smul, spinP_hodgeMat hη, smul_smul, h]
  module

/-- `spinM η` does not see `hodgeProjPlus η`. -/
theorem spinM_hodgeProjPlus {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X : etaSkew (etaC η)) : spinM η (hodgeProjPlus η X).1 = spinM η X.1 := by
  have h : (lamProd η)⁻¹ * lamProd η = 1 := inv_mul_cancel₀ (lamProd_ne_zero hη)
  rw [hodgeProjPlus_coe, map_smul, map_add, map_smul, spinM_hodgeMat hη, smul_smul, h]
  module

end Proj

/-! ### The centroid over `ℂ` -/

section CentroidC

/-- The entries of `etaC η` are nonzero for entries `±1`. -/
theorem etaC_ne_zero {η : Fin 4 → ℝ} (hη : ∀ i, η i = 1 ∨ η i = -1) (i : Fin 4) :
    etaC η i ≠ 0 := by
  change (η i : ℂ) ≠ 0
  rcases hη i with h | h <;> rw [h] <;> norm_num

/-- A combination of the two projectors in terms of `id` and `hodge (etaC η)`. -/
theorem smul_proj_add_smul_proj (η : Fin 4 → ℝ) (a b : ℂ) :
    a • hodgeProjPlus η + b • hodgeProjMinus η =
      ((a + b) / 2) • (LinearMap.id : etaSkew (etaC η) →ₗ[ℂ] etaSkew (etaC η)) +
        ((a - b) / 2 * (lamProd η)⁻¹) • hodge (etaC η) := by
  simp only [hodgeProjPlus, hodgeProjMinus]
  module

end CentroidC

/-! ### Base change: `ℂ ⊗[ℝ] etaSkew η` and `etaSkew (etaC η)` -/

section Tensor

/-- A real `η`-skew matrix, read over `ℂ`, is `etaC η`-skew. -/
theorem map_ofReal_mem (η : Fin 4 → ℝ) (X : etaSkew η) :
    X.1.map Complex.ofReal ∈ etaSkew (etaC η) := by
  rw [mem_etaSkew_iff]
  intro i j
  have h := (mem_etaSkew_iff η X.1).mp X.2 i j
  change ((X.1 j i : ℝ) : ℂ) * (η j : ℂ) = -((η i : ℂ) * ((X.1 i j : ℝ) : ℂ))
  exact_mod_cast h

/-- The real-linear map `etaSkew η → etaSkew (etaC η)` reading a real matrix over `ℂ`. -/
noncomputable def cplx (η : Fin 4 → ℝ) : etaSkew η →ₗ[ℝ] etaSkew (etaC η) where
  toFun X := ⟨X.1.map Complex.ofReal, map_ofReal_mem η X⟩
  map_add' X Y := Subtype.ext (by
    ext i j
    change (((X.1 + Y.1) i j : ℝ) : ℂ) = ((X.1 i j : ℝ) : ℂ) + ((Y.1 i j : ℝ) : ℂ)
    rw [Matrix.add_apply, Complex.ofReal_add])
  map_smul' r X := Subtype.ext (by
    ext i j
    change (((r • X.1) i j : ℝ) : ℂ) = r • ((X.1 i j : ℝ) : ℂ)
    rw [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul])

/-- Entries of `cplx η X`. -/
theorem cplx_apply (η : Fin 4 → ℝ) (X : etaSkew η) (i j : Fin 4) :
    (cplx η X).1 i j = ((X.1 i j : ℝ) : ℂ) :=
  rfl

/-- `cplx η` preserves the bracket. -/
theorem cplx_lie (η : Fin 4 → ℝ) (X Y : etaSkew η) : cplx η ⁅X, Y⁆ = ⁅cplx η X, cplx η Y⁆ := by
  apply Subtype.ext
  ext i j
  change (((X.1 * Y.1 - Y.1 * X.1) i j : ℝ) : ℂ) =
    ((cplx η X).1 * (cplx η Y).1 - (cplx η Y).1 * (cplx η X).1) i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four, cplx_apply]
  push_cast
  ring

/-- `cplx η` on a generator. -/
theorem cplx_gen (η : Fin 4 → ℝ) (i j : Fin 4) : cplx η (gen η i j) = gen (etaC η) i j := by
  apply Subtype.ext
  ext a b
  rw [cplx_apply, gen_coe, gen_coe]
  simp only [Matrix.sub_apply, Matrix.single_apply]
  split_ifs <;> simp [etaC]

/-- The real part of an `etaC η`-skew matrix is `η`-skew. -/
theorem map_re_mem (η : Fin 4 → ℝ) (Z : etaSkew (etaC η)) : Z.1.map Complex.re ∈ etaSkew η := by
  rw [mem_etaSkew_iff]
  intro i j
  have h : Z.1 j i * (η j : ℂ) = -((η i : ℂ) * Z.1 i j) :=
    (mem_etaSkew_iff (etaC η) Z.1).mp Z.2 i j
  have h1 := congrArg Complex.re h
  simpa using h1

/-- The imaginary part of an `etaC η`-skew matrix is `η`-skew. -/
theorem map_im_mem (η : Fin 4 → ℝ) (Z : etaSkew (etaC η)) : Z.1.map Complex.im ∈ etaSkew η := by
  rw [mem_etaSkew_iff]
  intro i j
  have h : Z.1 j i * (η j : ℂ) = -((η i : ℂ) * Z.1 i j) :=
    (mem_etaSkew_iff (etaC η) Z.1).mp Z.2 i j
  have h1 := congrArg Complex.im h
  simpa using h1

/-- The real part of an `etaC η`-skew matrix. -/
noncomputable def rePart (η : Fin 4 → ℝ) (Z : etaSkew (etaC η)) : etaSkew η :=
  ⟨Z.1.map Complex.re, map_re_mem η Z⟩

/-- The imaginary part of an `etaC η`-skew matrix. -/
noncomputable def imPart (η : Fin 4 → ℝ) (Z : etaSkew (etaC η)) : etaSkew η :=
  ⟨Z.1.map Complex.im, map_im_mem η Z⟩

theorem rePart_apply (η : Fin 4 → ℝ) (Z : etaSkew (etaC η)) (i j : Fin 4) :
    (rePart η Z).1 i j = (Z.1 i j).re :=
  rfl

theorem imPart_apply (η : Fin 4 → ℝ) (Z : etaSkew (etaC η)) (i j : Fin 4) :
    (imPart η Z).1 i j = (Z.1 i j).im :=
  rfl

end Tensor

section TensorEquiv

/-- The `ℂ`-linear map `ℂ ⊗[ℝ] etaSkew η → etaSkew (etaC η)` with `z ⊗ X ↦ z • X`. -/
noncomputable def toC (η : Fin 4 → ℝ) : ℂ ⊗[ℝ] etaSkew η →ₗ[ℂ] etaSkew (etaC η) :=
  LinearMap.liftBaseChange ℂ (cplx η)

theorem toC_tmul (η : Fin 4 → ℝ) (z : ℂ) (X : etaSkew η) :
    toC η (z ⊗ₜ[ℝ] X) = z • cplx η X :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The inverse of `toC η`: `Z ↦ 1 ⊗ Re Z + i ⊗ Im Z`. -/
noncomputable def fromC (η : Fin 4 → ℝ) (Z : etaSkew (etaC η)) : ℂ ⊗[ℝ] etaSkew η :=
  (1 : ℂ) ⊗ₜ[ℝ] rePart η Z + Complex.I ⊗ₜ[ℝ] imPart η Z

/-- `toC η (fromC η Z) = Z`. -/
theorem toC_fromC (η : Fin 4 → ℝ) (Z : etaSkew (etaC η)) : toC η (fromC η Z) = Z := by
  rw [fromC, map_add, toC_tmul, toC_tmul]
  apply Subtype.ext
  ext i j
  change (1 : ℂ) * (((rePart η Z).1 i j : ℝ) : ℂ) + Complex.I * (((imPart η Z).1 i j : ℝ) : ℂ) =
    Z.1 i j
  rw [rePart_apply, imPart_apply, one_mul, mul_comm]
  exact Complex.re_add_im (Z.1 i j)

/-- `fromC η` is additive. -/
theorem fromC_add (η : Fin 4 → ℝ) (Z W : etaSkew (etaC η)) :
    fromC η (Z + W) = fromC η Z + fromC η W := by
  have h1 : rePart η (Z + W) = rePart η Z + rePart η W := Subtype.ext (by
    ext i j
    change ((Z.1 + W.1) i j).re = (Z.1 i j).re + (W.1 i j).re
    rw [Matrix.add_apply, Complex.add_re])
  have h2 : imPart η (Z + W) = imPart η Z + imPart η W := Subtype.ext (by
    ext i j
    change ((Z.1 + W.1) i j).im = (Z.1 i j).im + (W.1 i j).im
    rw [Matrix.add_apply, Complex.add_im])
  rw [fromC, fromC, fromC, h1, h2, TensorProduct.tmul_add, TensorProduct.tmul_add]
  abel

/-- `fromC η (z • cplx η X) = z ⊗ X`. -/
theorem fromC_smul_cplx (η : Fin 4 → ℝ) (z : ℂ) (X : etaSkew η) :
    fromC η (z • cplx η X) = z ⊗ₜ[ℝ] X := by
  have h1 : rePart η (z • cplx η X) = z.re • X := Subtype.ext (by
    ext i j
    change (z * ((X.1 i j : ℝ) : ℂ)).re = z.re * X.1 i j
    simp)
  have h2 : imPart η (z • cplx η X) = z.im • X := Subtype.ext (by
    ext i j
    change (z * ((X.1 i j : ℝ) : ℂ)).im = z.im * X.1 i j
    simp)
  rw [fromC, h1, h2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← TensorProduct.add_tmul]
  congr 1
  rw [Complex.real_smul, Complex.real_smul, mul_one]
  exact Complex.re_add_im z

/-- `fromC η (toC η t) = t`. -/
theorem fromC_toC (η : Fin 4 → ℝ) (t : ℂ ⊗[ℝ] etaSkew η) : fromC η (toC η t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul z X => rw [toC_tmul, fromC_smul_cplx]
  | add s t hs ht => rw [map_add, fromC_add, hs, ht]

/-- `toC η` preserves the bracket. -/
theorem toC_lie (η : Fin 4 → ℝ) (s t : ℂ ⊗[ℝ] etaSkew η) :
    toC η ⁅s, t⁆ = ⁅toC η s, toC η t⁆ := by
  induction s using TensorProduct.inductionOn with
  | tmul z X =>
    induction t using TensorProduct.inductionOn with
    | tmul w Y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, toC_tmul, toC_tmul, toC_tmul, cplx_lie,
        smul_lie, lie_smul, smul_smul]
    | add t1 t2 h1 h2 =>
      have e : ⁅(z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] etaSkew η), t1 + t2⁆ =
          ⁅(z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] etaSkew η), t1⁆ + ⁅(z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] etaSkew η), t2⁆ :=
        lie_add (z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] etaSkew η) t1 t2
      rw [e, map_add, map_add, lie_add, h1, h2]
  | add s1 s2 h1 h2 => rw [add_lie, map_add, map_add, add_lie, h1, h2]

/-- The base change `ℂ ⊗[ℝ] etaSkew η` is the Lie algebra of `etaC η`-skew complex matrices:
`z ⊗ X ↦ z • X`. -/
noncomputable def tensorEquivC (η : Fin 4 → ℝ) : (ℂ ⊗[ℝ] etaSkew η) ≃ₗ⁅ℂ⁆ etaSkew (etaC η) :=
  { toC η with
    map_lie' := fun {s t} => toC_lie η s t
    invFun := fromC η
    left_inv := fromC_toC η
    right_inv := toC_fromC η }

theorem tensorEquivC_tmul (η : Fin 4 → ℝ) (z : ℂ) (X : etaSkew η) :
    tensorEquivC η (z ⊗ₜ[ℝ] X) = z • cplx η X :=
  toC_tmul η z X

end TensorEquiv

end Complexification

open Complexification

/-- **L4 (the equivalence).** For `η : Fin 4 → ℝ` with every entry `1` or `-1`: a Lie algebra
equivalence over `ℂ` from the Lie algebra of complex `4 × 4` matrices skew for
`diagonal (fun i => (η i : ℂ))` to `sl(2, ℂ) × sl(2, ℂ)`. It is pinned down by
`etaSkewCEquiv_gen`. -/
noncomputable def etaSkewCEquiv (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) :
    skewAdjointMatricesLieSubalgebra (Matrix.diagonal fun i => (η i : ℂ)) ≃ₗ⁅ℂ⁆ sl2C × sl2C :=
  { toFun := fun X =>
      (⟨spinP η X.1, LinearMap.mem_ker.2 (spinP_trace η X.1)⟩,
        ⟨spinM η X.1, LinearMap.mem_ker.2 (spinM_trace η X.1)⟩)
    map_add' := fun X Y =>
      Prod.ext (Subtype.ext ((spinP η).map_add X.1 Y.1)) (Subtype.ext ((spinM η).map_add X.1 Y.1))
    map_smul' := fun w X =>
      Prod.ext (Subtype.ext ((spinP η).map_smul w X.1)) (Subtype.ext ((spinM η).map_smul w X.1))
    map_lie' := fun {X Y} =>
      Prod.ext (Subtype.ext (spinP_bracket hη X Y)) (Subtype.ext (spinM_bracket hη X Y))
    invFun := fun AB => ⟨unspin η AB.1.1 AB.2.1, unspin_mem hη AB.1.1 AB.2.1⟩
    left_inv := fun X => Subtype.ext (unspin_spin hη X)
    right_inv := fun AB =>
      Prod.ext (Subtype.ext (spinP_unspin hη AB.1.1 AB.2.1 (LinearMap.mem_ker.1 AB.1.2)))
        (Subtype.ext (spinM_unspin hη AB.1.1 AB.2.1 (LinearMap.mem_ker.1 AB.2.2))) }

/-- **L4 (on generators).** For `i ≠ j`, the two components of the image of the generator
`gen (etaC η) i j` under `etaSkewCEquiv η hη` are `spinPlus η i j` and `spinMinus η i j`. -/
theorem etaSkewCEquiv_gen (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) (i j : Fin 4)
    (hij : i ≠ j) :
    ((etaSkewCEquiv η hη (gen (etaC η) i j)).1 : Matrix (Fin 2) (Fin 2) ℂ) = spinPlus η i j ∧
    ((etaSkewCEquiv η hη (gen (etaC η) i j)).2 : Matrix (Fin 2) (Fin 2) ℂ) = spinMinus η i j := by
  exact ⟨spinP_gen hη i j hij, spinM_gen hη i j hij⟩

/-- **L4 (the two projectors and the two factors).** For every `X`: the image of
`hodgeProjMinus η X` under `etaSkewCEquiv η hη` is `((image of X).1, 0)`, and the image of
`hodgeProjPlus η X` is `(0, (image of X).2)`. Here
`hodgeProjPlus η = ½ (id + (lamProd η)⁻¹ • hodge (etaC η))` and
`hodgeProjMinus η = ½ (id - (lamProd η)⁻¹ • hodge (etaC η))`. -/
theorem etaSkewCEquiv_hodgeProj (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (X : etaSkew (etaC η)) :
    etaSkewCEquiv η hη (hodgeProjMinus η X) = ((etaSkewCEquiv η hη X).1, 0) ∧
    etaSkewCEquiv η hη (hodgeProjPlus η X) = (0, (etaSkewCEquiv η hη X).2) := by
  constructor
  · exact Prod.ext (Subtype.ext (spinP_hodgeProjMinus hη X))
      (Subtype.ext (spinM_hodgeProjMinus hη X))
  · exact Prod.ext (Subtype.ext (spinP_hodgeProjPlus hη X))
      (Subtype.ext (spinM_hodgeProjPlus hη X))

/-- **L4 (corollary: the centroid over `ℂ`).** For `η : Fin 4 → ℝ` with every entry `1` or `-1`
and every `ℂ`-linear endomorphism `R` of `etaSkew (etaC η)` that is bracket-commuting, there is
exactly one pair `(a, b)` in `ℂ × ℂ` with `R = a • hodgeProjPlus η + b • hodgeProjMinus η`. -/
theorem centroid_complex (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (R : etaSkew (etaC η) →ₗ[ℂ] etaSkew (etaC η)) (hR : IsBracketCommuting R) :
    ∃! ab : ℂ × ℂ, R = ab.1 • hodgeProjPlus η + ab.2 • hodgeProjMinus η := by
  have hη' : ∀ i, etaC η i ≠ 0 := etaC_ne_zero hη
  have hΛ := lamProd_ne_zero hη
  obtain ⟨α, β, hαβ⟩ : ∃ α β : ℂ, R = α • LinearMap.id + β • hodge (etaC η) :=
    ⟨_, _, eq_smul_id_add_smul_hodge two_ne_zero (etaC η) hη' R hR⟩
  refine ⟨(α + β * lamProd η, α - β * lamProd η), ?_, ?_⟩
  · change R = (α + β * lamProd η) • hodgeProjPlus η + (α - β * lamProd η) • hodgeProjMinus η
    have e1 : (α + β * lamProd η + (α - β * lamProd η)) / 2 = α := by ring
    have e2 : (α + β * lamProd η - (α - β * lamProd η)) / 2 * (lamProd η)⁻¹ = β := by
      field_simp
      ring
    rw [smul_proj_add_smul_proj, e1, e2]
    exact hαβ
  · rintro ⟨a, b⟩ hab
    change R = a • hodgeProjPlus η + b • hodgeProjMinus η at hab
    rw [smul_proj_add_smul_proj, hαβ] at hab
    have hz : (α - (a + b) / 2) • (LinearMap.id : etaSkew (etaC η) →ₗ[ℂ] etaSkew (etaC η)) +
        (β - (a - b) / 2 * (lamProd η)⁻¹) • hodge (etaC η) = 0 := by
      rw [← sub_eq_zero.mpr hab]
      module
    obtain ⟨h1, h2⟩ := smul_id_add_smul_hodge_eq_zero (etaC η) hη' _ _ hz
    have h3 : β * lamProd η = (a - b) / 2 := by
      have h4 : β = (a - b) / 2 * (lamProd η)⁻¹ := by linear_combination h2
      rw [h4]
      field_simp
    refine Prod.ext ?_ ?_
    · change a = α + β * lamProd η
      linear_combination -h1 - h3
    · change b = α - β * lamProd η
      linear_combination -h1 + h3

/-- **L4, TENSOR FORM (separately marked; the equivalence).** For `η : Fin 4 → ℝ` with every
entry `1` or `-1`: a Lie algebra equivalence over `ℂ` from the base change `ℂ ⊗[ℝ] etaSkew η` to
`sl(2, ℂ) × sl(2, ℂ)`. It is pinned down by `tensorEtaSkewEquiv_tmul_gen`. -/
noncomputable def tensorEtaSkewEquiv (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) :
    (ℂ ⊗[ℝ] etaSkew η) ≃ₗ⁅ℂ⁆ sl2C × sl2C :=
  (tensorEquivC η).trans (etaSkewCEquiv η hη)

/-- **L4, TENSOR FORM (on generators).** For `z : ℂ` and `i ≠ j`, the two components of the image
of `z ⊗ₜ gen η i j` under `tensorEtaSkewEquiv η hη` are `z • spinPlus η i j` and
`z • spinMinus η i j`. -/
theorem tensorEtaSkewEquiv_tmul_gen (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1) (z : ℂ)
    (i j : Fin 4) (hij : i ≠ j) :
    ((tensorEtaSkewEquiv η hη (z ⊗ₜ[ℝ] gen η i j)).1 : Matrix (Fin 2) (Fin 2) ℂ) =
        z • spinPlus η i j ∧
    ((tensorEtaSkewEquiv η hη (z ⊗ₜ[ℝ] gen η i j)).2 : Matrix (Fin 2) (Fin 2) ℂ) =
        z • spinMinus η i j := by
  have h : tensorEtaSkewEquiv η hη (z ⊗ₜ[ℝ] gen η i j) =
      z • etaSkewCEquiv η hη (gen (etaC η) i j) := by
    change etaSkewCEquiv η hη (tensorEquivC η (z ⊗ₜ[ℝ] gen η i j)) = _
    rw [tensorEquivC_tmul, cplx_gen, map_smul]
  obtain ⟨h1, h2⟩ := etaSkewCEquiv_gen η hη i j hij
  rw [h]
  constructor
  · change z • ((etaSkewCEquiv η hη (gen (etaC η) i j)).1 : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [h1]
  · change z • ((etaSkewCEquiv η hη (gen (etaC η) i j)).2 : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [h2]

/-- Uniqueness for `etaSkewCEquiv_gen`: a Lie algebra equivalence over `ℂ` from `etaSkew (etaC η)`
to `sl(2, ℂ) × sl(2, ℂ)` whose values on the generators `gen (etaC η) i j`, `i ≠ j`, have the
components `spinPlus η i j` and `spinMinus η i j` agrees with `etaSkewCEquiv η hη` everywhere. -/
theorem Complexification.eq_etaSkewCEquiv_of_gen (η : Fin 4 → ℝ) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (e' : etaSkew (etaC η) ≃ₗ⁅ℂ⁆ sl2C × sl2C)
    (h : ∀ i j : Fin 4, i ≠ j →
      ((e' (gen (etaC η) i j)).1 : Matrix (Fin 2) (Fin 2) ℂ) = spinPlus η i j ∧
      ((e' (gen (etaC η) i j)).2 : Matrix (Fin 2) (Fin 2) ℂ) = spinMinus η i j)
    (X : etaSkew (etaC η)) : e' X = etaSkewCEquiv η hη X := by
  have hg : ∀ i j : Fin 4, e' (gen (etaC η) i j) = etaSkewCEquiv η hη (gen (etaC η) i j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [gen_self, map_zero, map_zero]
    · obtain ⟨a1, a2⟩ := h i j hij
      obtain ⟨b1, b2⟩ := etaSkewCEquiv_gen η hη i j hij
      exact Prod.ext (Subtype.ext (a1.trans b1.symm)) (Subtype.ext (a2.trans b2.symm))
  rw [eq_sum_gen two_ne_zero (etaC η) (etaC_ne_zero hη) X]
  simp only [map_sum, map_smul, hg]

/-- Uniqueness for `tensorEtaSkewEquiv_tmul_gen`: a Lie algebra equivalence over `ℂ` from
`ℂ ⊗[ℝ] etaSkew η` to `sl(2, ℂ) × sl(2, ℂ)` whose values on the tensors `z ⊗ₜ gen η i j`, `i ≠ j`,
have the components `z • spinPlus η i j` and `z • spinMinus η i j` agrees with
`tensorEtaSkewEquiv η hη` everywhere. -/
theorem Complexification.eq_tensorEtaSkewEquiv_of_tmul_gen (η : Fin 4 → ℝ)
    (hη : ∀ i, η i = 1 ∨ η i = -1) (e' : (ℂ ⊗[ℝ] etaSkew η) ≃ₗ⁅ℂ⁆ sl2C × sl2C)
    (h : ∀ (z : ℂ) (i j : Fin 4), i ≠ j →
      ((e' (z ⊗ₜ[ℝ] gen η i j)).1 : Matrix (Fin 2) (Fin 2) ℂ) = z • spinPlus η i j ∧
      ((e' (z ⊗ₜ[ℝ] gen η i j)).2 : Matrix (Fin 2) (Fin 2) ℂ) = z • spinMinus η i j)
    (t : ℂ ⊗[ℝ] etaSkew η) : e' t = tensorEtaSkewEquiv η hη t := by
  have hη0 : ∀ i, η i ≠ 0 := fun i => by rcases hη i with h | h <;> rw [h] <;> norm_num
  have hg : ∀ (z : ℂ) (i j : Fin 4),
      e' (z ⊗ₜ[ℝ] gen η i j) = tensorEtaSkewEquiv η hη (z ⊗ₜ[ℝ] gen η i j) := by
    intro z i j
    by_cases hij : i = j
    · subst hij
      rw [gen_self, TensorProduct.tmul_zero, map_zero, map_zero]
    · obtain ⟨a1, a2⟩ := h z i j hij
      obtain ⟨b1, b2⟩ := tensorEtaSkewEquiv_tmul_gen η hη z i j hij
      exact Prod.ext (Subtype.ext (a1.trans b1.symm)) (Subtype.ext (a2.trans b2.symm))
  induction t using TensorProduct.inductionOn with
  | tmul z X =>
    rw [eq_sum_gen two_ne_zero η hη0 X]
    simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul', map_sum,
      hg]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

end LorentzLie
