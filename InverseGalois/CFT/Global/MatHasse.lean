import Mathlib
import InverseGalois.CFT.Global.DiagRepr

/-!
# The Hasse principle for an arbitrary rational quadratic form

## Main results

* `InverseGalois.CFT.IsMatIsotropic`: isotropy of the quadratic form attached to a square matrix.
* `InverseGalois.CFT.isMatIsotropic_transpose_mul_mul_iff`: isotropy is a congruence invariant.
* `InverseGalois.CFT.isMatIsotropic_diagonal_iff`: matrix and diagonal isotropy agree.
* `InverseGalois.CFT.exists_transpose_mul_mul_eq_diagonal`: a symmetric matrix over a field in
  which `2` is invertible is congruent to a diagonal matrix.
* `InverseGalois.CFT.isMatIsotropic_rat_iff`: the Hasse–Minkowski theorem for an arbitrary
  symmetric rational matrix.
-/

namespace InverseGalois.CFT

open Local Matrix

/-- A square matrix is isotropic when its quadratic form vanishes at some nonzero vector. -/
def IsMatIsotropic {K : Type*} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ x : Fin n → K, x ≠ 0 ∧ x ⬝ᵥ M *ᵥ x = 0

/-- The value of a congruent matrix at a vector is the value of the original matrix at the
transformed vector. -/
theorem dotProduct_transpose_mul_mul {K : Type*} [Field K] {n : ℕ}
    (M P : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    x ⬝ᵥ (Pᵀ * M * P) *ᵥ x = (P *ᵥ x) ⬝ᵥ M *ᵥ (P *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- Isotropy is invariant under congruence by an invertible matrix. -/
theorem isMatIsotropic_transpose_mul_mul_iff {K : Type*} [Field K] {n : ℕ}
    {M P : Matrix (Fin n) (Fin n) K} (hP : P.det ≠ 0) :
    IsMatIsotropic (Pᵀ * M * P) ↔ IsMatIsotropic M := by
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 hP)
  constructor
  · rintro ⟨x, hx, hval⟩
    refine ⟨P *ᵥ x, ?_, by rw [← dotProduct_transpose_mul_mul, hval]⟩
    intro h
    exact hx (Matrix.mulVec_injective_iff_isUnit.2 hu (by rw [h, Matrix.mulVec_zero]))
  · rintro ⟨y, hy, hval⟩
    obtain ⟨x, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu y
    refine ⟨x, ?_, by rw [dotProduct_transpose_mul_mul]; exact hval⟩
    intro h
    exact hy (by rw [h, Matrix.mulVec_zero])

/-- Isotropy of a diagonal matrix is isotropy of the corresponding diagonal form. -/
theorem isMatIsotropic_diagonal_iff {K : Type*} [Field K] {n : ℕ} {d : Fin n → K} :
    IsMatIsotropic (Matrix.diagonal d) ↔ IsDiagIsotropic d := by
  have key : ∀ x : Fin n → K, x ⬝ᵥ (Matrix.diagonal d) *ᵥ x = ∑ i, d i * x i ^ 2 := by
    intro x
    rw [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mulVec_diagonal]; ring
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rwa [key] at h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rw [key]; exact h⟩

/-- The entries of a congruent matrix are the values of the original bilinear form on the columns
of the transforming matrix. -/
theorem transpose_mul_mul_apply {K : Type*} [Field K] {n : ℕ} (M P : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    (Pᵀ * M * P) i j = (fun k => P k i) ⬝ᵥ M *ᵥ (fun k => P k j) := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_comm {K : Type*} [Field K] {n : ℕ} {M : Matrix (Fin n) (Fin n) K}
    (hM : M.IsSymm) (x y : Fin n → K) : x ⬝ᵥ M *ᵥ y = y ⬝ᵥ M *ᵥ x := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hM.apply j i]
  ring

/-- A symmetric matrix over a field in which `2` is invertible is congruent to a diagonal
matrix. -/
theorem exists_transpose_mul_mul_eq_diagonal {K : Type*} [Field K] [Invertible (2 : K)] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} (hM : M.IsSymm) :
    ∃ (P : Matrix (Fin n) (Fin n) K) (d : Fin n → K), P.det ≠ 0 ∧
      Pᵀ * M * P = Matrix.diagonal d := by
  classical
  have hsymm : (Matrix.toLinearMap₂' K M).IsSymm := by
    rw [LinearMap.isSymm_def]
    intro x y
    simp only [RingHom.id_apply, Matrix.toLinearMap₂'_apply']
    exact dotProduct_mulVec_comm hM x y
  obtain ⟨v0, hv0⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  have hrank : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  set v : Module.Basis (Fin n) K (Fin n → K) := v0.reindex (finCongr hrank) with hv
  have hvo : ∀ i j : Fin n, i ≠ j → (v i) ⬝ᵥ M *ᵥ (v j) = 0 := by
    intro i j hij
    have := hv0 (i := (finCongr hrank).symm i) (j := (finCongr hrank).symm j)
      (by simpa using hij)
    rw [hv]
    simpa [Module.Basis.reindex_apply, Matrix.toLinearMap₂'_apply', Function.onFun,
      LinearMap.IsOrtho] using this
  refine ⟨(Pi.basisFun K (Fin n)).toMatrix v, fun i => (v i) ⬝ᵥ M *ᵥ (v i), ?_, ?_⟩
  · rw [← Module.Basis.det_apply]
    exact ((Pi.basisFun K (Fin n)).isUnit_det v).ne_zero
  · ext i j
    rw [transpose_mul_mul_apply]
    have hP : ∀ a b : Fin n, ((Pi.basisFun K (Fin n)).toMatrix v) a b = v b a := by
      intro a b
      rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.diagonal_apply_eq]
      simp only [hP]
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp only [hP]
      exact hvo i j hij

/-- Isotropy of a rational matrix read in an extension of the rational field, in terms of a
diagonalising congruence. -/
theorem isMatIsotropic_map_iff {L : Type*} [Field L] (f : ℚ →+* L) {n : ℕ}
    {M P : Matrix (Fin n) (Fin n) ℚ} {d : Fin n → ℚ} (hP : P.det ≠ 0)
    (hPd : Pᵀ * M * P = Matrix.diagonal d) :
    IsMatIsotropic (M.map f) ↔ IsDiagIsotropic fun i => f (d i) := by
  have hdet : (P.map f).det ≠ 0 := by
    rw [show P.map f = f.mapMatrix P from rfl, ← RingHom.map_det]
    exact fun h => hP (f.injective (by simpa using h))
  have hmap : (P.map f)ᵀ * (M.map f) * (P.map f) = Matrix.diagonal fun i => f (d i) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPd,
      Matrix.diagonal_map (map_zero f)]
  rw [← isMatIsotropic_transpose_mul_mul_iff hdet, hmap, isMatIsotropic_diagonal_iff]

/-- The Hasse–Minkowski theorem: a symmetric rational matrix is isotropic over the rational field
as soon as it is isotropic over the real field and over every field of `p`-adic numbers. -/
theorem isMatIsotropic_rat_iff {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} (hM : M.IsSymm) :
    IsMatIsotropic M ↔
      (∀ p : Nat.Primes, IsMatIsotropic (M.map fun q : ℚ => (q : ℚ_[(p : ℕ)]))) ∧
        IsMatIsotropic (M.map fun q : ℚ => (q : ℝ)) := by
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  obtain ⟨P, d, hP, hPd⟩ := exists_transpose_mul_mul_eq_diagonal hM
  have hQ : IsMatIsotropic M ↔ IsDiagIsotropic d := by
    rw [← isMatIsotropic_transpose_mul_mul_iff hP, hPd, isMatIsotropic_diagonal_iff]
  have key : ∀ {L : Type} [Field L] [CharZero L],
      IsMatIsotropic (M.map fun q : ℚ => (q : L)) ↔ IsDiagIsotropic fun i => ((d i : ℚ) : L) := by
    intro L _ _
    simpa [Rat.coe_castHom] using isMatIsotropic_map_iff (Rat.castHom L) hP hPd
  rw [hQ, isDiagIsotropic_rat_iff d]
  exact (and_congr (forall_congr' fun _ => key) key).symm

end InverseGalois.CFT
