/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicBrauer
import InverseGalois.CFT.Brauer.CrossedProductRecognition

/-!
# Cyclic algebras along a tower of cyclic extensions

Let `K ⊆ L ⊆ L'` be a tower of fields with `L' / K` a finite cyclic Galois extension, let `σ'` be
a generator of `Gal(L'/K)` and let `σ` be its restriction to `L`.  Writing `d` for the degree of
`L' / L`, the cyclic algebra `(L / K, σ, a)` and the cyclic algebra `(L' / K, σ', a ^ d)` have the
same class in the Brauer group of `K`.

The comparison is completely explicit.  Choose an `L`-basis `b` of `L'`.  Multiplication by an
element of `L'` and the semilinear action of `σ'` are both recorded by matrices over `L` in that
basis, and inside the algebra of `d × d` matrices over `A = (L / K, σ, a)` the matrix of `σ'`
multiplied by the diagonal matrix of the symbol of `A` is a unit `U` which conjugates the embedded
copy of `L'` by `σ'` and whose `[L' : K]`-th power is the scalar `a ^ d`.  A unit with these two
properties identifies the matrix algebra with the cyclic algebra `(L' / K, σ', a ^ d)`.

## Main results

* `InverseGalois.CFT.nonempty_algEquiv_cyclicAlgebra`: a simple algebra of the right dimension
  containing a copy of `L`, together with a unit conjugating that copy by a generator of
  `Gal(L/K)` and having the right power, is a cyclic algebra.
* `InverseGalois.CFT.nonempty_algEquiv_cyclicAlgebra_matrix`: matrices over such an algebra form
  the cyclic algebra of the larger field.
* `InverseGalois.CFT.cyclicBrauerHom_pow_finrank`: the cyclic algebra of a degree-th power is
  split.
* `InverseGalois.CFT.cyclicBrauerHom_restrictNormal`: **compatibility of cyclic algebras along a
  tower**: the class of `(L / K, σ, a)` is the class of `(L' / K, σ', a ^ [L' : L])`.

## Tags

cyclic algebra, crossed product, Brauer group, inflation, class field theory
-/

universe u

open Module

namespace InverseGalois.CFT

open groupCohomology

/-! ### The copy of the splitting field as a homomorphism of algebras -/

section Incl

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {f : Gal(L/K) × Gal(L/K) → Lˣ}

/-- The copy of `L` inside a crossed product, as a homomorphism of `K`-algebras. -/
noncomputable def CrossedProduct.inclAlgHom (hf : IsMulCocycle₂ f) : L →ₐ[K] CrossedProduct hf :=
  { CrossedProduct.incl hf with
    commutes' := fun k => (CrossedProduct.algebraMap_eq k).symm }

theorem CrossedProduct.inclAlgHom_apply (hf : IsMulCocycle₂ f) (x : L) :
    CrossedProduct.inclAlgHom hf x = CrossedProduct.incl hf x := rfl

end Incl

/-! ### Discrete logarithms of small powers -/

section DiscreteLog

variable {G : Type*} [Group G] [Fintype G] {g : G}

/-- The discrete logarithm of a power of a generator with exponent below the order of the group
is that exponent. -/
theorem val_dlog_pow (hg : ∀ x, x ∈ Subgroup.zpowers g) {k : ℕ} (hk : k < Nat.card G) :
    (dlog g (g ^ k)).val = k := by
  letI := neZero_card G
  rw [dlog_pow hg, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

end DiscreteLog

/-! ### Conjugation by a power of a unit -/

section Conjugation

variable {K L A : Type u} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

/-- Conjugation by the `k`-th power of a unit implements the `k`-th power of the automorphism it
implements. -/
theorem emb_comm_pow {σ₀ : Gal(L/K)} (emb : L →ₐ[K] A) {v : A}
    (hv : ∀ x : L, emb (σ₀ x) * v = v * emb x) (k : ℕ) :
    ∀ x : L, emb ((σ₀ ^ k) x) * v ^ k = v ^ k * emb x := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have hx : (σ₀ ^ (k + 1)) x = (σ₀ ^ k) (σ₀ x) := by
      rw [pow_succ]
      rfl
    rw [hx, pow_succ, ← mul_assoc, ih (σ₀ x), mul_assoc, hv x, ← mul_assoc]

end Conjugation

/-! ### Recognising a cyclic algebra -/

section Recognition

variable {K L A : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Ring A] [Algebra K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- **Recognition of a cyclic algebra.**  A simple algebra of dimension `[L : K] ^ 2` containing a
copy of `L` and a unit which conjugates that copy by a generator `σ₀` of `Gal(L/K)` and whose
`[L : K]`-th power is the scalar `a` is the cyclic algebra `(L / K, σ₀, a)`. -/
theorem nonempty_algEquiv_cyclicAlgebra {σ₀ : Gal(L/K)}
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (a : Kˣ) (emb : L →ₐ[K] A) (u : Aˣ)
    (hu : ∀ x : L, emb (σ₀ x) * (u : A) = (u : A) * emb x)
    (hun : (u : A) ^ finrank K L = algebraMap K A (a : K))
    (hdim : finrank K A = finrank K L * finrank K L) :
    Nonempty (cyclicAlgebra hσ₀ a ≃ₐ[K] A) := by
  classical
  letI := neZero_card Gal(L/K)
  have hcard : Nat.card Gal(L/K) = finrank K L := IsGalois.card_aut_eq_finrank K L
  have hUval : ∀ g : Gal(L/K),
      ((u ^ (dlog σ₀ g).val : Aˣ) : A) = (u : A) ^ (dlog σ₀ g).val :=
    fun g => Units.val_pow_eq_pow_val u _
  have hu' : ∀ (g : Gal(L/K)) (x : L),
      emb (g x) * ((u ^ (dlog σ₀ g).val : Aˣ) : A)
        = ((u ^ (dlog σ₀ g).val : Aˣ) : A) * emb x := by
    intro g x
    have h := emb_comm_pow emb hu (dlog σ₀ g).val x
    rw [pow_val_dlog hσ₀ g] at h
    rw [hUval]
    exact h
  have hmul : ∀ g h : Gal(L/K),
      ((u ^ (dlog σ₀ g).val : Aˣ) : A) * ((u ^ (dlog σ₀ h).val : Aˣ) : A)
        = emb ((cyclicUnitCocycle σ₀ a (g, h) : Lˣ) : L)
            * ((u ^ (dlog σ₀ (g * h)).val : Aˣ) : A) := by
    intro g h
    simp only [hUval]
    rw [← pow_add, cyclicUnitCocycle_apply, dlog_mul hσ₀]
    by_cases hlt : (dlog σ₀ g).val + (dlog σ₀ h).val < Nat.card Gal(L/K)
    · rw [if_pos hlt, ZMod.val_add_of_lt hlt, map_one, one_mul]
    · rw [if_neg hlt, ZMod.val_add_of_le (Nat.not_lt.mp hlt), AlgHom.commutes, ← hun, ← hcard,
        ← pow_add]
      congr 1
      omega
  exact ⟨AlgEquiv.ofBijective
    (crossedProductAlgHom emb (fun g => u ^ (dlog σ₀ g).val)
      (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) hu' hmul)
    (crossedProductAlgHom_bijective emb (fun g => u ^ (dlog σ₀ g).val)
      (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) hu' hmul hdim)⟩

end Recognition

/-! ### Coordinate matrices in a relative basis -/

section Coord

variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [IsGalois K L]

/-- An automorphism of the large field is semilinear over the small field for its own
restriction. -/
theorem restrictNormal_smul (τ' : Gal(L'/K)) (c : L) (y : L') :
    τ' (c • y) = (τ'.restrictNormal L) c • τ' y := by
  rw [Algebra.smul_def c y, map_mul, ← AlgEquiv.restrictNormal_commutes τ' L c, ← Algebra.smul_def]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of coordinates of a family of elements of `L'` with respect to a basis. -/
def coordMatrix (b : Basis ι L L') (w : ι → L') : Matrix ι ι L := fun i j => b.repr (w j) i

omit [Fintype ι] [DecidableEq ι] in
theorem coordMatrix_apply (b : Basis ι L L') (w : ι → L') (i j : ι) :
    coordMatrix b w i j = b.repr (w j) i := rfl

omit [DecidableEq ι] in
/-- The coordinates of a linear combination. -/
theorem repr_apply_sum (b : Basis ι L L') (i : ι) (c : ι → L) (v : ι → L') :
    b.repr (∑ m, c m • v m) i = ∑ m, c m * b.repr (v m) i := by
  rw [map_sum, Finsupp.finset_sum_apply]
  exact Finset.sum_congr rfl fun m _ => by rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

omit [DecidableEq ι] in
theorem sum_repr_smul (b : Basis ι L L') (x : L') : ∑ m, b.repr x m • b m = x := by
  simp

omit [Fintype ι] in
/-- The coordinate matrix of the basis itself is the identity. -/
theorem coordMatrix_self (b : Basis ι L L') : coordMatrix b (fun j => b j) = 1 := by
  ext i j
  rw [coordMatrix_apply, Basis.repr_self_apply, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- Multiplying a family by a scalar of `L'` multiplies its coordinate matrix by the matrix of
that scalar. -/
theorem coordMatrix_smul (b : Basis ι L L') (z : L') (w : ι → L') :
    coordMatrix b (fun j => z * w j) = Algebra.leftMulMatrix b z * coordMatrix b w := by
  ext i j
  have h : z * w j = ∑ m, b.repr (w j) m • (z * b m) := by
    have h' : z * ∑ m, b.repr (w j) m • b m = ∑ m, b.repr (w j) m • (z * b m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => mul_smul_comm _ _ _
    rwa [sum_repr_smul] at h'
  rw [coordMatrix_apply, h, repr_apply_sum, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun m _ => by
    rw [Algebra.leftMulMatrix_eq_repr_mul, coordMatrix_apply, mul_comm]

omit [DecidableEq ι] in
/-- Applying an automorphism to a family multiplies its coordinate matrix, on the left by the
coordinate matrix of the image of the basis and on the right by the conjugated matrix. -/
theorem coordMatrix_map (b : Basis ι L L') (τ' : Gal(L'/K)) (w : ι → L') :
    coordMatrix b (fun j => τ' (w j))
      = coordMatrix b (fun j => τ' (b j)) * (coordMatrix b w).map (τ'.restrictNormal L) := by
  ext i j
  have h : τ' (w j) = ∑ m, (τ'.restrictNormal L) (b.repr (w j) m) • τ' (b m) := by
    have h' : τ' (∑ m, b.repr (w j) m • b m)
        = ∑ m, (τ'.restrictNormal L) (b.repr (w j) m) • τ' (b m) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun m _ => restrictNormal_smul τ' _ _
    rwa [sum_repr_smul] at h'
  rw [coordMatrix_apply, h, repr_apply_sum, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun m _ => by
    rw [coordMatrix_apply, Matrix.map_apply, coordMatrix_apply, mul_comm]

end Coord

/-! ### Matrices over a cyclic algebra of the small field -/

section Tower

variable {K L L' A : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [FiniteDimensional K L']
  [IsGalois K L] [IsGalois K L'] [Ring A] [Algebra K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- **Matrices over a cyclic algebra of an intermediate field.**  If `A` is a simple algebra of
dimension `[L : K] ^ 2` containing a copy of `L` and a unit conjugating that copy by the
restriction of `σ'` whose `[L : K]`-th power is the scalar `a`, then the algebra of
`[L' : L] × [L' : L]` matrices over `A` is the cyclic algebra `(L' / K, σ', a ^ [L' : L])`. -/
theorem nonempty_algEquiv_cyclicAlgebra_matrix {σ' : Gal(L'/K)}
    (hσ' : ∀ x : Gal(L'/K), x ∈ Subgroup.zpowers σ') (a : Kˣ) (emb : L →ₐ[K] A) (u : Aˣ)
    (hu : ∀ x : L, emb ((σ'.restrictNormal L) x) * (u : A) = (u : A) * emb x)
    (hun : (u : A) ^ finrank K L = algebraMap K A (a : K))
    (hdim : finrank K A = finrank K L * finrank K L) :
    Nonempty (cyclicAlgebra hσ' (a ^ finrank L L') ≃ₐ[K]
      Matrix (Fin (finrank L L')) (Fin (finrank L L')) A) := by
  classical
  haveI : Module.Finite L L' := FiniteDimensional.right K L L'
  haveI : Nonempty (Fin (finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hfin : finrank K L' = finrank K L * finrank L L' :=
    (Module.finrank_mul_finrank K L L').symm
  obtain ⟨b⟩ : Nonempty (Basis (Fin (finrank L L')) L L') := ⟨Module.finBasis L L'⟩
  set ρ : L' →ₐ[K] Matrix (Fin (finrank L L')) (Fin (finrank L L')) L :=
    (Algebra.leftMulMatrix b).restrictScalars K with hρ
  have hρ_apply : ∀ y : L', ρ y = Algebra.leftMulMatrix b y := fun y => by rw [hρ]; rfl
  have hlm : ∀ z : L', Algebra.leftMulMatrix b z = coordMatrix b (fun j => z * b j) := by
    intro z
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, coordMatrix_apply]
  set S : Matrix (Fin (finrank L L')) (Fin (finrank L L')) L :=
    coordMatrix b (fun j => σ' (b j)) with hS
  set D : Matrix (Fin (finrank L L')) (Fin (finrank L L')) A :=
    Matrix.diagonal (fun _ => (u : A)) with hD
  set U₀ : Matrix (Fin (finrank L L')) (Fin (finrank L L')) A := emb.mapMatrix S * D with hU₀
  set emb' : L' →ₐ[K] Matrix (Fin (finrank L L')) (Fin (finrank L L')) A :=
    emb.mapMatrix.comp ρ with hemb'
  -- the diagonal matrix conjugates the entries by the restriction of `σ'`
  have hDcomm : ∀ X : Matrix (Fin (finrank L L')) (Fin (finrank L L')) L,
      D * emb.mapMatrix X = emb.mapMatrix (X.map (σ'.restrictNormal L)) * D := by
    intro X
    ext i j
    rw [hD, Matrix.diagonal_mul, Matrix.mul_diagonal, AlgHom.mapMatrix_apply,
      AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
    exact (hu (X i j)).symm
  have hDpow : ∀ (k : ℕ) (X : Matrix (Fin (finrank L L')) (Fin (finrank L L')) L),
      D ^ k * emb.mapMatrix X
        = emb.mapMatrix (X.map ⇑((σ'.restrictNormal L) ^ k)) * D ^ k := by
    intro k
    induction k with
    | zero =>
      intro X
      have h : X.map ⇑((σ'.restrictNormal L) ^ 0) = X := by
        ext i j
        rw [Matrix.map_apply, pow_zero]
        rfl
      rw [h, pow_zero, one_mul, mul_one]
    | succ k ih =>
      intro X
      have hmm : (X.map ⇑(σ'.restrictNormal L)).map ⇑((σ'.restrictNormal L) ^ k)
          = X.map ⇑((σ'.restrictNormal L) ^ (k + 1)) := by
        ext i j
        simp only [Matrix.map_apply]
        rw [pow_succ]
        rfl
      calc D ^ (k + 1) * emb.mapMatrix X
          = D ^ k * (D * emb.mapMatrix X) := by rw [pow_succ, mul_assoc]
        _ = D ^ k * (emb.mapMatrix (X.map (σ'.restrictNormal L)) * D) := by rw [hDcomm X]
        _ = (D ^ k * emb.mapMatrix (X.map (σ'.restrictNormal L))) * D := by rw [mul_assoc]
        _ = emb.mapMatrix ((X.map ⇑(σ'.restrictNormal L)).map ⇑((σ'.restrictNormal L) ^ k))
              * D ^ k * D := by rw [ih (X.map (σ'.restrictNormal L))]
        _ = emb.mapMatrix (X.map ⇑((σ'.restrictNormal L) ^ (k + 1))) * D ^ (k + 1) := by
              rw [hmm, mul_assoc, ← pow_succ]
  -- the semilinear identity
  have hsemi : ∀ x : L', ρ (σ' x) * S = S * (ρ x).map (σ'.restrictNormal L) := by
    intro x
    have h1 : ρ (σ' x) * S = coordMatrix b (fun j => σ' x * σ' (b j)) := by
      rw [hρ_apply, hS, ← coordMatrix_smul]
    have h2 : S * (ρ x).map (σ'.restrictNormal L) = coordMatrix b (fun j => σ' (x * b j)) := by
      rw [hρ_apply, hlm, hS, ← coordMatrix_map b σ' (fun j => x * b j)]
    rw [h1, h2]
    exact congrArg _ (funext fun j => (map_mul σ' x (b j)).symm)
  -- powers of the candidate unit
  have hUpow : ∀ k : ℕ,
      U₀ ^ k = emb.mapMatrix (coordMatrix b (fun j => (σ' ^ k) (b j))) * D ^ k := by
    intro k
    induction k with
    | zero =>
      have h : coordMatrix b (fun j => (σ' ^ 0) (b j)) = 1 := by
        have h0 : (fun j => (σ' ^ 0) (b j)) = fun j => b j := by
          funext j
          rw [pow_zero]
          rfl
        rw [h0]
        exact coordMatrix_self b
      rw [h, map_one, pow_zero, pow_zero, one_mul]
    | succ k ih =>
      have h2 : ((σ' ^ k).restrictNormal L) = (σ'.restrictNormal L) ^ k :=
        map_pow (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L) σ' k
      have hP : coordMatrix b (fun j => (σ' ^ (k + 1)) (b j))
          = coordMatrix b (fun j => (σ' ^ k) (b j)) * S.map ⇑((σ'.restrictNormal L) ^ k) := by
        have h1 : (fun j => (σ' ^ (k + 1)) (b j)) = fun j => (σ' ^ k) (σ' (b j)) := by
          funext j
          rw [pow_succ]
          rfl
        rw [h1, coordMatrix_map b (σ' ^ k) (fun j => σ' (b j)), ← hS, h2]
      calc U₀ ^ (k + 1)
          = emb.mapMatrix (coordMatrix b (fun j => (σ' ^ k) (b j))) * D ^ k
              * (emb.mapMatrix S * D) := by rw [pow_succ, ih, hU₀]
        _ = emb.mapMatrix (coordMatrix b (fun j => (σ' ^ k) (b j)))
              * (D ^ k * emb.mapMatrix S) * D := by simp only [mul_assoc]
        _ = emb.mapMatrix (coordMatrix b (fun j => (σ' ^ k) (b j)))
              * (emb.mapMatrix (S.map ⇑((σ'.restrictNormal L) ^ k)) * D ^ k) * D := by
              rw [hDpow k S]
        _ = emb.mapMatrix (coordMatrix b (fun j => (σ' ^ k) (b j))
              * S.map ⇑((σ'.restrictNormal L) ^ k)) * (D ^ k * D) := by
              rw [map_mul]
              simp only [mul_assoc]
        _ = emb.mapMatrix (coordMatrix b (fun j => (σ' ^ (k + 1)) (b j))) * D ^ (k + 1) := by
              rw [hP, pow_succ]
  -- the top power is the scalar `a ^ [L' : L]`
  have hUcard : U₀ ^ finrank K L'
      = algebraMap K (Matrix (Fin (finrank L L')) (Fin (finrank L L')) A)
          ((a ^ finrank L L' : Kˣ) : K) := by
    have hcard : Nat.card Gal(L'/K) = finrank K L' := IsGalois.card_aut_eq_finrank K L'
    have hone : σ' ^ finrank K L' = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hP1 : coordMatrix b (fun j => (σ' ^ finrank K L') (b j)) = 1 := by
      rw [hone]
      exact coordMatrix_self b
    have hu2 : (u : A) ^ finrank K L' = algebraMap K A ((a ^ finrank L L' : Kˣ) : K) := by
      rw [hfin, pow_mul, hun, Units.val_pow_eq_pow_val, map_pow]
    rw [hUpow, hP1, map_one, one_mul, hD, Matrix.diagonal_pow, Matrix.algebraMap_eq_diagonal]
    congr 1
    funext i
    rw [Pi.pow_apply, Pi.algebraMap_apply]
    exact hu2
  -- the candidate is a unit
  have hUunit : IsUnit U₀ := by
    refine (isUnit_pow_iff (n := finrank K L') ?_).mp ?_
    · exact Module.finrank_pos.ne'
    · rw [hUcard]
      exact (Units.map (algebraMap K
        (Matrix (Fin (finrank L L')) (Fin (finrank L L')) A)).toMonoidHom
          (a ^ finrank L L')).isUnit
  obtain ⟨U, hUval⟩ :
      ∃ U : (Matrix (Fin (finrank L L')) (Fin (finrank L L')) A)ˣ,
        (U : Matrix (Fin (finrank L L')) (Fin (finrank L L')) A) = U₀ :=
    ⟨hUunit.unit, hUunit.unit_spec⟩
  -- the unit conjugates the copy of `L'` by `σ'`
  have hu'' : ∀ x : L', emb' (σ' x) * (U : Matrix (Fin (finrank L L')) (Fin (finrank L L')) A)
      = (U : Matrix (Fin (finrank L L')) (Fin (finrank L L')) A) * emb' x := by
    intro x
    rw [hUval]
    simp only [hemb', AlgHom.comp_apply, hU₀]
    calc emb.mapMatrix (ρ (σ' x)) * (emb.mapMatrix S * D)
        = emb.mapMatrix (ρ (σ' x) * S) * D := by rw [map_mul, mul_assoc]
      _ = emb.mapMatrix (S * (ρ x).map (σ'.restrictNormal L)) * D := by rw [hsemi x]
      _ = emb.mapMatrix S * (emb.mapMatrix ((ρ x).map (σ'.restrictNormal L)) * D) := by
            rw [map_mul, mul_assoc]
      _ = emb.mapMatrix S * (D * emb.mapMatrix (ρ x)) := by rw [← hDcomm (ρ x)]
      _ = emb.mapMatrix S * D * emb.mapMatrix (ρ x) := by rw [mul_assoc]
  have hdim' : finrank K (Matrix (Fin (finrank L L')) (Fin (finrank L L')) A)
      = finrank K L' * finrank K L' := by
    rw [Module.finrank_matrix, Fintype.card_fin, hdim, hfin]
    ring
  refine nonempty_algEquiv_cyclicAlgebra hσ' (a ^ finrank L L') emb' U hu'' ?_ hdim'
  rw [hUval]
  exact hUcard

end Tower

/-! ### The symbol of a cyclic algebra -/

section Symbol

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ₀ : Gal(L/K)}

omit [IsGalois K L] in
/-- The cyclic cocycle is trivial at the pair of identities. -/
theorem cyclicUnitCocycle_one_one (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (a : Kˣ) :
    cyclicUnitCocycle σ₀ a (1, 1) = 1 := by
  have h0 : (dlog σ₀ (1 : Gal(L/K))).val = 0 := by
    have h := val_dlog_pow hσ₀ (k := 0) Nat.card_pos
    rwa [pow_zero] at h
  refine Units.ext ?_
  rw [cyclicUnitCocycle_apply, h0, Units.val_one]
  split_ifs with h
  · rfl
  · have := Nat.card_pos (α := Gal(L/K))
    omega

omit [IsGalois K L] in
/-- Small powers of the symbol of a cyclic algebra are the symbols of the powers of the
generator. -/
theorem single_one_pow (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (a : Kˣ)
    (hn : 2 ≤ Nat.card Gal(L/K)) : ∀ k : ℕ, k < Nat.card Gal(L/K) →
      CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) σ₀ 1 ^ k
        = CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) (σ₀ ^ k) 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [pow_zero, pow_zero, CrossedProduct.one_def]
    refine CrossedProduct.single_congr ?_
    rw [cyclicUnitCocycle_one_one hσ₀ a]
    simp
  | succ k ih =>
    intro hk
    have hk' : k < Nat.card Gal(L/K) := by omega
    have h1 : (dlog σ₀ σ₀).val = 1 := by
      have h := val_dlog_pow hσ₀ (k := 1) (by omega)
      rwa [pow_one] at h
    have hkv : (dlog σ₀ (σ₀ ^ k)).val = k := val_dlog_pow hσ₀ hk'
    rw [pow_succ, ih hk', CrossedProduct.single_mul_single, ← pow_succ]
    refine CrossedProduct.single_congr ?_
    rw [map_one, one_mul, one_mul, cyclicUnitCocycle_apply, hkv, h1, if_pos hk]

omit [IsGalois K L] in
/-- The top power of the symbol of a cyclic algebra is the defining scalar. -/
theorem single_one_pow_card (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (a : Kˣ)
    (hn : 2 ≤ Nat.card Gal(L/K)) :
    CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) σ₀ 1 ^ Nat.card Gal(L/K)
      = algebraMap K (cyclicAlgebra hσ₀ a) (a : K) := by
  have hprev := single_one_pow hσ₀ a hn (Nat.card Gal(L/K) - 1) (by omega)
  have h1 : (dlog σ₀ σ₀).val = 1 := by
    have h := val_dlog_pow hσ₀ (k := 1) (by omega)
    rwa [pow_one] at h
  have hkv : (dlog σ₀ (σ₀ ^ (Nat.card Gal(L/K) - 1))).val = Nat.card Gal(L/K) - 1 :=
    val_dlog_pow hσ₀ (by omega)
  have hsucc : Nat.card Gal(L/K) - 1 + 1 = Nat.card Gal(L/K) := by omega
  have hone : σ₀ ^ (Nat.card Gal(L/K) - 1) * σ₀ = 1 := by
    rw [← pow_succ, hsucc]
    exact pow_card_eq_one'
  calc CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) σ₀ 1 ^ Nat.card Gal(L/K)
      = CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) σ₀ 1
            ^ (Nat.card Gal(L/K) - 1)
          * CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) σ₀ 1 := by
        rw [← pow_succ, hsucc]
    _ = CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)
            (σ₀ ^ (Nat.card Gal(L/K) - 1)) 1
          * CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) σ₀ 1 := by rw [hprev]
    _ = CrossedProduct.single (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) 1
          (algebraMap K L (a : K)) := by
        rw [CrossedProduct.single_mul_single, hone]
        refine CrossedProduct.single_congr ?_
        rw [map_one, one_mul, one_mul, cyclicUnitCocycle_apply, hkv, h1, if_neg (by omega)]
    _ = algebraMap K (cyclicAlgebra hσ₀ a) (a : K) := by
        rw [CrossedProduct.algebraMap_eq, CrossedProduct.incl_eq_single]
        refine CrossedProduct.single_congr ?_
        rw [cyclicUnitCocycle_one_one hσ₀ a]
        simp

/-- A cyclic algebra of degree at least two contains a unit conjugating the copy of `L` by the
generator whose `[L : K]`-th power is the defining scalar. -/
theorem exists_unit_cyclicAlgebra (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (a : Kˣ)
    (hn : 2 ≤ finrank K L) :
    ∃ u : (cyclicAlgebra hσ₀ a)ˣ,
      (∀ x : L,
        CrossedProduct.inclAlgHom (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) (σ₀ x)
            * (u : cyclicAlgebra hσ₀ a)
          = (u : cyclicAlgebra hσ₀ a)
              * CrossedProduct.inclAlgHom (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) x) ∧
      (u : cyclicAlgebra hσ₀ a) ^ finrank K L = algebraMap K (cyclicAlgebra hσ₀ a) (a : K) := by
  have hcard : Nat.card Gal(L/K) = finrank K L := IsGalois.card_aut_eq_finrank K L
  refine ⟨(CrossedProduct.isUnit_single_one (isMulCocycle₂_cyclicUnitCocycle hσ₀ a) σ₀).unit,
    fun x => ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact (CrossedProduct.mul_single_one σ₀ x).symm
  · rw [IsUnit.unit_spec, ← hcard]
    exact single_one_pow_card hσ₀ a (by omega)

end Symbol

/-! ### Compatibility of cyclic algebras along a tower -/

section Descent

variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [FiniteDimensional K L']
  [IsGalois K L] [IsGalois K L']

omit [FiniteDimensional K L] [FiniteDimensional K L'] in
/-- The restriction of a generator of the Galois group of the larger extension generates the
Galois group of the smaller one. -/
theorem forall_mem_zpowers_restrictNormal {σ' : Gal(L'/K)}
    (hσ' : ∀ x : Gal(L'/K), x ∈ Subgroup.zpowers σ') (τ : Gal(L/K)) :
    τ ∈ Subgroup.zpowers (σ'.restrictNormal L) := by
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := L') τ
  obtain ⟨k, hk⟩ := hσ' τ'
  have hk' : σ' ^ k = τ' := hk
  refine ⟨k, ?_⟩
  show (σ'.restrictNormal L) ^ k = (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L) τ'
  exact (map_zpow (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L) σ' k).symm.trans
    (congrArg _ hk')

/-- The cyclic algebra whose scalar is a degree-th power is split. -/
theorem cyclicBrauerHom_pow_finrank {σ₀ : Gal(L/K)}
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (a : Kˣ) :
    cyclicBrauerHom hσ₀ (a ^ finrank K L) = 1 := by
  rw [← MonoidHom.mem_ker, mem_ker_cyclicBrauerHom_iff]
  refine ⟨Units.map (algebraMap K L).toMonoidHom a, ?_⟩
  have h : ((Units.map (algebraMap K L).toMonoidHom a : Lˣ) : L) = algebraMap K L (a : K) := rfl
  rw [h, Algebra.norm_algebraMap, Units.val_pow_eq_pow_val]

/-- **Compatibility of cyclic algebras along a tower.**  For a tower `K ⊆ L ⊆ L'` with `L' / K`
cyclic with generator `σ'`, the cyclic algebra of `L / K` for the restriction of `σ'` and a scalar
`a` has the Brauer class of the cyclic algebra of `L' / K` for `σ'` and the scalar
`a ^ [L' : L]`. -/
theorem cyclicBrauerHom_restrictNormal {σ' : Gal(L'/K)}
    (hσ' : ∀ x : Gal(L'/K), x ∈ Subgroup.zpowers σ') (a : Kˣ) :
    cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := L) hσ') a
      = cyclicBrauerHom hσ' (a ^ finrank L L') := by
  haveI : Module.Finite L L' := FiniteDimensional.right K L L'
  have hfin : finrank K L * finrank L L' = finrank K L' := Module.finrank_mul_finrank K L L'
  rcases Nat.lt_or_ge (finrank K L) 2 with h1 | h2
  · have he : finrank K L = 1 := by
      have hp : 0 < finrank K L := Module.finrank_pos
      omega
    have hA : cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := L) hσ') a = 1 := by
      have h := cyclicBrauerHom_pow_finrank (forall_mem_zpowers_restrictNormal (L := L) hσ') a
      rwa [he, pow_one] at h
    have hB : cyclicBrauerHom hσ' (a ^ finrank L L') = 1 := by
      have h := cyclicBrauerHom_pow_finrank hσ' a
      rwa [← hfin, he, one_mul] at h
    rw [hA, hB]
  · obtain ⟨u, hu, hun⟩ :=
      exists_unit_cyclicAlgebra (forall_mem_zpowers_restrictNormal (L := L) hσ') a h2
    have hdim : finrank K (cyclicAlgebra (forall_mem_zpowers_restrictNormal (L := L) hσ') a)
        = finrank K L * finrank K L := by
      rw [CrossedProduct.finrank_eq, IsGalois.card_aut_eq_finrank K L, sq]
    obtain ⟨e⟩ := nonempty_algEquiv_cyclicAlgebra_matrix hσ' a
      (CrossedProduct.inclAlgHom
        (isMulCocycle₂_cyclicUnitCocycle (forall_mem_zpowers_restrictNormal (L := L) hσ') a))
      u hu hun hdim
    have hd : finrank L L' ≠ 0 := Module.finrank_pos.ne'
    rw [cyclicBrauerHom_apply, cyclicBrauerHom_apply]
    exact (Quotient.sound (IsBrauerEquivalent.of_algEquiv_matrix hd e)).symm

end Descent

end InverseGalois.CFT
