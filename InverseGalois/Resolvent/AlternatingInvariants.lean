/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Alternating invariants of `ℚ[x₁,…,xₙ]` (work in progress)

The invariant theory underlying the descent of the `Aₙ`-orbit resolvent to `ℚ(T)`: the ring of
`Aₙ`-invariants of `ℚ[x₁,…,xₙ]` is `ℚ[e₁,…,eₙ][δ]`, where `δ = ∏_{i<j}(xⱼ − xᵢ)` is the
Vandermonde (a square root of the discriminant).  Concretely, every `Aₙ`-invariant polynomial is
`s + δ · t` with `s, t` symmetric.

This is the `Aₙ`-analogue of the fundamental theorem of symmetric polynomials
(`MvPolynomial.esymmAlgHom_surjective`), and is not in Mathlib.  It reduces to:

* `exists_symm_add_alternating` — every `Aₙ`-invariant splits as `symmetric + alternating`
  (using `Sₙ = Aₙ ⊔ Aₙ·τ`: for an odd `τ`, `τ · f = τ₀ · f` for any odd `τ₀`);
* `exists_symmetric_of_isAlternating` — every alternating polynomial is `δ · (symmetric)` (an
  alternating polynomial vanishes on each hyperplane `xᵢ = xⱼ`, hence is divisible by each
  `xⱼ − xᵢ`, hence by their product `δ`, and the quotient is symmetric).

The single remaining `sorry` is `vander_dvd_of_isAlternating` (the `δ`-divisibility of an
alternating polynomial — the hard `MvPolynomial`-UFD content).
-/

open Polynomial MvPolynomial

noncomputable section

namespace AlternatingInvariants

variable {n : ℕ}

/-- The Vandermonde polynomial `δ = ∏_{i<j} (Xⱼ − Xᵢ)` in `ℚ[x₁,…,xₙ]`. -/
def vander (n : ℕ) : MvPolynomial (Fin n) ℚ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (X j - X i)

/-- A polynomial is *alternating* if renaming the variables by `σ` multiplies it by `sign σ`. -/
def IsAlternating (p : MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), rename σ p = ((Equiv.Perm.sign σ : ℤ) : ℚ) • p

/-- The Vandermonde polynomial is alternating. -/
theorem vander_isAlternating : IsAlternating (vander n) := by
  intro σ
  show rename σ (vander n) = ((Equiv.Perm.sign σ : ℤ) : ℚ) • vander n
  simp only [vander]
  simp
  let v : Fin n → MvPolynomial (Fin n) ℚ := fun i => MvPolynomial.X i
  have vandermonde_comp_perm :
      Matrix.vandermonde (v ∘ σ) = Matrix.submatrix (Matrix.vandermonde v) σ id := by
    ext i j
    simp [Matrix.vandermonde_apply]
  have det_vandermonde_perm : Matrix.det (Matrix.vandermonde (v ∘ σ)) =
      ↑↑(Equiv.Perm.sign σ) * Matrix.det (Matrix.vandermonde v) := by
    rw [vandermonde_comp_perm, Matrix.det_permute]
  have hv' : (Matrix.vandermonde (v ∘ σ)).det =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((v ∘ σ) j - (v ∘ σ) i) :=
    Matrix.det_vandermonde _
  have hv : (Matrix.vandermonde v).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) :=
    Matrix.det_vandermonde _
  rw [hv'] at det_vandermonde_perm
  rw [hv] at det_vandermonde_perm
  simp [v] at det_vandermonde_perm
  rw [Algebra.smul_def]
  rw [map_intCast]
  exact det_vandermonde_perm

/-- The shear automorphism `X i ↦ X i - X j`, `X k ↦ X k` (k ≠ i), for `i ≠ j`. -/
def shear (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial (Fin n) ℚ ≃ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  AlgEquiv.ofAlgHom
    (aeval (fun k => if k = i then X i - X j else X k))
    (aeval (fun k => if k = i then X i + X j else X k))
    (by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.coe_id, id_eq]
      rcases eq_or_ne k i with rfl | hk
      · rw [if_pos rfl, map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
          if_pos rfl, if_neg hij.symm]
        ring
      · rw [if_neg hk, MvPolynomial.aeval_X, if_neg hk])
    (by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, AlgHom.coe_id, id_eq]
      rcases eq_or_ne k i with rfl | hk
      · rw [if_pos rfl, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
          if_pos rfl, if_neg hij.symm]
        ring
      · rw [if_neg hk, MvPolynomial.aeval_X, if_neg hk])

theorem shear_X_self {i j : Fin n} (hij : i ≠ j) :
    shear i j hij (X i) = X i - X j := by
  simp [shear]

/-- `X i - X j` is prime in `ℚ[x₁,…,xₙ]` for `i ≠ j` (it is the image of the prime `X i` under
the shear automorphism). -/
theorem prime_X_sub_X {i j : Fin n} (hij : i ≠ j) :
    Prime (X i - X j : MvPolynomial (Fin n) ℚ) := by
  rw [← shear_X_self hij]
  exact (MulEquiv.prime_iff (shear i j hij).toMulEquiv).mpr MvPolynomial.X_prime

/-- Distinct ordered pairs give relatively prime linear factors: if `{i,j} ≠ {k,l}` then
`X j - X i` and `X l - X k` share no common non-unit factor (evaluate at a point where the first
vanishes but the second does not). -/
theorem isRelPrime_X_sub_X_of_ne {i j k l : Fin n} (hij : i < j) (hkl : k < l)
    (hne : (i, j) ≠ (k, l)) :
    IsRelPrime (X j - X i : MvPolynomial (Fin n) ℚ) (X l - X k) := by
  have hp1 : Prime (X j - X i : MvPolynomial (Fin n) ℚ) := prime_X_sub_X (ne_of_gt hij)
  rw [hp1.irreducible.isRelPrime_iff_not_dvd]
  intro hdvd
  have hcast : ∀ a b : Fin n, ((a : ℕ) : ℚ) = ((b : ℕ) : ℚ) → a = b :=
    fun a b h => Fin.val_injective (Nat.cast_injective h)
  set v : Fin n → ℚ := fun m => if m = j then ((i : ℕ) : ℚ) else ((m : ℕ) : ℚ) with hv
  have hmap := map_dvd (MvPolynomial.aeval v) hdvd
  simp only [map_sub, MvPolynomial.aeval_X] at hmap
  have hvj : v j = ((i : ℕ) : ℚ) := by simp [hv]
  have hvi : v i = ((i : ℕ) : ℚ) := by simp [hv]
  rw [hvj, hvi, sub_self, zero_dvd_iff, sub_eq_zero] at hmap
  rcases eq_or_ne l j with rfl | hlj
  · have hkl' : k ≠ l := ne_of_lt hkl
    have hvk : v k = ((k : ℕ) : ℚ) := by simp [hv, hkl']
    rw [hvj, hvk] at hmap
    exact hne (by rw [hcast i k hmap])
  · rcases eq_or_ne k j with rfl | hkj
    · have hvl : v l = ((l : ℕ) : ℚ) := by simp [hv, hlj]
      rw [hvl, hvj] at hmap
      rw [hcast l i hmap] at hkl
      exact absurd hkl (not_lt.mpr hij.le)
    · have hvl : v l = ((l : ℕ) : ℚ) := by simp [hv, hlj]
      have hvk : v k = ((k : ℕ) : ℚ) := by simp [hv, hkj]
      rw [hvl, hvk] at hmap
      exact absurd (hcast l k hmap) (ne_of_gt hkl)

/-- Each linear factor `X i - X j` (`i ≠ j`) divides an alternating polynomial `p`: the
substitution `X i ↦ X j` sends `p` to `0` (since a transposition negates `p`), hence
`p ∈ (X i - X j)`. -/
theorem X_sub_X_dvd_of_isAlternating {i j : Fin n} (hij : i ≠ j)
    {p : MvPolynomial (Fin n) ℚ} (hp : IsAlternating p) :
    (X i - X j) ∣ p := by
  have hswap : rename (Equiv.swap i j) p = -p := by
    have h := hp (Equiv.swap i j)
    rw [Equiv.Perm.sign_swap hij] at h
    simpa using h
  let g : Fin n → MvPolynomial (Fin n) ℚ := fun k => if k = i then X j else X k
  have key : (MvPolynomial.aeval g).comp (rename (Equiv.swap i j)) =
      (MvPolynomial.aeval g : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ) := by
    apply MvPolynomial.algHom_ext
    intro m
    simp only [AlgHom.comp_apply, rename_X, MvPolynomial.aeval_X, g]
    rcases eq_or_ne m i with rfl | hmi
    · rw [Equiv.swap_apply_left, if_neg hij.symm, if_pos rfl]
    · rcases eq_or_ne m j with rfl | hmj
      · rw [Equiv.swap_apply_right, if_pos rfl, if_neg hmi]
      · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]
  have hφp : MvPolynomial.aeval g p = 0 := by
    have h1 : MvPolynomial.aeval g (rename (Equiv.swap i j) p) = MvPolynomial.aeval g p := by
      rw [← AlgHom.comp_apply, key]
    rw [hswap, map_neg] at h1
    have hsum : MvPolynomial.aeval g p + MvPolynomial.aeval g p = 0 :=
      neg_eq_iff_add_eq_zero.mp h1
    have h2 : (2 : MvPolynomial (Fin n) ℚ) * MvPolynomial.aeval g p = 0 := by
      rw [two_mul]; exact hsum
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  rw [← Ideal.mem_span_singleton]
  set I : Ideal (MvPolynomial (Fin n) ℚ) := Ideal.span {X i - X j} with hI
  have hπ : (Ideal.Quotient.mkₐ ℚ I).comp (MvPolynomial.aeval g) = Ideal.Quotient.mkₐ ℚ I := by
    apply MvPolynomial.algHom_ext
    intro m
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, g]
    split_ifs with hm
    · subst hm
      simp only [Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
      exact ⟨-1, by ring⟩
    · rfl
  have hp0 : Ideal.Quotient.mkₐ ℚ I p = 0 := by
    have hc := AlgHom.congr_fun hπ p
    rw [AlgHom.comp_apply, hφp, map_zero] at hc
    exact hc.symm
  rw [Ideal.Quotient.mkₐ_eq_mk] at hp0
  exact Ideal.Quotient.eq_zero_iff_mem.mp hp0

/-- An alternating polynomial is divisible by the Vandermonde polynomial: it vanishes on each
hyperplane `xᵢ = xⱼ`, so each `Xⱼ − Xᵢ` divides it, and these are pairwise coprime. -/
theorem vander_dvd_of_isAlternating {p : MvPolynomial (Fin n) ℚ} (hp : IsAlternating p) :
    vander n ∣ p := by
  rw [vander, Finset.prod_sigma']
  apply Finset.prod_dvd_of_isRelPrime
  · intro x hx y hy hxy
    obtain ⟨i, j⟩ := x
    obtain ⟨k, l⟩ := y
    simp only [Finset.coe_sigma, Finset.coe_univ, Set.mem_sigma_iff, Set.mem_univ,
      Finset.mem_coe, Finset.mem_Ioi, true_and] at hx hy
    exact isRelPrime_X_sub_X_of_ne hx hy (by simpa using hxy)
  · intro x hx
    obtain ⟨i, j⟩ := x
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hx
    exact X_sub_X_dvd_of_isAlternating (ne_of_gt hx) hp

/-- An alternating polynomial is the Vandermonde times a symmetric polynomial. -/
theorem exists_symmetric_of_isAlternating {p : MvPolynomial (Fin n) ℚ} (hp : IsAlternating p) :
    ∃ q : MvPolynomial (Fin n) ℚ, q.IsSymmetric ∧ p = vander n * q := by
  obtain ⟨q, hq⟩ := vander_dvd_of_isAlternating hp
  use q
  constructor
  · rw [MvPolynomial.IsSymmetric]
    intro σ
    have hp' := hp σ
    have hvander := vander_isAlternating σ
    rw [hq] at hp'
    rw [map_mul] at hp'
    rw [hvander] at hp'
    rw [Algebra.smul_mul_assoc] at hp'
    have hsign_ne : (↑↑(Equiv.Perm.sign σ) : ℚ) ≠ 0 := by
      have h1 := Int.units_eq_one_or (Equiv.Perm.sign σ)
      rcases h1 with h | h <;> simp [h]
    have hp'' : vander n * rename σ q = vander n * q := by
      exact smul_right_injective _ hsign_ne hp'
    have hvander_ne : vander n ≠ 0 := by
      unfold vander
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      have hlt : i < j := Finset.mem_Ioi.mp hj
      have h : (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin n) ℚ) ≠ 0 := by
        intro heq
        have := congr_arg
          (MvPolynomial.aeval (fun k => if k = i then (0 : ℚ) else 1 : Fin n → ℚ)) heq
        simp at this
        exact hlt.ne this.symm
      exact h
    exact mul_right_injective₀ hvander_ne hp''
  · exact hq

/-- An `Aₙ`-invariant polynomial splits as a symmetric part plus an alternating part.

For an odd permutation `τ₀`, set `s = (p + τ₀·p)/2` and `a = (p − τ₀·p)/2`; since `Sₙ = Aₙ ⊔ Aₙτ₀`
and `p` is `Aₙ`-invariant, `s` is symmetric and `a` is alternating. -/
theorem exists_symm_add_alternating (hn : 2 ≤ n) {p : MvPolynomial (Fin n) ℚ}
    (hp : ∀ σ ∈ alternatingGroup (Fin n), rename σ p = p) :
    ∃ s a : MvPolynomial (Fin n) ℚ, s.IsSymmetric ∧ IsAlternating a ∧ p = s + a := by
  have h2 : 2 ≤ n := hn
  have : ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = -1 := by
    use Equiv.swap ⟨0, by linarith⟩ ⟨1, by linarith⟩
    simp
  obtain ⟨τ₀, hτ₀⟩ := this
  let s := (1/2 : ℚ) • (p + rename τ₀ p)
  let a := (1/2 : ℚ) • (p - rename τ₀ p)
  refine ⟨s, a, ?_, ?_, ?_⟩
  · intro σ
    simp only [s]
    have hrename_smul : ∀ c : ℚ, ∀ q : MvPolynomial (Fin n) ℚ,
        rename σ (c • q) = c • rename σ q := fun c q => map_smul (MvPolynomial.rename σ) c q
    have hrename_add : ∀ q r : MvPolynomial (Fin n) ℚ,
        rename σ (q + r) = rename σ q + rename σ r := fun q r => map_add (MvPolynomial.rename σ) q r
    have hrename_rename : ∀ τ : Equiv.Perm (Fin n), ∀ q : MvPolynomial (Fin n) ℚ,
        rename σ (rename τ q) = rename (σ * τ) q := by
      intro τ q
      exact MvPolynomial.rename_rename τ σ q
    simp [hrename_smul, hrename_add, hrename_rename]
    by_cases hσ : σ ∈ alternatingGroup (Fin n)
    · have h1 : rename σ p = p := hp σ hσ
      have hσ' : τ₀⁻¹ * σ * τ₀ ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
        simp [hσ]
      have h2 : rename (τ₀⁻¹ * σ * τ₀) p = p := hp _ hσ'
      rw [h1]
      have h3 : rename (↑τ₀⁻¹) (rename (σ * τ₀) p) = p := by
        rw [rename_rename]
        exact h2
      have h4 : rename (σ * τ₀) p = rename τ₀ p := by
        have eq1 := congrArg (rename τ₀) h3
        rw [rename_rename] at eq1
        simp at eq1
        exact eq1
      simp [← Equiv.Perm.coe_mul]
      rw [h4]
    · have hσ_odd : Equiv.Perm.sign σ = -1 := by
        have h := Int.units_eq_one_or (Equiv.Perm.sign σ)
        rcases h with h | h <;> simp_all [Equiv.Perm.mem_alternatingGroup]
      have hστ₀_even : Equiv.Perm.sign (σ * τ₀) = 1 := by simp [hσ_odd, hτ₀]
      have hστ₀ : σ * τ₀ ∈ alternatingGroup (Fin n) := by
        simp [Equiv.Perm.mem_alternatingGroup, hστ₀_even]
      have hσinvτ₀_even : Equiv.Perm.sign (σ⁻¹ * τ₀) = 1 := by simp [hσ_odd, hτ₀]
      have hσinvτ₀ : σ⁻¹ * τ₀ ∈ alternatingGroup (Fin n) := by
        simp [Equiv.Perm.mem_alternatingGroup, hσinvτ₀_even]
      have h2 : rename (σ⁻¹ * τ₀) p = p := hp _ hσinvτ₀
      have h3 : rename (↑σ⁻¹) (rename τ₀ p) = p := by
        rw [rename_rename]
        exact h2
      have h4 : rename τ₀ p = rename σ p := by
        have eq1 := congrArg (rename σ) h3
        rw [rename_rename] at eq1
        simp at eq1
        exact eq1
      rw [h4]
      simp only [show (⇑σ ∘ ⇑τ₀) = ⇑(σ * τ₀) from rfl]
      have h5 : rename (σ * τ₀) p = p := hp _ hστ₀
      rw [h5]
      module
  · intro σ
    have hrename_smul : ∀ c : ℚ, ∀ q : MvPolynomial (Fin n) ℚ,
        rename σ (c • q) = c • rename σ q := fun c q => map_smul (MvPolynomial.rename σ) c q
    have hrename_add : ∀ q r : MvPolynomial (Fin n) ℚ,
        rename σ (q + r) = rename σ q + rename σ r := fun q r => map_add (MvPolynomial.rename σ) q r
    have hrename_sub : ∀ q r : MvPolynomial (Fin n) ℚ,
        rename σ (q - r) = rename σ q - rename σ r := fun q r => (MvPolynomial.rename σ).map_sub q r
    have hrename_rename : ∀ τ : Equiv.Perm (Fin n), ∀ q : MvPolynomial (Fin n) ℚ,
        rename σ (rename τ q) = rename (σ * τ) q := by
      intro τ q; exact MvPolynomial.rename_rename τ σ q
    simp only [a]
    rw [hrename_smul]
    rw [hrename_sub]
    by_cases hσ : σ ∈ alternatingGroup (Fin n)
    · have hsign : Equiv.Perm.sign σ = 1 := by
        rw [Equiv.Perm.mem_alternatingGroup] at hσ; exact hσ
      rw [hsign]
      simp
      have h1 : rename σ p = p := hp σ hσ
      have hστ₀_inv : τ₀⁻¹ * σ * τ₀ ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
        simp [hsign]
      have h2 : rename (τ₀⁻¹ * σ * τ₀) p = p := hp _ hστ₀_inv
      have h3 : rename (↑τ₀⁻¹) (rename (σ * τ₀) p) = p := by rw [rename_rename]; exact h2
      have h4 : rename (σ * τ₀) p = rename τ₀ p := by
        have eq1 := congrArg (rename τ₀) h3
        rw [rename_rename] at eq1; simp at eq1; exact eq1
      simp [← Equiv.Perm.coe_mul]
      rw [h1, h4]
    · have hσ_odd : Equiv.Perm.sign σ = -1 := by
        have h := Int.units_eq_one_or (Equiv.Perm.sign σ)
        rcases h with h | h <;> simp_all [Equiv.Perm.mem_alternatingGroup]
      rw [hσ_odd]
      simp [neg_smul]
      have hστ₀ : σ * τ₀ ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup]
        simp [hσ_odd, hτ₀]
      have h1 : rename (σ * τ₀) p = p := hp _ hστ₀
      have hσinvτ₀ : σ⁻¹ * τ₀ ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup]
        simp [hσ_odd, hτ₀]
      have h2 : rename (σ⁻¹ * τ₀) p = p := hp _ hσinvτ₀
      have h3 : rename (↑σ⁻¹) (rename τ₀ p) = p := by rw [rename_rename]; exact h2
      have h4 : rename τ₀ p = rename σ p := by
        have eq1 := congrArg (rename σ) h3
        rw [rename_rename] at eq1; simp at eq1; exact eq1
      simp [← Equiv.Perm.coe_mul]
      rw [h4, h1]
      module
  · simp [s, a]
    module

/-- **`Aₙ`-invariants `= ℚ[e][δ]`.** Every `Aₙ`-invariant polynomial is `s + δ · t` with `s`
and `t` symmetric (so, after the fundamental theorem of symmetric polynomials, a polynomial in
`e₁,…,eₙ` and `δ`). Assembled from the split into symmetric + alternating parts and the
`δ`-divisibility of alternating polynomials. -/
theorem exists_symm_add_vander_mul_symm (hn : 2 ≤ n) {p : MvPolynomial (Fin n) ℚ}
    (hp : ∀ σ ∈ alternatingGroup (Fin n), rename σ p = p) :
    ∃ s t : MvPolynomial (Fin n) ℚ, s.IsSymmetric ∧ t.IsSymmetric ∧ p = s + vander n * t := by
  obtain ⟨s, a, hs, ha, hpsa⟩ := exists_symm_add_alternating hn hp
  obtain ⟨t, ht, hat⟩ := exists_symmetric_of_isAlternating ha
  exact ⟨s, t, hs, ht, by rw [hpsa, hat]⟩

end AlternatingInvariants

end
