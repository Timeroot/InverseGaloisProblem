/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.SplitCompositum
import InverseGalois.Rigidity.RET.Genus.OrdMem
import InverseGalois.Rigidity.RET.Wreath.Independence

/-!
# A radicand whose conjugates are independent modulo `p`-th powers

Let `N` be a number field which is Galois over `ℚ`, with group `U`.  Building a Kummer extension of
`N` whose Galois group is the regular representation of `U` over the field with `p` elements needs
an element `b` of `N` whose whole orbit `σ b` is independent modulo `p`-th powers, and the cheapest
way to produce one is to read the independence off a single prime.

Choose a rational prime `q` splitting completely in `N`.  Its decomposition group is then trivial,
so the primes `σ 𝔔` above it are pairwise distinct, and a small separation argument produces an
element `b` of `𝔔` lying outside `𝔔 ^ 2` and outside every other `σ 𝔔`.  The matrix of orders
`ord (σ 𝔔) (τ b)` is then the identity matrix, and a relation `y ^ p = ∏ (σ b) ^ m σ` read at the
prime `σ 𝔔` says exactly that `p` divides `m σ`.

The separation argument is elementary: with `e + f = 1`, `e` in the square and `f` in the product of
the other primes, the element `c * f + e` is congruent to `c` modulo the square and to `1` modulo
each of the others.

## Main results

* `InverseGalois.Shafarevich.exists_mem_notMem_sq_notMem` — the separation argument, over an
  arbitrary commutative ring.
* `InverseGalois.Shafarevich.exists_conj_indep` — **the orbit of a suitable element of a Galois
  number field is independent modulo `p`-th powers**, and in particular consists of distinct
  nonzero elements.

## Tags

number field, Galois group, prime, valuation, independence, Kummer theory
-/

open IsDedekindDomain NumberField InverseGalois.NumberTheory Pointwise

namespace InverseGalois.Shafarevich

/-! ### Separating a prime from finitely many others -/

/-- **An element of a prime, outside its square and outside finitely many comaximal ideals.**

Writing `1 = e + f` with `e` in the square and `f` in the product of the other ideals, the element
`c * f + e` differs from `c` by an element of the square and from `1` by an element of each of the
others. -/
theorem exists_mem_notMem_sq_notMem {R : Type*} [CommRing R] {P : Ideal R} {ι : Type*}
    {s : Finset ι} {Q : ι → Ideal R} (hsup : ∀ i ∈ s, P ⊔ Q i = ⊤) (hne : ∀ i ∈ s, Q i ≠ ⊤)
    {c : R} (hc : c ∈ P) (hc2 : c ∉ P ^ 2) :
    ∃ b : R, b ∈ P ∧ b ∉ P ^ 2 ∧ ∀ i ∈ s, b ∉ Q i := by
  have hcop : IsCoprime (P ^ 2) (∏ i ∈ s, Q i) :=
    IsCoprime.pow_left (IsCoprime.prod_right fun i hi => Ideal.isCoprime_iff_sup_eq.mpr (hsup i hi))
  have hone : (1 : R) ∈ P ^ 2 ⊔ ∏ i ∈ s, Q i := by
    rw [Ideal.isCoprime_iff_sup_eq.mp hcop]
    exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp hone
  refine ⟨c * f + e, ?_, ?_, ?_⟩
  · exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc) (Ideal.pow_le_self two_ne_zero he)
  · intro hb
    refine hc2 ?_
    have h1 : c * f ∈ P ^ 2 := by
      have hrw : c * f = c * f + e - e := by ring
      rw [hrw]
      exact Ideal.sub_mem _ hb he
    have h2 : c * e ∈ P ^ 2 := Ideal.mul_mem_left _ _ he
    have hrw : c = c * f + c * e := by rw [← mul_add, add_comm f e, hef, mul_one]
    rw [hrw]
    exact Ideal.add_mem _ h1 h2
  · intro i hi hb
    have hfi : f ∈ Q i := (Ideal.prod_le_inf.trans (Finset.inf_le hi)) hf
    have hei : e ∈ Q i := by
      have hrw : e = c * f + e - c * f := by ring
      rw [hrw]
      exact Ideal.sub_mem _ hb (Ideal.mul_mem_left _ _ hfi)
    exact hne i hi ((Ideal.eq_top_iff_one _).mpr (hef ▸ Ideal.add_mem _ hei hfi))

/-! ### The orbit of a suitable element -/

variable (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]

/-- **A Galois number field contains an element whose orbit is independent modulo `p`-th powers.**

The element is chosen at a prime above a rational prime that splits completely: it has order one
there and order zero at every conjugate of that prime, so the matrix of orders of the conjugates of
the element is the identity matrix, and a relation between them modulo `p`-th powers is forced to
have all its exponents divisible by `p`. -/
theorem exists_conj_indep {p : ℕ} :
    ∃ b : N, (∀ σ : Gal(N/ℚ), σ b ≠ 0) ∧ (Function.Injective fun σ : Gal(N/ℚ) => σ b) ∧
      ∀ (m : Gal(N/ℚ) → ℤ) (y : N), y ≠ 0 → y ^ p = ∏ σ : Gal(N/ℚ), (σ b) ^ (m σ) →
        ∀ σ, (p : ℤ) ∣ m σ := by
  classical
  -- a rational prime splitting completely in `N`
  obtain ⟨q, hq, hsplit⟩ := (infinite_setOf_prime_splitsCompletely N).nonempty
  have hqZ : ((q : ℤ)) ≠ 0 := by exact_mod_cast hq.ne_zero
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hqZ).mpr (Nat.prime_iff_prime_int.mp hq)
  have hspanbot : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hqZ
  -- a prime of the ring of integers above it
  obtain ⟨⟨P, hPmem⟩⟩ := (Ideal.span {(q : ℤ)}).nonempty_primesOver (S := 𝓞 N)
  haveI hPprime : P.IsPrime := hPmem.1
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hPmem.2
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hspanbot hPmem
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0
  -- the decomposition group is trivial, so the conjugate primes are pairwise distinct
  have hstab : MulAction.stabilizer Gal(N/ℚ) P = ⊥ :=
    InverseGalois.CFT.stabilizer_eq_bot_of_splitsCompletely N hq P hsplit
  have hinjP : Function.Injective fun σ : Gal(N/ℚ) => σ • P := by
    intro σ τ h
    have h' : σ • P = τ • P := h
    have hmem : σ⁻¹ * τ ∈ MulAction.stabilizer Gal(N/ℚ) P := by
      show (σ⁻¹ * τ) • P = P
      rw [mul_smul, ← h', inv_smul_smul]
    rw [hstab, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem
  have hconj0 : ∀ σ : Gal(N/ℚ), σ • P ≠ ⊥ := by
    intro σ hbot
    refine hP0 ?_
    have := congrArg (fun I : Ideal (𝓞 N) => σ⁻¹ • I) hbot
    simpa using this
  have hconjmax : ∀ σ : Gal(N/ℚ), (σ • P).IsMaximal := fun σ =>
    Ideal.IsPrime.isMaximal inferInstance (hconj0 σ)
  -- an element of `P`, outside `P ^ 2` and outside every conjugate of `P`
  obtain ⟨c, hcP, hcP2⟩ : ∃ c, c ∈ P ∧ c ∉ P ^ 2 := by
    have hlt : P ^ 2 < P := by simpa using Ideal.pow_succ_lt_pow hP0 1
    obtain ⟨c, hcP, hc2⟩ := SetLike.exists_of_lt hlt
    exact ⟨c, hcP, hc2⟩
  have hsup : ∀ σ ∈ (Finset.univ : Finset Gal(N/ℚ)).erase 1, P ⊔ σ • P = ⊤ := by
    intro σ hσ
    refine hPmax.coprime_of_ne (hconjmax σ) fun heq => ?_
    have h1 : (1 : Gal(N/ℚ)) • P = σ • P := by rw [one_smul]; exact heq
    exact (Finset.mem_erase.mp hσ).1 (hinjP h1).symm
  obtain ⟨b, hbP, hbP2, hbQ⟩ := exists_mem_notMem_sq_notMem hsup
    (fun σ _ => (hconjmax σ).ne_top) hcP hcP2
  have hb0 : b ≠ 0 := fun h => hbP2 (h ▸ Ideal.zero_mem _)
  have hsmul0 : ∀ (σ : Gal(N/ℚ)) (x : 𝓞 N), x ≠ 0 → σ • x ≠ 0 := by
    intro σ x hx h
    exact hx (by rw [← inv_smul_smul σ x, h, smul_zero])
  -- the conjugate primes, as points of the height-one spectrum
  let v : Gal(N/ℚ) → HeightOneSpectrum (𝓞 N) := fun σ => ⟨σ • P, inferInstance, hconj0 σ⟩
  have hcoe : ∀ (σ : Gal(N/ℚ)) (x : 𝓞 N),
      algebraMap (𝓞 N) N (σ • x) = σ (algebraMap (𝓞 N) N x) := fun _ _ => rfl
  -- the matrix of orders is the identity matrix
  have hord_self : ∀ σ : Gal(N/ℚ),
      Rigidity.RET.ord N (v σ) (σ (algebraMap (𝓞 N) N b)) = 1 := by
    intro σ
    rw [← hcoe]
    have hmem : (σ • b) ∈ (v σ).asIdeal ^ 1 := by
      show (σ • b) ∈ (σ • P) ^ 1
      rw [pow_one]
      exact Ideal.smul_mem_pointwise_smul σ b P hbP
    have hnot : (σ • b) ∉ (v σ).asIdeal ^ (1 + 1) := by
      show (σ • b) ∉ (σ • P) ^ 2
      rw [← smul_pow', Ideal.smul_mem_pointwise_smul_iff]
      exact hbP2
    simpa using Rigidity.RET.ord_eq_of_mem_pow_of_notMem_pow (K := N) (v σ)
      (hsmul0 σ b hb0) hmem hnot
  have hord_other : ∀ σ τ : Gal(N/ℚ), τ ≠ σ →
      Rigidity.RET.ord N (v σ) (τ (algebraMap (𝓞 N) N b)) = 0 := by
    intro σ τ hτσ
    rw [← hcoe]
    have hkey : ((σ⁻¹ * τ)⁻¹ : Gal(N/ℚ)) ∈ (Finset.univ : Finset Gal(N/ℚ)).erase 1 := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      simp only [ne_eq, inv_eq_one, inv_mul_eq_one]
      exact fun h => hτσ h.symm
    have hout := hbQ _ hkey
    have hmem : (τ • b) ∈ (v σ).asIdeal ^ 0 := by simp
    have hnot : (τ • b) ∉ (v σ).asIdeal ^ (0 + 1) := by
      show (τ • b) ∉ (σ • P) ^ (0 + 1)
      rw [zero_add, pow_one]
      intro hmem'
      exact hout (Ideal.mem_inv_pointwise_smul_iff.mpr
        (by rw [← smul_smul]; exact Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hmem'))
    simpa using Rigidity.RET.ord_eq_of_mem_pow_of_notMem_pow (K := N) (v σ)
      (hsmul0 τ b hb0) hmem hnot
  -- the three conclusions
  have hne0 : ∀ σ : Gal(N/ℚ), σ (algebraMap (𝓞 N) N b) ≠ 0 := by
    intro σ h
    rw [map_eq_zero_iff σ σ.injective] at h
    exact hb0 (FaithfulSMul.algebraMap_injective (𝓞 N) N (by rw [h, map_zero]))
  refine ⟨algebraMap (𝓞 N) N b, hne0, ?_, ?_⟩
  · intro σ τ h
    by_contra hne'
    have h1 : Rigidity.RET.ord N (v σ) (σ (algebraMap (𝓞 N) N b)) = 1 := hord_self σ
    rw [show σ (algebraMap (𝓞 N) N b) = τ (algebraMap (𝓞 N) N b) from h,
      hord_other σ τ (Ne.symm hne')] at h1
    exact absurd h1 (by norm_num)
  · intro m y hy hpow σ
    refine Rigidity.RET.Wreath.dvd_of_pow_eq_prod_zpow_ord (R := 𝓞 N) (K := N) hne0 hy hpow σ
      {v σ} (fun w hw τ hτ => ?_) ?_
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact hord_other σ τ hτ
    · rw [Finset.gcd_singleton, hord_self σ]
      simpa using isCoprime_one_right

end InverseGalois.Shafarevich
