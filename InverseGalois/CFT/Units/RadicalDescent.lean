/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.AdicRadical
import InverseGalois.CFT.Units.TowerCoboundary

/-!
# The radical of the opposite of a prime over an intermediate field

Let `k ⊆ F ⊆ L` be a tower of number fields with `F` normal over `k` and `L` normal over `F`, let
`q` be an odd prime whose primitive root of unity lies in `L`, and let `w` be a place of `L`
containing `q`.  The completion of `L` at `w` carries a radical of the opposite of `q` of every
exponent dividing `q - 1`, and that radical is fixed by the whole decomposition group over `F`, so
it already lies in the completion of `F` at the place below.

This file records that descent together with the action it carries.  An automorphism of `L` over
`k` fixing the place restricts to an automorphism of `F` over `k` fixing the place below, and the
automorphisms of the two completions attached to the two agree on the smaller one; so the descended
radical is multiplied, by the restricted automorphism, by exactly the root of unity that the
original automorphism produced upstairs.  Since the smaller completion receives the larger one
injectively, the root of unity descends as well, along with its order and with the congruence
naming its residue.

## Main results

* `InverseGalois.CFT.exists_pow_eq_neg_natCast_adicCompletion_intermediate`: **the completion of an
  intermediate field, at the place below a place of a normal extension containing an odd prime
  whose primitive root of unity lies there, carries a radical of the opposite of that prime of
  every exponent whose complementary factor is the degree of the upper layer**, multiplied by a
  root of unity of the same exponent congruent to the complementary power of the exponent to which
  the automorphism raises the root of unity.
* `InverseGalois.CFT.exists_pow_eq_neg_natCast_aut_eq_algebraMap_mul`: **the automorphism of the
  intermediate completion multiplies the radical by a root of unity prescribed in the completion of
  the base**, as soon as that root of unity has the prescribed residue.

## Tags

number field, adic completion, decomposition group, radical, root of unity, Teichmüller character,
ramification, class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped WithZero

/-! ### Descending the radical to the intermediate completion -/

section RadicalDescent

variable {k F L : Type*} [Field k] [NumberField k] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L]
  [IsGalois k F] [IsGalois F L] (w : HeightOneSpectrum (𝓞 L))

variable (F) in
omit [NumberField k] in
/-- **The completion of an intermediate field, at the place below a place of a normal extension
containing an odd prime whose primitive root of unity lies there, carries a radical of the opposite
of that prime of every exponent whose complementary factor is the degree of the upper layer.**  The
radical upstairs is fixed by the decomposition group over the intermediate field, so it comes from
below; an automorphism of the top field fixing the place acts on the smaller completion through its
restriction, so the root of unity by which it multiplies the radical comes from below as well, with
the same order and the same residue. -/
theorem exists_pow_eq_neg_natCast_adicCompletion_intermediate {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {ζ : L} (hζ : IsPrimitiveRoot ζ q) (hmem : ((q : ℕ) : 𝓞 L) ∈ w.asIdeal) {M N : ℕ}
    (hMN : M * N = q - 1) (hM : Nat.card Gal(L/F) = M) :
    ∃ ν : (primeUnder (𝓞 F) w).adicCompletion F,
      ν ^ N = -((q : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F) ∧
        ∀ (σ : Gal(L/k)) (hσ : σ • w = w) (a : ℕ), σ ζ = ζ ^ a →
          ∃ ξ : (primeUnder (𝓞 F) w).adicCompletion F,
            adicCompletionAut (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
                (restrictNormalHom_smul_primeUnder F hσ) ν = ξ * ν ∧ ξ ^ N = 1 ∧
              Valued.v (ξ - ((a : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F) ^ M) < 1 := by
  haveI : CharZero (w.adicCompletion L) :=
    charZero_of_injective_algebraMap (algebraMap L (w.adicCompletion L)).injective
  have hN : N ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hMN
    have := hq.one_lt
    omega
  obtain ⟨ν, hνpow, hνaut, hνfix⟩ :=
    exists_pow_eq_neg_natCast_adicCompletion w hq hodd hζ hmem hMN
  obtain ⟨νB, hνB⟩ := mem_range_algebraMap_of_forall_dvd_pow_sub_one F w hq hζ hM hνfix
  have hinj : Function.Injective
      (algebraMap ((primeUnder (𝓞 F) w).adicCompletion F) (w.adicCompletion L)) :=
    (algebraMap ((primeUnder (𝓞 F) w).adicCompletion F) (w.adicCompletion L)).injective
  have hν0 : ν ≠ 0 := by
    intro h
    rw [h, zero_pow hN, eq_comm, neg_eq_zero] at hνpow
    exact (Nat.cast_ne_zero (R := w.adicCompletion L)).mpr hq.ne_zero hνpow
  have hνB0 : νB ≠ 0 := fun h => hν0 (by rw [← hνB, h, map_zero])
  refine ⟨νB, hinj ?_, ?_⟩
  · rw [map_pow, hνB, hνpow, map_neg, map_natCast]
  · intro σ hσ a hσζ
    obtain ⟨ξ, hξ1, hξ2, hξ3⟩ := hνaut (adicCompletionAut w σ hσ)
      (valued_adicCompletionAut w σ hσ) a (adicCompletionAut_algebraMap_pow w σ hσ hσζ)
    obtain ⟨ξB, hξB⟩ : ∃ ξB : (primeUnder (𝓞 F) w).adicCompletion F,
        adicCompletionAut (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
          (restrictNormalHom_smul_primeUnder F hσ) νB = ξB * νB :=
      ⟨_, (div_mul_cancel₀ _ hνB0).symm⟩
    have hstep : algebraMap ((primeUnder (𝓞 F) w).adicCompletion F) (w.adicCompletion L)
        (adicCompletionAut (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
          (restrictNormalHom_smul_primeUnder F hσ) νB) = ξ * ν := by
      rw [algebraMap_adicCompletion F w,
        ← adicCompletionAut_adicCompletionComap_restrict F w σ hσ νB,
        ← algebraMap_adicCompletion F w, hνB, hξ1]
    have hξmap : algebraMap ((primeUnder (𝓞 F) w).adicCompletion F) (w.adicCompletion L) ξB
        = ξ := by
      rw [hξB, map_mul, hνB] at hstep
      exact mul_right_cancel₀ hν0 hstep
    refine ⟨ξB, hξB, hinj ?_, ?_⟩
    · rw [map_pow, hξmap, hξ2, map_one]
    · have hvalmap := valued_adicCompletionComap (𝓞 F) (K := L) w
        (ξB - ((a : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F) ^ M)
      rw [← algebraMap_adicCompletion F w, map_sub, hξmap, map_pow, map_natCast] at hvalmap
      rw [hvalmap] at hξ3
      rcases lt_trichotomy
          (Valued.v (ξB - ((a : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F) ^ M)) 1 with
        hlt | heq | hgt
      · exact hlt
      · rw [heq, one_pow] at hξ3
        exact absurd hξ3 (lt_irrefl 1)
      · exact absurd hξ3 (not_lt.mpr (one_le_pow₀ hgt.le))

/-! ### Naming the root of unity in the completion of the base -/

variable (F) in
/-- **The automorphism of the intermediate completion multiplies the radical by a root of unity
prescribed in the completion of the base.**  A root of unity of the base completion whose residue
is the same power of the same natural number has the same image as the root of unity produced by
the descent, two roots of unity of an order prime to the residue characteristic being equal as soon
as their difference is small. -/
theorem exists_pow_eq_neg_natCast_aut_eq_algebraMap_mul {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {ζL : L} (hζL : IsPrimitiveRoot ζL q) (hmem : ((q : ℕ) : 𝓞 L) ∈ w.asIdeal) {M N : ℕ}
    (hMN : M * N = q - 1) (hM : Nat.card Gal(L/F) = M) {b : ℕ} {σ : Gal(L/k)} (hσ : σ • w = w)
    (hσζ : σ ζL = ζL ^ b)
    {ζ : (primeUnder (𝓞 k) (primeUnder (𝓞 F) w)).adicCompletion k} (hζpow : ζ ^ N = 1)
    (hζres : Valued.v (ζ - ((b ^ M : ℕ) :
      (primeUnder (𝓞 k) (primeUnder (𝓞 F) w)).adicCompletion k)) < 1) :
    ∃ ν : (primeUnder (𝓞 F) w).adicCompletion F,
      ν ^ N = -((q : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F) ∧
        adicCompletionAut (primeUnder (𝓞 F) w) (AlgEquiv.restrictNormalHom F σ)
            (restrictNormalHom_smul_primeUnder F hσ) ν
          = algebraMap ((primeUnder (𝓞 k) (primeUnder (𝓞 F) w)).adicCompletion k)
              ((primeUnder (𝓞 F) w).adicCompletion F) ζ * ν := by
  have hq1 : 1 < q := hq.one_lt
  have hN : N ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hMN
    omega
  obtain ⟨ν, hνpow, hact⟩ :=
    exists_pow_eq_neg_natCast_adicCompletion_intermediate (k := k) F w hq hodd hζL hmem hMN hM
  obtain ⟨ξ, hξ1, hξ2, hξ3⟩ := hact σ hσ b hσζ
  rw [← Nat.cast_pow] at hξ3
  refine ⟨ν, hνpow, ?_⟩
  rw [hξ1]
  refine congrArg (· * ν) ?_
  have hmemF : ((q : ℕ) : 𝓞 F) ∈ (primeUnder (𝓞 F) w).asIdeal := by
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  obtain ⟨e, hres⟩ := exists_hasResidueChar_of_mem hq (primeUnder (𝓞 F) w) hmemF
  have hNq : ¬ q ∣ N := by
    intro hd
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd
    have h2 := Nat.le_of_dvd (by omega) (Dvd.intro_left M hMN)
    omega
  have hNv : Valued.v ((N : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F) = 1 :=
    valued_natCast_eq_one_of_not_dvd hq (valued_residueChar_lt_one hres) hNq
  have hζmap : (algebraMap ((primeUnder (𝓞 k) (primeUnder (𝓞 F) w)).adicCompletion k)
      ((primeUnder (𝓞 F) w).adicCompletion F) ζ) ^ N = 1 := by
    rw [← map_pow, hζpow, map_one]
  have hζmapres : Valued.v ((algebraMap
        ((primeUnder (𝓞 k) (primeUnder (𝓞 F) w)).adicCompletion k)
        ((primeUnder (𝓞 F) w).adicCompletion F) ζ)
      - ((b ^ M : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F)) < 1 := by
    have hv := valued_adicCompletionComap (𝓞 k) (K := F) (primeUnder (𝓞 F) w)
      (ζ - ((b ^ M : ℕ) : (primeUnder (𝓞 k) (primeUnder (𝓞 F) w)).adicCompletion k))
    rw [← algebraMap_adicCompletion k (primeUnder (𝓞 F) w), map_sub, map_natCast] at hv
    rw [hv]
    exact pow_lt_one₀ zero_le' hζres (ramIdx_ne_zero (A := 𝓞 k) (primeUnder (𝓞 F) w))
  have hdiff := Valuation.map_sub Valued.v
    ((algebraMap ((primeUnder (𝓞 k) (primeUnder (𝓞 F) w)).adicCompletion k)
        ((primeUnder (𝓞 F) w).adicCompletion F) ζ)
      - ((b ^ M : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F))
    (ξ - ((b ^ M : ℕ) : (primeUnder (𝓞 F) w).adicCompletion F))
  rw [sub_sub_sub_cancel_right] at hdiff
  exact (eq_of_valued_sub_lt_one hN hNv hζmap hξ2
    (lt_of_le_of_lt hdiff (max_lt hζmapres hξ3))).symm

end RadicalDescent

end InverseGalois.CFT
