/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.CyclotomicRadical
import InverseGalois.CFT.Units.AdicUnitGen
import InverseGalois.CFT.Units.CompletionGalois

/-!
# A radical of the opposite of a prime in the completion of a cyclotomic field

A primitive root of unity of a number field stays primitive in a completion, because the completion
receives the field injectively.  So for a place containing an odd prime `q`, the completion of a
number field containing a primitive `q`-th root of unity carries a radical of the opposite of `q`
of any exponent dividing `q - 1`: one and the same radical for every automorphism preserving the
valuation, each of which multiplies it by a root of unity congruent to the corresponding power of
the exponent to which it raises the root of unity, and fixes it outright as soon as that power is
congruent to one.

The automorphisms of the completion attached to the automorphisms of a decomposition group are
among these: they preserve the valuation, and they act on the image of the field through the global
automorphism they come from.  Since the base field plays no role in that description, one and the
same radical answers for the decomposition group over every base at once.

An automorphism raises a primitive root of unity of prime order to a nonzero power, and iterating
it raises the root to the iterated power; so an automorphism of finite order raises the root to an
exponent whose power of that order is congruent to one.  Over an intermediate field the order of
every automorphism divides the number of automorphisms of the extension, so the radical is fixed by
the whole decomposition group over that intermediate field, and therefore comes from the completion
of the intermediate field.

## Main results

* `InverseGalois.CFT.isPrimitiveRoot_algebraMap_adicCompletion`: a primitive root of unity stays
  primitive in the completion.
* `InverseGalois.CFT.exists_pow_eq_neg_natCast_adicCompletion`: **the completion of a number field
  containing a primitive root of unity of odd prime order, at a place containing that prime,
  carries a radical of the opposite of the prime of every exponent dividing one less than it**,
  the same radical for every isometry of the completion.
* `InverseGalois.CFT.adicCompletionAut_algebraMap`: **the automorphism of the completion attached to
  an automorphism of the decomposition group acts on the image of the field through that
  automorphism.**
* `InverseGalois.CFT.dvd_pow_sub_one_of_pow_eq_one`: **an automorphism of finite order raises a root
  of unity to an exponent whose power of that order is congruent to one.**
* `InverseGalois.CFT.mem_range_algebraMap_of_forall_dvd_pow_sub_one`: **an element of the completion
  fixed by every isometry raising a primitive root of unity of prime order to a power congruent to
  one modulo that prime, after as many iterations as the degree of the extension, comes from the
  completion of the base.**

## Tags

number field, adic completion, decomposition group, root of unity, radical, Teichmüller character,
ramification, class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped WithZero

/-! ### The radical in the completion -/

section AdicRadical

variable {K : Type*} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- A primitive root of unity of a number field stays primitive in a completion, which receives the
field injectively. -/
theorem isPrimitiveRoot_algebraMap_adicCompletion {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (algebraMap K (w.adicCompletion K) ζ) n :=
  hζ.map_of_injective (algebraMap K (w.adicCompletion K)).injective

/-- **The completion of a number field containing a primitive root of unity of odd prime order, at a
place containing that prime, carries a radical of the opposite of the prime of every exponent
dividing one less than it.**  The prime is the residue characteristic of the completion and the root
of unity stays primitive there, so the radical of the abstract construction is available; the same
radical answers for every isometry of the completion, which multiplies it by a root of unity
congruent to the corresponding power of the exponent to which the isometry raises the root of unity,
and fixes it as soon as that power is congruent to one. -/
theorem exists_pow_eq_neg_natCast_adicCompletion {q : ℕ} (hq : q.Prime) (hodd : Odd q) {ζ : K}
    (hζ : IsPrimitiveRoot ζ q) (hmem : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) {M N : ℕ}
    (hMN : M * N = q - 1) :
    ∃ ν : w.adicCompletion K, ν ^ N = -((q : ℕ) : w.adicCompletion K) ∧
      (∀ τ : w.adicCompletion K ≃+* w.adicCompletion K,
        (∀ z : w.adicCompletion K, Valued.v (τ z) = Valued.v z) → ∀ a : ℕ,
        τ (algebraMap K (w.adicCompletion K) ζ) = algebraMap K (w.adicCompletion K) ζ ^ a →
        ∃ ξ : w.adicCompletion K, τ ν = ξ * ν ∧ ξ ^ N = 1 ∧
          Valued.v (ξ - ((a : ℕ) : w.adicCompletion K) ^ M) < 1) ∧
      ∀ τ : w.adicCompletion K ≃+* w.adicCompletion K,
        (∀ z : w.adicCompletion K, Valued.v (τ z) = Valued.v z) → ∀ a : ℕ,
        τ (algebraMap K (w.adicCompletion K) ζ) = algebraMap K (w.adicCompletion K) ζ ^ a →
        q ∣ a ^ M - 1 → τ ν = ν := by
  obtain ⟨e, hres⟩ := exists_hasResidueChar_of_mem hq w hmem
  exact exists_pow_eq_neg_natCast_forall_aut hres hodd
    (isPrimitiveRoot_algebraMap_adicCompletion w hζ) hMN

end AdicRadical

/-! ### The decomposition group on the image of the field -/

section Decomposition

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]
  (w : HeightOneSpectrum (𝓞 K))

/-- **The automorphism of the completion attached to an automorphism of the decomposition group acts
on the image of the field through that automorphism.** -/
theorem adicCompletionAut_algebraMap (σ : Gal(K/k)) (hσ : σ • w = w) (x : K) :
    adicCompletionAut w σ hσ (algebraMap K (w.adicCompletion K) x)
      = algebraMap K (w.adicCompletion K) (σ x) := by
  show adicCompletionAut w σ hσ ((x : WithVal (w.valuation K)) : w.adicCompletion K) = _
  rw [adicCompletionAut_coe]
  rfl

/-- The automorphism of the completion attached to an automorphism of the decomposition group raises
the image of a root of unity to the same power as that automorphism does. -/
theorem adicCompletionAut_algebraMap_pow (σ : Gal(K/k)) (hσ : σ • w = w) {ζ : K} {a : ℕ}
    (hσζ : σ ζ = ζ ^ a) :
    adicCompletionAut w σ hσ (algebraMap K (w.adicCompletion K) ζ)
      = algebraMap K (w.adicCompletion K) ζ ^ a := by
  rw [adicCompletionAut_algebraMap w σ hσ ζ, hσζ, map_pow]

end Decomposition

/-! ### Powers of an automorphism on a root of unity -/

section AutPow

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Iterating an automorphism raises a root of unity to the iterated power of the exponent. -/
theorem aut_pow_apply_eq_pow_pow {ζ : K} {a : ℕ} {σ : Gal(K/F)} (hσ : σ ζ = ζ ^ a) (j : ℕ) :
    (σ ^ j) ζ = ζ ^ a ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hσ, ← pow_mul, ← pow_succ']

/-- **An automorphism of finite order raises a root of unity to an exponent whose power of that
order is congruent to one.**  Iterating the automorphism that many times fixes the root of unity,
and a power of a primitive root of unity is itself exactly when the order divides the exponent. -/
theorem dvd_pow_sub_one_of_pow_eq_one {q : ℕ} (hq : q ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ q)
    {σ : Gal(K/F)} {a M : ℕ} (hσ : σ ζ = ζ ^ a) (ha : a ≠ 0) (hM : σ ^ M = 1) : q ∣ a ^ M - 1 := by
  have hfix : ζ ^ a ^ M = ζ := by
    rw [← aut_pow_apply_eq_pow_pow hσ M, hM, AlgEquiv.one_apply]
  have hb1 : 1 ≤ a ^ M := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero ha)
  refine hζ.dvd_of_pow_eq_one _ (mul_right_cancel₀ (hζ.ne_zero hq) ?_)
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel hb1, hfix]

/-- **An automorphism raises a primitive root of unity of prime order to a nonzero power.**  The
image is again a root of unity of the same order, hence a power of the root, and that power is not
the empty one because the automorphism does not send the root to one. -/
theorem exists_ne_zero_aut_eq_pow {q : ℕ} (hq : q.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ q)
    (σ : Gal(K/F)) : ∃ a : ℕ, a ≠ 0 ∧ σ ζ = ζ ^ a := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hpow : (σ ζ) ^ q = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hpow
  refine ⟨a, ?_, ha.symm⟩
  rintro rfl
  rw [pow_zero] at ha
  exact hζ.ne_one hq.one_lt (σ.injective (by rw [← ha, map_one]))

end AutPow

/-! ### Descending to an intermediate field -/

section Descent

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [IsGalois F K] (w : HeightOneSpectrum (𝓞 K))

variable (F) in
/-- An element of the completion fixed by every automorphism of the decomposition group over a base
comes from the completion of that base. -/
theorem mem_range_algebraMap_of_forall_adicCompletionAut_eq {z : w.adicCompletion K}
    (h : ∀ (σ : Gal(K/F)) (hσ : σ • w = w), adicCompletionAut w σ hσ z = z) :
    z ∈ Set.range (algebraMap ((primeUnder (𝓞 F) w).adicCompletion F) (w.adicCompletion K)) :=
  (mem_range_algebraMap_iff_forall_stabilizer_smul_eq F w z).mp
    fun σ => h σ.1 (mem_stabilizer_iff.mp σ.2)

variable (F) in
/-- **An element of the completion fixed by every isometry raising a primitive root of unity of
prime order to a power congruent to one modulo that prime, after as many iterations as the degree of
the extension, comes from the completion of the base.**  Every automorphism of the decomposition
group is such an isometry: its order divides the number of automorphisms of the extension. -/
theorem mem_range_algebraMap_of_forall_dvd_pow_sub_one {q : ℕ} (hq : q.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ q) {M : ℕ} (hM : Nat.card Gal(K/F) = M) {z : w.adicCompletion K}
    (hz : ∀ τ : w.adicCompletion K ≃+* w.adicCompletion K,
      (∀ y : w.adicCompletion K, Valued.v (τ y) = Valued.v y) → ∀ a : ℕ,
      τ (algebraMap K (w.adicCompletion K) ζ) = algebraMap K (w.adicCompletion K) ζ ^ a →
      q ∣ a ^ M - 1 → τ z = z) :
    z ∈ Set.range (algebraMap ((primeUnder (𝓞 F) w).adicCompletion F) (w.adicCompletion K)) := by
  refine mem_range_algebraMap_of_forall_adicCompletionAut_eq F w fun σ hσ => ?_
  obtain ⟨a, ha, hσζ⟩ := exists_ne_zero_aut_eq_pow hq hζ σ
  refine hz _ (valued_adicCompletionAut w σ hσ) a (adicCompletionAut_algebraMap_pow w σ hσ hσζ) ?_
  exact dvd_pow_sub_one_of_pow_eq_one hq.ne_zero hζ hσζ ha (hM ▸ pow_card_eq_one')

end Descent

end InverseGalois.CFT
