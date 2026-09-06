/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.GaloisSplitting
import InverseGalois.CFT.Brauer.RatReciprocity
import InverseGalois.CFT.Brauer.SubcyclotomicReciprocity
import InverseGalois.CFT.Cyclotomic.AuxiliarySubfield
import InverseGalois.CFT.Cyclotomic.TotallyRamified

/-!
# Global reciprocity over the rationals

The invariants of a Brauer class over the rationals add up to zero, with no restriction on the
order of the class.  For a class split by the reals this is the reduction that spends one auxiliary
prime per bad prime, available for every prime exponent now that the exponent two has its own
supply of auxiliary primes.  What is left is to move an arbitrary class into that case, and since
the Brauer group of the reals has order two it is enough to exhibit a single class which the reals
do not split and whose invariants already add up to zero.

That class is the quaternion algebra ramified at three and at infinity: the cyclic algebra with
coefficient minus one over the cyclotomic field of the cube roots of unity.  Its invariant at the
conductor is one half, because the power residue symbol there reads half the predecessor of the
conductor and the degree is two, which does not divide it.  Were the reals to split the class, the
reduction would already force the sum of its invariants to vanish, and the invariant at the
conductor would be the whole sum; so the reals do not split it.  Its archimedean invariant is
therefore nontrivial, and the only nontrivial element of order two in the rationals modulo the
integers is one half, so the two invariants cancel.

Multiplying by that class moves any class the reals do not split into one they do, and the total
invariant is unchanged.  Splitting the order of a class into its two-part and its odd part then
covers every class, since every Brauer class of a perfect field is of finite order.

## Main results

* `InverseGalois.CFT.QModZ.eq_half_of_add_self_eq_zero`: the only nontrivial element of order two
  in the rationals modulo the integers is one half.
* `InverseGalois.CFT.totalInvariant_cyclicBrauerHom_rat_eq_mul_infinite`: the sum of all the local
  invariants of a cyclic algebra over the rationals with a coefficient that is a unit at every
  finite place has one finite term and one archimedean term.
* `InverseGalois.CFT.exists_brauer_corrector_real`: **a Brauer class of the rationals of order two
  which the reals do not split and whose invariants add up to zero.**
* `InverseGalois.CFT.totalInvariant_eq_one_of_pow_eq_one_two_pow`: **the invariants of a Brauer
  class of two-power order over the rationals add up to zero.**
* `InverseGalois.CFT.totalInvariant_eq_one`: **the invariants of a Brauer class over the rationals
  add up to zero** — global reciprocity.

## Tags

Brauer group, local invariant, global reciprocity, quaternion algebra, cyclotomic field, real
place, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField

/-! ### The element of order two -/

section Torsion

/-- **The only nontrivial element of order two in the rationals modulo the integers is one
half.**  Twice such an element is an integer, so the element is half an integer, and an even
numerator would make it vanish. -/
theorem QModZ.eq_half_of_add_self_eq_zero {t : QModZ} (h2 : t + t = 0) (ht : t ≠ 0) :
    t = QuotientAddGroup.mk (1 / 2 : ℚ) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) t
  have h2' : (QuotientAddGroup.mk (r + r) : QModZ) = 0 := by rw [← map_add] at h2; exact h2
  obtain ⟨k, hk⟩ := (QModZ.mk_eq_zero_iff _).mp h2'
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine absurd ((QModZ.mk_eq_zero_iff _).mpr ⟨m, ?_⟩) ht
    rw [hm] at hk
    push_cast at hk
    linarith
  · have key : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) (r - 1 / 2) = 0 := by
      refine (QModZ.mk_eq_zero_iff _).mpr ⟨m, ?_⟩
      rw [hm] at hk
      push_cast at hk ⊢
      linarith
    rw [map_sub, sub_eq_zero] at key
    exact key

/-- **A nontrivial element of order two of the invariant group is the class of one half.** -/
theorem eq_ofAdd_half_of_sq_eq_one {t : Multiplicative QModZ} (h2 : t ^ 2 = 1) (ht : t ≠ 1) :
    t = Multiplicative.ofAdd (QuotientAddGroup.mk (1 / 2 : ℚ)) := by
  refine Multiplicative.toAdd.injective (QModZ.eq_half_of_add_self_eq_zero ?_ ?_)
  · have h := congrArg Multiplicative.toAdd h2
    simpa [sq] using h
  · intro h
    refine ht (Multiplicative.toAdd.injective ?_)
    simpa using h

/-- The class of one half is nontrivial in the rationals modulo the integers. -/
theorem QModZ.mk_half_ne_zero : (QuotientAddGroup.mk (1 / 2 : ℚ) : QModZ) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (QModZ.mk_eq_zero_iff _).mp h
  have h2 : (2 : ℚ) * (k : ℚ) = 1 := by rw [hk]; norm_num
  have h2' : (2 : ℤ) * k = 1 := by exact_mod_cast h2
  omega

/-- The class of one half has order two in the rationals modulo the integers. -/
theorem QModZ.mk_half_add_self :
    (QuotientAddGroup.mk (1 / 2 : ℚ) : QModZ) + QuotientAddGroup.mk (1 / 2 : ℚ) = 0 := by
  have h : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) (1 / 2 : ℚ)
      + (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) (1 / 2 : ℚ) = 0 := by
    rw [← map_add]
    exact (QModZ.mk_eq_zero_iff _).mpr ⟨1, by norm_num⟩
  exact h

end Torsion

/-! ### The single infinite place of the rationals -/

section Infinite

/-- **The rationals have a single infinite place**, since they have a single embedding into the
complex numbers. -/
theorem subsingleton_infinitePlace_rat : Subsingleton (InfinitePlace ℚ) := by
  refine ⟨fun u v => Subtype.ext ?_⟩
  obtain ⟨φ, hφ⟩ := u.2
  obtain ⟨ψ, hψ⟩ := v.2
  rw [← hφ, ← hψ, Subsingleton.elim φ ψ]

/-- The product of the archimedean invariants over the rationals has a single factor. -/
theorem prod_infinitePlaceInvariant_rat (x : BrauerGroup.{0, 0} ℚ) (u : InfinitePlace ℚ) :
    ∏ v : InfinitePlace ℚ, infinitePlaceInvariant ℚ v x = infinitePlaceInvariant ℚ u x := by
  haveI := subsingleton_infinitePlace_rat
  exact Fintype.prod_subsingleton _ u

/-- **A Brauer class of the rationals with a nontrivial archimedean invariant is not split by the
reals**, and conversely. -/
theorem infinitePlaceInvariant_rat_eq_one_iff (u : InfinitePlace ℚ) (x : BrauerGroup.{0, 0} ℚ) :
    infinitePlaceInvariant ℚ u x = 1 ↔ x ∈ BrauerGroup.relative ℚ ℝ := by
  rw [infinitePlaceInvariant_eq_one_iff, relative_completion_rat_eq_relative_real]

end Infinite

/-! ### One finite place and one infinite place -/

section OnePlace

/-- **The sum of all the local invariants of a cyclic algebra over the rationals has one finite
term and one archimedean term** when the splitting field sits inside a cyclotomic field whose
conductor has a single prime factor `q`, and the coefficient is a unit at every finite place.
Unlike the totally real case the archimedean term is kept, since nothing forces it to vanish. -/
theorem totalInvariant_cyclicBrauerHom_rat_eq_mul_infinite {K : Type} [Field K] [NumberField K]
    [IsGalois ℚ K] {σ₀ : Gal(K/ℚ)} (hσ₀ : ∀ x : Gal(K/ℚ), x ∈ Subgroup.zpowers σ₀) (N : ℕ)
    [NeZero N] (E : Type) [Field E] [NumberField E] [IsCyclotomicExtension {N} ℚ E] [Algebra K E]
    {q : ℕ} (hq : q.Prime) (hN : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ℓ = q) {a : ℚˣ}
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (a : ℚ) = 1) (u : InfinitePlace ℚ) :
    totalInvariant ℚ (cyclicBrauerHom hσ₀ a)
      = placeInvariant ℚ (ratPlace q hq) (cyclicBrauerHom hσ₀ a)
        * infinitePlaceInvariant ℚ u (cyclicBrauerHom hσ₀ a) := by
  classical
  have hvan : ∀ v ∉ ({ratPlace q hq} : Finset (HeightOneSpectrum (𝓞 ℚ))),
      placeInvariant ℚ v (cyclicBrauerHom hσ₀ a) = 1 := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    refine placeInvariant_cyclicBrauerHom_rat_eq_one_of_notMem hσ₀ N E v (fun ℓ hℓ hdvd hmem =>
      hv ?_) (ha v)
    refine heightOneSpectrum_rat_eq_of_natCast_mem hq ?_ (natCast_mem_ratPlace q hq)
    rw [← hN ℓ hℓ hdvd]
    exact hmem
  rw [totalInvariant_apply, finprod_placeInvariant_eq_prod ℚ _ _ hvan, Finset.prod_singleton,
    prod_infinitePlaceInvariant_rat _ u]

end OnePlace

/-! ### The quaternion algebra ramified at three and at infinity -/

section Corrector

variable (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {3} ℚ L] [IsGalois ℚ L]

/-- The cyclotomic field of the cube roots of unity is quadratic over the rationals. -/
theorem card_gal_cyclotomic_three : Nat.card Gal(L/ℚ) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [IsGalois.card_aut_eq_finrank ℚ L, finrank_cyclotomic_of_prime 3 L]

/-- **The invariant at the conductor of the cyclic algebra with coefficient minus one over the
cyclotomic field of the cube roots of unity is one half.**  The power residue symbol there reads
half the predecessor of the conductor, which is one, and the degree is two. -/
theorem placeInvariant_cyclicBrauerHom_three_neg_one {g : ℕ} (hg : Nat.Coprime g 3)
    (hgord : ∀ k : ℕ, 3 ∣ g ^ k - 1 → (3 - 1) ∣ k)
    (hgen : ∀ x : Gal(L/ℚ), x ∈ Subgroup.zpowers (cyclotomicPowerAut 3 L hg)) {a : ℚˣ}
    (hap : (a : ℚ) = -1) :
    placeInvariant ℚ (ratPlace 3 Nat.prime_three)
        (cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := L) hgen) a)
      = Multiplicative.ofAdd (QuotientAddGroup.mk (1 / 2 : ℚ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclotomicExtension {3 ^ 1} ℚ L := by rw [pow_one]; infer_instance
  have hodd : Odd 3 := by decide
  obtain ⟨W, hW⟩ := exists_primeUnder_eq (𝓞 ℚ) (𝓞 L) (ratPlace 3 Nat.prime_three)
  haveI := liesOver_span_of_primeUnder_eq_ratPlace Nat.prime_three W hW
  have hmem : ((3 : ℕ) : 𝓞 L) ∈ (primeUnder (𝓞 L) W).asIdeal := by
    rw [primeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact natCast_mem_of_liesOver_span (q := 3) W.asIdeal
  haveI := liesOver_span_of_natCast_mem Nat.prime_three (primeUnder (𝓞 L) W) hmem
  have hinert : Ideal.inertia Gal(L/ℚ) (primeUnder (𝓞 L) W).asIdeal = ⊤ :=
    inertia_eq_top_cyclotomic_primePow 3 1 L _
  have hinv := placeInvariant_cyclicBrauerHom_conductor 3 L L Nat.prime_three hodd W
    (card_gal_cyclotomic_three L) hinert hg hgord hgen
    (dvd_neg_one_sub_pow_half Nat.prime_three hodd hg hgord) (by rw [hap]; norm_num)
  rw [primeUnder_eq_ratPlace Nat.prime_three (primeUnder (𝓞 L) W)] at hinv
  rw [hinv, show (((3 - 1) / 2 : ℕ) : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num,
    zmodQModZ_intCast]
  norm_num

end Corrector

/-! ### Correcting the archimedean invariant -/

section Real

/-- **A Brauer class of the rationals of order two which the reals do not split and whose
invariants add up to zero.**  It is the cyclic algebra with coefficient minus one over the
cyclotomic field of the cube roots of unity.  Its invariant at three is one half; if the reals
split it, its invariants would already be known to add up to zero and the invariant at three would
be the whole sum, which is absurd.  So the archimedean invariant is nontrivial, hence also one
half, and the two cancel. -/
theorem exists_brauer_corrector_real :
    ∃ z : BrauerGroup.{0, 0} ℚ, z ^ 2 = 1 ∧ z ∉ BrauerGroup.relative ℚ ℝ ∧
      totalInvariant ℚ z = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := CyclotomicField 3 ℚ with hL
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {3} ℚ L
  obtain ⟨g, hg, hgord⟩ := exists_nat_primitiveRoot_of_prime (q := 3) Nat.prime_three
  have hgen := forall_mem_zpowers_cyclotomicPowerAut 3 L Nat.prime_three hg hgord
  set a : ℚˣ := -1 with ha
  have hap : (a : ℚ) = -1 := by rw [ha, Units.val_neg, Units.val_one]
  set z := cyclicBrauerHom (forall_mem_zpowers_restrictNormal (L := L) hgen) a with hz
  have hfr : finrank ℚ L = 2 := finrank_cyclotomic_of_prime 3 L
  have hz2 : z ^ 2 = 1 := by
    have h := pow_finrank_eq_one_of_mem_relative (L := L) z
      (cyclicBrauerHom_mem_relative (forall_mem_zpowers_restrictNormal (L := L) hgen) a)
    rwa [hfr] at h
  have hcond : placeInvariant ℚ (ratPlace 3 Nat.prime_three) z
      = Multiplicative.ofAdd (QuotientAddGroup.mk (1 / 2 : ℚ)) :=
    placeInvariant_cyclicBrauerHom_three_neg_one L hg hgord hgen hap
  obtain ⟨u⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  have hunit : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (a : ℚ) = 1 := by
    intro v
    rw [hap, Valuation.map_neg, map_one]
  have hN : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 3 → ℓ = 3 := fun ℓ hℓ hd =>
    (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp hd
  have hsplit : totalInvariant ℚ z
      = placeInvariant ℚ (ratPlace 3 Nat.prime_three) z * infinitePlaceInvariant ℚ u z :=
    totalInvariant_cyclicBrauerHom_rat_eq_mul_infinite _ 3 L Nat.prime_three hN hunit u
  have hhalf : Multiplicative.ofAdd (QuotientAddGroup.mk (1 / 2 : ℚ))
      ≠ (1 : Multiplicative QModZ) :=
    fun h => QModZ.mk_half_ne_zero (Multiplicative.toAdd.injective h)
  have hnotreal : z ∉ BrauerGroup.relative ℚ ℝ := by
    intro hmemreal
    have hinf : infinitePlaceInvariant ℚ u z = 1 :=
      (infinitePlaceInvariant_rat_eq_one_iff u z).mpr hmemreal
    have hzero : totalInvariant ℚ z = 1 :=
      totalInvariant_eq_one_of_mem_relative_real (e := 1) Nat.prime_two hasAuxPrimes_two
        hmemreal (by rw [pow_one]; exact hz2)
    rw [hsplit, hinf, mul_one, hcond] at hzero
    exact hhalf hzero
  refine ⟨z, hz2, hnotreal, ?_⟩
  have hinfne : infinitePlaceInvariant ℚ u z ≠ 1 := fun h =>
    hnotreal ((infinitePlaceInvariant_rat_eq_one_iff u z).mp h)
  have hinfsq : infinitePlaceInvariant ℚ u z ^ 2 = 1 := by
    rw [← map_pow, hz2, map_one]
  rw [hsplit, hcond, eq_ofAdd_half_of_sq_eq_one hinfsq hinfne, ← ofAdd_add,
    QModZ.mk_half_add_self]
  rfl

/-- **The product of two Brauer classes of the rationals which the reals do not split is split by
the reals**, because the Brauer group of the reals has order two. -/
theorem mul_mem_relative_real_of_notMem {x z : BrauerGroup.{0, 0} ℚ}
    (hx : x ∉ BrauerGroup.relative ℚ ℝ) (hz : z ∉ BrauerGroup.relative ℚ ℝ) :
    x * z ∈ BrauerGroup.relative ℚ ℝ := by
  have hker : ∀ y : BrauerGroup.{0, 0} ℚ,
      y ∈ BrauerGroup.relative ℚ ℝ ↔ BrauerGroup.baseChangeHom ℝ y = 1 := fun y => by
    rw [BrauerGroup.relative, MonoidHom.mem_ker]
  rw [hker] at hx hz ⊢
  rw [map_mul, eq_of_ne_one_brauerGroup_real hx hz, ← sq]
  exact sq_eq_one_brauerGroup_real _

end Real

/-! ### Global reciprocity -/

section Reciprocity

/-- **The invariants of a Brauer class of two-power order over the rationals add up to zero.**  If
the reals split the class this is the reduction spending one auxiliary prime per bad prime; if not,
multiplying by the quaternion algebra ramified at three and at infinity moves the class into that
case without changing the sum of its invariants. -/
theorem totalInvariant_eq_one_of_pow_eq_one_two_pow {e : ℕ} {x : BrauerGroup.{0, 0} ℚ}
    (hx : x ^ 2 ^ e = 1) : totalInvariant ℚ x = 1 := by
  by_cases hxreal : x ∈ BrauerGroup.relative ℚ ℝ
  · exact totalInvariant_eq_one_of_mem_relative_real Nat.prime_two hasAuxPrimes_two hxreal hx
  obtain ⟨z, hz2, hzreal, hztot⟩ := exists_brauer_corrector_real
  have hxz : x * z ∈ BrauerGroup.relative ℚ ℝ := mul_mem_relative_real_of_notMem hxreal hzreal
  have hpow : (x * z) ^ 2 ^ max e 1 = 1 := by
    obtain ⟨k, hk⟩ : (2 : ℕ) ^ e ∣ 2 ^ max e 1 := pow_dvd_pow 2 (le_max_left e 1)
    obtain ⟨l, hl⟩ : (2 : ℕ) ^ 1 ∣ 2 ^ max e 1 := pow_dvd_pow 2 (le_max_right e 1)
    have h1 : x ^ 2 ^ max e 1 = 1 := by rw [hk, pow_mul, hx, one_pow]
    have h2 : z ^ 2 ^ max e 1 = 1 := by rw [hl, pow_mul, pow_one, hz2, one_pow]
    rw [mul_pow, h1, h2, one_mul]
  have hsum := totalInvariant_eq_one_of_mem_relative_real Nat.prime_two hasAuxPrimes_two hxz hpow
  rwa [map_mul, hztot, mul_one] at hsum

/-- **The invariants of a Brauer class of finite order over the rationals add up to zero.**
Splitting the order into its two-part and its odd part, a Bézout relation writes the class as a
product of a class of two-power order and a class of odd order. -/
theorem totalInvariant_eq_one_of_pow_eq_one_nat {n : ℕ} (hn : n ≠ 0) {x : BrauerGroup.{0, 0} ℚ}
    (hx : x ^ n = 1) : totalInvariant ℚ x = 1 := by
  set k := n.factorization 2 with hk
  set q := 2 ^ k with hq
  set m := n / q with hm
  have hqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime q m := Nat.Coprime.pow_left k (Nat.coprime_ordCompl Nat.prime_two hn)
  have hmodd : Odd m :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))
  have hA : totalInvariant ℚ (x ^ m) = 1 :=
    totalInvariant_eq_one_of_pow_eq_one_two_pow (e := k)
      (by rw [← pow_mul, mul_comm m q, hqm, hx])
  have hB : totalInvariant ℚ (x ^ q) = 1 :=
    totalInvariant_eq_one_of_pow_eq_one_odd m hmodd (x ^ q) (by rw [← pow_mul, hqm, hx])
  have hbez : (1 : ℤ) = (q : ℤ) * Nat.gcdA q m + (m : ℤ) * Nat.gcdB q m := by
    have hg := Nat.gcd_eq_gcd_ab q m
    rwa [hcop, Nat.cast_one] at hg
  have hsplit : x = (x ^ q) ^ (Nat.gcdA q m) * (x ^ m) ^ (Nat.gcdB q m) := by
    rw [← zpow_natCast x q, ← zpow_natCast x m, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
      zpow_one]
  rw [hsplit, map_mul, map_zpow, map_zpow, hA, hB, one_zpow, one_zpow, one_mul]

/-- **Global reciprocity over the rationals: the invariants of a Brauer class add up to zero.**
Every Brauer class of a perfect field is of finite order, being split by a finite Galois
extension. -/
theorem totalInvariant_eq_one (x : BrauerGroup.{0, 0} ℚ) : totalInvariant ℚ x = 1 := by
  obtain ⟨n, hn, hxn⟩ := exists_pow_eq_one x
  exact totalInvariant_eq_one_of_pow_eq_one_nat hn hxn

end Reciprocity

end InverseGalois.CFT
