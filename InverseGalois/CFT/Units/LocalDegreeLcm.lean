/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.InertPlace

/-!
# The degree of a cyclic extension is the least common multiple of its local degrees

The order of the decomposition group at a place is the local degree there, and it divides the
degree of the extension.  Conversely, for a cyclic extension every prime power dividing the degree
is already reached by one of the local degrees: an exponent obtained from the degree by dividing out
one prime does not kill a generator, so some decomposition group has order failing to divide it, and
the finitely many places produced this way have the whole degree as their least common multiple.
Discarding any prescribed finite set of places of the base costs nothing.

Restated multiplicatively, the complementary degrees, the quotients of the degree by the local
degrees, have no common factor with the degree.  This is the arithmetic behind the surjectivity of
the sum of the local invariants on the classes of a cyclic algebra: a single place already carries
each prime part of the degree, so a suitable combination of local invariants realises any prescribed
value.

## Main results

* `InverseGalois.CFT.exists_finset_dvd_lcm_card_stabilizer`: **finitely many places of a cyclic
  extension, all avoiding a prescribed finite set of places of the base, have local degrees whose
  least common multiple is a multiple of the degree.**
* `InverseGalois.CFT.exists_finset_gcd_localDegree_eq_one`: **the complementary degrees at those
  places, together with the degree itself, have greatest common divisor one.**
* `InverseGalois.CFT.exists_finset_intCombination_localDegree_modEq`: **some integral combination of
  the complementary degrees at those places is congruent to one modulo the degree.**

## Tags

number field, local degree, cyclic extension, decomposition group, class field theory
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain MulAction InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

section LocalDegreeLcm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {S : Set (HeightOneSpectrum (𝓞 k))} {σ₀ : Gal(K/k)}

/-- **Finitely many places of a cyclic extension, all lying over primes outside a prescribed finite
set, have local degrees whose least common multiple is a multiple of the degree.**  For each prime
`p` dividing the degree `n`, the exponent `n / p` does not kill a generator, so some place away from
the prescribed set has local degree not dividing `n / p`; collecting one such place for every prime
factor of `n` gives the required finite set, since a proper divisor of `n` divides `n / p` for some
prime factor `p`. -/
theorem exists_finset_dvd_lcm_card_stabilizer
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (hS : S.Finite) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 K)), (∀ v ∈ F, primeUnder (𝓞 k) v ∉ S) ∧
      Nat.card Gal(K/k) ∣ F.lcm fun v => Nat.card ↥(stabilizer Gal(K/k) v) := by
  classical
  set n := Nat.card Gal(K/k) with hn
  have hn0 : n ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hord : orderOf σ₀ = n := orderOf_eq_card_of_forall_mem_zpowers hσ₀
  have hkey : ∀ p ∈ n.primeFactors, ∃ v : HeightOneSpectrum (𝓞 K),
      primeUnder (𝓞 k) v ∉ S ∧ ¬ Nat.card ↥(stabilizer Gal(K/k) v) ∣ n / p := by
    intro p hp
    obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.mp hp
    refine exists_card_stabilizer_not_dvd hσ₀ hS (m := n / p) ?_
    intro hpow
    have hdvd : n ∣ n / p := by
      have hd := orderOf_dvd_of_pow_eq_one hpow
      rwa [hord] at hd
    have hlt : n / p < n := Nat.div_lt_self hnpos hpp.one_lt
    have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hnpos hpn) hpp.pos
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  choose f hf1 hf2 using hkey
  refine ⟨n.primeFactors.attach.image fun p => f p.1 p.2, ?_, ?_⟩
  · intro v hv
    obtain ⟨⟨p, hp⟩, -, rfl⟩ := Finset.mem_image.mp hv
    exact hf1 p hp
  · set L := (n.primeFactors.attach.image fun p => f p.1 p.2).lcm
      fun v => Nat.card ↥(stabilizer Gal(K/k) v) with hL
    have hLn : L ∣ n := Finset.lcm_dvd fun v _ => Subgroup.card_subgroup_dvd_card _
    by_contra hcon
    obtain ⟨t, ht⟩ := hLn
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [mul_one] at ht
      exact hcon ht.dvd
    have hpp : t.minFac.Prime := Nat.minFac_prime ht1
    have hpt : t.minFac ∣ t := Nat.minFac_dvd t
    have htn : t ∣ n := ⟨L, by rw [ht, mul_comm]⟩
    have hpn : t.minFac ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpt.trans htn, hn0⟩
    have h1 : Nat.card ↥(stabilizer Gal(K/k) (f t.minFac hpn)) ∣ L :=
      Finset.dvd_lcm (Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨t.minFac, hpn⟩))
    have h2 : L ∣ n / t.minFac := by
      rw [ht, Nat.mul_div_assoc L hpt]
      exact dvd_mul_right L _
    exact hf2 t.minFac hpn (h1.trans h2)

/-- **The degree of a cyclic extension has greatest common divisor one with the complementary
degrees at finitely many places lying over primes outside a prescribed finite set.**  A common
divisor `g` of the degree and of every complementary degree makes every local degree divide the
degree divided by `g`, hence makes the least common multiple of the local degrees divide it too, and
that forces `g` to be one. -/
theorem exists_finset_gcd_localDegree_eq_one
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (hS : S.Finite) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 K)), (∀ v ∈ F, primeUnder (𝓞 k) v ∉ S) ∧
      Nat.gcd (Nat.card Gal(K/k))
        (F.gcd fun v => Nat.card Gal(K/k) / Nat.card ↥(stabilizer Gal(K/k) v)) = 1 := by
  obtain ⟨F, hFS, hFdvd⟩ := exists_finset_dvd_lcm_card_stabilizer hσ₀ hS
  refine ⟨F, hFS, ?_⟩
  set n := Nat.card Gal(K/k) with hn
  have hn0 : n ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  set g := Nat.gcd n (F.gcd fun v => n / Nat.card ↥(stabilizer Gal(K/k) v)) with hg
  have hgn : g ∣ n := Nat.gcd_dvd_left _ _
  have hg0 : 0 < g := Nat.pos_of_ne_zero fun h => hn0 (Nat.eq_zero_of_gcd_eq_zero_left (hg ▸ h))
  have hstep : ∀ v ∈ F, Nat.card ↥(stabilizer Gal(K/k) v) ∣ n / g := by
    intro v hv
    have hnv : Nat.card ↥(stabilizer Gal(K/k) v) ∣ n := Subgroup.card_subgroup_dvd_card _
    obtain ⟨c, hc⟩ : g ∣ n / Nat.card ↥(stabilizer Gal(K/k) v) :=
      (Nat.gcd_dvd_right _ _).trans (Finset.gcd_dvd hv)
    have hgd : n = g * (Nat.card ↥(stabilizer Gal(K/k) v) * c) := by
      rw [show g * (Nat.card ↥(stabilizer Gal(K/k) v) * c)
        = Nat.card ↥(stabilizer Gal(K/k) v) * (g * c) by ring, ← hc]
      exact (Nat.mul_div_cancel' hnv).symm
    exact ⟨c, by rw [hgd, Nat.mul_div_cancel_left _ hg0]⟩
  have hnng : n ∣ n / g := hFdvd.trans (Finset.lcm_dvd hstep)
  have hdivpos : 0 < n / g := by
    rw [Nat.div_pos_iff]
    exact ⟨hg0, Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hgn⟩
  have hdivg : n / g = n := le_antisymm (Nat.div_le_self n g) (Nat.le_of_dvd hdivpos hnng)
  have hmul : n * g = n := by
    have hcancel := Nat.div_mul_cancel hgn
    rwa [hdivg] at hcancel
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0) ?_
  rw [mul_one]
  exact hmul

end LocalDegreeLcm

section Bezout

/-- **A greatest common divisor of a family of natural numbers indexed by a finite set is an
integral linear combination of that family.**  Adjoining one index at a time reduces this to the
Bézout identity for a pair. -/
theorem exists_intCombination_eq_finsetGcd {β : Type*} (s : Finset β) (f : β → ℕ) :
    ∃ c : β → ℤ, ∑ b ∈ s, c b * (f b : ℤ) = ((s.gcd f : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ : ∃ d : β → ℤ, ∀ b, d b = if b = a then Nat.gcdA (f a) (s.gcd f)
        else Nat.gcdB (f a) (s.gcd f) * c b := ⟨_, fun _ => rfl⟩
    refine ⟨d, ?_⟩
    have hs : ∀ b ∈ s, d b * (f b : ℤ) = Nat.gcdB (f a) (s.gcd f) * (c b * (f b : ℤ)) := by
      intro b hb
      rw [hd b, if_neg (by rintro rfl; exact ha hb), mul_assoc]
    rw [Finset.sum_insert ha, hd a, if_pos rfl, Finset.sum_congr rfl hs, ← Finset.mul_sum, hc,
      Finset.gcd_insert, gcd_eq_nat_gcd, Nat.gcd_eq_gcd_ab]
    ring

end Bezout

section LocalDegreeCombination

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {S : Set (HeightOneSpectrum (𝓞 k))} {σ₀ : Gal(K/k)}

/-- **Some integral combination of the complementary degrees at finitely many places of a cyclic
extension, all lying over primes outside a prescribed finite set, is congruent to one modulo the
degree.**  Equivalently, the local invariants at those places already generate the group of global
invariants, the invariant at a place being a multiple of the reciprocal of the local degree. -/
theorem exists_finset_intCombination_localDegree_modEq
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀) (hS : S.Finite) :
    ∃ (F : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℤ),
      (∀ v ∈ F, primeUnder (𝓞 k) v ∉ S) ∧
      (∑ v ∈ F, c v * ((Nat.card Gal(K/k) / Nat.card ↥(stabilizer Gal(K/k) v) : ℕ) : ℤ)) ≡ 1
        [ZMOD (Nat.card Gal(K/k) : ℤ)] := by
  obtain ⟨F, hFS, hgcd⟩ := exists_finset_gcd_localDegree_eq_one hσ₀ hS
  set n := Nat.card Gal(K/k) with hn
  set f : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun v => n / Nat.card ↥(stabilizer Gal(K/k) v) with hf
  obtain ⟨c, hc⟩ := exists_intCombination_eq_finsetGcd F f
  refine ⟨F, fun v => Nat.gcdB n (F.gcd f) * c v, hFS, ?_⟩
  have hkey : (1 : ℤ) = n * Nat.gcdA n (F.gcd f) + ((F.gcd f : ℕ) : ℤ) * Nat.gcdB n (F.gcd f) := by
    have hab := Nat.gcd_eq_gcd_ab n (F.gcd f)
    rw [hgcd] at hab
    exact_mod_cast hab
  have hsum : (∑ v ∈ F, Nat.gcdB n (F.gcd f) * c v * (f v : ℤ))
      = Nat.gcdB n (F.gcd f) * ((F.gcd f : ℕ) : ℤ) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hc]
  rw [hsum]
  refine Int.modEq_iff_dvd.mpr ⟨Nat.gcdA n (F.gcd f), ?_⟩
  linear_combination hkey

end LocalDegreeCombination

end InverseGalois.CFT
