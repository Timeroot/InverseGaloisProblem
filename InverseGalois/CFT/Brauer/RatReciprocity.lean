/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceInvariantFinite
import InverseGalois.CFT.Brauer.SubcyclotomicCorrector
import InverseGalois.CFT.Cyclotomic.Splitting
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.Scholz.AuxPrimePair
import InverseGalois.CFT.Scholz.DyadicAuxPrime
import InverseGalois.CFT.Scholz.PrimeIndependence

/-!
# Global reciprocity over the rationals for a class of odd order

The invariants of a Brauer class over the rationals add up to zero.  For a class of odd prime-power
order this is proved by reducing the number of primes carrying a nontrivial invariant until only
one is left, at which point a single subfield of a cyclotomic field splits the class and the
invariants of a cyclic algebra cancel.  A class of arbitrary odd order is a product of classes of
prime-power order, one for each prime factor, so the prime-power case carries the general one.

The reduction spends one auxiliary prime per step.  Two rational primes carrying nontrivial
invariants are both power non-residues modulo infinitely many primes, by the density argument
behind the choice of auxiliary primes in the Scholz–Reichardt construction; modulo such a prime
each of them is the coefficient of a cyclic algebra whose invariants live only at it and at the
auxiliary prime.  Multiplying by suitable powers of those two algebras cancels both invariants at
the cost of creating one at the auxiliary prime, and leaves the total invariant unchanged.  The
count therefore drops by one at each step.

## Main results

* `InverseGalois.CFT.HasAuxPrimes`: the supply of auxiliary primes the reduction consumes, with a
  prescribed excess of the degree of the correcting field over the order of the class.
* `InverseGalois.CFT.exists_prime_two_mul_dvd_sub_one_pow_ne_one` and
  `InverseGalois.CFT.hasAuxPrimes_of_odd`: **an auxiliary prime congruent to one modulo twice a
  given odd prime power, modulo which two prescribed rational primes are both power non-residues
  for the prime exponent** — a supply with no excess.
* `InverseGalois.CFT.totalInvariant_eq_one_of_pow_eq_one`: **the invariants of a Brauer class of
  odd prime-power order over the rationals add up to zero.**
* `InverseGalois.CFT.totalInvariant_eq_one_of_pow_eq_one_odd`: **the invariants of a Brauer class
  of odd order over the rationals add up to zero.**

## Tags

Brauer group, local invariant, global reciprocity, cyclotomic field, power residue symbol,
auxiliary prime, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField InverseGalois.NumberTheory

/-! ### The place attached to a rational prime -/

section Place

/-- The place attached to a rational prime depends only on the prime. -/
theorem ratPlace_congr {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p = q) :
    ratPlace p hp = ratPlace q hq := by
  subst h
  rfl

end Place

/-! ### The auxiliary prime -/

section AuxPrime

/-- **A supply of auxiliary primes for the reduction**, with a prescribed excess `j`.  For every
nonzero exponent, every two rational primes and every finite set of primes to avoid it produces a
prime congruent to one modulo twice that power of `ℓ` modulo which neither of the two prescribed
primes is an `ℓ ^ (j + 1)`-th power residue.  The excess measures how much larger than the order of
a Brauer class the degree of the field correcting it has to be. -/
def HasAuxPrimes (ℓ j : ℕ) : Prop :=
  ∀ d : ℕ, d ≠ 0 → ∀ p₁ p₂ : ℕ, p₁.Prime → p₂.Prime → ∀ T : Finset ℕ,
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ 2 * ℓ ^ d ∣ q - 1 ∧
      ((p₁ : ℕ) : ZMod q) ^ ((q - 1) / ℓ ^ (j + 1)) ≠ 1 ∧
      ((p₂ : ℕ) : ZMod q) ^ ((q - 1) / ℓ ^ (j + 1)) ≠ 1

/-- **An auxiliary prime congruent to one modulo twice a given odd prime power, modulo which two
prescribed rational primes are both power non-residues for the prime exponent.**  A rational prime
is never an `ℓ`-th power in the rationals, so the density argument behind the choice of auxiliary
primes applies to the cyclotomic field of the `ℓ^e`-th roots of unity, whose Galois group is
abelian and which contains the `ℓ`-th roots of unity; a prime splitting completely there is
congruent to one modulo `ℓ^e`, hence odd, and an odd prime congruent to one modulo an odd number is
congruent to one modulo twice it. -/
theorem exists_prime_two_mul_dvd_sub_one_pow_ne_one {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    (he : e ≠ 0) {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ 2 * ℓ ^ e ∣ q - 1 ∧
      ((p₁ : ℕ) : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 ∧ ((p₂ : ℕ) : ZMod q) ^ ((q - 1) / ℓ) ≠ 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (ℓ ^ e) := ⟨pow_ne_zero e hℓ.ne_zero⟩
  have hℓ3 : 2 < ℓ := by
    rcases hℓ.two_le.lt_or_eq with h | h
    · exact h
    · rw [← h, Nat.odd_iff] at hℓodd
      omega
  have hle : ℓ ≤ ℓ ^ e := Nat.le_self_pow he ℓ
  have hnil : Group.IsNilpotent Gal(↥(cycSubfield (ℓ ^ e))/ℚ) :=
    nilpotent_of_mulEquiv
      (IsCyclotomicExtension.Rat.galEquivZMod (ℓ ^ e) ↥(cycSubfield (ℓ ^ e))).symm
  have hprod : ℓ ^ e = ℓ ^ (e - 1) * ℓ := by
    conv_lhs => rw [show e = (e - 1) + 1 by omega]
    rw [pow_succ]
  have hζ : IsPrimitiveRoot (cycRoot (ℓ ^ e) ^ ℓ ^ (e - 1)) ℓ :=
    IsPrimitiveRoot.pow (Nat.pos_of_ne_zero (pow_ne_zero e hℓ.ne_zero)) (cycRoot_spec (ℓ ^ e)) hprod
  have hmem : cycRoot (ℓ ^ e) ∈ cycSubfield (ℓ ^ e) := IntermediateField.subset_adjoin ℚ _ rfl
  have hζA : cycRoot (ℓ ^ e) ^ ℓ ^ (e - 1) ∈ cycSubfield (ℓ ^ e) := pow_mem hmem _
  have hv : ∀ p : ℕ, p.Prime → ∀ y : ℚ, y ^ ℓ ≠ ((p : ℤ) : ℚ) := by
    intro p hp
    have h := pow_ne_prod_pow (ℓ := ℓ) (S := ({p} : Finset ℕ)) (a := fun _ => 1) (p₀ := p)
      (fun r hr => by rwa [Finset.mem_singleton.mp hr]) (Finset.mem_singleton_self p)
      (fun hd => hℓ.one_lt.ne' (Nat.dvd_one.mp hd))
    intro y
    simpa using h y
  have hpow : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥(cycSubfield (ℓ ^ e)) q →
      ℓ ^ e ∣ q - 1 := by
    intro q hq hqℓ hs
    haveI : Fact q.Prime := ⟨hq⟩
    have hnd : ¬ q ∣ ℓ ^ e := fun h =>
      hqℓ ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp (hq.dvd_of_dvd_pow h))
    exact (Nat.modEq_iff_dvd' hq.one_le).mp
      (modEq_of_splitsCompletely (ℓ ^ e) ↥(cycSubfield (ℓ ^ e)) q hnd hs).symm
  obtain ⟨q, hqp, hqT, hqℓ, hqs, hq₁, hq₂⟩ :=
    exists_prime_splitsCompletely_pow_ne_one₂ (A := cycSubfield (ℓ ^ e)) (v₁ := (p₁ : ℤ))
      (v₂ := (p₂ : ℤ)) hℓ3 hnil hζ hζA (hv p₁ hp₁) (hv p₂ hp₂) T
      fun r hr hrℓ hs => dvd_trans (dvd_pow_self ℓ he) (hpow r hr hrℓ hs)
  have hdvd : ℓ ^ e ∣ q - 1 := hpow q hqp hqℓ hqs
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hpar : 2 ∣ q - 1 := by
    obtain ⟨m, hm⟩ := hqp.odd_of_ne_two hq2
    omega
  have hcop : Nat.Coprime 2 (ℓ ^ e) :=
    ((Nat.coprime_primes Nat.prime_two hℓ).mpr (by omega)).pow_right e
  exact ⟨q, hqp, hqT, Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpar hdvd, by exact_mod_cast hq₁,
    by exact_mod_cast hq₂⟩

/-- **An odd prime has a supply of auxiliary primes with no excess**: two rational primes are
already non-residues for the prime exponent itself modulo infinitely many primes congruent to one
modulo twice any power of it. -/
theorem hasAuxPrimes_of_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) : HasAuxPrimes ℓ 0 := by
  intro d hd p₁ p₂ hp₁ hp₂ T
  obtain ⟨q, hqp, hqT, hqdvd, hq₁, hq₂⟩ :=
    exists_prime_two_mul_dvd_sub_one_pow_ne_one hℓ hℓodd hd hp₁ hp₂ T
  exact ⟨q, hqp, hqT, hqdvd, by simpa using hq₁, by simpa using hq₂⟩

/-- **The prime two has a supply of auxiliary primes with excess one**: two rational primes are
both fourth-power non-residues modulo infinitely many primes congruent to one modulo twice any
power of two.  Squares would not do, since such a prime is congruent to one modulo eight and two is
therefore a square modulo it. -/
theorem hasAuxPrimes_two : HasAuxPrimes 2 1 := by
  intro d hd p₁ p₂ hp₁ hp₂ T
  have hexp : (2 : ℕ) * 2 ^ d = 2 ^ (d + 1) := by rw [pow_succ]; ring
  have he : 2 ≤ d + 1 := by omega
  by_cases hboth : p₁ = 2 ∧ p₂ = 2
  · obtain ⟨h1, h2⟩ := hboth
    subst h1
    subst h2
    obtain ⟨q, hqp, hqT, hqdvd, hq₁, -⟩ :=
      exists_prime_dvd_sub_one_pow_four_ne_one he Nat.prime_two Nat.prime_three
        (by rintro ⟨-, h⟩; norm_num at h) T
    exact ⟨q, hqp, hqT, by rw [hexp]; exact hqdvd, by simpa using hq₁, by simpa using hq₁⟩
  · obtain ⟨q, hqp, hqT, hqdvd, hq₁, hq₂⟩ :=
      exists_prime_dvd_sub_one_pow_four_ne_one he hp₁ hp₂ hboth T
    exact ⟨q, hqp, hqT, by rw [hexp]; exact hqdvd, by simpa using hq₁, by simpa using hq₂⟩

end AuxPrime

/-! ### Reducing the number of bad primes -/

section Reduction

/-- **Reciprocity for a class of prime-power order with at most one bad prime.**  A single
auxiliary prime modulo which that prime is a power non-residue splits the class over the
corresponding subfield of a cyclotomic field. -/
theorem totalInvariant_eq_one_of_forall_eq {ℓ j e : ℕ} (hℓ : ℓ.Prime) (haux : HasAuxPrimes ℓ j)
    (he : e ≠ 0) {x : BrauerGroup.{0, 0} ℚ} (hxreal : x ∈ BrauerGroup.relative ℚ ℝ)
    (hx : x ^ ℓ ^ e = 1) {p₀ : ℕ} (hp₀ : p₀.Prime)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 → p = p₀) :
    totalInvariant ℚ x = 1 := by
  classical
  obtain ⟨q, hqp, hqT, hqdvd, hq₀, -⟩ := haux (e + j) (by omega) p₀ p₀ hp₀ hp₀ ({p₀} : Finset ℕ)
  have harith : e + j - e + 1 = j + 1 := by omega
  refine totalInvariant_eq_one_of_forall_pow_ne_one_primePow hℓ he (Nat.le_add_right e j) hxreal hx
    hqp hqdvd fun p hp hinv => ?_
  have hpeq : p = p₀ := hbad p hp hinv
  refine ⟨fun h => hqT (Finset.mem_singleton.mpr (h ▸ hpeq)), ?_⟩
  rw [hpeq, harith]
  exact hq₀

/-- **Reciprocity for a class of prime-power order whose bad primes lie in a set of at most one
element.** -/
theorem totalInvariant_eq_one_of_card_le_one {ℓ j e : ℕ} (hℓ : ℓ.Prime) (haux : HasAuxPrimes ℓ j)
    (he : e ≠ 0) {x : BrauerGroup.{0, 0} ℚ} (hxreal : x ∈ BrauerGroup.relative ℚ ℝ)
    (hx : x ^ ℓ ^ e = 1)
    (S : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 1)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 → p ∈ S) :
    totalInvariant ℚ x = 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀S⟩
  · exact totalInvariant_eq_one_of_forall_eq hℓ haux he hxreal hx Nat.prime_two
      fun p hp hinv => absurd (hbad p hp hinv) (Finset.notMem_empty p)
  · exact totalInvariant_eq_one_of_forall_eq hℓ haux he hxreal hx (hSp p₀ hp₀S)
      fun p hp hinv => Finset.card_le_one.mp hcard p (hbad p hp hinv) p₀ hp₀S

/-- **Reciprocity for a class of prime-power order whose bad primes lie in a set of bounded size**,
by induction on the bound.  Two bad primes are cancelled at once against a common auxiliary prime,
which lowers the count by one at the cost of raising the order of the class by the excess of the
supply of auxiliary primes. -/
theorem totalInvariant_eq_one_of_card_le {ℓ j : ℕ} (hℓ : ℓ.Prime) (haux : HasAuxPrimes ℓ j)
    (n : ℕ) :
    ∀ e : ℕ, e ≠ 0 → ∀ x : BrauerGroup.{0, 0} ℚ, x ∈ BrauerGroup.relative ℚ ℝ → x ^ ℓ ^ e = 1 →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → S.card ≤ n →
        (∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 → p ∈ S) →
        totalInvariant ℚ x = 1 := by
  classical
  induction n with
  | zero =>
    intro e he x hxreal hx S hSp hcard hbad
    exact totalInvariant_eq_one_of_card_le_one hℓ haux he hxreal hx S hSp (by omega) hbad
  | succ n ih =>
    intro e he x hxreal hx S hSp hcard hbad
    by_cases hle : S.card ≤ 1
    · exact totalInvariant_eq_one_of_card_le_one hℓ haux he hxreal hx S hSp hle hbad
    have hlt : 1 < S.card := by omega
    obtain ⟨p₁, hp₁S, p₂, hp₂S, hne⟩ := Finset.one_lt_card.mp hlt
    have hp₁ : p₁.Prime := hSp p₁ hp₁S
    have hp₂ : p₂.Prime := hSp p₂ hp₂S
    obtain ⟨q, hqp, hqS, hqdvd, hq₁, hq₂⟩ := haux (e + j) (by omega) p₁ p₂ hp₁ hp₂ S
    have harith : e + j - e + 1 = j + 1 := by omega
    have hq₁' : ((p₁ : ℕ) : ZMod q) ^ ((q - 1) / ℓ ^ (e + j - e + 1)) ≠ 1 := by rwa [harith]
    have hq₂' : ((p₂ : ℕ) : ZMod q) ^ ((q - 1) / ℓ ^ (e + j - e + 1)) ≠ 1 := by rwa [harith]
    have hp₁q : p₁ ≠ q := fun h => hqS (h ▸ hp₁S)
    have hp₂q : p₂ ≠ q := fun h => hqS (h ▸ hp₂S)
    have hinvpow : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((placeInvariant ℚ v x)⁻¹) ^ ℓ ^ e = 1 := by
      intro v
      rw [inv_pow, ← map_pow, hx, map_one, inv_one]
    have hxd : x ^ ℓ ^ (e + j) = 1 := by
      rw [pow_add, pow_mul, hx, one_pow]
    obtain ⟨y₁, hy₁pow, hy₁tot, hy₁real, hy₁p, hy₁van⟩ :=
      exists_placeInvariant_eq_of_pow_ne_one hℓ he (Nat.le_add_right e j) hqp hqdvd hp₁ hp₁q hq₁'
        (hinvpow (ratPlace p₁ hp₁))
    obtain ⟨y₂, hy₂pow, hy₂tot, hy₂real, hy₂p, hy₂van⟩ :=
      exists_placeInvariant_eq_of_pow_ne_one hℓ he (Nat.le_add_right e j) hqp hqdvd hp₂ hp₂q hq₂'
        (hinvpow (ratPlace p₂ hp₂))
    have hkey : totalInvariant ℚ (x * y₁ * y₂) = totalInvariant ℚ x := by
      rw [map_mul, map_mul, hy₁tot, hy₂tot, mul_one, mul_one]
    rw [← hkey]
    refine ih (e + j) (by omega) (x * y₁ * y₂) (mul_mem (mul_mem hxreal hy₁real) hy₂real)
      (by rw [mul_pow, mul_pow, hxd, hy₁pow, hy₂pow, one_mul, one_mul])
      (insert q (S \ ({p₁, p₂} : Finset ℕ))) ?_ ?_ ?_
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr'
      · exact hqp
      · exact hSp r (Finset.mem_sdiff.mp hr').1
    · have hpair : ({p₁, p₂} : Finset ℕ) ⊆ S := by
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr'
        · exact hp₁S
        · exact Finset.mem_singleton.mp hr' ▸ hp₂S
      have hsub : (S \ ({p₁, p₂} : Finset ℕ)).card = S.card - 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpair, Finset.card_pair hne]
      have hins := Finset.card_insert_le q (S \ ({p₁, p₂} : Finset ℕ))
      omega
    · intro r hr hinv
      by_contra hnot
      refine hinv ?_
      rw [Finset.mem_insert] at hnot
      push_neg at hnot
      obtain ⟨hrq, hrS⟩ := hnot
      rw [Finset.mem_sdiff] at hrS
      push_neg at hrS
      rw [map_mul, map_mul]
      by_cases hr₁ : r = p₁
      · rw [ratPlace_congr hr hp₁ hr₁, hy₁p,
          hy₂van (ratPlace p₁ hp₁) (ratPlace_ne_ratPlace hp₁ hp₂ hne)
            (ratPlace_ne_ratPlace hp₁ hqp hp₁q), mul_one, mul_inv_cancel]
      by_cases hr₂ : r = p₂
      · rw [ratPlace_congr hr hp₂ hr₂,
          hy₁van (ratPlace p₂ hp₂) (ratPlace_ne_ratPlace hp₂ hp₁ (Ne.symm hne))
            (ratPlace_ne_ratPlace hp₂ hqp hp₂q), hy₂p, mul_one, mul_inv_cancel]
      have hrS' : r ∉ S := by
        intro h
        rcases Finset.mem_insert.mp (hrS h) with h' | h'
        · exact hr₁ h'
        · exact hr₂ (Finset.mem_singleton.mp h')
      have hxr : placeInvariant ℚ (ratPlace r hr) x = 1 := by
        by_contra hc
        exact hrS' (hbad r hr hc)
      rw [hxr, hy₁van (ratPlace r hr) (ratPlace_ne_ratPlace hr hp₁ hr₁)
          (ratPlace_ne_ratPlace hr hqp hrq),
        hy₂van (ratPlace r hr) (ratPlace_ne_ratPlace hr hp₂ hr₂)
          (ratPlace_ne_ratPlace hr hqp hrq), mul_one, mul_one]

end Reduction

/-! ### Global reciprocity -/

section Reciprocity

/-- **The invariants of a Brauer class of odd prime-power order over the rationals add up to
zero.**  Its invariants are nontrivial at only finitely many places, and the rational primes below
them form a finite set which the reduction shrinks one element at a time. -/
theorem totalInvariant_eq_one_of_pow_eq_one {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    {x : BrauerGroup.{0, 0} ℚ} (hx : x ^ ℓ ^ e = 1) : totalInvariant ℚ x = 1 := by
  classical
  rcases eq_or_ne e 0 with rfl | he
  · rw [pow_zero, pow_one] at hx
    rw [hx, map_one]
  have hfin := finite_setOf_placeInvariant_ne_one (k := ℚ) x
  obtain ⟨S, hSp, hbad⟩ : ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 → p ∈ S := by
    refine ⟨hfin.toFinset.image fun v => Rat.HeightOneSpectrum.natGenerator v, ?_, ?_⟩
    · intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
      exact Rat.HeightOneSpectrum.prime_natGenerator v
    · intro p hp hinv
      exact Finset.mem_image.mpr ⟨ratPlace p hp, hfin.mem_toFinset.mpr hinv,
        natGenerator_eq_of_natCast_mem hp (natCast_mem_ratPlace p hp)⟩
  exact totalInvariant_eq_one_of_card_le hℓ (hasAuxPrimes_of_odd hℓ hℓodd) S.card e he x
    (mem_relative_real_of_odd_pow_eq_one hℓodd.pow hx) hx S hSp le_rfl hbad

/-- **The invariants of a Brauer class of odd order over the rationals add up to zero.**  Splitting
the order at its least prime factor into a prime power and a coprime cofactor, a Bézout relation
writes the class as a product of a class killed by the prime power and a class killed by the
strictly smaller cofactor; the first is covered by the prime-power case and the second by
induction. -/
theorem totalInvariant_eq_one_of_pow_eq_one_odd :
    ∀ n : ℕ, Odd n → ∀ x : BrauerGroup.{0, 0} ℚ, x ^ n = 1 → totalInvariant ℚ x = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd x hx
    have hn : n ≠ 0 := by
      rintro rfl
      rw [Nat.odd_iff] at hodd
      omega
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with h1 | h1
    · rw [← h1, pow_one] at hx
      rw [hx, map_one]
    set p := n.minFac with hp
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have hpodd : Odd p := hodd.of_dvd_nat (Nat.minFac_dvd n)
    set k := n.factorization p with hk
    set q := p ^ k with hq
    set m := n / q with hm
    have hqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hcop : Nat.Coprime q m := Nat.Coprime.pow_left k (Nat.coprime_ordCompl hpp hn)
    have hm0 : m ≠ 0 := by
      intro hc
      rw [hc, mul_zero] at hqm
      exact hn hqm.symm
    have hk1 : 1 ≤ k := hpp.factorization_pos_of_dvd hn (Nat.minFac_dvd n)
    have hq2 : 2 ≤ q := le_trans hpp.two_le (le_trans (le_of_eq (pow_one p).symm)
      (Nat.pow_le_pow_right hpp.pos hk1))
    have hmn : m < n := by
      rw [← hqm]
      nlinarith [Nat.pos_of_ne_zero hm0]
    have hmdvd : m ∣ n := ⟨q, by rw [← hqm]; exact mul_comm q m⟩
    have hA : totalInvariant ℚ (x ^ m) = 1 := by
      refine totalInvariant_eq_one_of_pow_eq_one (e := k) hpp hpodd ?_
      rw [← pow_mul, mul_comm m q, hqm, hx]
    have hB : totalInvariant ℚ (x ^ q) = 1 := by
      refine ih m hmn (hodd.of_dvd_nat hmdvd) (x ^ q) ?_
      rw [← pow_mul, hqm, hx]
    have hbez : (1 : ℤ) = (q : ℤ) * Nat.gcdA q m + (m : ℤ) * Nat.gcdB q m := by
      have hg := Nat.gcd_eq_gcd_ab q m
      rwa [hcop, Nat.cast_one] at hg
    have hsplit : x = (x ^ q) ^ (Nat.gcdA q m) * (x ^ m) ^ (Nat.gcdB q m) := by
      rw [← zpow_natCast x q, ← zpow_natCast x m, ← zpow_mul, ← zpow_mul, ← zpow_add,
        ← hbez, zpow_one]
    rw [hsplit, map_mul, map_zpow, map_zpow, hA, hB, one_zpow, one_zpow, one_mul]

end Reciprocity

end InverseGalois.CFT
