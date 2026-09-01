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
import InverseGalois.CFT.Scholz.PrimeIndependence

/-!
# Global reciprocity over the rationals for a class of odd prime order

The invariants of a Brauer class over the rationals add up to zero.  For a class of odd prime order
this is proved by reducing the number of primes carrying a nontrivial invariant until only one is
left, at which point a single subfield of a cyclotomic field splits the class and the invariants of
a cyclic algebra cancel.

The reduction spends one auxiliary prime per step.  Two rational primes carrying nontrivial
invariants are both power non-residues modulo infinitely many primes, by the density argument
behind the choice of auxiliary primes in the Scholz–Reichardt construction; modulo such a prime
each of them is the coefficient of a cyclic algebra whose invariants live only at it and at the
auxiliary prime.  Multiplying by suitable powers of those two algebras cancels both invariants at
the cost of creating one at the auxiliary prime, and leaves the total invariant unchanged.  The
count therefore drops by one at each step.

## Main results

* `InverseGalois.CFT.exists_prime_two_mul_dvd_sub_one_pow_ne_one`: **an auxiliary prime congruent
  to one modulo twice a given odd prime, modulo which two prescribed rational primes are both power
  non-residues.**
* `InverseGalois.CFT.totalInvariant_eq_one_of_pow_eq_one`: **the invariants of a Brauer class of
  odd prime order over the rationals add up to zero.**

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

/-- **An auxiliary prime congruent to one modulo twice a given odd prime, modulo which two
prescribed rational primes are both power non-residues.**  A rational prime is never an `N`-th
power in the rationals, so the density argument behind the choice of auxiliary primes applies to
the cyclotomic field of the `N`-th roots of unity, whose Galois group is abelian; a prime splitting
completely there is congruent to one modulo `N`, hence odd, and an odd prime congruent to one
modulo an odd number is congruent to one modulo twice it. -/
theorem exists_prime_two_mul_dvd_sub_one_pow_ne_one {N : ℕ} (hN : N.Prime) (hNodd : Odd N)
    {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (T : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ T ∧ 2 * N ∣ q - 1 ∧
      ((p₁ : ℕ) : ZMod q) ^ ((q - 1) / N) ≠ 1 ∧ ((p₂ : ℕ) : ZMod q) ^ ((q - 1) / N) ≠ 1 := by
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  have hN3 : 2 < N := by
    rcases hN.two_le.lt_or_eq with h | h
    · exact h
    · rw [← h, Nat.odd_iff] at hNodd
      omega
  have hnil : Group.IsNilpotent Gal(↥(cycSubfield N)/ℚ) :=
    nilpotent_of_mulEquiv (IsCyclotomicExtension.Rat.galEquivZMod N ↥(cycSubfield N)).symm
  have hζA : cycRoot N ∈ cycSubfield N := IntermediateField.subset_adjoin ℚ _ rfl
  have hv : ∀ p : ℕ, p.Prime → ∀ y : ℚ, y ^ N ≠ ((p : ℤ) : ℚ) := by
    intro p hp
    have h := pow_ne_prod_pow (ℓ := N) (S := ({p} : Finset ℕ)) (a := fun _ => 1) (p₀ := p)
      (fun r hr => by rwa [Finset.mem_singleton.mp hr]) (Finset.mem_singleton_self p)
      (fun hd => hN.one_lt.ne' (Nat.dvd_one.mp hd))
    intro y
    simpa using h y
  have hpow : ∀ q : ℕ, q.Prime → q ≠ N → SplitsCompletely ↥(cycSubfield N) q → N ∣ q - 1 := by
    intro q hq hqN hs
    haveI : Fact q.Prime := ⟨hq⟩
    have hnd : ¬ q ∣ N := fun h => hqN ((Nat.prime_dvd_prime_iff_eq hq hN).mp h)
    exact (Nat.modEq_iff_dvd' hq.one_le).mp
      (modEq_of_splitsCompletely N ↥(cycSubfield N) q hnd hs).symm
  obtain ⟨q, hqp, hqT, hqN, hqs, hq₁, hq₂⟩ :=
    exists_prime_splitsCompletely_pow_ne_one₂ (A := cycSubfield N) (v₁ := (p₁ : ℤ))
      (v₂ := (p₂ : ℤ)) hN3 hnil (cycRoot_spec N) hζA (hv p₁ hp₁) (hv p₂ hp₂) T hpow
  have hdvd : N ∣ q - 1 := hpow q hqp hqN hqs
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hpar : 2 ∣ q - 1 := by
    obtain ⟨m, hm⟩ := hqp.odd_of_ne_two hq2
    omega
  have hcop : Nat.Coprime 2 N := (Nat.coprime_primes Nat.prime_two hN).mpr (by omega)
  exact ⟨q, hqp, hqT, Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpar hdvd, by exact_mod_cast hq₁,
    by exact_mod_cast hq₂⟩

end AuxPrime

/-! ### Reducing the number of bad primes -/

section Reduction

/-- **Reciprocity for a class of odd prime order with at most one bad prime.**  A single auxiliary
prime modulo which that prime is a power non-residue splits the class over the corresponding
subfield of a cyclotomic field. -/
theorem totalInvariant_eq_one_of_forall_eq {N : ℕ} (hN : N.Prime) (hNodd : Odd N)
    {x : BrauerGroup.{0, 0} ℚ} (hx : x ^ N = 1) {p₀ : ℕ} (hp₀ : p₀.Prime)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 → p = p₀) :
    totalInvariant ℚ x = 1 := by
  classical
  obtain ⟨q, hqp, hqT, hqdvd, hq₀, -⟩ :=
    exists_prime_two_mul_dvd_sub_one_pow_ne_one hN hNodd hp₀ hp₀ ({p₀} : Finset ℕ)
  refine totalInvariant_eq_one_of_forall_pow_ne_one hN hNodd hx hqp hqdvd fun p hp hinv => ?_
  have hpeq : p = p₀ := hbad p hp hinv
  refine ⟨fun h => hqT (Finset.mem_singleton.mpr (h ▸ hpeq)), ?_⟩
  rw [hpeq]
  exact hq₀

/-- **Reciprocity for a class of odd prime order whose bad primes lie in a set of at most one
element.** -/
theorem totalInvariant_eq_one_of_card_le_one {N : ℕ} (hN : N.Prime) (hNodd : Odd N)
    {x : BrauerGroup.{0, 0} ℚ} (hx : x ^ N = 1) (S : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime)
    (hcard : S.card ≤ 1)
    (hbad : ∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 → p ∈ S) :
    totalInvariant ℚ x = 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀S⟩
  · exact totalInvariant_eq_one_of_forall_eq hN hNodd hx Nat.prime_two
      fun p hp hinv => absurd (hbad p hp hinv) (Finset.notMem_empty p)
  · exact totalInvariant_eq_one_of_forall_eq hN hNodd hx (hSp p₀ hp₀S)
      fun p hp hinv => Finset.card_le_one.mp hcard p (hbad p hp hinv) p₀ hp₀S

/-- **Reciprocity for a class of odd prime order whose bad primes lie in a set of bounded size**,
by induction on the bound.  Two bad primes are cancelled at once against a common auxiliary prime,
which lowers the count by one. -/
theorem totalInvariant_eq_one_of_card_le {N : ℕ} (hN : N.Prime) (hNodd : Odd N) (n : ℕ) :
    ∀ x : BrauerGroup.{0, 0} ℚ, x ^ N = 1 →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → S.card ≤ n →
        (∀ (p : ℕ) (hp : p.Prime), placeInvariant ℚ (ratPlace p hp) x ≠ 1 → p ∈ S) →
        totalInvariant ℚ x = 1 := by
  classical
  induction n with
  | zero =>
    intro x hx S hSp hcard hbad
    exact totalInvariant_eq_one_of_card_le_one hN hNodd hx S hSp (by omega) hbad
  | succ n ih =>
    intro x hx S hSp hcard hbad
    by_cases hle : S.card ≤ 1
    · exact totalInvariant_eq_one_of_card_le_one hN hNodd hx S hSp hle hbad
    have hlt : 1 < S.card := by omega
    obtain ⟨p₁, hp₁S, p₂, hp₂S, hne⟩ := Finset.one_lt_card.mp hlt
    have hp₁ : p₁.Prime := hSp p₁ hp₁S
    have hp₂ : p₂.Prime := hSp p₂ hp₂S
    obtain ⟨q, hqp, hqS, hqdvd, hq₁, hq₂⟩ :=
      exists_prime_two_mul_dvd_sub_one_pow_ne_one hN hNodd hp₁ hp₂ S
    have hp₁q : p₁ ≠ q := fun h => hqS (h ▸ hp₁S)
    have hp₂q : p₂ ≠ q := fun h => hqS (h ▸ hp₂S)
    have hinvpow : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((placeInvariant ℚ v x)⁻¹) ^ N = 1 := by
      intro v
      rw [inv_pow, ← map_pow, hx, map_one, inv_one]
    obtain ⟨y₁, hy₁pow, hy₁tot, hy₁p, hy₁van⟩ :=
      exists_placeInvariant_eq_of_pow_ne_one hN hNodd hqp hqdvd hp₁ hp₁q hq₁
        (hinvpow (ratPlace p₁ hp₁))
    obtain ⟨y₂, hy₂pow, hy₂tot, hy₂p, hy₂van⟩ :=
      exists_placeInvariant_eq_of_pow_ne_one hN hNodd hqp hqdvd hp₂ hp₂q hq₂
        (hinvpow (ratPlace p₂ hp₂))
    have hkey : totalInvariant ℚ (x * y₁ * y₂) = totalInvariant ℚ x := by
      rw [map_mul, map_mul, hy₁tot, hy₂tot, mul_one, mul_one]
    rw [← hkey]
    refine ih (x * y₁ * y₂) (by rw [mul_pow, mul_pow, hx, hy₁pow, hy₂pow, one_mul, one_mul])
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

/-- **The invariants of a Brauer class of odd prime order over the rationals add up to zero.**  Its
invariants are nontrivial at only finitely many places, and the rational primes below them form a
finite set which the reduction shrinks one element at a time. -/
theorem totalInvariant_eq_one_of_pow_eq_one {N : ℕ} (hN : N.Prime) (hNodd : Odd N)
    {x : BrauerGroup.{0, 0} ℚ} (hx : x ^ N = 1) : totalInvariant ℚ x = 1 := by
  classical
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
  exact totalInvariant_eq_one_of_card_le hN hNodd S.card x hx S hSp le_rfl hbad

end Reciprocity

end InverseGalois.CFT
