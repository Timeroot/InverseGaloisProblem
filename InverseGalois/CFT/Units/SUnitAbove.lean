/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Places
import InverseGalois.CFT.Units.PrimeAbove
import InverseGalois.CFT.Units.SUnitHerbrand
import InverseGalois.CFT.Units.SUnitValuation

/-!
# The `S`-units of a number field seen in an extension

An `S`-unit of a number field stays an `S`-unit in an extension, for the set of primes of the
extension lying above `S`.  There is something to prove: the order of an element at a prime of the
extension is not read off from its order below unless the element is integral, and an `S`-unit is
a quotient whose numerator and denominator may well be divisible by primes outside `S`.

The proof clears those primes one at a time.  A power of every prime is principal, the exponent
being the order of the class group, and dividing an `S`-unit by a suitable power of a generator of
such a principal power removes one prime from `S` without changing anything at the primes of the
extension that are of interest, because a generator of a power of a prime lies outside every other
prime and so has order zero at every prime of the extension above another one.  When no primes are
left the `S`-unit is a unit of the ring of integers, which is a unit upstairs too.

## Main results

* `InverseGalois.CFT.ord_algebraMap_eq_zero_of_notMem_primeUnder`: an element of the ring of
  integers of the base has order zero at a prime of the extension whose prime below misses it.
* `InverseGalois.CFT.ord_map_eq_zero_of_mem_sUnits`: **an `S`-unit has order zero at every prime of
  an extension not lying above `S`.**
* `InverseGalois.CFT.map_mem_sUnits_of_mem_sUnits`: **an `S`-unit of a number field is a unit for
  the primes of an extension above `S`.**

## Tags

number field, S-unit, prime below, class group, order, extension
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### An integral element at a prime of the extension -/

section Integral

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

omit [NumberField K] in
/-- An element of the ring of integers of the base field has order zero at a prime of the
extension whose prime below does not contain it.  Order zero is valuation one, and the valuation
of an integral element is one exactly when the prime misses it. -/
theorem ord_algebraMap_eq_zero_of_notMem_primeUnder {w : HeightOneSpectrum (𝓞 M)} {r : 𝓞 K}
    (hr : r ∉ (primeUnder (𝓞 K) w).asIdeal) :
    ord M w (algebraMap K M (algebraMap (𝓞 K) K r)) = 0 := by
  have hmem : algebraMap (𝓞 K) (𝓞 M) r ∉ w.asIdeal := fun h => hr h
  have h0 : algebraMap (𝓞 K) (𝓞 M) r ≠ 0 := fun h => hmem (h ▸ Ideal.zero_mem _)
  have hne : algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) r) ≠ 0 := fun h =>
    h0 (FaithfulSMul.algebraMap_injective (𝓞 M) M (by rw [h, map_zero]))
  have htower : algebraMap K M (algebraMap (𝓞 K) K r)
      = algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) r) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [htower, ← valuation_eq_one_iff_ord_eq_zero w hne]
  exact (valuation_eq_one_iff_notMem M w _).2 hmem

end Integral

/-! ### An `S`-unit at a prime of the extension -/

section Above

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/-- **An `S`-unit has order zero at every prime of an extension not lying above `S`.**  Removing
one prime of `S` at a time, by dividing a power of the `S`-unit by a power of a generator of a
principal power of that prime, reduces the claim to a unit of the ring of integers. -/
theorem ord_map_eq_zero_of_mem_sUnits (X : Finset (HeightOneSpectrum (𝓞 K)))
    {w : HeightOneSpectrum (𝓞 M)} :
    ∀ u : Kˣ, u ∈ sUnits K (X : Set (HeightOneSpectrum (𝓞 K))) →
      primeUnder (𝓞 K) w ∉ X →
      ord M w ((Units.map (algebraMap K M : K →* M) u : Mˣ) : M) = 0 := by
  classical
  induction X using Finset.induction_on with
  | empty =>
    intro u hu _
    rw [Finset.coe_empty] at hu
    obtain ⟨ε, hε⟩ := exists_unitsToSUnitsHom_eq (K := K) (u := ⟨u, hu⟩)
      fun v => mem_sUnits.mp hu v (Set.notMem_empty v)
    have hcoe : (u : K) = algebraMap (𝓞 K) K (ε : 𝓞 K) := by
      rw [← coe_unitsToSUnitsHom_apply (K := K) (∅ : Set (HeightOneSpectrum (𝓞 K))) ε, hε]
    have hεmem : (ε : 𝓞 K) ∉ (primeUnder (𝓞 K) w).asIdeal := fun hm =>
      (primeUnder (𝓞 K) w).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm ε.isUnit)
    rw [Units.coe_map, MonoidHom.coe_coe, hcoe]
    exact ord_algebraMap_eq_zero_of_notMem_primeUnder hεmem
  | @insert v₀ X' hv₀ ih =>
    intro u hu hw
    have hwX' : primeUnder (𝓞 K) w ∉ X' := fun h => hw (Finset.mem_insert_of_mem h)
    have hwne : primeUnder (𝓞 K) w ≠ v₀ := fun h => hw (h ▸ Finset.mem_insert_self _ _)
    -- a power of the removed prime is principal
    obtain ⟨a₀, ha₀⟩ := exists_span_eq_pow_card_classGroup (𝓞 K) v₀
    have hN0 : Nat.card (ClassGroup (𝓞 K)) ≠ 0 := Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
    have hnebot : v₀.asIdeal ^ Nat.card (ClassGroup (𝓞 K)) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v₀.ne_bot)
    have ha0ne : a₀ ≠ 0 := fun h0 =>
      hnebot (by rw [← ha₀, h0]; exact Ideal.span_singleton_eq_bot.mpr rfl)
    have hx0 : algebraMap (𝓞 K) K a₀ ≠ 0 := by
      refine fun hz => ha0ne (FaithfulSMul.algebraMap_injective (𝓞 K) K ?_)
      rw [hz, map_zero]
    set α : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a₀) hx0 with hα
    have hαcoe : ((α : Kˣ) : K) = algebraMap (𝓞 K) K a₀ := rfl
    set n : ℤ := ord K v₀ ((u : Kˣ) : K) with hn
    -- dividing removes the prime from the set
    have hcoe : ((u ^ Nat.card (ClassGroup (𝓞 K)) * α ^ (-n) : Kˣ) : K)
        = ((u : Kˣ) : K) ^ Nat.card (ClassGroup (𝓞 K)) * ((α : Kˣ) : K) ^ (-n) := by
      push_cast
      ring
    have hu'mem : u ^ Nat.card (ClassGroup (𝓞 K)) * α ^ (-n)
        ∈ sUnits K (X' : Set (HeightOneSpectrum (𝓞 K))) := by
      refine mem_sUnits.mpr fun v hv => ?_
      rw [hcoe, ord_mul v (pow_ne_zero _ (Units.ne_zero u)) (zpow_ne_zero _ (Units.ne_zero α)),
        ord_pow v (Units.ne_zero u), ord_zpow v (Units.ne_zero α), hαcoe]
      by_cases hvv : v = v₀
      · subst hvv
        rw [ord_of_span_eq_pow_self (K := K) ha₀, ← hn]
        ring
      · have h1 : ord K v ((u : Kˣ) : K) = 0 := by
          refine mem_sUnits.mp hu v ?_
          rw [Finset.coe_insert, Set.mem_insert_iff]
          rintro (rfl | hvX')
          · exact hvv rfl
          · exact hv hvX'
        rw [h1, ord_of_span_eq_pow_of_ne (K := K) ha₀ hvv]
        ring
    -- the generator is invisible at the prime of the extension
    have ha0not : a₀ ∉ (primeUnder (𝓞 K) w).asIdeal := by
      intro hm
      have hpos := (mem_iff_ord_pos (K := K) (primeUnder (𝓞 K) w) ha0ne).1 hm
      rw [ord_of_span_eq_pow_of_ne (K := K) ha₀ hwne] at hpos
      exact lt_irrefl 0 hpos
    have hαzero : ord M w ((Units.map (algebraMap K M : K →* M) α : Mˣ) : M) = 0 := by
      rw [Units.coe_map, MonoidHom.coe_coe, hαcoe]
      exact ord_algebraMap_eq_zero_of_notMem_primeUnder ha0not
    have hih := ih _ hu'mem hwX'
    rw [map_mul, map_pow, map_zpow] at hih
    have hcoeM : ((Units.map (algebraMap K M : K →* M) u ^ Nat.card (ClassGroup (𝓞 K))
          * Units.map (algebraMap K M : K →* M) α ^ (-n) : Mˣ) : M)
        = ((Units.map (algebraMap K M : K →* M) u : Mˣ) : M) ^ Nat.card (ClassGroup (𝓞 K))
          * ((Units.map (algebraMap K M : K →* M) α : Mˣ) : M) ^ (-n) := by
      push_cast
      ring
    rw [hcoeM, ord_mul w (pow_ne_zero _ (Units.ne_zero _)) (zpow_ne_zero _ (Units.ne_zero _)),
      ord_pow w (Units.ne_zero _), ord_zpow w (Units.ne_zero _), hαzero, mul_zero, add_zero,
      mul_eq_zero] at hih
    exact hih.resolve_left (Int.natCast_ne_zero.2 hN0)

/-- **An `S`-unit of a number field is a unit for the primes of an extension above `S`.** -/
theorem map_mem_sUnits_of_mem_sUnits (X : Finset (HeightOneSpectrum (𝓞 K))) {u : Kˣ}
    (hu : u ∈ sUnits K (X : Set (HeightOneSpectrum (𝓞 K)))) :
    Units.map (algebraMap K M : K →* M) u
      ∈ sUnits M {w : HeightOneSpectrum (𝓞 M) | primeUnder (𝓞 K) w ∈ X} :=
  mem_sUnits.mpr fun _ hw => ord_map_eq_zero_of_mem_sUnits X u hu hw

end Above

/-! ### Enlarging the set of primes -/

section Mono

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The group of `X`-units grows with `X`. -/
theorem sUnits_mono {X Y : Set (HeightOneSpectrum R)} (h : X ⊆ Y) : sUnits K X ≤ sUnits K Y :=
  fun _ hu => mem_sUnits.mpr fun v hv => mem_sUnits.mp hu v fun hvX => hv (h hvX)

end Mono

end InverseGalois.CFT
