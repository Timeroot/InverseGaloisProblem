/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.CyclicPairing
import InverseGalois.CFT.PoitouTate.Prescribed

/-!
# The complement of the unramified classes at an odd exponent, above the exponent as well

At a place away from the exponent the unramified classes of a local field are their own orthogonal
complement for the norm residue symbol: they pair trivially with themselves, and there are exactly
as many of them as of their complement.  Above the exponent the first half fails — there are far
more classes there, and the unramified ones are no longer isotropic — so the complement can only be
contained in them.  That containment is all that a condition of being unramified needs of a place,
and it holds at **every** place once the exponent is odd.

The reason is that a class pairs trivially with itself at an odd exponent, the symbol of a class
against itself being its symbol against minus one and minus one being an odd power of itself.  So a
class in the complement of the unramified ones pairs trivially with the subgroup they generate
together with it; were it not unramified that subgroup would be everything, since the unramified
classes have index the exponent and the exponent is prime, and only the trivial class pairs
trivially with everything.

## Main results

* `InverseGalois.CFT.perpSubgroupLeft_unramifiedClasses_le_of_odd`: **at an odd prime exponent the
  classes of a local field pairing trivially with every unramified class are unramified**, whatever
  the residue characteristic.
* `InverseGalois.CFT.perpSubgroupLeft_localUnramified_le_of_odd`: the same at any finite place of a
  number field, the places above the exponent included.
* `InverseGalois.CFT.perpSubgroupLeft_localClassPairing_top`: the companion condition, imposing
  nothing at a place, has for complement the trivial class alone.

## Tags

norm residue symbol, unramified, orthogonal complement, local class, Poitou-Tate duality
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Valued WithZero

/-! ### The complement of the unramified classes of a local field -/

section Local

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e n : ℕ} [NeZero n] {ζ : K}

/-- **At an odd prime exponent the classes of a local field pairing trivially with every unramified
class are unramified**, at every residue characteristic.

A class outside the unramified ones generates together with them a subgroup of index dividing the
exponent and different from the unramified classes themselves, so all of the classes, the exponent
being prime.  At an odd exponent a class pairs trivially with itself, so such a class would pair
trivially with every class at all, and only the trivial class does that. -/
theorem perpSubgroupLeft_unramifiedClasses_le_of_odd
    (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n)
    (hn : n.Prime) (hodd : Odd n) :
    perpSubgroupLeft (A := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
        (localSymbolQuotDual hres hm hζ) (unramifiedClasses hm n)
      ≤ unramifiedClasses hm n := by
  intro b hb
  by_contra hbU
  have hker : unramifiedClasses hm n ⊔ Subgroup.zpowers b
      ≤ (localSymbolQuotDual hres hm hζ b).ker := by
    refine sup_le (fun a ha => MonoidHom.mem_ker.2 (mem_perpSubgroupLeft.1 hb a ha)) ?_
    rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.2 (localSymbolQuotDual_self_eq_one hres hm hζ hodd b)
  have hdvd : (unramifiedClasses hm n ⊔ Subgroup.zpowers b).index ∣ n := by
    have h := Subgroup.index_dvd_of_le
      (le_sup_left : unramifiedClasses hm n ≤ unramifiedClasses hm n ⊔ Subgroup.zpowers b)
    rwa [index_unramifiedClasses hm] at h
  have htop : unramifiedClasses hm n ⊔ Subgroup.zpowers b = ⊤ := by
    rcases hn.eq_one_or_self_of_dvd _ hdvd with h1 | hn'
    · exact Subgroup.index_eq_one.1 h1
    · refine absurd ?_ hbU
      have h := Subgroup.relIndex_mul_index
        (le_sup_left : unramifiedClasses hm n ≤ unramifiedClasses hm n ⊔ Subgroup.zpowers b)
      rw [hn', index_unramifiedClasses hm] at h
      have hrel : (unramifiedClasses hm n).relIndex
          (unramifiedClasses hm n ⊔ Subgroup.zpowers b) = 1 :=
        Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne n)) (by rw [one_mul]; exact h)
      exact Subgroup.relIndex_eq_one.1 hrel (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hbot : perpSubgroupLeft (A := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
      (localSymbolQuotDual hres hm hζ) ⊤ = ⊥ :=
    perpSubgroupLeft_top (injective_localSymbolQuotDual hres hm hζ)
  refine hbU ?_
  rw [Subgroup.mem_bot.1 (hbot.le (mem_perpSubgroupLeft.2 fun a _ =>
    MonoidHom.mem_ker.1 (hker (htop.ge (Subgroup.mem_top a)))))]
  exact one_mem _

end Local

/-! ### The complement of the unramified classes at a place of a number field -/

section AdicPlace

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **At an odd prime exponent the classes at a finite place of a number field pairing trivially
with every unramified class are unramified**, the places above the exponent included. -/
theorem perpSubgroupLeft_localUnramified_le_of_odd
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hodd : Odd n)
    (v : HeightOneSpectrum (𝓞 K)) :
    perpSubgroupLeft (A := localClasses v n) (localClassPairing hres hζ v) (localUnramified v n)
      ≤ localUnramified v n :=
  perpSubgroupLeft_unramifiedClasses_le_of_odd (hres v)
    (isUnitValGen_one (valued_adicCompletion_surjective v))
    (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective) hn hodd

/-- **Only the trivial class at a finite place pairs trivially with every class there**, so the
condition imposing nothing at a place has for complement the trivial class alone. -/
theorem perpSubgroupLeft_localClassPairing_top
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (v : HeightOneSpectrum (𝓞 K)) :
    perpSubgroupLeft (A := localClasses v n) (localClassPairing hres hζ v) ⊤ = ⊥ :=
  perpSubgroupLeft_top (injective_localSymbolQuotDual (hres v)
    (isUnitValGen_one (valued_adicCompletion_surjective v))
    (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective))

end AdicPlace

end InverseGalois.CFT
