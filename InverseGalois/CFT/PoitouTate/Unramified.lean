/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceInvariant
import InverseGalois.CFT.Brauer.TameSymbol
import InverseGalois.CFT.Kummer.LocalPowRepresentatives
import InverseGalois.CFT.Kummer.PowIndex
import InverseGalois.CFT.PoitouTate.Isotropic

/-!
# The unramified classes of a local field are their own orthogonal complement

A class of a local field modulo `n`-th powers is **unramified** when the valuation of any of its
representatives is divisible by `n`; equivalently, when the extension obtained by adjoining an
`n`-th root of a representative is unramified.  Reading the valuation modulo `n` is a homomorphism
onto the integers modulo `n`, killed by the `n`-th powers, so the unramified classes are the kernel
of a surjection onto `ZMod n` and therefore have index exactly `n`.

Away from the residue characteristic the norm residue symbol of two unramified classes is trivial:
each representative is a unit times an `n`-th power, the `n`-th powers drop out of a
bimultiplicative symbol, and the symbol of two units is trivial in the tame case.  So the
unramified classes pair trivially with themselves.

When the group of all classes has order `n ^ 2` — which is what the local index formula gives at a
place not dividing `n`, once the `n`-th roots of unity are present — the unramified classes are
exactly half of it, and the counting lemma for a perfect self-pairing upgrades trivial
self-pairing to equality: **the unramified classes are precisely their own orthogonal complement.**
This is the local condition that cuts out the Selmer group in the global duality argument.

## Main results

* `InverseGalois.CFT.localSymbol_eq_one_of_dvd_unitValDiv`: two elements whose valuations are
  divisible by `n` have trivial norm residue symbol, away from the residue characteristic.
* `InverseGalois.CFT.index_unramifiedClasses`: the unramified classes have index `n`.
* `InverseGalois.CFT.perpSubgroup_unramifiedClasses`: **the unramified classes are their own
  orthogonal complement under the norm residue symbol.**
* `InverseGalois.CFT.perpSubgroup_unramifiedClasses_adicCompletion`: the same at a finite place of
  a number field containing the `n`-th roots of unity and not dividing `n`.

## Tags

local field, norm residue symbol, unramified, orthogonal complement, maximal isotropic,
Poitou-Tate duality, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open scoped Valued WithZero

section Symbol

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e n : ℕ} [NeZero n] {ζ : K}

/-- **The norm residue symbol of two elements of divisible valuation is trivial**, away from the
residue characteristic: each is a unit times an `n`-th power, and the symbol of two units is
trivial in the tame case. -/
theorem localSymbol_eq_one_of_dvd_unitValDiv (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) {a b : Kˣ}
    (ha : (n : ℤ) ∣ unitValDiv hm (Additive.ofMul a))
    (hb : (n : ℤ) ∣ unitValDiv hm (Additive.ofMul b)) :
    localSymbol hres hm hζ a b = 1 := by
  obtain ⟨π, hπ⟩ := exists_unitValDiv_eq_one hm
  have hgen : ∀ (c : Kˣ) (r : ℤ), unitValDiv hm (Additive.ofMul c) = n * r →
      ∃ u : Kˣ, Valued.v (u : K) = 1 ∧ c = u * (π ^ r) ^ n := by
    intro c r hcr
    refine ⟨c * π ^ (-unitValDiv hm (Additive.ofMul c)),
      valued_mul_zpow_uniformiser hm hπ c, ?_⟩
    rw [mul_assoc, ← zpow_natCast (π ^ r) n, ← zpow_mul, ← zpow_add, hcr]
    have h0 : -((n : ℤ) * r) + r * (n : ℤ) = 0 := by ring
    rw [h0, zpow_zero, mul_one]
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  obtain ⟨u, hu1, rfl⟩ := hgen a i hi
  obtain ⟨w, hw1, rfl⟩ := hgen b j hj
  rw [map_mul (localSymbol hres hm hζ) u ((π ^ i) ^ n), MonoidHom.mul_apply,
    localSymbol_eq_one_of_isPow_left hres hm hζ ⟨π ^ i, rfl⟩ _, mul_one,
    map_mul (localSymbol hres hm hζ u) w ((π ^ j) ^ n),
    localSymbol_eq_one_of_isPow_right hres hm hζ u ⟨π ^ j, rfl⟩, mul_one]
  exact localSymbol_eq_one_of_valued_eq_one hres hm hζ hn hpn hu1 hw1

end Symbol

section Unramified

variable {K : Type} [Field K] [Valued K ℤᵐ⁰] {m : ℤ} {n : ℕ}

/-- The valuation of a unit, divided by a generator of the value group and read modulo `n`. -/
def unitValMod (hm : IsUnitValGen K m) (n : ℕ) : Kˣ →* Multiplicative (ZMod n) :=
  MonoidHom.toAdditiveLeft.symm ((Int.castAddHom (ZMod n)).comp (unitValDiv hm))

theorem unitValMod_apply (hm : IsUnitValGen K m) (n : ℕ) (a : Kˣ) :
    unitValMod hm n a
      = Multiplicative.ofAdd ((unitValDiv hm (Additive.ofMul a) : ℤ) : ZMod n) := rfl

theorem unitValMod_eq_one_iff [NeZero n] (hm : IsUnitValGen K m) (a : Kˣ) :
    unitValMod hm n a = 1 ↔ (n : ℤ) ∣ unitValDiv hm (Additive.ofMul a) := by
  rw [unitValMod_apply, ← ofAdd_zero, Equiv.apply_eq_iff_eq]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ n

theorem unitValMod_pow (hm : IsUnitValGen K m) (c : Kˣ) : unitValMod hm n (c ^ n) = 1 := by
  rw [unitValMod_apply, ofMul_pow, _root_.map_nsmul, ← ofAdd_zero]
  congr 1
  rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

/-- The valuation modulo `n`, read on the classes modulo `n`-th powers. -/
noncomputable def unitValModQuot (hm : IsUnitValGen K m) (n : ℕ) :
    (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) →* Multiplicative (ZMod n) :=
  QuotientGroup.lift _ (unitValMod hm n) (by
    rintro _ ⟨c, rfl⟩
    exact unitValMod_pow hm c)

@[simp]
theorem unitValModQuot_mk (hm : IsUnitValGen K m) (n : ℕ) (a : Kˣ) :
    unitValModQuot hm n (a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = unitValMod hm n a := rfl

/-- **The unramified classes**: those classes modulo `n`-th powers whose valuation is divisible by
`n`. -/
noncomputable def unramifiedClasses (hm : IsUnitValGen K m) (n : ℕ) :
    Subgroup (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := (unitValModQuot hm n).ker

theorem mk_mem_unramifiedClasses_iff [NeZero n] (hm : IsUnitValGen K m) (a : Kˣ) :
    (a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈ unramifiedClasses hm n
      ↔ (n : ℤ) ∣ unitValDiv hm (Additive.ofMul a) := by
  rw [unramifiedClasses, MonoidHom.mem_ker, unitValModQuot_mk, unitValMod_eq_one_iff]

/-- **The valuation modulo `n` is onto the integers modulo `n`**, because there is a uniformiser. -/
theorem surjective_unitValModQuot [NeZero n] (hm : IsUnitValGen K m) :
    Function.Surjective (unitValModQuot hm n) := by
  obtain ⟨π, hπ⟩ := exists_unitValDiv_eq_one hm
  intro y
  refine ⟨((π ^ (Multiplicative.toAdd y).val : Kˣ) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range), ?_⟩
  rw [unitValModQuot_mk, unitValMod_apply, ofMul_pow, _root_.map_nsmul, hπ, nsmul_eq_mul, mul_one,
    Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  rfl

/-- **The unramified classes have index `n`.** -/
theorem index_unramifiedClasses [NeZero n] (hm : IsUnitValGen K m) :
    (unramifiedClasses hm n).index = n := by
  rw [unramifiedClasses, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (surjective_unitValModQuot hm)).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- **The unramified classes are half of all the classes**, when there are `n` squared of them. -/
theorem card_unramifiedClasses [NeZero n] (hm : IsUnitValGen K m)
    (hcard : Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = n * n) :
    Nat.card ↥(unramifiedClasses hm n) = n := by
  have h := (unramifiedClasses hm n).index_mul_card
  rw [index_unramifiedClasses, hcard] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne n)) h

end Unramified

section SelfDual

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [PerfectField K] {m : ℤ} {p e n : ℕ} [NeZero n] {ζ : K}

/-- The classes of a local field modulo `n`-th powers inject into their own character group by
pairing on the **left** under the norm residue symbol. -/
theorem injective_flip_localSymbolQuotDual (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) : Function.Injective (localSymbolQuotDual hres hm hζ).flip := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | _ a =>
    rw [QuotientGroup.eq_one_iff]
    refine (forall_localSymbol_eq_one_iff_isPow hres hm hζ a).mp fun b => ?_
    exact congrArg (fun f => f (b : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) hx

/-- **The unramified classes pair trivially with themselves** under the norm residue symbol, when
the residue characteristic does not divide the exponent. -/
theorem unramifiedClasses_le_perpSubgroup (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (hζ : IsPrimitiveRoot ζ n) (hn : n.Prime) (hpn : ¬ p ∣ n) :
    unramifiedClasses hm n
      ≤ perpSubgroup (A := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
        (localSymbolQuotDual hres hm hζ) (unramifiedClasses hm n) := by
  intro x hx
  rw [mem_perpSubgroup]
  intro y hy
  induction x using QuotientGroup.induction_on with
  | _ a =>
    induction y using QuotientGroup.induction_on with
    | _ b =>
      rw [localSymbolQuotDual_mk]
      exact localSymbol_eq_one_of_dvd_unitValDiv hres hm hζ hn hpn
        ((mk_mem_unramifiedClasses_iff hm a).mp hx) ((mk_mem_unramifiedClasses_iff hm b).mp hy)

/-- **The unramified classes are their own orthogonal complement** under the norm residue symbol:
they pair trivially with themselves, and there are exactly as many of them as of their
complement. -/
theorem perpSubgroup_unramifiedClasses [Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)]
    (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) (hζ : IsPrimitiveRoot ζ n)
    (hn : n.Prime) (hpn : ¬ p ∣ n)
    (hcard : Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = n * n) :
    perpSubgroup (A := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
        (localSymbolQuotDual hres hm hζ) (unramifiedClasses hm n)
      = unramifiedClasses hm n :=
  perpSubgroup_eq_self (injective_flip_localSymbolQuotDual hres hm hζ)
    (unramifiedClasses_le_perpSubgroup hres hm hζ hn hpn)
    (by rw [card_unramifiedClasses hm hcard, hcard])

end SelfDual

section AdicPlace

open IsDedekindDomain NumberField

variable {K : Type} [Field K] [NumberField K] {p e n : ℕ} [NeZero n] {ζ : K}

/-- **At a place not dividing the exponent the classes modulo `n`-th powers number `n` squared**,
once the `n`-th roots of unity are present in the ground field. -/
theorem card_quotient_range_powMonoidHom_adicCompletion (hzeta : IsPrimitiveRoot ζ n)
    (v : HeightOneSpectrum (𝓞 K)) (hv : FinitePlace.mk v ((n : ℕ) : K) = 1) :
    Nat.card ((v.adicCompletion K)ˣ ⧸
        (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) = n * n := by
  have h := index_range_powMonoidHom_units_adicCompletion v (NeZero.ne n)
  rw [hv, mul_one, card_rootsOfUnity_of_isPrimitiveRoot (L := v.adicCompletion K) hzeta] at h
  exact_mod_cast h

/-- **The unramified classes of a completion at a place not dividing the exponent are their own
orthogonal complement** under the norm residue symbol. -/
theorem perpSubgroup_unramifiedClasses_adicCompletion (hzeta : IsPrimitiveRoot ζ n)
    {v : HeightOneSpectrum (𝓞 K)} (hres : HasResidueChar (v.adicCompletion K) p e)
    (hn : n.Prime) (hpn : ¬ p ∣ n) (hv : FinitePlace.mk v ((n : ℕ) : K) = 1) :
    perpSubgroup (A := (v.adicCompletion K)ˣ ⧸
        (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
        (localSymbolQuotDual hres (isUnitValGen_one (valued_adicCompletion_surjective v))
          (hzeta.map_of_injective (algebraMap K (v.adicCompletion K)).injective))
        (unramifiedClasses (isUnitValGen_one (valued_adicCompletion_surjective v)) n)
      = unramifiedClasses (isUnitValGen_one (valued_adicCompletion_surjective v)) n := by
  haveI := finiteIndex_range_powMonoidHom_units_adicCompletion v (NeZero.ne n)
  exact perpSubgroup_unramifiedClasses hres _ _ hn hpn
    (card_quotient_range_powMonoidHom_adicCompletion hzeta v hv)

end AdicPlace

end InverseGalois.CFT
