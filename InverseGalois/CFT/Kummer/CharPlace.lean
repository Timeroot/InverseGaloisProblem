/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.RadicalLevel
import InverseGalois.CFT.Kummer.InertiaOrd
import InverseGalois.CFT.Kummer.LocalPowerConverse
import InverseGalois.CFT.PoitouTate.GlobalClasses
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.CFT.Profinite.SymbolCyclic

/-!
# The Kummer character of a unit at a place

A unit `a` of a number field `K` whose `p`-th roots lie in a Galois extension `Ω` of `K` containing
a primitive `p`-th root of unity has a Kummer character, the homomorphism sending an automorphism of
`Ω` to the exponent by which it multiplies a chosen `p`-th root of `a`.  This file records what that
character sees at a prime of `Ω`, in both directions.

The local class of `a` at a place `v` of `K` is trivial exactly when `a` is a `p`-th power in the
completion at `v`, a reformulation of the definition of the local class that unwinds the quotient by
the `p`-th powers.  For a prime `P` of `Ω` above `v`, being a `p`-th power in the completion is in
turn exactly the statement that the whole decomposition subgroup at `P` fixes the chosen root, so
the Kummer character vanishes on the decomposition subgroup at `P` precisely when the local class at
`v` vanishes.  Contrapositively, a nontrivial local class at `v` produces an element of the
decomposition subgroup at any prime above `v` on which the character does not vanish, which is how
generation of a character group is read off from local information.

In the other direction, the inertia subgroup sees less: at a prime away from `p` the character
vanishes on inertia as soon as the order of `a` at the place below is a multiple of `p`, with no
condition on `a` beyond its order.  That is the statement that a radical whose radicand is a `p`-th
power up to a unit is unramified, transported through the dictionary between the character and the
action on the root.

## Main results

* `InverseGalois.CFT.localClassHom_eq_one_iff_exists_pow`: the local class of a unit at a place is
  trivial exactly when the unit is a power in the completion at that place.
* `InverseGalois.CFT.dvd_placeValue_of_localClassHom_eq_one`: a unit with trivial local class at a
  place has order there a multiple of the exponent.
* `InverseGalois.CFT.kummerChar_eq_zero_iff_smul_root_eq`: the Kummer character of a unit vanishes
  at an automorphism exactly when that automorphism fixes the chosen root.
* `InverseGalois.CFT.coe_root_pow`: the chosen root of a unit is a root of it.
* `InverseGalois.CFT.kummerChar_eq_zero_of_mem_inertia`: **the Kummer character of a unit whose
  order at a place away from the exponent is a multiple of the exponent vanishes on the inertia
  subgroup at every prime above that place.**
* `InverseGalois.CFT.kummerChar_eq_zero_of_mem_stabilizer`: the Kummer character of a unit with
  trivial local class at a place vanishes on the decomposition subgroup at every prime above it.
* `InverseGalois.CFT.localClassHom_eq_one_of_forall_mem_stabilizer`: a unit whose Kummer character
  vanishes on the decomposition subgroup at a prime has trivial local class at the place below.
* `InverseGalois.CFT.exists_mem_stabilizer_kummerChar_ne_zero`: **a unit with nontrivial local class
  at a place has an element of the decomposition subgroup at any prime above it on which its Kummer
  character does not vanish.**

## Tags

number field, Kummer theory, Kummer character, decomposition group, inertia subgroup, local class
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

open scoped Pointwise

/-! ### Triviality of a local class -/

section Class

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]

/-- **The local class of a unit at a place is trivial exactly when the unit is a power in the
completion at that place.**  The local class is the image of the unit in the quotient of the units
of the completion by their powers, so its triviality is membership in the subgroup of powers, and a
nonzero element of the completion which is a power is the power of a unit. -/
theorem localClassHom_eq_one_iff_exists_pow (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    localClassHom v n a = 1 ↔
      ∃ c : v.adicCompletion K, c ^ n = algebraMap K (v.adicCompletion K) (a : K) := by
  constructor
  · intro h1
    rw [localClassHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨(c : v.adicCompletion K), ?_⟩
    rw [← Units.val_pow_eq_pow_val]
    exact congrArg Units.val hc
  · rintro ⟨c, hc⟩
    have hane : algebraMap K (v.adicCompletion K) (a : K) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).2 a.ne_zero
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_pow (NeZero.ne n)] at hc
      exact hane hc.symm
    rw [localClassHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Units.coe_map]
    show c ^ n = algebraMap K (v.adicCompletion K) (a : K)
    exact hc

/-- A unit whose local class at a place is trivial has order there a multiple of the exponent,
since the trivial class is in particular unramified. -/
theorem dvd_placeValue_of_localClassHom_eq_one {v : HeightOneSpectrum (𝓞 K)} {a : Kˣ}
    (h : localClassHom v n a = 1) : (n : ℤ) ∣ placeValue v a :=
  (localClassHom_mem_localUnramified_iff v a).1 (h ▸ one_mem _)

end Class

/-! ### The character and the action on the root -/

section CharPlace

variable {K : Type} {Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {n : ℕ} [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

omit [NumberField K] in
/-- **The Kummer character of a unit vanishes at an automorphism exactly when that automorphism
fixes the chosen root.**  An automorphism multiplies the root by the power of the root of unity
whose exponent is the value of the character, and the root of unity is primitive, so that power is
trivial exactly when the exponent vanishes. -/
theorem kummerChar_eq_zero_iff_smul_root_eq (a : Kˣ) (g : Gal(Ω/K)) :
    kummerChar h a g = 0 ↔ g • h.root a = h.root a := by
  have hkey := smul_root_eq_kummerRootUnit_pow h a g
  constructor
  · intro h0
    rw [hkey, h0, ZMod.val_zero, pow_zero, one_mul]
  · intro hfix
    rw [hfix] at hkey
    have hone : kummerRootUnit Ω hζ ^ (kummerChar h a g).val = 1 :=
      mul_right_cancel (b := h.root a) (by rw [one_mul, ← hkey])
    have hprim : IsPrimitiveRoot (algebraMap K Ω ζ) n :=
      hζ.map_of_injective (algebraMap K Ω).injective
    have honeΩ : (algebraMap K Ω ζ) ^ (kummerChar h a g).val = 1 := by
      rw [← coe_kummerRootUnit (Ω := Ω) (hζ := hζ), ← Units.val_pow_eq_pow_val, hone,
        Units.val_one]
    have hzero : (kummerChar h a g).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt (hprim.dvd_of_pow_eq_one _ honeΩ) (ZMod.val_lt _)
    exact (ZMod.val_eq_zero _).1 hzero

omit [NumberField K] [IsGalois K Ω] in
/-- The chosen root of a unit is a root of it, read in the field rather than in its units. -/
theorem coe_root_pow (a : Kˣ) : ((h.root a : Ωˣ) : Ω) ^ n = algebraMap K Ω (a : K) := by
  rw [← Units.val_pow_eq_pow_val, h.root_pow a, Units.coe_map]
  rfl

/-- **The Kummer character of a unit whose order at a place away from the exponent is a multiple of
the exponent vanishes on the inertia subgroup at every prime above that place.**  Inertia fixes such
a radical, and the character vanishes exactly at the automorphisms fixing the root. -/
theorem kummerChar_eq_zero_of_mem_inertia (hn : n.Prime) {P : Ideal (𝓞 Ω)} [P.IsPrime]
    (hnP : (n : 𝓞 Ω) ∉ P) {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P)
    {a : Kˣ} (hord : (n : ℤ) ∣ placeValue v a) {σ : Gal(Ω/K)}
    (hσ : σ ∈ Ideal.inertia Gal(Ω/K) P) : kummerChar h a σ = 0 := by
  refine (kummerChar_eq_zero_iff_smul_root_eq h a σ).2 (Units.ext ?_)
  refine forall_inertia_smul_eq_of_dvd_ord hn hζ hnP a.ne_zero (coe_root_pow h a).symm hv ?_ hσ
  rwa [placeValue_eq_neg_ord, dvd_neg] at hord

/-- The Kummer character of a unit with trivial local class at a place vanishes on the whole
decomposition subgroup at every prime above that place: the unit is a power in the completion, so
the decomposition subgroup fixes the root. -/
theorem kummerChar_eq_zero_of_mem_stabilizer {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P) {a : Kˣ}
    (hloc : localClassHom v n a = 1) {σ : Gal(Ω/K)} (hσ : σ ∈ stabilizer Gal(Ω/K) P) :
    kummerChar h a σ = 0 :=
  (kummerChar_eq_zero_iff_smul_root_eq h a σ).2 (Units.ext
    (forall_stabilizer_smul_eq_of_exists_pow_adicCompletion hζ (NeZero.ne n)
      (coe_root_pow h a).symm hv ((localClassHom_eq_one_iff_exists_pow v a).1 hloc) ⟨σ, hσ⟩))

/-- A unit whose Kummer character vanishes on the decomposition subgroup at a prime has trivial
local class at the place below it, the converse of the previous statement. -/
theorem localClassHom_eq_one_of_forall_mem_stabilizer {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P) {a : Kˣ}
    (hchar : ∀ σ ∈ stabilizer Gal(Ω/K) P, kummerChar h a σ = 0) : localClassHom v n a = 1 :=
  (localClassHom_eq_one_iff_exists_pow v a).2
    (exists_pow_adicCompletion_of_forall_stabilizer_smul_eq hζ (NeZero.ne n) (coe_root_pow h a).symm
      (fun σ => congrArg Units.val
        ((kummerChar_eq_zero_iff_smul_root_eq h a (σ : Gal(Ω/K))).1 (hchar σ σ.2))) hv)

/-- **A unit with nontrivial local class at a place has an element of the decomposition subgroup at
any prime above it on which its Kummer character does not vanish.**  This is the contrapositive of
the criterion for the local class to be trivial, and is what makes a character built from units with
prescribed local behaviour surject onto the decomposition subgroups it is designed for. -/
theorem exists_mem_stabilizer_kummerChar_ne_zero {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P) {a : Kˣ}
    (hloc : localClassHom v n a ≠ 1) :
    ∃ σ ∈ stabilizer Gal(Ω/K) P, kummerChar h a σ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  exact hloc (localClassHom_eq_one_of_forall_mem_stabilizer h hv hcon)

end CharPlace

end InverseGalois.CFT
