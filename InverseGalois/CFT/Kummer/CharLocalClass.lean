/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharPlace

/-!
# The Kummer character on a decomposition subgroup is the local class

The Kummer character of a unit vanishes on the decomposition subgroup at a prime exactly when the
unit is a power in the completion at the place below, and the character is additive in the unit.
Putting the two together, the restriction of the character to a decomposition subgroup depends on
the unit only through its class in the units of that completion modulo powers, and it determines
that class: **the local class at a place and the character on a decomposition subgroup above it are
the same piece of information.**

That is the form in which an arithmetic construction which prescribes local classes is read as one
which prescribes characters.  A family of units built to have given classes at given places has,
above those places, given characters on the decomposition subgroups, and two families with the same
classes there are indistinguishable by any character built out of them.

The same holds one subgroup down at a place away from the exponent: a unit whose order at the place
is a multiple of the exponent has vanishing character on the inertia subgroup, so units whose orders
agree modulo the exponent have the same character there.

## Main results

* `InverseGalois.CFT.kummerChar_mul_units` — the Kummer character is additive in the unit.
* `InverseGalois.CFT.kummerChar_eq_of_localClassHom_eq` — **units with the same class in a
  completion have the same Kummer character on every decomposition subgroup above that place.**
* `InverseGalois.CFT.localClassHom_eq_of_forall_kummerChar_eq` — **the converse**, so the class is
  read off the character.
* `InverseGalois.CFT.forall_kummerChar_eq_iff_localClassHom_eq` — the two statements as one.
* `InverseGalois.CFT.kummerChar_eq_of_dvd_placeValue` — units whose quotient has order divisible by
  the exponent have the same Kummer character on the inertia subgroup.

## Tags

Kummer theory, decomposition group, local class, completion, inertia
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

open scoped Pointwise

/-! ### Additivity in the unit -/

section Mul

variable {K : Type} {Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {n : ℕ} [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

/-- **The Kummer character is additive in the unit**, the Kummer cochain of a product being the
product of the Kummer cochains. -/
theorem kummerChar_mul_units (a b : Kˣ) (g : Gal(Ω/K)) :
    kummerChar h (a * b) g = kummerChar h a g + kummerChar h b g := by
  show (h.cochain (a * b) g).toAdd = _
  rw [h.cochain_mul a b]
  rfl

/-- The Kummer character of the unit one vanishes. -/
theorem kummerChar_one_units (g : Gal(Ω/K)) : kummerChar h (1 : Kˣ) g = 0 := by
  have h1 := kummerChar_mul_units h 1 1 g
  rw [mul_one] at h1
  refine add_left_cancel (a := kummerChar h (1 : Kˣ) g) ?_
  rw [add_zero]
  exact h1.symm

/-- The Kummer character of an inverse is the negative of the Kummer character. -/
theorem kummerChar_inv_units (a : Kˣ) (g : Gal(Ω/K)) :
    kummerChar h a⁻¹ g = -kummerChar h a g := by
  have h1 := kummerChar_mul_units h a a⁻¹ g
  rw [mul_inv_cancel, kummerChar_one_units] at h1
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h1.symm

/-- The Kummer characters of two units agree at an automorphism exactly when the character of their
quotient vanishes there. -/
theorem kummerChar_eq_iff_kummerChar_div_eq_zero (a b : Kˣ) (g : Gal(Ω/K)) :
    kummerChar h a g = kummerChar h b g ↔ kummerChar h (a * b⁻¹) g = 0 := by
  rw [kummerChar_mul_units, kummerChar_inv_units, ← sub_eq_add_neg, sub_eq_zero]

end Mul

/-! ### The character on a decomposition subgroup and the class in the completion -/

section Local

variable {K : Type} {Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {n : ℕ} [NeZero n] {ζ : K} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData K Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

/-- **Units with the same class in a completion have the same Kummer character on every
decomposition subgroup above that place.**  Their quotient is a power in the completion, so its
character vanishes on the decomposition subgroup, and the character is additive in the unit. -/
theorem kummerChar_eq_of_localClassHom_eq {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P) {a b : Kˣ}
    (hloc : localClassHom v n a = localClassHom v n b) {σ : Gal(Ω/K)}
    (hσ : σ ∈ stabilizer Gal(Ω/K) P) : kummerChar h a σ = kummerChar h b σ := by
  have hq : localClassHom v n (a * b⁻¹) = 1 := by
    rw [_root_.map_mul, _root_.map_inv, hloc, mul_inv_cancel]
  exact (kummerChar_eq_iff_kummerChar_div_eq_zero h a b σ).2
    (kummerChar_eq_zero_of_mem_stabilizer h hv hq hσ)

/-- **The class of a unit in a completion is read off its Kummer character on a decomposition
subgroup above that place.**  Two units whose characters agree there have a quotient whose character
vanishes there, and a unit whose character vanishes on a decomposition subgroup is a power in the
completion at the place below. -/
theorem localClassHom_eq_of_forall_kummerChar_eq {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P) {a b : Kˣ}
    (hchar : ∀ σ ∈ stabilizer Gal(Ω/K) P, kummerChar h a σ = kummerChar h b σ) :
    localClassHom v n a = localClassHom v n b := by
  have hq : localClassHom v n (a * b⁻¹) = 1 :=
    localClassHom_eq_one_of_forall_mem_stabilizer h hv fun σ hσ =>
      (kummerChar_eq_iff_kummerChar_div_eq_zero h a b σ).1 (hchar σ hσ)
  rw [_root_.map_mul, _root_.map_inv] at hq
  exact mul_inv_eq_one.1 hq

/-- **The local class at a place and the Kummer character on a decomposition subgroup above it are
the same piece of information.** -/
theorem forall_kummerChar_eq_iff_localClassHom_eq {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P) {a b : Kˣ} :
    (∀ σ ∈ stabilizer Gal(Ω/K) P, kummerChar h a σ = kummerChar h b σ) ↔
      localClassHom v n a = localClassHom v n b :=
  ⟨localClassHom_eq_of_forall_kummerChar_eq h hv,
    fun hloc _ hσ => kummerChar_eq_of_localClassHom_eq h hv hloc hσ⟩

/-- **Units whose quotient has order at a place away from the exponent divisible by the exponent
have the same Kummer character on the inertia subgroup at every prime above that place.** -/
theorem kummerChar_eq_of_dvd_placeValue (hn : n.Prime) {P : Ideal (𝓞 Ω)} [P.IsPrime]
    (hnP : (n : 𝓞 Ω) ∉ P) {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.under (𝓞 K) P)
    {a b : Kˣ} (hord : (n : ℤ) ∣ placeValue v (a * b⁻¹)) {σ : Gal(Ω/K)}
    (hσ : σ ∈ Ideal.inertia Gal(Ω/K) P) : kummerChar h a σ = kummerChar h b σ :=
  (kummerChar_eq_iff_kummerChar_div_eq_zero h a b σ).2
    (kummerChar_eq_zero_of_mem_inertia h hn hnP hv hord hσ)

end Local

end InverseGalois.CFT
