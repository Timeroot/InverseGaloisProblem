/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.SUnitDivisible

/-!
# One finite Galois extension holding the roots of the divisible units

The units of a number field whose order is divisible by a fixed exponent away from a prescribed
finite set of places are carried,
modulo exponent-th powers, by a single finitely generated subgroup.  Adjoining an exponent-th root
of each of finitely many generators therefore produces a finite extension holding an exponent-th
root of **every** one of them at once: the elements of the base having a root in a given extension
form a subgroup, so it is enough that the generators do, and a unit differs from an element of the
subgroup they generate by an exponent-th power of the base itself.

Passing to the normal closure costs nothing in finiteness and makes the extension Galois, which is
the form in which the decomposition groups of its primes can be spoken of.

## Main results

* `InverseGalois.CFT.exists_isGalois_forall_exists_pow`: **one finite Galois extension of the base
  holds an exponent-th root of every unit whose order is divisible by the exponent away from a
  prescribed finite set of places.**

## Tags

number field, Kummer theory, radical, normal closure, S-unit, class group
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

section RootField

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω]

/-- **One finite Galois extension of the base holds an exponent-th root of every unit of an
intermediate number field whose order is divisible by the exponent away from a prescribed finite set
of places.**

The units in question are carried modulo exponent-th powers by a single finitely generated
subgroup; adjoining a root of each generator to the intermediate field and passing to the normal
closure gives the extension, because the elements having a root in it form a subgroup containing
the generators, and a unit differs from a member of that subgroup by an exponent-th power. -/
theorem exists_isGalois_forall_exists_pow (K : IntermediateField k Ω) [NumberField ↥K] {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) {Tz : Set (HeightOneSpectrum (𝓞 ↥K))} (hTz : Tz.Finite) :
    ∃ M : IntermediateField k Ω, K ≤ M ∧ FiniteDimensional k ↥M ∧ IsGalois k ↥M ∧
      ∀ u : (↥K)ˣ,
        (∀ v : HeightOneSpectrum (𝓞 ↥K), v ∉ Tz → (ℓ : ℤ) ∣ ord ↥K v (u : ↥K)) →
        ∃ y ∈ M, y ^ ℓ = algebraMap (↥K) Ω (u : ↥K) := by
  classical
  haveI : FiniteDimensional k ↥K := Module.Finite.of_restrictScalars_finite ℚ k ↥K
  obtain ⟨H, hHfg, hH⟩ := exists_fg_forall_mul_pow ↥K ℓ hTz
  obtain ⟨gs, hgs⟩ := hHfg
  have hroot : ∀ g : (↥K)ˣ, ∃ y : Ω, y ^ ℓ = algebraMap (↥K) Ω (g : ↥K) :=
    fun g => IsAlgClosed.exists_pow_nat_eq _ (Nat.pos_of_ne_zero hℓ)
  choose r hr using hroot
  have hint : ∀ y ∈ r '' (gs : Set (↥K)ˣ), IsIntegral k y := fun y _ =>
    Algebra.IsIntegral.isIntegral (R := k) y
  haveI : Finite ↥(r '' (gs : Set (↥K)ˣ)) := (gs.finite_toSet.image r).to_subtype
  haveI : FiniteDimensional k ↥(IntermediateField.adjoin k (r '' (gs : Set (↥K)ˣ))) :=
    IntermediateField.finiteDimensional_adjoin hint
  set M₀ : IntermediateField k Ω := K ⊔ IntermediateField.adjoin k (r '' (gs : Set (↥K)ˣ))
    with hM₀
  haveI : FiniteDimensional k ↥M₀ := IntermediateField.finiteDimensional_sup _ _
  set M : IntermediateField k Ω := IntermediateField.normalClosure k ↥M₀ Ω with hMdef
  haveI : FiniteDimensional k ↥M := by rw [hMdef]; infer_instance
  haveI : Normal k ↥M := by rw [hMdef]; infer_instance
  haveI : Algebra.IsSeparable k ↥M := by rw [hMdef]; infer_instance
  have hM₀M : M₀ ≤ M := hMdef ▸ IntermediateField.le_normalClosure M₀
  have hKM : K ≤ M := le_trans (le_sup_left : K ≤ M₀) hM₀M
  let D : Subgroup (↥K)ˣ :=
    { carrier := {x : (↥K)ˣ | ∃ y ∈ M, y ^ ℓ = algebraMap (↥K) Ω (x : ↥K)}
      mul_mem' := by
        rintro a b ⟨ya, hya, hya'⟩ ⟨yb, hyb, hyb'⟩
        exact ⟨ya * yb, mul_mem hya hyb, by
          rw [mul_pow, hya', hyb', Units.val_mul, _root_.map_mul]⟩
      one_mem' := ⟨1, one_mem _, by rw [one_pow, Units.val_one, _root_.map_one]⟩
      inv_mem' := by
        rintro a ⟨y, hy, hy'⟩
        have hane : algebraMap (↥K) Ω (a : ↥K) ≠ 0 :=
          (map_ne_zero_iff _ (algebraMap (↥K) Ω).injective).2 a.ne_zero
        have hyne : y ≠ 0 := fun h => hane (by rw [← hy', h, zero_pow hℓ])
        exact ⟨y⁻¹, inv_mem hy, by
          rw [inv_pow, hy', Units.val_inv_eq_inv_val, map_inv₀]⟩ }
  have hHD : H ≤ D := by
    rw [← hgs]
    refine (Subgroup.closure_le D).2 fun g hg => ?_
    refine ⟨r g, hM₀M ?_, hr g⟩
    exact (le_sup_right : IntermediateField.adjoin k (r '' (gs : Set (↥K)ˣ)) ≤ M₀)
      (IntermediateField.subset_adjoin k _ ⟨g, hg, rfl⟩)
  refine ⟨M, hKM, inferInstance, ⟨⟩, fun u hu => ?_⟩
  obtain ⟨g, hgH, z, hz⟩ := hH u hu
  obtain ⟨y, hyM, hy⟩ := hHD hgH
  have hzM : algebraMap (↥K) Ω (z : ↥K) ∈ M := hKM (z : ↥K).2
  refine ⟨y * algebraMap (↥K) Ω (z : ↥K), mul_mem hyM hzM, ?_⟩
  rw [mul_pow, hy, ← _root_.map_pow, ← _root_.map_mul, ← Units.val_pow_eq_pow_val,
    ← Units.val_mul, ← hz]

end RootField

end InverseGalois.CFT
