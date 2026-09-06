/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerHom

/-!
# Kummer data survive an enlargement of the base

A Kummer situation over a level of a Galois extension is the data of a group of `n`-th roots of
unity of the level, a primitive one among them, and an `n`-th root in the extension of every unit
of the level.  **All of that survives passing to a larger level**, provided the extension has an
`n`-th root of each of its own units — which is automatic when it is algebraically closed.

Only one of the conditions has any content.  A larger level might a priori have more `n`-th roots
of unity than the smaller one, but it does not: a primitive `n`-th root of unity of the smaller
level stays primitive, and every `n`-th root of unity of the larger one is one of its powers,
hence already comes from the smaller level.  The remaining conditions are transported along the
inclusion, which is an injective homomorphism of fields.

The action of the Galois group of the larger level on the roots of unity plays no role, because a
Kummer situation forces it to be trivial; so the trivial action is taken.

## Main definitions

* `InverseGalois.CFT.unitsInclusion`: the units of a level inside the units of a larger one.
* `InverseGalois.CFT.trivialMulDistribMulAction`: the trivial action of a group on a commutative
  group.

## Main results

* `InverseGalois.CFT.algebraMap_unitsInclusion`: the inclusion of the units is compatible with
  reading the units in the whole extension.
* `InverseGalois.CFT.isKummerData_of_le`: **Kummer data for a level are Kummer data for a larger
  level**, along the inclusion of the units.

## Tags

Kummer theory, intermediate field, roots of unity, compositum
-/

namespace InverseGalois.CFT

/-! ### The units of a larger level -/

section Inclusion

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {K L : IntermediateField k Ω}

/-- **The units of a level inside the units of a larger one.** -/
def unitsInclusion (h : K ≤ L) : (↥K)ˣ →* (↥L)ˣ :=
  Units.map (IntermediateField.inclusion h).toRingHom.toMonoidHom

/-- The inclusion of the units of a level into the units of a larger one is injective. -/
theorem injective_unitsInclusion (h : K ≤ L) : Function.Injective (unitsInclusion h) :=
  Units.map_injective (IntermediateField.inclusion_injective h)

/-- Reading the image of a unit of a level in the whole extension gives the unit itself, read
there. -/
theorem algebraMap_unitsInclusion (h : K ≤ L) (a : (↥K)ˣ) :
    Units.map (algebraMap ↥L Ω : ↥L →* Ω) (unitsInclusion h a)
      = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a :=
  Units.ext rfl

end Inclusion

/-! ### The trivial action -/

section Trivial

/-- **The trivial action of a group on a commutative group.** -/
def trivialMulDistribMulAction (G M : Type*) [Group G] [CommGroup M] :
    MulDistribMulAction G M where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

end Trivial

/-! ### Kummer data for a larger level -/

section Sup

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {K L : IntermediateField k Ω}
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ιK : M →* (↥K)ˣ}
variable {p : ℕ} [NeZero p]

/-- **Kummer data for a level are Kummer data for a larger level.**  A primitive root of unity
stays primitive, so every root of unity of the larger level is one of its powers and therefore
already comes from the smaller one; the remaining conditions are transported along the inclusion,
and roots of the units of the larger level are supplied by the extension. -/
theorem isKummerData_of_le (hK : IsKummerData ↥K Ω M ιK p) (hKL : K ≤ L)
    (hroot : ∀ x : Ωˣ, ∃ y : Ωˣ, y ^ p = x) :
    letI := trivialMulDistribMulAction Gal(Ω/↥L) M
    IsKummerData ↥L Ω M ((unitsInclusion hKL).comp ιK) p := by
  letI := trivialMulDistribMulAction Gal(Ω/↥L) M
  obtain ⟨ζ, hζ⟩ := hK.exists_isPrimitiveRoot
  obtain ⟨ζ', rfl⟩ := hζ.isUnit (NeZero.ne p)
  have hζp : ζ' ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hζ.pow_eq_one)
  have hζL : IsPrimitiveRoot (IntermediateField.inclusion hKL (ζ' : ↥K)) p :=
    hζ.map_of_injective (IntermediateField.inclusion_injective hKL)
  have hpow : ∀ i : ℕ, ((unitsInclusion hKL (ζ' ^ i) : (↥L)ˣ) : ↥L)
      = IntermediateField.inclusion hKL (ζ' : ↥K) ^ i := by
    intro i
    rw [unitsInclusion, Units.coe_map, Units.val_pow_eq_pow_val]
    exact map_pow _ _ _
  refine ⟨⟨IntermediateField.inclusion hKL (ζ' : ↥K), hζL⟩, fun _ _ => rfl,
    (injective_unitsInclusion hKL).comp hK.injective, fun m => ?_, fun y hy => ?_,
    fun a => hroot _⟩
  · rw [MonoidHom.comp_apply, ← map_pow, hK.pow_eq_one m, map_one]
  · obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_pow_eq_one (ξ := (y : ↥L))
      (by rw [← Units.val_pow_eq_pow_val, hy, Units.val_one])
    obtain ⟨m, hm⟩ := hK.exists_ι_eq (ζ' ^ i)
      (by rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow])
    refine ⟨m, ?_⟩
    rw [MonoidHom.comp_apply, hm]
    exact Units.ext ((hpow i).trans hi)

end Sup

end InverseGalois.CFT
