/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaRestrict
import InverseGalois.CFT.Kummer.InfiniteLevelPower
import InverseGalois.CFT.Kummer.UnramifiedOrd

/-!
# Inertia fixes a radical whose radicand has order a multiple of the exponent

Let `Ω` be an arbitrary Galois extension of a number field `k` containing a primitive `p`-th root of
unity, let `b` be an element of `Ω` whose `p`-th power `a` lies in `k`, and let `P` be a nonzero
prime of the integers of `Ω` away from `p`.  If the order of `a` at the place of `k` below `P` is a
multiple of `p`, then the inertia subgroup at `P` fixes `b`.

The criterion for an extension of number fields is the statement that a radical whose radicand is a
unit below is fixed by inertia, rescaled so that only the order of the radicand modulo the exponent
matters.  The passage to an arbitrary extension is a descent to a level: the radical generates a
finite Galois subextension, an element of inertia at `P` restricts to an element of inertia at the
prime of that level below `P`, and the place of `k` below the place of the level is the place of `k`
below `P`, so the criterion applies there and the restriction fixes the radical.  Restricting
inertia downwards asks nothing of the extension, which is what makes the descent available in this
direction with no surjectivity input.

## Main results

* `InverseGalois.CFT.forall_inertia_smul_eq_of_dvd_ord`: **the inertia subgroup at a nonzero prime
  away from the exponent of an arbitrary Galois extension fixes every radical whose radicand has
  order a multiple of the exponent at the place below.**

## Tags

number field, infinite Galois theory, inertia subgroup, Kummer theory, radical, order
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

section Inertia

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {p : ℕ}

/-- **The inertia subgroup at a nonzero prime away from the exponent of an arbitrary Galois
extension fixes every radical whose radicand has order a multiple of the exponent at the place
below.**  The radical lies in a finite Galois level, an element of inertia restricts to an element
of inertia of the level at the prime below, and the place of the base field below that prime is the
place the order is read at, so the criterion for an extension of number fields applies to the
restriction and the radical is fixed. -/
theorem forall_inertia_smul_eq_of_dvd_ord {P : Ideal (𝓞 Ω)} [P.IsPrime] (hp : p.Prime) {ζ : k}
    (hζ : IsPrimitiveRoot ζ p) (hpP : (p : 𝓞 Ω) ∉ P) {b : Ω} {a : k} (hane : a ≠ 0)
    (ha : algebraMap k Ω a = b ^ p) {v : HeightOneSpectrum (𝓞 k)}
    (hv : v.asIdeal = Ideal.under (𝓞 k) P) (hord : (p : ℤ) ∣ ord k v a) {σ : Gal(Ω/k)}
    (hσ : σ ∈ Ideal.inertia Gal(Ω/k) P) : σ b = b := by
  obtain ⟨L, hLfin, hLgal, hbL⟩ := exists_isGalois_level_mem k b
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  have hunder : Ideal.under (𝓞 k) (Ideal.under (𝓞 ↥L) P) = v.asIdeal := by
    rw [Ideal.under_under, hv]
  have hbot : Ideal.under (𝓞 ↥L) P ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    rw [← hunder, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  haveI : (Ideal.under (𝓞 ↥L) P).IsPrime := Ideal.IsPrime.under _ P
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 ↥L), w.asIdeal = Ideal.under (𝓞 ↥L) P :=
    ⟨⟨Ideal.under (𝓞 ↥L) P, inferInstance, hbot⟩, rfl⟩
  have hbb : (algebraMap (↥L) Ω) (⟨b, hbL⟩ : ↥L) = b := rfl
  have haL : (⟨b, hbL⟩ : ↥L) ^ p = algebraMap k ↥L a := by
    refine (algebraMap (↥L) Ω).injective ?_
    rw [← IsScalarTower.algebraMap_apply k ↥L Ω, map_pow, hbb, ha]
  have hveq : primeUnder (𝓞 k) w = v :=
    HeightOneSpectrum.ext (by rw [primeUnder_asIdeal, hw, hunder])
  have hpw : (p : 𝓞 ↥L) ∉ w.asIdeal := by
    rw [hw, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hpP
  have hσL : σ.restrictNormal ↥L ∈ Ideal.inertia Gal(↥L/k) w.asIdeal := by
    rw [hw]
    exact restrictNormal_mem_inertia L P hσ
  have hfix : σ.restrictNormal ↥L (⟨b, hbL⟩ : ↥L) = (⟨b, hbL⟩ : ↥L) :=
    eq_of_mem_inertia_of_radical_of_dvd_ord hp hζ hpw hσL hane (by rw [hveq]; exact hord) haL
  have hcom := AlgEquiv.restrictNormal_commutes σ ↥L (⟨b, hbL⟩ : ↥L)
  rw [hfix] at hcom
  exact hcom.symm

end Inertia

end InverseGalois.CFT
