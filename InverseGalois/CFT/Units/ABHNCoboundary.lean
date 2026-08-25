/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNTorsion

/-!
# The multiplicative form of the Albert-Brauer-Hasse-Noether coboundary theorem

The Albert-Brauer-Hasse-Noether theorem is proved for two-cocycles with values in the additive
group `Additive Kˣ`, because the machinery of idele classes and Herbrand quotients is additive.
The cocycles produced by embedding problems, on the other hand, arrive multiplicatively: they take
their values in the roots of unity of the base field, viewed inside `Kˣ`.

The translation is purely formal.  The Galois action on `Additive Kˣ` is the Galois action on `Kˣ`,
and a cocycle with values in the image of `kˣ` is automatically Galois-invariant, so the additive
cocycle identity for the inflated cocycle is exactly the multiplicative cocycle identity in `kˣ`.

## Main results

* `InverseGalois.CFT.toMul_globalUnitsAut`: the Galois action on the additive group of units is
  the Galois action on the units.
* `InverseGalois.CFT.smul_algebraMap_units`: the Galois group fixes the units coming from the base
  field.
* `InverseGalois.CFT.exists_isMulCoboundary_of_odd`: **a two-cocycle with values in the units of the
  base field, killed by an odd integer and a coboundary at every ramified finite place, is the
  coboundary of a one-cochain with values in the units of the extension.**

## Tags

number field, Albert-Brauer-Hasse-Noether, group cohomology, two-cocycle, coboundary, units
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **The Galois action on the additive group of units is the Galois action on the units.** -/
theorem toMul_globalUnitsAut (σ : Gal(K/k)) (u : Additive Kˣ) :
    (globalUnitsAut σ u).toMul = σ • u.toMul :=
  Units.ext rfl

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **The Galois group fixes the units coming from the base field.** -/
theorem smul_algebraMap_units (σ : Gal(K/k)) (c : kˣ) :
    σ • Units.map (algebraMap k K : k →* K) c = Units.map (algebraMap k K : k →* K) c :=
  Units.ext (σ.commutes _)

/-- **A two-cocycle with values in the units of the base field, killed by an odd integer and a
coboundary at every ramified finite place, is the coboundary of a one-cochain with values in the
units of the extension.**  This is the Albert-Brauer-Hasse-Noether theorem for cocycles of odd
order, written multiplicatively: the values lie in the base field, so the Galois group fixes them
and the inflated additive cocycle identity is the multiplicative one. -/
theorem exists_isMulCoboundary_of_odd {n : ℕ} (hn : Odd n)
    {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → Kˣ, ∀ g h : Gal(K/k),
      g • b h / b (g * h) * b g = Units.map (algebraMap k K : k →* K) (a g h) := by
  classical
  set ι : kˣ →* Kˣ := Units.map (algebraMap k K : k →* K) with hι
  set A : Gal(K/k) → Gal(K/k) → Additive Kˣ := fun x y => Additive.ofMul (ι (a x y)) with hA
  have hApow : ∀ x y : Gal(K/k), n • A x y = 0 := by
    intro x y
    rw [hA]
    show n • Additive.ofMul (ι (a x y)) = 0
    rw [← ofMul_pow, ← map_pow, hpow, map_one]
    rfl
  have hAcocycle : ∀ x y z : Gal(K/k),
      globalUnitsAut x (A y z) + A x (y * z) = A (x * y) z + A x y := by
    intro x y z
    have hfix : (globalUnitsAut x (A y z)) = A y z := by
      refine Additive.toMul.injective ?_
      rw [toMul_globalUnitsAut]
      exact smul_algebraMap_units x (a y z)
    rw [hfix, hA]
    show Additive.ofMul (ι (a y z)) + Additive.ofMul (ι (a x (y * z)))
      = Additive.ofMul (ι (a (x * y) z)) + Additive.ofMul (ι (a x y))
    rw [← ofMul_mul, ← ofMul_mul, ← map_mul, ← map_mul, ha]
  obtain ⟨b, hb⟩ := exists_sub_add_eq_globalUnits_of_odd hn hApow hAcocycle hram
  refine ⟨fun g => (b g).toMul, fun g h => ?_⟩
  have h2 := congrArg Additive.toMul (hb g h)
  rw [toMul_add, toMul_sub, toMul_globalUnitsAut] at h2
  exact h2.symm

end InverseGalois.CFT
