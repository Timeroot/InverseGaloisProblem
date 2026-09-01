/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNCoboundary

/-!
# The multiplicative Albert-Brauer-Hasse-Noether theorem at every place

The additive form of the Albert-Brauer-Hasse-Noether theorem takes a two-cocycle with values in the
units of the top field and a splitting of it at every place, archimedean or not.  The cocycles that
arise from embedding problems have their values in the units of the *base* field, and arrive
multiplicatively.  Translating between the two costs nothing: the Galois group fixes the units of
the base field, so the additive cocycle identity for the inflated cocycle is the multiplicative one
for the original.

The forms of the theorem already available place restrictions on the integer killing the cocycle —
that it be odd, or coprime to the local degrees at the archimedean places — in exchange for
assuming a local splitting only at the ramified finite places.  The form proved here makes no
assumption on the cocycle at all and asks instead for a local splitting at every place.

## Main results

* `InverseGalois.CFT.smulUnitsAut_infiniteUnitHom_algebraMap`: the decomposition group at an
  archimedean place fixes the local units coming from the base field.
* `InverseGalois.CFT.exists_isMulCoboundary_of_forall_place`: **a two-cocycle with values in the
  units of the base field which splits at every place of the extension is the coboundary of a
  one-cochain with values in the units of the extension.**

## Tags

number field, Albert-Brauer-Hasse-Noether, group cohomology, two-cocycle, coboundary, units, place
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

omit [NumberField k] [NumberField K] [IsGalois k K] in
/-- **The decomposition group at an archimedean place fixes the local units coming from the base
field.**  The embedding of the units into the units of the completion is equivariant, and the
Galois group fixes the units of the base field. -/
theorem smulUnitsAut_infiniteUnitHom_algebraMap (w : InfinitePlace K)
    (σ : ↥(stabilizer Gal(K/k) w)) (c : kˣ) :
    smulUnitsAut σ (Additive.ofMul (infiniteUnitHom w (Units.map (algebraMap k K : k →* K) c)))
      = Additive.ofMul (infiniteUnitHom w (Units.map (algebraMap k K : k →* K) c)) := by
  have h := smulUnitsAut_infiniteUnitHom (k := k) w σ
    (Additive.ofMul (Units.map (algebraMap k K : k →* K) c))
  rw [toMul_ofMul] at h
  rw [h, toMul_globalUnitsAut, toMul_ofMul, smul_algebraMap_units]

/-- **A two-cocycle with values in the units of the base field which splits at every place of the
extension is the coboundary of a one-cochain with values in the units of the extension.**  This is
the Albert-Brauer-Hasse-Noether theorem written multiplicatively: the values lie in the base field,
so the Galois group fixes them and the inflated additive cocycle identity is the multiplicative
one. -/
theorem exists_isMulCoboundary_of_forall_place
    {a : Gal(K/k) → Gal(K/k) → kˣ}
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hinf : ∀ w : InfinitePlace K, ∃ c : ↥(stabilizer Gal(K/k) w) → Additive w.Completionˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) w),
        Additive.ofMul (infiniteUnitHom w (Units.map (algebraMap k K : k →* K) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → Kˣ, ∀ g h : Gal(K/k),
      g • b h / b (g * h) * b g = Units.map (algebraMap k K : k →* K) (a g h) := by
  classical
  set ι : kˣ →* Kˣ := Units.map (algebraMap k K : k →* K) with hι
  set A : Gal(K/k) → Gal(K/k) → Additive Kˣ := fun x y => Additive.ofMul (ι (a x y)) with hA
  have hAcocycle : ∀ x y z : Gal(K/k),
      globalUnitsAut x (A y z) + A x (y * z) = A (x * y) z + A x y := by
    intro x y z
    have hfix : globalUnitsAut x (A y z) = A y z := by
      refine Additive.toMul.injective ?_
      rw [toMul_globalUnitsAut]
      exact smul_algebraMap_units x (a y z)
    rw [hfix, hA]
    show Additive.ofMul (ι (a y z)) + Additive.ofMul (ι (a x (y * z)))
      = Additive.ofMul (ι (a (x * y) z)) + Additive.ofMul (ι (a x y))
    rw [← ofMul_mul, ← ofMul_mul, ← map_mul, ← map_mul, ha]
  obtain ⟨b, hb⟩ := exists_sub_add_eq_globalUnits hAcocycle hinf hfin
  refine ⟨fun g => (b g).toMul, fun g h => ?_⟩
  have h2 := congrArg Additive.toMul (hb g h)
  rw [toMul_add, toMul_sub, toMul_globalUnitsAut] at h2
  exact h2.symm

end InverseGalois.CFT
