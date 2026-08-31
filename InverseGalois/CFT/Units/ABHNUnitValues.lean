/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNTorsion

/-!
# The places where a two-cocycle of the units fails to be a unit

A nonzero element of a number field has nonzero order at only finitely many primes, so each value
of a two-cocycle of the Galois group with values in the units is a unit of the valuation ring at
all but finitely many places.  At a place where every value is such a unit and which is unramified
over the base, the decomposition group is cyclic and the second cohomology of the units of the
valuation ring vanishes, so the local component of the cocycle is a coboundary.

Together these say that a two-cocycle of the units is locally a coboundary outside a finite set of
places, with no torsion hypothesis on the cocycle: the hypothesis of `ABHNTorsion` is replaced by
the observation that the values are units almost everywhere.

## Main results

* `InverseGalois.CFT.finite_setOf_unitVal_adicUnitHom_ne_zero`: a unit of a number field is a unit
  of the valuation ring at all but finitely many places.
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_of_unitVal`: **at an unramified finite place where
  every value of a two-cocycle of the units is a unit of the valuation ring, the local component of
  that cocycle is a coboundary.**

## Tags

number field, idele, group cohomology, two-cocycle, coboundary, decomposition group, unramified
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

/-! ### The places where a unit is not a unit of the valuation ring -/

section UnitValues

variable (K : Type) [Field K] [NumberField K]

/-- **A unit of a number field is a unit of the valuation ring at all but finitely many places**,
because it has nonzero order at only finitely many primes. -/
theorem finite_setOf_unitVal_adicUnitHom_ne_zero (u : Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | unitVal (Additive.ofMul (adicUnitHom v u)) ≠ 0}.Finite := by
  have h := fullDiag_mem_idele K (Additive.ofMul u)
  rw [mem_idele, Filter.eventually_cofinite] at h
  exact h

end UnitValues

/-! ### The local coboundary at a place where the values are units -/

section Coboundary

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **At an unramified finite place where every value of a two-cocycle of the units is a unit of
the valuation ring, the local component of that cocycle is a coboundary.**  The second cohomology
of the cyclic decomposition group with values in those units vanishes. -/
theorem exists_sub_add_eq_adicUnits_of_unitVal (v : HeightOneSpectrum (𝓞 K))
    (hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal)
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (hu : ∀ x y : Gal(K/k), unitVal (Additive.ofMul (adicUnitHom v (a x y).toMul)) = 0)
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y) :
    ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  classical
  set ι : Additive Kˣ →+ Additive (v.adicCompletion K)ˣ :=
    MonoidHom.toAdditive (adicUnitHom v) with hι
  have hιapp : ∀ x : Additive Kˣ, ι x = Additive.ofMul (adicUnitHom v x.toMul) := fun _ => rfl
  have hmem : ∀ x y : Gal(K/k), ι (a x y) ∈ (unitVal (A := v.adicCompletion K)).ker := by
    intro x y
    rw [AddMonoidHom.mem_ker, hιapp]
    exact hu x y
  set f : ↥(stabilizer Gal(K/k) v) → ↥(stabilizer Gal(K/k) v) →
      ↥(unitVal (A := v.adicCompletion K)).ker :=
    fun s t => ⟨ι (a s.1 t.1), hmem s.1 t.1⟩ with hf
  have hcocycle : ∀ x y z : ↥(stabilizer Gal(K/k) v),
      kerUnitValAutHom (valued_smul_adicCompletion v) x (f y z) + f x (y * z)
        = f (x * y) z + f x y := by
    intro x y z
    refine Subtype.ext ?_
    show smulUnitsAut x (ι (a y.1 z.1)) + ι (a x.1 (y.1 * z.1))
      = ι (a (x.1 * y.1) z.1) + ι (a x.1 y.1)
    rw [hιapp, smulUnitsAut_adicUnitHom, ← hιapp, ← map_add, ← map_add, ha]
  obtain ⟨c, hc⟩ := exists_sub_add_eq_adicUnits v hunr hcocycle
  refine ⟨fun t => (c t : Additive (v.adicCompletion K)ˣ), fun s t => ?_⟩
  exact congrArg (Subtype.val (p := fun x => x ∈ (unitVal (A := v.adicCompletion K)).ker)) (hc s t)

end Coboundary

end InverseGalois.CFT
