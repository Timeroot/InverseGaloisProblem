/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnitValuation
import InverseGalois.CFT.Units.CompletionGalois

/-!
# The units of a completion fixed by the decomposition group

The completion of a Galois extension of number fields at a prime is a Galois extension of the
completion of the base at the prime below, with Galois group the decomposition group.  Passing to
unit groups, the units fixed by the decomposition group are exactly the units coming from the
completion of the base: a fixed element of the completion comes from below, and it is nonzero
because it is a unit, hence a unit below.

This is the local ingredient in the description of the ideles fixed by the Galois group.

## Main definitions

* `InverseGalois.CFT.adicUnitsComap`: **the units of the completion of the base field, viewed in
  the completion at a prime above.**

## Main results

* `InverseGalois.CFT.adicUnitsComap_injective`: the inclusion of the local units of the base is
  injective.
* `InverseGalois.CFT.mem_range_adicUnitsComap_iff`: **the units of the completion fixed by the
  decomposition group are those coming from the completion of the base.**

## Tags

number field, completion, unit group, decomposition group, idele
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section CompletionUnits

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The units of the completion of the base field, viewed in the completion at a prime above**,
written additively. -/
noncomputable def adicUnitsComap :
    Additive ((primeUnder (𝓞 k) w).adicCompletion k)ˣ →+ Additive (w.adicCompletion K)ˣ :=
  MonoidHom.toAdditive (Units.map
    (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)).toMonoidHom)

variable (k) in
@[simp]
theorem coe_adicUnitsComap (u : Additive ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
    ((Additive.toMul (adicUnitsComap k w u) : (w.adicCompletion K)ˣ) : w.adicCompletion K)
      = algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
        ((Additive.toMul u : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
          (primeUnder (𝓞 k) w).adicCompletion k) := rfl

variable (k) in
/-- **The inclusion of the local units of the base field is injective.** -/
theorem adicUnitsComap_injective : Function.Injective (adicUnitsComap k w) := by
  intro u u' h
  refine Additive.toMul.injective (Units.ext ?_)
  refine FaithfulSMul.algebraMap_injective ((primeUnder (𝓞 k) w).adicCompletion k)
    (w.adicCompletion K) ?_
  rw [← coe_adicUnitsComap k w u, ← coe_adicUnitsComap k w u', h]

variable (k) in
/-- The decomposition group fixes the local units of the base field. -/
theorem smulUnitsAut_adicUnitsComap (σ : ↥(stabilizer Gal(K/k) w))
    (u : Additive ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
    smulUnitsAut σ (adicUnitsComap k w u) = adicUnitsComap k w u := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [coe_smulUnitsAut_apply, coe_adicUnitsComap]
  exact stabilizer_smul_algebraMap k w σ _

variable (k) in
/-- **The units of the completion fixed by the decomposition group are exactly those coming from
the completion of the base.** -/
theorem mem_range_adicUnitsComap_iff [IsGalois k K] (u : Additive (w.adicCompletion K)ˣ) :
    u ∈ (adicUnitsComap k w).range ↔ ∀ σ : ↥(stabilizer Gal(K/k) w), smulUnitsAut σ u = u := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨c, rfl⟩ σ
    exact smulUnitsAut_adicUnitsComap k w σ c
  · set x : (w.adicCompletion K)ˣ := Additive.toMul u with hx
    have hfix : ∀ σ : ↥(stabilizer Gal(K/k) w), σ • (x : w.adicCompletion K) = x := by
      intro σ
      have hσ := congrArg
        (fun a => ((Additive.toMul a : (w.adicCompletion K)ˣ) : w.adicCompletion K)) (h σ)
      simpa only [coe_smulUnitsAut_apply] using hσ
    obtain ⟨c, hc⟩ :=
      (mem_range_algebraMap_iff_forall_stabilizer_smul_eq k w (x : w.adicCompletion K)).mp hfix
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by rw [← hc, map_zero])
    refine ⟨Additive.ofMul (Units.mk0 c hc0), Additive.toMul.injective (Units.ext ?_)⟩
    rw [coe_adicUnitsComap]
    exact hc

end CompletionUnits

end InverseGalois.CFT
