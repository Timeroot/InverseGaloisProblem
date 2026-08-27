/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicAction
import InverseGalois.CFT.Local.UnitValuation

/-!
# The unit group of an adic completion as a module over the decomposition group

The decomposition group at a prime of a Galois extension of number fields acts on the completion
there by isometries, so the valuation of a unit is a homomorphism onto the integers on which the
group acts trivially.  The Herbrand quotient of the units of the completion is therefore the
Herbrand quotient of the units of its ring of integers, multiplied by the order of the group.

## Main results

* `InverseGalois.CFT.valued_smul_adicCompletion`: the decomposition group acts on the completion by
  isometries.
* `InverseGalois.CFT.ker_unitVal_eq_unitGroup_adicCompletionIntegers`: the kernel of the valuation
  on the units of the completion is the unit group of its ring of integers.
* `InverseGalois.CFT.herbrand_adicUnits_mul`: **the Herbrand quotient of the units of the
  completion is that of the units of its ring of integers, multiplied by the order of the group.**

## Tags

number field, adic completion, decomposition group, unit group, Herbrand quotient
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped WithZero

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
  (v : HeightOneSpectrum (𝓞 K))

/-- **The decomposition group acts on the completion by isometries.** -/
theorem valued_smul_adicCompletion (σ : ↥(stabilizer Gal(K/k) v)) (x : v.adicCompletion K) :
    Valued.v (σ • x) = Valued.v x :=
  valued_stabilizer_smul v σ x

theorem valued_adicCompletion_surjective :
    Function.Surjective (Valued.v : v.adicCompletion K → ℤᵐ⁰) :=
  HeightOneSpectrum.valuedAdicCompletion_surjective K v

/-- **The kernel of the valuation on the units of the completion is the unit group of its ring of
integers.** -/
theorem ker_unitVal_eq_unitGroup_adicCompletionIntegers
    {x : Additive (v.adicCompletion K)ˣ} :
    x ∈ (unitVal (A := v.adicCompletion K)).ker ↔
      (Additive.toMul x : (v.adicCompletion K)ˣ) ∈
        ValuationSubring.unitGroup (v.adicCompletionIntegers K) :=
  mem_ker_unitVal_iff_mem_unitGroup

/-- **The Herbrand quotient of the units of the completion is that of the units of its ring of
integers, multiplied by the order of the group.** -/
theorem herbrand_adicUnits_mul (σ : ↥(stabilizer Gal(K/k) v)) {n : ℕ} (hn : n ≠ 0)
    (hσ : σ ^ n = 1)
    [Finite (tateH0 (kerUnitValAut (valued_smul_adicCompletion v) σ) n)]
    [Finite (tateH0 (smulUnitsAut (R := v.adicCompletion K) σ) n)]
    [Finite (tateHm1 (kerUnitValAut (valued_smul_adicCompletion v) σ) n)]
    [Finite (tateHm1 (smulUnitsAut (R := v.adicCompletion K) σ) n)] :
    herbrand (kerUnitValAut (valued_smul_adicCompletion v) σ) n * n
      = herbrand (smulUnitsAut (R := v.adicCompletion K) σ) n :=
  herbrand_smulUnitsAut_mul (valued_smul_adicCompletion v)
    (isUnitValGen_one (valued_adicCompletion_surjective v)) σ hn hσ

end InverseGalois.CFT
