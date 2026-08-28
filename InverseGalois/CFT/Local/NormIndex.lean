/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Tate.CyclicHilbert90
import InverseGalois.CFT.Tate.H0Norm

/-!
# The norm index of a cyclic extension of local fields

The decomposition group at a finite place of a number field acts on the completion there, and the
Herbrand quotient of the group of units of that completion is the order of the decomposition group.
Hilbert's theorem 90 says that the lower of the two Tate groups vanishes, because the action on the
completion is faithful and the completion is a field.  Dividing, the upper Tate group has order the
order of the decomposition group: this is the local norm index, the statement that the elements of
the base which are norms from the completion form a subgroup of index the local degree.

## Main results

* `InverseGalois.CFT.subsingleton_tateHm1_adicUnitsField`: **Hilbert's theorem 90 for a completion
  of a number field**, that the lower Tate group of the units vanishes.
* `InverseGalois.CFT.card_tateHm1_adicUnitsField`: the same, read as an order.
* `InverseGalois.CFT.card_tateH0_adicUnitsField`: **the norm index of a cyclic extension of local
  fields is the local degree.**
* `InverseGalois.CFT.exists_normHom_adicUnits_eq_nsmul`: **every multiple of the local degree of a
  local unit fixed by the decomposition group is a local norm.**

## Tags

local field, norm index, Hilbert theorem 90, Tate cohomology, decomposition group
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section Adic

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  {k : Type*} [Field k] [Algebra k K] [Fintype ↥(stabilizer Gal(K/k) v)]
  {σ : ↥(stabilizer Gal(K/k) v)} (hgen : ∀ g : ↥(stabilizer Gal(K/k) v), g ∈ Subgroup.zpowers σ)
  {d : ℕ} (hσ : σ ^ d = 1) (hcard : Nat.card ↥(stabilizer Gal(K/k) v) = d)

include hgen hcard

/-- **Hilbert's theorem 90 for a completion of a number field.**  The decomposition group acts
faithfully on the completion, which is a field, so an element whose conjugates multiply to one is a
quotient of an element by its conjugate. -/
theorem subsingleton_tateHm1_adicUnitsField :
    Subsingleton (tateHm1 (smulUnitsAut (R := v.adicCompletion K) σ) d) :=
  ⟨fun x y => by
    rw [tateHm1_unitsSmulAut_eq_zero hgen hcard x, tateHm1_unitsSmulAut_eq_zero hgen hcard y]⟩

/-- The lower Tate group of the units of a completion of a number field has order one. -/
theorem card_tateHm1_adicUnitsField :
    Nat.card (tateHm1 (smulUnitsAut (R := v.adicCompletion K) σ) d) = 1 :=
  haveI := subsingleton_tateHm1_adicUnitsField v hgen hcard
  Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

variable [NeZero d]

include hσ

/-- **The norm index of a cyclic extension of local fields is the local degree.**  The Herbrand
quotient of the units of the completion is the order of the decomposition group, and the
denominator of that quotient is one by Hilbert's theorem 90. -/
theorem card_tateH0_adicUnitsField :
    Nat.card (tateH0 (smulUnitsAut (R := v.adicCompletion K) σ) d) = d := by
  have hq := herbrand_adicUnits_eq_card v hgen hσ hcard
  rw [herbrand, card_tateHm1_adicUnitsField v hgen hcard] at hq
  push_cast at hq
  rw [div_one] at hq
  exact_mod_cast hq

/-- **Every multiple of the local degree of a local unit fixed by the decomposition group is a
local norm.**  The norm index is the local degree, and the order of the zeroth Tate group
annihilates it. -/
theorem exists_normHom_adicUnits_eq_nsmul (x : Additive (v.adicCompletion K)ˣ)
    (hx : smulUnitsAut (R := v.adicCompletion K) σ x = x) {m : ℕ} (hm : d ∣ m) :
    ∃ y, normHom (smulUnitsAut (R := v.adicCompletion K) σ) d y = m • x :=
  exists_normHom_eq_nsmul x hx (by rwa [card_tateH0_adicUnitsField v hgen hσ hcard])

end Adic

end InverseGalois.CFT
