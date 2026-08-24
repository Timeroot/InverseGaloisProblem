/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.QuotientFixed
import InverseGalois.CFT.Units.IdeleClass

/-!
# The idele classes fixed by the Galois group

The idele class group is the quotient of the ideles by the diagonal image of the units of the
field, and a class fixed by a Galois automorphism need not obviously be the class of a fixed idele:
a representative only satisfies that the difference between it and its image is a principal idele.
That difference has norm zero, so Hilbert's theorem 90 for the units of the field produces a unit
whose own difference accounts for it, and subtracting off the corresponding principal idele makes
the representative fixed.

For a cyclic Galois group Hilbert's theorem 90 is the vanishing of the Tate group `Ĥ⁻¹` of the unit
group, which holds because the group acts faithfully on a field.  So the fixed classes are exactly
the classes of the fixed ideles, which is the passage from the ideles to the idele classes in the
description of the fixed points of a Galois extension.

## Main results

* `InverseGalois.CFT.subsingleton_tateHm1_globalUnitsAut`: **Hilbert's theorem 90 for the units of a
  number field.**
* `InverseGalois.CFT.exists_fixed_ideleClass`: **an idele class fixed by the action is the class of
  a fixed idele.**
* `InverseGalois.CFT.mem_ker_sigmaSubOne_ideleClassAut_iff`: the classes fixed by the action are
  exactly the classes of the fixed ideles.

## Tags

number field, idele class group, Hilbert theorem 90, fixed points, Galois action
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section IdeleClassFixed

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]

/-! ### Hilbert's theorem 90 for the units of the field -/

omit [NumberField K] in
/-- The action of a Galois automorphism on the units of the field is the action induced by the
underlying element of the Galois group on the semiring of the field. -/
theorem globalUnitsAut_eq_addAut_unitsSmulAut (σ : Gal(K/k)) :
    globalUnitsAut (k := k) (K := K) σ = addAut (unitsSmulAut K σ) :=
  AddEquiv.ext fun _ => Additive.toMul.injective (Units.ext rfl)

variable {σ : Gal(K/k)} {d : ℕ} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)
  (hcard : Nat.card Gal(K/k) = d)

include hgen hcard

omit [NumberField K] in
/-- **Hilbert's theorem 90 for the units of a number field.**  A cyclic Galois group acts
faithfully on the field, so a unit whose conjugates multiply to one is a quotient of a unit by its
conjugate. -/
theorem subsingleton_tateHm1_globalUnitsAut [Finite Gal(K/k)] :
    Subsingleton (tateHm1 (globalUnitsAut (k := k) (K := K) σ) d) := by
  rw [globalUnitsAut_eq_addAut_unitsSmulAut]
  exact ⟨fun x y => by
    rw [tateHm1_unitsSmulAut_eq_zero hgen hcard x, tateHm1_unitsSmulAut_eq_zero hgen hcard y]⟩

/-! ### Lifting a fixed class to a fixed idele -/

/-- **An idele class fixed by the action of a generator of the Galois group is the class of a fixed
idele**: the difference between a representative and its image is a principal idele of norm zero,
hence the principal idele of a difference, which can be subtracted off. -/
theorem exists_fixed_ideleClass [Finite Gal(K/k)] (hσ : σ ^ d = 1)
    {x : ↥(idele K) ⧸ (ideleDiag K).range} (hx : ideleClassAut (k := k) σ x = x) :
    ∃ a : ↥(idele K), ideleAut (k := k) σ a = a ∧ QuotientAddGroup.mk a = x := by
  haveI := subsingleton_tateHm1_globalUnitsAut (k := k) (K := K) hgen hcard
  exact exists_fixed_mk_eq_of_range (σA := globalUnitsAut σ) (ideleDiag K)
    (fun a => (ideleAut_ideleDiag σ a).symm) (ideleDiag_injective K)
    (ideleAut_pow_eq_one σ hσ) hx

/-- **The idele classes fixed by the action of a generator of the Galois group are exactly the
classes of the fixed ideles.** -/
theorem mem_ker_sigmaSubOne_ideleClassAut_iff [Finite Gal(K/k)] (hσ : σ ^ d = 1)
    (x : ↥(idele K) ⧸ (ideleDiag K).range) :
    x ∈ (sigmaSubOne (ideleClassAut (k := k) σ)).ker ↔
      ∃ a : ↥(idele K), a ∈ (sigmaSubOne (M := ↥(idele K)) (ideleAut (k := k) σ)).ker ∧
        QuotientAddGroup.mk a = x := by
  rw [mem_ker_sigmaSubOne_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := exists_fixed_ideleClass hgen hcard hσ h
    exact ⟨a, (mem_ker_sigmaSubOne_iff _ a).mpr ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rw [ideleClassAut_mk, (mem_ker_sigmaSubOne_iff _ a).mp ha]

end IdeleClassFixed

end InverseGalois.CFT
