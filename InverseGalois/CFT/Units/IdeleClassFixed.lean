/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.QuotientFixed
import InverseGalois.CFT.Units.IdeleClass
import InverseGalois.CFT.Units.IdeleNorm

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

The same argument runs for the whole Galois group at once, cyclic or not.  A class fixed by every
automorphism has a representative whose differences with its conjugates are principal ideles, and
the corresponding family of units is a multiplicative `1`-cocycle; the general form of Hilbert's
theorem 90 makes it the coboundary of one unit, and subtracting the associated principal idele from
the representative makes it fixed by the whole group.

## Main results

* `InverseGalois.CFT.subsingleton_tateHm1_globalUnitsAut`: **Hilbert's theorem 90 for the units of a
  number field.**
* `InverseGalois.CFT.exists_fixed_ideleClass`: **an idele class fixed by the action is the class of
  a fixed idele.**
* `InverseGalois.CFT.mem_ker_sigmaSubOne_ideleClassAut_iff`: the classes fixed by the action are
  exactly the classes of the fixed ideles.
* `InverseGalois.CFT.exists_fixed_ideleClass_of_forall`: **an idele class fixed by the whole Galois
  group is the class of an idele fixed by the whole Galois group.**

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

/-! ### Lifting a class fixed by the whole group -/

section FixedGroup

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K]

omit [NumberField K] [FiniteDimensional k K] in
/-- The action of a Galois automorphism on the units of the field is the scalar action of the
automorphism. -/
theorem galUnits_eq_smul (σ : Gal(K/k)) (u : Kˣ) : galUnits σ u = σ • u := rfl

/-- **An idele class fixed by the whole Galois group is the class of an idele fixed by the whole
Galois group.**  A representative differs from each of its conjugates by a principal idele, and
those principal ideles form a multiplicative `1`-cocycle with values in the units of the field, so
Hilbert's theorem 90 makes them the coboundary of a single unit, whose principal idele can be
subtracted off. -/
theorem exists_fixed_ideleClass_of_forall
    {x : ↥(idele K) ⧸ (ideleDiag K).range}
    (hx : ∀ σ : Gal(K/k), ideleClassAut (k := k) σ x = x) :
    ∃ a : ↥(idele K), (∀ σ : Gal(K/k), ideleAut (k := k) σ a = a) ∧
      QuotientAddGroup.mk a = x := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hmem : ∀ σ : Gal(K/k), ideleAut (k := k) σ a - a ∈ (ideleDiag K).range := by
    intro σ
    have h := hx σ
    rw [ideleClassAut_mk] at h
    exact QuotientAddGroup.eq_iff_sub_mem.mp h
  choose u hu using hmem
  have key : ∀ σ τ : Gal(K/k),
      ideleDiag K (u (σ * τ)) = ideleDiag K (globalUnitsAut σ (u τ) + u σ) := by
    intro σ τ
    rw [map_add, ← ideleAut_ideleDiag]
    simp only [hu]
    rw [ideleAut_mul, map_sub]
    abel
  set f : Gal(K/k) → Kˣ := fun σ => Additive.toMul (u σ) with hfdef
  have hcocycle : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    refine Additive.ofMul.injective (ideleDiag_injective K ?_)
    have h2 : (Additive.ofMul (σ • f τ * f σ) : Additive Kˣ)
        = globalUnitsAut (k := k) σ (u τ) + u σ := Additive.toMul.injective (Units.ext rfl)
    rw [h2]
    exact key σ τ
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcocycle
  refine ⟨a - ideleDiag K (Additive.ofMul β), fun σ => ?_, ?_⟩
  · have hβσ : globalUnitsAut (k := k) σ (Additive.ofMul β) = Additive.ofMul β + u σ := by
      refine Additive.toMul.injective ?_
      show galUnits (k := k) σ β = β * f σ
      have h := hβ σ
      rw [div_eq_iff_eq_mul] at h
      rw [galUnits_eq_smul, h, mul_comm]
    have hua : ideleAut (k := k) σ a = a + ideleDiag K (u σ) := by
      rw [hu σ]; abel
    rw [map_sub, ideleAut_ideleDiag, hβσ, hua, map_add]
    abel
  · refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
    rw [sub_sub_cancel_left]
    exact ⟨-Additive.ofMul β, by rw [map_neg]⟩

end FixedGroup

end InverseGalois.CFT
