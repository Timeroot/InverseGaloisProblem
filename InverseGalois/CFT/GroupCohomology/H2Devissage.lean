/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.H2Transport
import InverseGalois.CFT.GroupCohomology.InfResTwo

/-!
# Dévissage of the second cohomology along a quotient

Let `π : G → G'` be a surjection, and suppose the module of a representation of `G'` sits inside
the module of a representation of `G` as the part fixed by the kernel of `π`, compatibly with the
two actions.  Then that module *is* the module of invariants of the kernel, and the representation
of `G'` on it is the one induced on the quotient.

Reading the count furnished by inflation and restriction in degree two through that identification
bounds the second cohomology of `G` by the product of the second cohomology of `G'` and the second
cohomology of the kernel, provided the first cohomology of the kernel vanishes.  This is the form
in which the count is applied to a tower of fields, where the middle field is presented as a field
in its own right rather than as the fixed field of a subgroup.

## Main definitions

* `InverseGalois.CFT.devissageEquiv`: the module of a representation of the quotient, identified
  with the invariants of the kernel.

## Main results

* `InverseGalois.CFT.card_H2_quotientToInvariants_of_devissage`: the second cohomology of the
  representation induced on the invariants of the kernel has as many elements as the second
  cohomology of the given representation of the quotient.
* `InverseGalois.CFT.exists_zsmul_eq_zero_imp_dvd_H2_of_devissage`: **a class annihilated only by
  the multiples of a number is matched by such a class of the given representation of the
  quotient.**
* `InverseGalois.CFT.finite_and_card_H2_le_of_devissage`: **the second cohomology of `G` is finite
  and has at most as many elements as the product of the second cohomology of the quotient and the
  second cohomology of the kernel.**

## Tags

group cohomology, second cohomology, inflation, restriction, dévissage
-/

open CategoryTheory groupCohomology

namespace InverseGalois.CFT

noncomputable section

variable {G G' : Type} [Group G] [Group G'] {A : Rep ℤ G} {B : Rep ℤ G'}

section Devissage

variable (π : G →* G') (φ : B →ₗ[ℤ] A)
  (hφinj : Function.Injective φ)
  (hφeq : ∀ (g : G) (b : B), φ (B.ρ (π g) b) = A.ρ g (φ b))
  (hφrange : ∀ a : A, (∀ s : G, π s = 1 → A.ρ s a = a) → ∃ b : B, φ b = a)

include hφinj hφeq hφrange

/-- The module of a representation of the quotient, identified with the invariants of the kernel. -/
def devissageEquiv : B ≃+ ↥(A.quotientToInvariants π.ker) :=
  AddEquiv.ofBijective
    (LinearMap.codRestrict (Representation.invariants (A.ρ.comp π.ker.subtype)) φ fun b s => by
      show A.ρ (s : G) (φ b) = φ b
      have hs : π (s : G) = 1 := s.2
      rw [← hφeq, hs, map_one, Module.End.one_apply]).toAddMonoidHom
    ⟨fun _ _ h => hφinj (Subtype.ext_iff.1 h), by
      rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := hφrange a fun s hs => ha ⟨s, hs⟩
      exact ⟨b, Subtype.ext hb⟩⟩

@[simp]
theorem devissageEquiv_apply (b : B) :
    ((devissageEquiv π φ hφinj hφeq hφrange b :
      ↥(A.quotientToInvariants π.ker)) : A) = φ b := rfl

theorem coe_devissageEquiv_symm (a : ↥(A.quotientToInvariants π.ker)) :
    φ ((devissageEquiv π φ hφinj hφeq hφrange).symm a) = (a : A) := by
  rw [← devissageEquiv_apply π φ hφinj hφeq hφrange, AddEquiv.apply_symm_apply]

theorem devissage_intertwines (hπ : Function.Surjective π)
    (q : G ⧸ π.ker) (a : ↥(A.quotientToInvariants π.ker)) :
    (devissageEquiv π φ hφinj hφeq hφrange).symm ((A.quotientToInvariants π.ker).ρ q a)
      = B.ρ (QuotientGroup.quotientKerEquivOfSurjective π hπ q)
          ((devissageEquiv π φ hφinj hφeq hφrange).symm a) := by
  induction q using QuotientGroup.induction_on with
  | @H g =>
  refine (devissageEquiv π φ hφinj hφeq hφrange).injective ?_
  rw [AddEquiv.apply_symm_apply]
  refine Subtype.ext ?_
  show A.ρ g (a : A) = φ (B.ρ (π g) ((devissageEquiv π φ hφinj hφeq hφrange).symm a))
  rw [hφeq, coe_devissageEquiv_symm]

/-- The second cohomology of the representation induced on the invariants of the kernel has as many
elements as the second cohomology of the given representation of the quotient. -/
theorem card_H2_quotientToInvariants_of_devissage (hπ : Function.Surjective π) :
    Nat.card ↥(H2 (A.quotientToInvariants π.ker)) = Nat.card ↥(H2 B) :=
  card_H2_eq_of_addEquiv (QuotientGroup.quotientKerEquivOfSurjective π hπ)
    (devissageEquiv π φ hφinj hφeq hφrange).symm
    (devissage_intertwines π φ hφinj hφeq hφrange hπ)

/-- **A class of the representation induced on the invariants of the kernel that is annihilated
only by the multiples of a number is matched by such a class of the given representation of the
quotient.** -/
theorem exists_zsmul_eq_zero_imp_dvd_H2_of_devissage (hπ : Function.Surjective π) {n : ℕ}
    (h : ∃ γ : ↥(H2 (A.quotientToInvariants π.ker)), ∀ m : ℤ, m • γ = 0 → (n : ℤ) ∣ m) :
    ∃ γ : ↥(H2 B), ∀ m : ℤ, m • γ = 0 → (n : ℤ) ∣ m :=
  exists_zsmul_eq_zero_imp_dvd_H2_of_addEquiv (QuotientGroup.quotientKerEquivOfSurjective π hπ)
    (devissageEquiv π φ hφinj hφeq hφrange).symm
    (devissage_intertwines π φ hφinj hφeq hφrange hπ) h

/-- The second cohomology of the representation induced on the invariants of the kernel is finite
as soon as the second cohomology of the given representation of the quotient is. -/
theorem finite_H2_quotientToInvariants_of_devissage (hπ : Function.Surjective π)
    [Finite ↥(H2 B)] : Finite ↥(H2 (A.quotientToInvariants π.ker)) :=
  finite_H2_of_addEquiv (QuotientGroup.quotientKerEquivOfSurjective π hπ)
    (devissageEquiv π φ hφinj hφeq hφrange).symm
    (devissage_intertwines π φ hφinj hφeq hφrange hπ)

/-- **The second cohomology of a group is finite and has at most as many elements as the product of
the second cohomology of a quotient and the second cohomology of the kernel**, once the first
cohomology of the kernel vanishes and the module of the quotient is the module of invariants of the
kernel. -/
theorem finite_and_card_H2_le_of_devissage (hπ : Function.Surjective π)
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ π.ker.subtype).obj A) 1), z = 0)
    [Finite ↥(H2 B)] [Finite ↥(H2 ((Action.res _ π.ker.subtype).obj A))] :
    Finite ↥(H2 A) ∧ Nat.card ↥(H2 A)
      ≤ Nat.card ↥(H2 B) * Nat.card ↥(H2 ((Action.res _ π.ker.subtype).obj A)) := by
  haveI : Finite ↥(H2 (A.quotientToInvariants π.ker)) :=
    finite_H2_quotientToInvariants_of_devissage π φ hφinj hφeq hφrange hπ
  obtain ⟨hfin, hle⟩ := finite_and_card_H2_le (A := A) (S := π.ker) hH1
  refine ⟨hfin, ?_⟩
  rwa [card_H2_quotientToInvariants_of_devissage π φ hφinj hφeq hφrange hπ] at hle

end Devissage

end

end InverseGalois.CFT
