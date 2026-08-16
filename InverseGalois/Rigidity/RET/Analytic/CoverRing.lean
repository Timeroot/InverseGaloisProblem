/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Identity
import InverseGalois.Rigidity.RET.Analytic.Moderate
import InverseGalois.Rigidity.RET.Analytic.FixedSubring

/-!
# The ring of functions of a covering, and its Galois group

The holomorphic functions of moderate growth on the total space of a covering of a punctured plane
form a subring of the functions on that space, and the deck group acts on it by ring
automorphisms.  If the total space is connected the ring is a domain, by the identity theorem, so
it has a fraction field; and if the deck group acts faithfully — that is, if for each nontrivial
deck transformation some function of the ring is moved by it — that fraction field is a Galois
extension of the fraction field of the invariants, with the deck group as Galois group and degree
the order of the group.

Faithfulness is the one thing the topology of a covering does not supply: it asks for enough
functions on the total space, which is the analytic content of the Riemann existence theorem.
Everything else on this page is formal.

## Main definitions

* `Rigidity.RET.IsOverBase` — the acting group moves the fibres of the projection into themselves.
* `Rigidity.RET.coverRing` — the holomorphic functions of moderate growth, as a subring.

## Main results

* `Rigidity.RET.coverRing_isDomain` — on a connected covering that subring is a domain.
* `Rigidity.RET.coverRingAction` — the deck group acts on it by ring automorphisms.
* `Rigidity.RET.faithfulSMul_coverRing` — the action is faithful as soon as every nontrivial deck
  transformation moves some function of the ring.
* `Rigidity.RET.isGalois_coverRing`, `Rigidity.RET.mulEquivAlgEquiv_coverRing`,
  `Rigidity.RET.finrank_coverRing` — the fraction field of the ring is a Galois extension of the
  fraction field of the invariants, with the deck group as Galois group and degree its order.
-/

open Topology

noncomputable section

namespace Rigidity.RET

/-! ### Composing with a symmetry over the base -/

section Comp

variable {Y : Type*} {f F : Y → ℂ} {S : Finset ℂ}

/-- **Moderate growth is preserved by a symmetry of the total space over the base**: the estimates
are estimates in the base coordinate, which the symmetry does not change. -/
theorem IsModerate.comp {σ : Y → Y} (hmod : IsModerate f S F) (hσ : ∀ y, f (σ y) = f y) :
    IsModerate f S fun y => F (σ y) where
  punct := by
    intro s hs
    obtain ⟨ρ, hρ, C, hC, N, hb⟩ := hmod.punct s hs
    refine ⟨ρ, hρ, C, hC, N, fun y hy => ?_⟩
    have hval := hb (σ y) (by rw [hσ]; exact hy)
    rwa [hσ] at hval
  infty := by
    obtain ⟨A, R₀, m, hA, hb⟩ := hmod.infty
    refine ⟨A, R₀, m, hA, fun y hy => ?_⟩
    have hval := hb (σ y) (by rw [hσ]; exact hy)
    rwa [hσ] at hval

end Comp

section Holo

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ}

/-- Holomorphy is preserved by a symmetry of the total space over the base. -/
theorem IsHolo.comp_homeomorph {perm : Y ≃ₜ Y} (h : IsHolo f g) (hperm : ∀ y, f (perm y) = f y) :
    IsHolo f fun y => g (perm y) := fun y => (h (perm y)).comp_homeomorph hperm

end Holo

/-! ### The subring -/

section Ring

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ}

/-- **The holomorphic functions of moderate growth on a covering, as a subring** of the functions
on the total space. -/
def coverRing (hf : IsLocalHomeomorph f) (S : Finset ℂ) : Subring (Y → ℂ) where
  carrier := {F | IsHolo f F ∧ IsModerate f S F}
  zero_mem' := ⟨fun y => isHoloAt_const hf 0 y, isModerate_const f S 0⟩
  one_mem' := ⟨fun y => isHoloAt_const hf 1 y, isModerate_const f S 1⟩
  add_mem' := fun ha hb => ⟨fun y => (ha.1 y).add (hb.1 y), ha.2.add hb.2⟩
  mul_mem' := fun ha hb => ⟨fun y => (ha.1 y).mul (hb.1 y), ha.2.mul hb.2⟩
  neg_mem' := fun ha => ⟨fun y => (ha.1 y).neg, ha.2.neg⟩

@[simp]
theorem mem_coverRing {hf : IsLocalHomeomorph f} {S : Finset ℂ} {F : Y → ℂ} :
    F ∈ coverRing hf S ↔ IsHolo f F ∧ IsModerate f S F := Iff.rfl

/-- **The ring of functions of a connected covering is a domain.**  A product of two holomorphic
functions vanishes identically only if one of them does, by the identity theorem. -/
instance coverRing_isDomain [Nonempty Y] [PreconnectedSpace Y] (hf : IsLocalHomeomorph f)
    (S : Finset ℂ) : IsDomain ↥(coverRing hf S) := by
  haveI : Nontrivial ↥(coverRing hf S) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have hval := congrFun (congrArg Subtype.val h) (Classical.arbitrary Y)
    simp at hval
  haveI : NoZeroDivisors ↥(coverRing hf S) := by
    refine ⟨fun {F G} h => ?_⟩
    have hfun : (fun y => (F : Y → ℂ) y * (G : Y → ℂ) y) = 0 := congrArg Subtype.val h
    rcases IsHolo.eq_zero_or_eq_zero_of_mul_eq_zero hf (mem_coverRing.1 F.2).1
      (mem_coverRing.1 G.2).1 hfun with h' | h'
    · exact Or.inl (Subtype.ext h')
    · exact Or.inr (Subtype.ext h')
  exact NoZeroDivisors.to_isDomain _

end Ring

/-! ### The action of the deck group -/

section Action

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ}
variable {H : Type*} [Group H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **A group acting on the total space over the base**: each element moves every fibre of the
projection into itself. -/
class IsOverBase (H : Type*) [Group H] [MulAction H Y] (f : Y → ℂ) : Prop where
  /-- the projection does not see the action. -/
  smul_eq : ∀ (a : H) (y : Y), f (a • y) = f y

/-- **The deck group acts on the ring of functions of the covering by ring automorphisms.** -/
instance coverRingAction (hf : IsLocalHomeomorph f) (S : Finset ℂ) [IsOverBase H f] :
    MulSemiringAction H ↥(coverRing hf S) where
  smul a F :=
    ⟨fun y => (F : Y → ℂ) (a⁻¹ • y),
      ⟨fun y => ((mem_coverRing.1 F.2).1 (a⁻¹ • y)).comp_homeomorph
          (perm := Homeomorph.smul a⁻¹) (IsOverBase.smul_eq a⁻¹),
        (mem_coverRing.1 F.2).2.comp (IsOverBase.smul_eq a⁻¹)⟩⟩
  one_smul F := by
    refine Subtype.ext (funext fun y => ?_)
    show (F : Y → ℂ) ((1 : H)⁻¹ • y) = (F : Y → ℂ) y
    rw [inv_one, one_smul]
  mul_smul a b F := by
    refine Subtype.ext (funext fun y => ?_)
    show (F : Y → ℂ) ((a * b)⁻¹ • y) = (F : Y → ℂ) (b⁻¹ • a⁻¹ • y)
    rw [mul_inv_rev, mul_smul]
  smul_zero a := Subtype.ext (funext fun _ => rfl)
  smul_add a F G := Subtype.ext (funext fun _ => rfl)
  smul_one a := Subtype.ext (funext fun _ => rfl)
  smul_mul a F G := Subtype.ext (funext fun _ => rfl)

theorem coverRing_smul_coe (hf : IsLocalHomeomorph f) (S : Finset ℂ) [IsOverBase H f] (a : H)
    (F : ↥(coverRing hf S)) (y : Y) :
    ((a • F : ↥(coverRing hf S)) : Y → ℂ) y = (F : Y → ℂ) (a⁻¹ • y) :=
  rfl

/-- **The action of the deck group on the functions of the covering is faithful as soon as every
nontrivial deck transformation moves one of them.** -/
theorem faithfulSMul_coverRing (hf : IsLocalHomeomorph f) (S : Finset ℂ) [IsOverBase H f]
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    FaithfulSMul H ↥(coverRing hf S) := by
  refine ⟨fun {a b} h => ?_⟩
  by_contra hab
  have hc : b⁻¹ * a ≠ 1 := fun h0 => hab (inv_mul_eq_one.1 h0).symm
  obtain ⟨F, hF, y, hy⟩ := hsep _ hc
  have hfun := congrArg Subtype.val (h ⟨F, hF⟩)
  have hval := congrFun hfun (a • y)
  rw [coverRing_smul_coe, coverRing_smul_coe, inv_smul_smul, ← mul_smul] at hval
  exact hy hval.symm

end Action

/-! ### The Galois extension -/

section Galois

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]

attribute [local instance] FractionRing.liftAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The function field of a connected covering is a Galois extension of the field of invariant
functions**, provided every nontrivial deck transformation moves some function of moderate
growth. -/
theorem isGalois_coverRing (hf : IsLocalHomeomorph f) (S : Finset ℂ) [IsOverBase H f]
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    IsGalois (FractionRing ↥(FixedPoints.subring ↥(coverRing hf S) H))
      (FractionRing ↥(coverRing hf S)) := by
  haveI := faithfulSMul_coverRing hf S hsep
  exact isGalois_fractionRing _ H

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The deck group is the Galois group of the function field of the covering over the field of
invariant functions.** -/
def mulEquivAlgEquiv_coverRing (hf : IsLocalHomeomorph f) (S : Finset ℂ) [IsOverBase H f]
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    H ≃* (FractionRing ↥(coverRing hf S) ≃ₐ[FractionRing
      ↥(FixedPoints.subring ↥(coverRing hf S) H)] FractionRing ↥(coverRing hf S)) := by
  haveI := faithfulSMul_coverRing hf S hsep
  exact mulEquivAlgEquiv_fractionRing _ H

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The degree of the function field of the covering over the field of invariant functions is the
order of the deck group.** -/
theorem finrank_coverRing (hf : IsLocalHomeomorph f) (S : Finset ℂ) [IsOverBase H f]
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    Module.finrank (FractionRing ↥(FixedPoints.subring ↥(coverRing hf S) H))
      (FractionRing ↥(coverRing hf S)) = Nat.card H := by
  haveI := faithfulSMul_coverRing hf S hsep
  exact finrank_fractionRing _ H

end Galois

end Rigidity.RET

end
