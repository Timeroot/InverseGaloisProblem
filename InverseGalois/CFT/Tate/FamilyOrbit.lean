/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.Family
import InverseGalois.CFT.Tate.OrbitCocycle

/-!
# A family of modules over a single orbit

A family of modules indexed by a transitive orbit of a cyclic group is determined by the module at
one chosen point of the orbit together with the action of the stabiliser of that point: choosing
for every point the group element that reaches it from the base point identifies all of the modules
with the module at the base point, and the action on sections becomes a shift of the index with a
rescaling that is trivial except where the index wraps around.

That is the content of the identification proved here.  Its consequence is the computation of the
Herbrand quotient of the group of sections: it is the Herbrand quotient of the module at the base
point for a full turn of the orbit, which is a generator of the stabiliser.  This is the local
factor of the group of ideles at a place of the base field, now written with the honest product of
the completions at the places above it rather than with a transported copy.

## Main definitions

* `InverseGalois.CFT.stabAut`: the action of the stabiliser of the base point on the module there.
* `InverseGalois.CFT.orbitFamilyEquiv`: **the identification of the sections of the family with
  copies of the module at the base point.**

## Main results

* `InverseGalois.CFT.orbitFamilyEquiv_familyAut`: the identification carries the action of a
  generator to a twisted shift of the index.
* `InverseGalois.CFT.herbrand_familyAut_orbit`: **the Herbrand quotient of the sections of a family
  over a transitive orbit is the Herbrand quotient of the module at the base point for a full
  turn.**

## Tags

Tate cohomology, Herbrand quotient, orbit, induced module, decomposition group, idele
-/

namespace InverseGalois.CFT

open MulAction

variable {G X : Type*} [Group G] [MulAction G X] [Fintype X] {σ : G} (x₀ : X)
  (htrans : ∀ y : X, ∃ k : ℕ, ((orbitShift X σ) ^ k) x₀ = y) {H : Subgroup G}
  (hH : ∀ g : G, g • x₀ = x₀ → g ∈ H) (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)
  {M : X → Type*} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)

/-! ### The action of the stabiliser at the base point -/

omit [Fintype X] in
/-- **The action of a subgroup fixing the base point on the module there.** -/
def stabAut : ↥H →* (M x₀ ≃+ M x₀) where
  toFun g := F.transport (hH' g)
  map_one' := by
    ext a
    exact (F.transport_congr (OneMemClass.coe_one H) (hH' 1) (one_smul G x₀) a).trans
      (F.transport_one_self x₀ a)
  map_mul' g h := by
    ext a
    rw [AddAut.mul_apply]
    exact (F.transport_congr (Subgroup.coe_mul H g h) (hH' (g * h))
        (by rw [mul_smul, hH' h, hH' g]) a).trans
      (F.transport_trans (hH' h) (hH' g) _ a).symm

omit [Fintype X] in
@[simp]
theorem stabAut_apply (g : ↥H) (a : M x₀) : stabAut x₀ hH' F g a = F.transport (hH' g) a := rfl

/-! ### The identification with copies of the module at the base point -/

/-- **The transport of the module at the base point to the module at a point of the orbit.** -/
noncomputable def orbitTransport (x : X) : M x₀ ≃+ M x :=
  F.transport (orbitSection_smul x₀ htrans x)

/-- **The identification of the sections of a family over a transitive orbit with copies of the
module at the base point.** -/
noncomputable def orbitFamilyEquiv : (∀ x, M x) ≃+ (X → M x₀) where
  toFun f x := (orbitTransport x₀ htrans F x).symm (f x)
  invFun f x := orbitTransport x₀ htrans F x (f x)
  left_inv f := funext fun x => (orbitTransport x₀ htrans F x).apply_symm_apply (f x)
  right_inv f := funext fun x => (orbitTransport x₀ htrans F x).symm_apply_apply (f x)
  map_add' _ _ := funext fun _ => map_add _ _ _

@[simp]
theorem orbitFamilyEquiv_apply (f : ∀ x, M x) (x : X) :
    orbitFamilyEquiv x₀ htrans F f x = (orbitTransport x₀ htrans F x).symm (f x) := rfl

/-! ### The action of a generator becomes a twisted shift -/

/-- **The identification carries the action of a generator to a twisted shift of the index.**  The
rescaling is the cocycle left over from the choice of a group element reaching each point of the
orbit from the base point. -/
theorem orbitFamilyEquiv_familyAut (f : ∀ x, M x) :
    orbitFamilyEquiv x₀ htrans F (F.familyAut σ f)
      = twistShiftAut (stabAut x₀ hH' F) (orbitCocycleSub x₀ htrans hH) (orbitShift X σ)
          (orbitFamilyEquiv x₀ htrans F f) := by
  funext x
  set y : X := σ⁻¹ • x with hy
  set b : M x₀ := (orbitTransport x₀ htrans F y).symm (f y) with hb
  have hfy : f y = orbitTransport x₀ htrans F y b :=
    ((orbitTransport x₀ htrans F y).apply_symm_apply (f y)).symm
  have hsy : orbitSection x₀ htrans y • x₀ = y := orbitSection_smul x₀ htrans y
  have hsx : orbitSection x₀ htrans x • x₀ = x := orbitSection_smul x₀ htrans x
  have hσy : σ • y = x := smul_inv_smul σ x
  have hc : (orbitCocycleSub x₀ htrans hH x : G)
      = (orbitSection x₀ htrans x)⁻¹ * σ * orbitSection x₀ htrans y := rfl
  have hgroup : orbitSection x₀ htrans x * (orbitCocycleSub x₀ htrans hH x : G)
      = σ * orbitSection x₀ htrans y := by
    rw [hc]
    group
  have h₃ : (σ * orbitSection x₀ htrans y) • x₀ = x := by rw [mul_smul, hsy, hσy]
  have h₄ : (orbitSection x₀ htrans x * (orbitCocycleSub x₀ htrans hH x : G)) • x₀ = x := by
    rw [hgroup, h₃]
  refine (orbitTransport x₀ htrans F x).symm_apply_eq.mpr ?_
  rw [twistShiftAut_apply, orbitShift_apply, ← hy, orbitFamilyEquiv_apply, ← hb, stabAut_apply,
    F.familyAut_apply_eq_transport hσy f, hfy, orbitTransport, orbitTransport,
    F.transport_trans hsy hσy h₃, F.transport_trans (hH' _) hsx h₄]
  exact F.transport_congr hgroup.symm h₃ h₄ b

/-! ### The Herbrand quotient -/

include htrans hH hH' in
/-- **The Herbrand quotient of the sections of a family of modules over a transitive orbit** is the
Herbrand quotient of the module at the base point for a full turn of the orbit.  Transporting the
modules to the base point presents the sections as the module induced from the stabiliser. -/
theorem herbrand_familyAut_orbit {m n : ℕ} (hz : (orbitTurn σ x₀ hH) ^ m = 1)
    (hn : period (orbitShift X σ) x₀ * m = n) :
    herbrand (F.familyAut σ) n = herbrand (stabAut x₀ hH' F (orbitTurn σ x₀ hH)) m := by
  rw [herbrand_congr (orbitFamilyEquiv x₀ htrans F)
    (orbitFamilyEquiv_familyAut x₀ htrans hH hH' F) n]
  exact herbrand_twistShiftAut_orbitCocycle x₀ htrans hH (stabAut x₀ hH' F) hz hn

end InverseGalois.CFT
