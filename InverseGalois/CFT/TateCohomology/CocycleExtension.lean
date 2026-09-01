/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.AugmentationIdeal

/-!
# The extension of the base ring attached to a one cocycle

A one cocycle of a representation twists the action of the group on the sum of the representation
and the base ring: the group acts on the summand carrying the representation as it should, on the
summand carrying the base ring trivially, and it moves the second summand into the first along the
cocycle.  The cocycle identity is exactly what makes the twisted maps compose, and the value of a
cocycle at the neutral element vanishes, so the twisted maps are a representation.

The two summands make the twisted representation an extension of the base ring with trivial action
by the representation.  The class of the base ring in degree zero lifts to the vector of the second
summand, and the failure of that lift to be invariant is the cocycle itself, so the connecting map
of the extension carries the class of one in degree zero to the class of the cocycle in degree one.

## Main definitions

* `InverseGalois.CFT.Tate.cocycleObj`: the representation twisted by a one cocycle.
* `InverseGalois.CFT.Tate.cocycleSeq`: the extension of the base ring by the representation.

## Main results

* `InverseGalois.CFT.Tate.H0toH1_eq_H1π`: **the connecting map out of degree zero, computed on a
  lift and on the cochain measuring its failure to be invariant.**
* `InverseGalois.CFT.Tate.cocycleSeq_shortExact`: **the twisted representation is an extension of
  the base ring by the representation.**
* `InverseGalois.CFT.Tate.H0toH1_cocycleSeq`: **the connecting map of that extension carries the
  class of one to the class of the cocycle.**

## Tags

Tate cohomology, one cocycle, extension, connecting homomorphism
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### The connecting map out of degree zero -/

section Connecting

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

/-- **The connecting map out of degree zero, computed on a lift** of an invariant vector and on the
cochain measuring the failure of that lift to be invariant. -/
theorem H0toH1_eq_H1π (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = (z : X.X₃))
    (x : groupCohomology.cocycles₁ X.X₁)
    (hx : X.f.hom ∘ (x : G → X.X₁) = groupCohomology.d₀₁ X.X₂ y) :
    H0toH1 hX (H0mk X.X₃.ρ z) = groupCohomology.H1π X.X₁ x := by
  rw [H0toH1_H0mk, groupCohomology.δ₀_apply hX z y hy (x : G → X.X₁) hx]
  rfl

end Connecting

/-! ### Twisting the action by a cocycle -/

section Twist

variable (A : Rep k G) (b : groupCohomology.cocycles₁ A)

/-- **The twisted action of an element of the group** on the sum of a representation and the base
ring. -/
def cocycleLinear (τ : G) : ↥A.V × k →ₗ[k] ↥A.V × k :=
  LinearMap.prod
    (A.ρ τ ∘ₗ LinearMap.fst k ↥A.V k
      + LinearMap.toSpanSingleton k ↥A.V (b τ) ∘ₗ LinearMap.snd k ↥A.V k)
    (LinearMap.snd k ↥A.V k)

omit [Finite G] in
@[simp]
theorem cocycleLinear_apply (τ : G) (p : ↥A.V × k) :
    cocycleLinear A b τ p = (A.ρ τ p.1 + p.2 • b τ, p.2) := rfl

/-- **The representation twisted by a one cocycle.** -/
def cocycleRep : Representation k G (↥A.V × k) where
  toFun := cocycleLinear A b
  map_one' := by
    refine LinearMap.ext fun p => Prod.ext ?_ rfl
    show A.ρ 1 p.1 + p.2 • b 1 = p.1
    rw [groupCohomology.cocycles₁_map_one b, smul_zero, add_zero, map_one, Module.End.one_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun p => Prod.ext ?_ rfl
    show A.ρ (σ * τ) p.1 + p.2 • b (σ * τ)
      = A.ρ σ (A.ρ τ p.1 + p.2 • b τ) + p.2 • b σ
    rw [(groupCohomology.mem_cocycles₁_iff (b : G → ↥A.V)).1 b.2 σ τ, map_add, map_smul,
      map_mul, Module.End.mul_apply, smul_add]
    abel

/-- **The extension of the base ring attached to a one cocycle.** -/
def cocycleObj : Rep k G := Rep.of (cocycleRep A b)

omit [Finite G] in
@[simp]
theorem cocycleObj_ρ_apply (τ : G) (p : ↥A.V × k) :
    (cocycleObj A b).ρ τ p = (A.ρ τ p.1 + p.2 • b τ, p.2) := rfl

/-- **The inclusion of the representation into the twisted extension.** -/
def cocycleInl : ↥A.V →ₗ[k] ↥(cocycleObj A b).V := LinearMap.inl k ↥A.V k

/-- **The projection of the twisted extension onto the base ring.** -/
def cocycleSnd : ↥(cocycleObj A b).V →ₗ[k] ↥(Rep.trivial k G k).V := LinearMap.snd k ↥A.V k

omit [Finite G] in
theorem cocycleInl_equivariant (τ : G) :
    cocycleInl A b ∘ₗ A.ρ τ = (cocycleObj A b).ρ τ ∘ₗ cocycleInl A b := by
  refine LinearMap.ext fun m => Prod.ext ?_ rfl
  show A.ρ τ m = A.ρ τ m + (0 : k) • (b τ : ↥A.V)
  rw [zero_smul, add_zero]

omit [Finite G] in
theorem cocycleSnd_equivariant (τ : G) :
    cocycleSnd A b ∘ₗ (cocycleObj A b).ρ τ = (Rep.trivial k G k).ρ τ ∘ₗ cocycleSnd A b :=
  LinearMap.ext fun _ => rfl

/-- **The extension of the base ring with trivial action by a representation** attached to a one
cocycle. -/
def cocycleSeq : ShortComplex (Rep k G) where
  X₁ := A
  X₂ := cocycleObj A b
  X₃ := Rep.trivial k G k
  f := mkHom (cocycleInl A b) (cocycleInl_equivariant A b)
  g := mkHom (cocycleSnd A b) (cocycleSnd_equivariant A b)
  zero := by
    ext m
    rfl

omit [Finite G] in
/-- **The twisted representation is an extension of the base ring by the representation.** -/
theorem cocycleSeq_shortExact : (cocycleSeq A b).ShortExact :=
  shortExact_of_linearMap (fun _ _ h => congrArg Prod.fst h) (fun c => ⟨(0, c), rfl⟩)
    fun p hp => ⟨p.1, Prod.ext rfl hp.symm⟩

/-! ### The class of the cocycle -/

/-- **The connecting map of the twisted extension carries the class of one in degree zero to the
class of the cocycle in degree one.** -/
theorem H0toH1_cocycleSeq :
    H0toH1 (cocycleSeq_shortExact A b)
        (H0mk (Rep.trivial k G k).ρ ⟨1, mem_invariants_trivial k G 1⟩)
      = groupCohomology.H1π A b := by
  refine H0toH1_eq_H1π (cocycleSeq_shortExact A b) _ ((0 : ↥A.V), (1 : k)) rfl b ?_
  have h : ∀ τ : G, ((b τ : ↥A.V), (0 : k))
      = (A.ρ τ (0 : ↥A.V) + (1 : k) • (b τ : ↥A.V), (1 : k)) - ((0 : ↥A.V), (1 : k)) := by
    intro τ
    rw [map_zero, zero_add, one_smul]
    exact Prod.ext (sub_zero _).symm (sub_self _).symm
  exact funext h

end Twist

end

end InverseGalois.CFT.Tate
