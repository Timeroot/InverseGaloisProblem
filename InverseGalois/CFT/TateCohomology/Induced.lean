/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Norm

/-!
# The functions on a finite group, and the vanishing of its middle Tate groups

The functions from a finite group to a module carry the representation that translates the
argument.  Its invariants are the constant functions, and the norm of a function is the constant
function whose value is the sum of the values of the function: a point mass has any prescribed sum,
so every invariant is a norm, and translating a point mass moves its support anywhere, so in the
coinvariants a function is the class of the point mass at the neutral element carrying the sum of
its values.  Both middle Tate groups of the functions on the group therefore vanish.

Every representation embeds equivariantly into the functions on the group, by sending a vector to
the map that records all of its translates.  That embedding is the first step of the dimension
shift that carries a statement about the complete cohomology in one degree to the neighbouring
degree.

## Main definitions

* `InverseGalois.CFT.Tate.inducedRep`: the representation on the functions on the group that
  translates the argument.
* `InverseGalois.CFT.Tate.coindEmb`: the embedding of a representation into the functions on the
  group.

## Main results

* `InverseGalois.CFT.Tate.normMap_inducedRep`: **the norm of a function is the constant function
  whose value is the sum of its values.**
* `InverseGalois.CFT.Tate.mem_invariants_inducedRep_iff`: **the invariants are the constant
  functions.**
* `InverseGalois.CFT.Tate.H0_inducedRep_eq_zero`,
  `InverseGalois.CFT.Tate.Hm1_inducedRep_eq_zero`: **both middle Tate groups of the functions on
  the group vanish.**
* `InverseGalois.CFT.Tate.coindEmb_equivariant`, `InverseGalois.CFT.Tate.coindEmb_injective`:
  **every representation embeds equivariantly into the functions on the group.**

## Tags

Tate cohomology, induced representation, coinduced representation, dimension shifting
-/

namespace InverseGalois.CFT.Tate

open Representation

noncomputable section

variable {k G M V : Type*} [CommRing k] [Group G] [Finite G]
  [AddCommGroup M] [Module k M] [AddCommGroup V] [Module k V]

/-! ### The functions on the group -/

section Induced

variable (k G M)

/-- **The representation on the functions from a group to a module** that translates the
argument. -/
def inducedRep : Representation k G (G → M) where
  toFun g := LinearMap.funLeft k M (· * g)
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [LinearMap.funLeft, mul_assoc]

variable {k G M}

omit [Finite G] in
@[simp]
theorem inducedRep_apply (g : G) (f : G → M) (x : G) : inducedRep k G M g f x = f (x * g) := rfl

omit [Finite G] in
/-- **The norm of a function on the group is the constant function whose value is the sum of its
values.** -/
theorem normMap_inducedRep [Fintype G] (f : G → M) (x : G) :
    normMap (inducedRep k G M) f x = ∑ y : G, f y := by
  rw [normMap_apply]
  simp only [Finset.sum_apply, inducedRep_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun g => rfl

omit [Finite G] in
/-- **The invariants of the functions on the group are the constant functions.** -/
theorem mem_invariants_inducedRep_iff (f : G → M) :
    f ∈ (inducedRep k G M).invariants ↔ ∀ x : G, f x = f 1 := by
  constructor
  · intro hf x
    have h := congrFun (hf x) 1
    rwa [inducedRep_apply, one_mul] at h
  · intro hf
    refine fun g => funext fun x => ?_
    rw [inducedRep_apply, hf (x * g), hf x]

omit [Finite G] in
/-- Translating a point mass moves its support anywhere. -/
theorem inducedRep_pi_single [DecidableEq G] (g x : G) (m : M) :
    inducedRep k G M g (Pi.single x m) = Pi.single (x * g⁻¹) m := by
  refine funext fun y => ?_
  rw [inducedRep_apply, Pi.single_apply, Pi.single_apply]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · rw [← h, mul_inv_cancel_right]
  · rw [h, inv_mul_cancel_right]

omit [Finite G] in
/-- In the coinvariants of the functions on the group a function is the class of the point mass at
the neutral element carrying the sum of its values. -/
theorem mk_eq_mk_pi_single [Fintype G] [DecidableEq G] (f : G → M) :
    Coinvariants.mk (inducedRep k G M) f
      = Coinvariants.mk (inducedRep k G M) (Pi.single 1 (∑ y : G, f y)) := by
  have hsingle : ∀ x : G, Coinvariants.mk (inducedRep k G M) (Pi.single x (f x))
      = Coinvariants.mk (inducedRep k G M) (Pi.single (1 : G) (f x)) := by
    intro x
    rw [← Coinvariants.mk_self_apply (inducedRep k G M) x (Pi.single x (f x)),
      inducedRep_pi_single, mul_inv_cancel]
  calc Coinvariants.mk (inducedRep k G M) f
      = Coinvariants.mk (inducedRep k G M) (∑ x : G, Pi.single x (f x)) := by
        rw [Finset.univ_sum_single]
    _ = ∑ x : G, Coinvariants.mk (inducedRep k G M) (Pi.single x (f x)) := by rw [map_sum]
    _ = ∑ x : G, Coinvariants.mk (inducedRep k G M) (Pi.single (1 : G) (f x)) :=
        Finset.sum_congr rfl fun x _ => hsingle x
    _ = Coinvariants.mk (inducedRep k G M) (∑ x : G, Pi.single (1 : G) (f x)) :=
        (map_sum _ _ _).symm
    _ = Coinvariants.mk (inducedRep k G M) (Pi.single 1 (∑ y : G, f y)) := by
        congr 1
        refine funext fun z => ?_
        simp only [Finset.sum_apply, Pi.single_apply]
        by_cases hz : z = (1 : G)
        · simp [hz]
        · simp [hz]

/-- **The Tate group in degree zero of the functions on the group vanishes.** -/
theorem H0_inducedRep_eq_zero (x : H0 (inducedRep k G M)) : x = 0 := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨y, rfl⟩ := H0mk_surjective (inducedRep k G M) x
  refine (H0mk_eq_zero_iff _ _).mpr ⟨Pi.single 1 ((y : G → M) 1), funext fun z => ?_⟩
  rw [normMap_inducedRep, Finset.sum_pi_single']
  simp only [Finset.mem_univ, if_true]
  exact (((mem_invariants_inducedRep_iff (y : G → M)).mp y.2) z).symm

/-- **The Tate group in degree minus one of the functions on the group vanishes.** -/
theorem Hm1_inducedRep_eq_zero (x : Hm1 (inducedRep k G M)) : x = 0 := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨y, hy⟩ := x
  obtain ⟨f, rfl⟩ := Coinvariants.mk_surjective (inducedRep k G M) y
  have hzero : ∑ z : G, f z = 0 := by
    have h := (coinvariantsNorm_eq_zero_iff (inducedRep k G M) f).mp hy
    have := congrFun h 1
    rwa [normMap_inducedRep] at this
  refine Subtype.ext ?_
  show Coinvariants.mk (inducedRep k G M) f = 0
  rw [mk_eq_mk_pi_single f, hzero, Pi.single_zero, map_zero]

end Induced

/-! ### The embedding into the functions on the group -/

section Embedding

variable (ρ : Representation k G V)

/-- **The embedding of a representation into the functions on the group**, recording all the
translates of a vector. -/
def coindEmb : V →ₗ[k] (G → V) where
  toFun v x := ρ x v
  map_add' v w := by ext x; simp
  map_smul' c v := by ext x; simp

omit [Finite G] in
@[simp]
theorem coindEmb_apply (v : V) (x : G) : coindEmb ρ v x = ρ x v := rfl

omit [Finite G] in
/-- **The embedding into the functions on the group is equivariant.** -/
theorem coindEmb_equivariant (g : G) :
    coindEmb ρ ∘ₗ ρ g = inducedRep k G V g ∘ₗ coindEmb ρ := by
  ext v x
  simp [Module.End.mul_apply, map_mul]

omit [Finite G] in
/-- **The embedding into the functions on the group is injective.** -/
theorem coindEmb_injective : Function.Injective (coindEmb ρ) := by
  intro v w h
  simpa using congrFun h 1

end Embedding

end

end InverseGalois.CFT.Tate
