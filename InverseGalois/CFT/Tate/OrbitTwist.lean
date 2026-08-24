/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Fibers
import InverseGalois.CFT.Tate.Orbit
import InverseGalois.CFT.Tate.OrbitInduced

/-!
# A family of copies of a module permuted with a twist

Let a permutation of a finite set act on the families of elements of a fixed module indexed by that
set, by shifting the index and rescaling by an element of a group acting on the module.  When the
rescaling factor is trivial at every place of an orbit but the last, such a family is the module
induced from the factor at that last place, and its Herbrand quotient is the Herbrand quotient of
the module for the action of that factor.

This is the local factor of the group of ideles at a place of the base field, written without
choosing an isomorphism of the completions above it.  The places above a fixed place form one
orbit; a generator of the Galois group carries the component at one of them to the component at
the next; and transporting all of the components to the component at a chosen place turns the
generator into a shift of the index which is trivial except when the index wraps around, where it
becomes the action of the decomposition group.

## Main definitions

* `InverseGalois.CFT.cocycleTwistAut`: rescaling each component by a group element.
* `InverseGalois.CFT.permShiftAut`: shifting the index along a permutation.
* `InverseGalois.CFT.twistShiftAut`: **the two combined.**

## Main results

* `InverseGalois.CFT.herbrand_twistShiftAut`: **the Herbrand quotient of a twisted shift over a
  transitive orbit is that of the module for the twisting element.**
* `InverseGalois.CFT.exists_normHom_twistShiftAut`: **a fixed family is a norm for a twisted shift
  over a transitive orbit as soon as its value at the base point is a norm for the twisting
  element.**

## Tags

Tate cohomology, Herbrand quotient, orbit, induced module, idele
-/

namespace InverseGalois.CFT

open MulAction

variable {X Γ B : Type*} [Group Γ] [AddCommGroup B] (ρ : Γ →* (B ≃+ B))

/-! ### Twisting and shifting -/

/-- **Rescaling each component of a family by a group element.** -/
def cocycleTwistAut (c : X → Γ) : (X → B) ≃+ (X → B) where
  toFun f x := ρ (c x) (f x)
  invFun f x := (ρ (c x)).symm (f x)
  left_inv f := funext fun x => (ρ (c x)).symm_apply_apply (f x)
  right_inv f := funext fun x => (ρ (c x)).apply_symm_apply (f x)
  map_add' f g := funext fun x => map_add (ρ (c x)) (f x) (g x)

@[simp]
theorem cocycleTwistAut_apply (c : X → Γ) (f : X → B) (x : X) :
    cocycleTwistAut ρ c f x = ρ (c x) (f x) := rfl

variable (B) in
/-- **Shifting the index of a family along a permutation.** -/
def permShiftAut (p : Equiv.Perm X) : (X → B) ≃+ (X → B) where
  toFun f := f ∘ p
  invFun f := f ∘ p.symm
  left_inv f := funext fun x => congrArg f (p.apply_symm_apply x)
  right_inv f := funext fun x => congrArg f (p.symm_apply_apply x)
  map_add' _ _ := rfl

@[simp]
theorem permShiftAut_apply (p : Equiv.Perm X) (f : X → B) (x : X) :
    permShiftAut B p f x = f (p x) := rfl

/-- **A shift of the index followed by a rescaling of each component.** -/
def twistShiftAut (c : X → Γ) (p : Equiv.Perm X) : (X → B) ≃+ (X → B) :=
  (permShiftAut B p).trans (cocycleTwistAut ρ c)

@[simp]
theorem twistShiftAut_apply (c : X → Γ) (p : Equiv.Perm X) (f : X → B) (x : X) :
    twistShiftAut ρ c p f x = ρ (c x) (f (p x)) := rfl

/-! ### The Herbrand quotient -/

variable [Fintype X] (p : Equiv.Perm X) (x₀ : X)

/-- The presentation of a twisted shift over a transitive orbit as an induced module. -/
theorem twistShiftAut_orbitEquiv {c : X → Γ} {z : Γ}
    (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y)
    (hc : ∀ j : ZMod (period p x₀), j ≠ -1 → c (orbitPoint p x₀ j) = 1)
    (hlast : c (orbitPoint p x₀ (-1)) = z) (f : X → B) (j : ZMod (period p x₀)) :
    twistShiftAut ρ c p f (orbitEquiv p x₀ htrans j)
      = indTwist (ρ z) j (f (orbitEquiv p x₀ htrans (j + 1))) := by
  have hφ : ∀ i : ZMod (period p x₀), orbitEquiv p x₀ htrans i = orbitPoint p x₀ i := fun _ => rfl
  rw [hφ, hφ, twistShiftAut_apply, apply_orbitPoint]
  by_cases h : j = -1
  · subst h
    rw [hlast, indTwist_neg_one]
  · rw [hc j h, indTwist_of_ne _ h, map_one]

/-- **The Herbrand quotient of a twisted shift over a transitive orbit** is the Herbrand quotient
of the module for the twisting element.  The rescaling factors are trivial except where the index
wraps around, so the family is the module induced from the factor at the chosen point. -/
theorem herbrand_twistShiftAut {c : X → Γ} {z : Γ}
    (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y)
    (hc : ∀ j : ZMod (period p x₀), j ≠ -1 → c (orbitPoint p x₀ j) = 1)
    (hlast : c (orbitPoint p x₀ (-1)) = z) {m n : ℕ} (hz : z ^ m = 1)
    (hn : period p x₀ * m = n) :
    herbrand (twistShiftAut ρ c p) n = herbrand (ρ z) m :=
  herbrand_of_orbitInd _ hn (by rw [← map_pow, hz, map_one]) (orbitEquiv p x₀ htrans)
    (twistShiftAut_orbitEquiv ρ p x₀ htrans hc hlast)

/-- The upper Tate group of a twisted shift over a transitive orbit vanishes as soon as it vanishes
for the twisting element. -/
theorem subsingleton_tateH0_twistShiftAut {c : X → Γ} {z : Γ}
    (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y)
    (hc : ∀ j : ZMod (period p x₀), j ≠ -1 → c (orbitPoint p x₀ j) = 1)
    (hlast : c (orbitPoint p x₀ (-1)) = z) {m n : ℕ} (hz : z ^ m = 1)
    (hn : period p x₀ * m = n) (h : Subsingleton (tateH0 (ρ z) m)) :
    Subsingleton (tateH0 (twistShiftAut ρ c p) n) :=
  subsingleton_tateH0_of_orbitInd _ hn (by rw [← map_pow, hz, map_one])
    (orbitEquiv p x₀ htrans) (twistShiftAut_orbitEquiv ρ p x₀ htrans hc hlast) h

/-- **A fixed family is a norm for a twisted shift over a transitive orbit as soon as its value at
the base point is a norm for the twisting element.**  The family is the module induced from the
factor at the base point, and Shapiro's lemma reads a norm there as a norm here. -/
theorem exists_normHom_twistShiftAut {c : X → Γ} {z : Γ}
    (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y)
    (hc : ∀ j : ZMod (period p x₀), j ≠ -1 → c (orbitPoint p x₀ j) = 1)
    (hlast : c (orbitPoint p x₀ (-1)) = z) {m n : ℕ} (hz : z ^ m = 1)
    (hn : period p x₀ * m = n) {f : X → B} (hf : twistShiftAut ρ c p f = f)
    (h : ∃ b, normHom (ρ z) m b = f x₀) :
    ∃ u, normHom (twistShiftAut ρ c p) n u = f :=
  exists_normHom_of_orbitInd _ hn (by rw [← map_pow, hz, map_one]) (orbitEquiv p x₀ htrans)
    (twistShiftAut_orbitEquiv ρ p x₀ htrans hc hlast) hf (by rwa [orbitEquiv_zero])

/-- The lower Tate group of a twisted shift over a transitive orbit vanishes as soon as it vanishes
for the twisting element. -/
theorem subsingleton_tateHm1_twistShiftAut {c : X → Γ} {z : Γ}
    (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y)
    (hc : ∀ j : ZMod (period p x₀), j ≠ -1 → c (orbitPoint p x₀ j) = 1)
    (hlast : c (orbitPoint p x₀ (-1)) = z) {m n : ℕ} (hz : z ^ m = 1)
    (hn : period p x₀ * m = n) (h : Subsingleton (tateHm1 (ρ z) m)) :
    Subsingleton (tateHm1 (twistShiftAut ρ c p) n) :=
  subsingleton_tateHm1_of_orbitInd _ hn (by rw [← map_pow, hz, map_one])
    (orbitEquiv p x₀ htrans) (twistShiftAut_orbitEquiv ρ p x₀ htrans hc hlast) h

end InverseGalois.CFT
