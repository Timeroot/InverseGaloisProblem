/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.Shapiro

/-!
# A family indexed by an orbit is an induced module

The induced module of Shapiro's lemma is presented as the tuples indexed by the residues modulo
the length of an orbit.  A family of copies of a module indexed by an abstract orbit is the same
thing once the orbit is enumerated: transporting along the enumeration turns an automorphism that
shifts the index by one, twisting by `τ` on passing the last position, into the automorphism of the
induced module.

This is the form in which Shapiro's lemma applies to the local components of the ideles.  The
places of a cyclic extension lying over a fixed place of the base field form a single orbit; a
generator of the Galois group carries the component at one place to the component at the next, and
after a full turn it acts on the component at the starting place through the decomposition group
there.

## Main definitions

* `InverseGalois.CFT.orbitIndEquiv`: the comparison of a family indexed by an orbit with the
  induced module.

## Main results

* `InverseGalois.CFT.indTwist_of_shift_of_last`: a shift of the index together with the twist at
  the last position is the presentation the comparison needs.
* `InverseGalois.CFT.herbrand_of_orbitInd`: **the Herbrand quotient of a family indexed by an
  orbit is that of the module at one point, for the automorphism of a full turn.**

## Tags

Tate cohomology, Shapiro's lemma, induced module, orbit, Herbrand quotient
-/

namespace InverseGalois.CFT

variable {X B : Type*} [AddCommGroup B] {d : ℕ}

/-! ### The comparison with the induced module -/

/-- **The comparison of a family indexed by an orbit with the induced module**, given an
enumeration of the orbit by the residues modulo its length. -/
def orbitIndEquiv (φ : ZMod d ≃ X) : (X → B) ≃+ (ZMod d → B) where
  toFun f := f ∘ φ
  invFun g := g ∘ φ.symm
  left_inv f := funext fun x => congrArg f (φ.apply_symm_apply x)
  right_inv g := funext fun j => congrArg g (φ.symm_apply_apply j)
  map_add' _ _ := rfl

@[simp]
theorem orbitIndEquiv_apply (φ : ZMod d ≃ X) (f : X → B) (j : ZMod d) :
    orbitIndEquiv φ f j = f (φ j) := rfl

variable (τ : B ≃+ B)

/-- **A shift of the index together with the twist at the last position** is the presentation the
comparison needs. -/
theorem indTwist_of_shift_of_last {s : (X → B) ≃+ (X → B)} (φ : ZMod d ≃ X)
    (hshift : ∀ (f : X → B) (j : ZMod d), j ≠ -1 → s f (φ j) = f (φ (j + 1)))
    (hlast : ∀ f : X → B, s f (φ (-1)) = τ (f (φ 0))) (f : X → B) (j : ZMod d) :
    s f (φ j) = indTwist τ j (f (φ (j + 1))) := by
  by_cases h : j = -1
  · subst h
    rw [indTwist_neg_one, neg_add_cancel, hlast]
  · rw [indTwist_of_ne τ h, hshift f j h]
    rfl

/-- The comparison is equivariant for a shift of the index twisted at the last position. -/
theorem orbitIndEquiv_equivariant {s : (X → B) ≃+ (X → B)} (φ : ZMod d ≃ X)
    (hs : ∀ (f : X → B) (j : ZMod d), s f (φ j) = indTwist τ j (f (φ (j + 1)))) (f : X → B) :
    orbitIndEquiv φ (s f) = indAut τ d (orbitIndEquiv φ f) :=
  funext fun j => by rw [orbitIndEquiv_apply, indAut_apply, orbitIndEquiv_apply, hs]

/-! ### The Herbrand quotient -/

/-- **The Herbrand quotient of a family indexed by an orbit is that of the module at one point**,
for the automorphism given by a full turn of the orbit. -/
theorem herbrand_of_orbitInd [NeZero d] {m n : ℕ} (hn : d * m = n) (hτ : τ ^ m = 1)
    {s : (X → B) ≃+ (X → B)} (φ : ZMod d ≃ X)
    (hs : ∀ (f : X → B) (j : ZMod d), s f (φ j) = indTwist τ j (f (φ (j + 1)))) :
    herbrand s n = herbrand τ m := by
  subst hn
  rw [herbrand_congr (orbitIndEquiv φ) (orbitIndEquiv_equivariant τ φ hs) (d * m),
    herbrand_indAut τ m hτ]

/-- The upper Tate group of a family indexed by an orbit vanishes as soon as it vanishes for the
module at one point. -/
theorem subsingleton_tateH0_of_orbitInd [NeZero d] {m n : ℕ} (hn : d * m = n) (hτ : τ ^ m = 1)
    {s : (X → B) ≃+ (X → B)} (φ : ZMod d ≃ X)
    (hs : ∀ (f : X → B) (j : ZMod d), s f (φ j) = indTwist τ j (f (φ (j + 1))))
    (h : Subsingleton (tateH0 τ m)) : Subsingleton (tateH0 s n) := by
  subst hn
  haveI := subsingleton_tateH0_indAut (d := d) τ m hτ h
  exact ⟨fun _ _ => (tateH0Congr (orbitIndEquiv φ) (orbitIndEquiv_equivariant τ φ hs)
    (d * m)).injective (Subsingleton.elim _ _)⟩

/-- The lower Tate group of a family indexed by an orbit vanishes as soon as it vanishes for the
module at one point. -/
theorem subsingleton_tateHm1_of_orbitInd [NeZero d] {m n : ℕ} (hn : d * m = n) (hτ : τ ^ m = 1)
    {s : (X → B) ≃+ (X → B)} (φ : ZMod d ≃ X)
    (hs : ∀ (f : X → B) (j : ZMod d), s f (φ j) = indTwist τ j (f (φ (j + 1))))
    (h : Subsingleton (tateHm1 τ m)) : Subsingleton (tateHm1 s n) := by
  subst hn
  haveI := subsingleton_tateHm1_indAut (d := d) τ m hτ h
  exact ⟨fun _ _ => (tateHm1Congr (orbitIndEquiv φ) (orbitIndEquiv_equivariant τ φ hs)
    (d * m)).injective (Subsingleton.elim _ _)⟩

end InverseGalois.CFT
