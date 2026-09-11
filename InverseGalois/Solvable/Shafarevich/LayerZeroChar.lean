/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerExtension

/-!
# The characters of a group named by the functionals on its zeroth layer

A homomorphism from a group to the residues modulo a prime kills the first term of the descending
central series, so it is read off from a functional on the zeroth layer, and conversely every
functional names one.  The naming is a bijection, additive in the functional and natural in the
group: pulling a functional back along a homomorphism names the character read through that
homomorphism.

This is the dictionary the reciprocity residue is written in.  The residue is defined on the units
of the base field and the arithmetic hands it a character of a Galois group presented as a quotient
of a generic operator group; the naming turns that character into a functional on the zeroth layer,
where the counting argument lives, and the naturality is what lets a relation established after a
shrinking be read at the level the arithmetic named.

## Main definitions

* `InverseGalois.Shafarevich.zeroDualChar` — the character of the group named by a functional on
  the zeroth layer.
* `InverseGalois.Shafarevich.zeroDualCharQuot` — **the character of a quotient by a term of the
  descending central series named by a functional on the zeroth layer.**

## Main results

* `InverseGalois.Shafarevich.exists_zeroDualCharQuot_eq` — **every character of such a quotient is
  named by a functional on the zeroth layer.**
* `InverseGalois.Shafarevich.zeroDualCharQuot_add` — the naming is additive in the functional.
* `InverseGalois.Shafarevich.zeroDualCharQuot_comp` — **the functional pulled back along a
  homomorphism names the character read through the induced map of quotients.**

## Tags

p-central series, layer, dual space, character, Shafarevich's theorem, embedding problem
-/

namespace InverseGalois.Shafarevich

section ZeroChar

variable {p : ℕ} {P Q : Type*} [Group P] [Group Q]

/-- The character of the group named by a functional on the zeroth layer. -/
def zeroDualChar (p : ℕ) (ψ : Module.Dual (ZMod p) (Layer p P 0)) :
    P →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (ψ (layerZeroMk p x))
  map_one' := by
    show Multiplicative.ofAdd (ψ (layerZeroMk p (1 : P))) = 1
    rw [layerZeroMk_one, _root_.map_zero]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (ψ (layerZeroMk p (x * y)))
      = Multiplicative.ofAdd (ψ (layerZeroMk p x)) * Multiplicative.ofAdd (ψ (layerZeroMk p y))
    rw [layerZeroMk_mul, _root_.map_add, ofAdd_add]

@[simp]
theorem zeroDualChar_apply (ψ : Module.Dual (ZMod p) (Layer p P 0)) (x : P) :
    zeroDualChar p ψ x = Multiplicative.ofAdd (ψ (layerZeroMk p x)) := rfl

/-- **The character of a quotient by a term of the descending central series named by a functional
on the zeroth layer.**  The term is contained in the first one, which every character kills. -/
def zeroDualCharQuot (p : ℕ) (ψ : Module.Dual (ZMod p) (Layer p P 0)) (m : ℕ) (hm : 1 ≤ m) :
    P ⧸ pCentral p P m →* Multiplicative (ZMod p) :=
  QuotientGroup.lift _ (zeroDualChar p ψ)
    ((pCentral_le_pCentral p hm).trans (pCentral_one_le_ker (zeroDualChar p ψ)))

@[simp]
theorem zeroDualCharQuot_mk (ψ : Module.Dual (ZMod p) (Layer p P 0)) (m : ℕ) (hm : 1 ≤ m) (x : P) :
    zeroDualCharQuot p ψ m hm (QuotientGroup.mk x)
      = Multiplicative.ofAdd (ψ (layerZeroMk p x)) := rfl

/-- **Every character of the quotient is named by a functional on the zeroth layer.** -/
theorem exists_zeroDualCharQuot_eq {m : ℕ} (hm : 1 ≤ m)
    (g : P ⧸ pCentral p P m →* Multiplicative (ZMod p)) :
    ∃ ψ : Module.Dual (ZMod p) (Layer p P 0), zeroDualCharQuot p ψ m hm = g := by
  refine ⟨layerZeroLift (g.comp (QuotientGroup.mk' (pCentral p P m))), MonoidHom.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  show Multiplicative.ofAdd
    (layerZeroLift (g.comp (QuotientGroup.mk' (pCentral p P m))) (layerZeroMk p y)) = _
  rw [layerZeroLift_layerZeroMk]
  rfl

/-- The naming is additive in the functional. -/
theorem zeroDualCharQuot_add (ψ ψ' : Module.Dual (ZMod p) (Layer p P 0)) (m : ℕ) (hm : 1 ≤ m)
    (x : P ⧸ pCentral p P m) :
    zeroDualCharQuot p (ψ + ψ') m hm x
      = zeroDualCharQuot p ψ m hm x * zeroDualCharQuot p ψ' m hm x := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  show Multiplicative.ofAdd ((ψ + ψ') (layerZeroMk p y)) = _
  rw [LinearMap.add_apply, ofAdd_add]
  rfl

/-- The functional pulled back along a homomorphism names the character read through that
homomorphism. -/
theorem zeroDualChar_comp (f : P →* Q) (ψ : Module.Dual (ZMod p) (Layer p Q 0)) :
    zeroDualChar p (ψ.comp (layerLinear p f 0)) = (zeroDualChar p ψ).comp f := by
  refine MonoidHom.ext fun x => ?_
  show Multiplicative.ofAdd (ψ (layerLinear p f 0 (layerZeroMk p x)))
    = Multiplicative.ofAdd (ψ (layerZeroMk p (f x)))
  rw [layerLinear_apply, layerMap_layerZeroMk]

/-- **The functional pulled back along a homomorphism names the character read through the induced
map of quotients.** -/
theorem zeroDualCharQuot_comp (f : P →* Q) (ψ : Module.Dual (ZMod p) (Layer p Q 0)) (m : ℕ)
    (hm : 1 ≤ m) :
    zeroDualCharQuot p (ψ.comp (layerLinear p f 0)) m hm
      = (zeroDualCharQuot p ψ m hm).comp (pCentralMap p m f) := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  show Multiplicative.ofAdd (ψ (layerLinear p f 0 (layerZeroMk p y)))
    = Multiplicative.ofAdd (ψ (layerZeroMk p (f y)))
  rw [layerLinear_apply, layerMap_layerZeroMk]

end ZeroChar

end InverseGalois.Shafarevich
