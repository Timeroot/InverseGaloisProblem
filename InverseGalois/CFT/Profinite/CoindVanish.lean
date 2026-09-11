/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.InfRes

/-!
# A module which is the functions on the group has no second cohomology

A coefficient module carries, for every homomorphism out of it, a reading as functions on the
group: send an element to the record of the values of the homomorphism at all of its translates.
That reading is equivariant for translation on the right, and when it is bijective the module is
exactly the functions on the group with values in the target of the homomorphism.

Such a module has no cohomology at all.  In degree two the contraction is explicit and short: read
a two cocycle through the homomorphism, freeze its first argument, and the resulting one cochain
has the cocycle for coboundary.  The cocycle relation, with the frozen argument in the first slot,
is precisely the identity that has to be checked.  Nothing about the group is used except that a
cochain on a discrete group is smooth, so the statement applies verbatim to the Galois group of a
finite extension.

This is the vanishing that turns a bound on the everywhere locally trivial classes by the image of
inflation from a finite level into the vanishing of those classes: if the coefficients are the
functions on the group of the level, there is nothing at the level to inflate.

## Main definitions

* `InverseGalois.CFT.translateEval`: the record of the values of a homomorphism at all the
  translates of an element.
* `InverseGalois.CFT.translateEvalHom`: the same, as a homomorphism into the functions on the
  group.
* `InverseGalois.CFT.homTranslate`: the reading of a homomorphism into the module as a family of
  homomorphisms into the values.
* `InverseGalois.CFT.homCompHom`: composition with a map of the target, on the homomorphisms into
  it.

## Main results

* `InverseGalois.CFT.translateEval_smul`: the reading is equivariant for translation on the right.
* `InverseGalois.CFT.bijective_homTranslate`: **the homomorphisms into a module which is the
  functions on the group are again the functions on the group.**
* `InverseGalois.CFT.subsingleton_smoothH2_of_bijective_translateEval`: **a module of a discrete
  group which is the functions on the group has no second cohomology.**

## Tags

group cohomology, coinduced module, discrete group, smooth cochain, cohomologically trivial
-/

namespace InverseGalois.CFT

open groupCohomology

section Translate

variable {G N X : Type*} [Group G] [CommGroup N] [MulDistribMulAction G N] [CommGroup X]

/-- **The reading of a module as functions on the group**: the record of the values of a
homomorphism out of the module at all the translates of an element. -/
def translateEval (π : N →* X) (n : N) : G → X := fun x => π (x • n)

theorem translateEval_apply (π : N →* X) (n : N) (x : G) : translateEval π n x = π (x • n) := rfl

/-- **The reading of a module as functions on the group is equivariant** for translation on the
right. -/
theorem translateEval_smul (π : N →* X) (g : G) (n : N) (x : G) :
    translateEval π (g • n) x = translateEval π n (x * g) := by
  rw [translateEval_apply, translateEval_apply, mul_smul]

/-- The reading of a module as functions on the group, as a homomorphism. -/
def translateEvalHom (π : N →* X) : N →* (G → X) where
  toFun := translateEval π
  map_one' := funext fun x => by
    rw [Pi.one_apply, translateEval_apply, smul_one, _root_.map_one]
  map_mul' n m := funext fun x => by
    rw [Pi.mul_apply, translateEval_apply, translateEval_apply, translateEval_apply, smul_mul',
      _root_.map_mul]

theorem translateEvalHom_apply (π : N →* X) (n : N) :
    (translateEvalHom π : N →* (G → X)) n = translateEval π n := rfl

/-- **A module whose reading as functions on the group is bijective is the functions on the
group.** -/
noncomputable def translateEvalEquiv (π : N →* X)
    (hbij : Function.Bijective (translateEval (G := G) π)) :
    N ≃* (G → X) :=
  MulEquiv.ofBijective (translateEvalHom π) hbij

theorem translateEvalEquiv_apply (π : N →* X)
    (hbij : Function.Bijective (translateEval (G := G) π)) (n : N) :
    translateEvalEquiv π hbij n = translateEval π n := rfl

end Translate

/-! ### Homomorphisms into a module which is the functions on the group -/

section HomTranslate

variable {G M N X : Type*} [MulOneClass M] [CommGroup N] [CommGroup X]

/-- The record of the values of a family of homomorphisms at a fixed element of the source. -/
def swapHom (F : G → (M →* X)) : M →* (G → X) where
  toFun m x := F x m
  map_one' := funext fun x => by rw [Pi.one_apply, _root_.map_one]
  map_mul' m m' := funext fun x => by rw [Pi.mul_apply, _root_.map_mul]

theorem swapHom_apply (F : G → (M →* X)) (m : M) (x : G) : swapHom F m x = F x m := rfl

/-- **The reading of a homomorphism into a module as a family of homomorphisms into the values**:
compose with the reading of the module as functions on the group, and evaluate at a point of the
group. -/
def homTranslate (Θ : N →* (G → X)) (w : M →* N) (x : G) : M →* X :=
  MonoidHom.mk' (fun m => Θ (w m) x) fun m m' => by
    show Θ (w (m * m')) x = Θ (w m) x * Θ (w m') x
    rw [_root_.map_mul, _root_.map_mul, Pi.mul_apply]

theorem homTranslate_apply (Θ : N →* (G → X)) (w : M →* N) (x : G) (m : M) :
    homTranslate Θ w x m = Θ (w m) x := rfl

/-- **Composition with a map of the target**, on the homomorphisms into it. -/
def homCompHom (π : N →* X) : (M →* N) →* (M →* X) where
  toFun w := π.comp w
  map_one' := MonoidHom.ext fun _ => _root_.map_one π
  map_mul' w v := MonoidHom.ext fun m => _root_.map_mul π (w m) (v m)

theorem homCompHom_apply (π : N →* X) (w : M →* N) (m : M) : homCompHom π w m = π (w m) := rfl

/-- **Homomorphisms into a module which is the functions on the group are the functions on the
group with values in the homomorphisms into the values.**  Being the functions on the group is
therefore inherited by the homomorphisms out of any group into the module. -/
theorem bijective_homTranslate (Θ : N ≃* (G → X)) :
    Function.Bijective (fun w : M →* N => homTranslate Θ.toMonoidHom w) := by
  constructor
  · intro w w' h
    refine MonoidHom.ext fun m => Θ.injective (funext fun x => ?_)
    exact congrArg (fun f : M →* X => f m) (congrFun h x)
  · intro F
    refine ⟨Θ.symm.toMonoidHom.comp (swapHom F), ?_⟩
    funext x
    refine MonoidHom.ext fun m => ?_
    show Θ (Θ.symm (swapHom F m)) x = F x m
    rw [MulEquiv.apply_symm_apply, swapHom_apply]

end HomTranslate

section Vanish

variable {X : Type*} [CommGroup X]

private theorem translateAlg {A B C D : X} (h : C * D = A * B) : C / B * D = A := by
  rw [div_mul_eq_mul_div, h, mul_div_assoc, div_self', mul_one]

variable {G N : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [CommGroup N]
  [MulDistribMulAction G N]

/-- **A module of a discrete group which is the functions on the group has no second
cohomology.**  Given a two cocycle, freeze its first argument and read the result through the
homomorphism: that is a one cochain, because the module is the functions on the group, and the
cocycle relation with the frozen argument in the first slot says exactly that its coboundary is the
cocycle one started with. -/
theorem subsingleton_smoothH2_of_bijective_translateEval (π : N →* X)
    (hbij : Function.Bijective (translateEval (G := G) π)) : Subsingleton (SmoothH2 G N) := by
  have key : ∀ y : SmoothH2 G N, y = 1 := by
    intro y
    obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective y
    choose b hb using fun σ : G => hbij.2 (fun x : G => π (a (x, σ)))
    refine (smoothH2Mk_eq_one_iff ha hs).2 ⟨b, isSmooth₁_of_discreteTopology b, ?_⟩
    funext q
    obtain ⟨σ, τ⟩ := q
    refine hbij.1 (funext fun x => ?_)
    have hcy := congrArg π (ha x σ τ)
    rw [_root_.map_mul, _root_.map_mul] at hcy
    have hbσ : π (x • b σ) = π (a (x, σ)) := congrFun (hb σ) x
    have hbτ : π ((x * σ) • b τ) = π (a (x * σ, τ)) := congrFun (hb τ) (x * σ)
    have hbστ : π (x • b (σ * τ)) = π (a (x, σ * τ)) := congrFun (hb (σ * τ)) x
    show π (x • coboundary₂ b (σ, τ)) = π (x • a (σ, τ))
    rw [coboundary₂_apply, smul_mul', smul_div', _root_.map_mul, _root_.map_div, ← mul_smul,
      hbσ, hbτ, hbστ]
    exact translateAlg hcy
  exact ⟨fun z w => (key z).trans (key w).symm⟩

end Vanish

end InverseGalois.CFT
