/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Finite
import InverseGalois.CFT.Tate.Herbrand

/-!
# The short exact sequence of an equivariant surjection

An equivariant surjection of modules over a cyclic group has an invariant kernel, and the three
terms form a short exact sequence.  When the kernel is finite the Herbrand quotients of the source
and of the target agree.

This is how the torsion of the unit group of a number field is discarded: the units surject onto
the units modulo torsion, the kernel is the finite group of roots of unity, and the Herbrand
quotient may therefore be computed on the free quotient.

## Main definitions

* `InverseGalois.CFT.kerEquivAut`: the restriction of an automorphism to the kernel of an
  equivariant surjection.
* `InverseGalois.CFT.surjTateSES`: the short exact sequence of an equivariant surjection.

## Main results

* `InverseGalois.CFT.kerEquivAut_pow_eq_one`: the restricted automorphism inherits the order.
* `InverseGalois.CFT.herbrand_eq_of_finite_ker`: **an equivariant surjection with finite kernel
  does not change the Herbrand quotient.**

## Tags

Tate cohomology, Herbrand quotient, short exact sequence, kernel
-/

namespace InverseGalois.CFT

variable {B C : Type*} [AddCommGroup B] [AddCommGroup C] {n : ℕ}

/-! ### The restriction to the kernel -/

/-- **The restriction of an automorphism to the kernel of an equivariant surjection.** -/
def kerEquivAut (σB : B ≃+ B) (σC : C ≃+ C) (g : B →+ C) (hg : ∀ b, g (σB b) = σC (g b)) :
    g.ker ≃+ g.ker where
  toFun x := ⟨σB x, by
    rw [AddMonoidHom.mem_ker, hg, AddMonoidHom.mem_ker.mp x.2, map_zero]⟩
  invFun x := ⟨σB.symm x, by
    have hx := hg (σB.symm x)
    rw [σB.apply_symm_apply, AddMonoidHom.mem_ker.mp x.2] at hx
    exact AddMonoidHom.mem_ker.mpr (by simpa using (σC.map_eq_zero_iff).mp hx.symm)⟩
  left_inv x := Subtype.ext (σB.symm_apply_apply x)
  right_inv x := Subtype.ext (σB.apply_symm_apply x)
  map_add' x y := Subtype.ext (σB.map_add x y)

variable (σB : B ≃+ B) (σC : C ≃+ C) (g : B →+ C) (hg : ∀ b, g (σB b) = σC (g b))

@[simp]
theorem coe_kerEquivAut_apply (x : g.ker) : ((kerEquivAut σB σC g hg x : g.ker) : B) = σB x := rfl

/-- The powers of the restriction are the restrictions of the powers. -/
theorem coe_pow_kerEquivAut_apply (k : ℕ) (x : g.ker) :
    ((((kerEquivAut σB σC g hg) ^ k) x : g.ker) : B) = (σB ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, coe_kerEquivAut_apply, ih, ← pow_succ_apply]

variable {σB σC g hg}

/-- **The restricted automorphism inherits the order of the automorphism.** -/
theorem kerEquivAut_pow_eq_one (hσB : σB ^ n = 1) : (kerEquivAut σB σC g hg) ^ n = 1 :=
  AddEquiv.ext fun x => Subtype.ext (by rw [coe_pow_kerEquivAut_apply, hσB]; rfl)

/-! ### The short exact sequence -/

/-- **The short exact sequence of an equivariant surjection.** -/
def surjTateSES (hσB : σB ^ n = 1) (hσC : σC ^ n = 1) (hsurj : Function.Surjective g) :
    TateSES n g.ker B C where
  σA := kerEquivAut σB σC g hg
  σB := σB
  σC := σC
  hσA := kerEquivAut_pow_eq_one hσB
  hσB := hσB
  hσC := hσC
  f := g.ker.subtype
  g := g
  hf _ := rfl
  hg := hg
  finj _ _ hab := Subtype.ext hab
  gsurj := hsurj
  range_eq_ker := AddSubgroup.range_subtype _

@[simp]
theorem surjTateSES_σB (hσB : σB ^ n = 1) (hσC : σC ^ n = 1) (hsurj : Function.Surjective g) :
    (surjTateSES (hg := hg) hσB hσC hsurj).σB = σB := rfl

@[simp]
theorem surjTateSES_σC (hσB : σB ^ n = 1) (hσC : σC ^ n = 1) (hsurj : Function.Surjective g) :
    (surjTateSES (hg := hg) hσB hσC hsurj).σC = σC := rfl

/-! ### The Herbrand quotient -/

/-- **An equivariant surjection with finite kernel does not change the Herbrand quotient.** -/
theorem herbrand_eq_of_finite_ker [Finite g.ker] [NeZero n] [Module.Finite ℤ B]
    [Module.Finite ℤ C] (hg : ∀ b, g (σB b) = σC (g b)) (hσB : σB ^ n = 1) (hσC : σC ^ n = 1)
    (hsurj : Function.Surjective g) : herbrand σB n = herbrand σC n := by
  have h := (surjTateSES (hg := hg) hσB hσC hsurj).herbrand_eq_of_finite_sub
  rwa [surjTateSES_σB, surjTateSES_σC] at h

end InverseGalois.CFT
