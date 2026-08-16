/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverHolo

/-!
# Families of polynomials with holomorphic coefficients

A polynomial attached to each point of a space lying locally homeomorphically over the plane has
*holomorphic coefficients* when each of its coefficients, read as a function of the point, is
holomorphic.  This is the right notion to carry along when a polynomial is built out of
holomorphic functions: it is stable under sums and products, because a coefficient of a sum is a
sum of coefficients and a coefficient of a product is a finite sum of products of them, and it
holds for the polynomials built from a holomorphic function by `Polynomial.C` and for the
polynomials that do not vary with the point at all.

Every polynomial assembled from those pieces therefore has holomorphic coefficients, with no need
to compute the coefficients themselves.

## Main definitions

* `Rigidity.RET.HoloCoeffs` — every coefficient of the family is a holomorphic function.

## Main results

* `Rigidity.RET.HoloCoeffs.add`, `Rigidity.RET.HoloCoeffs.sub`, `Rigidity.RET.HoloCoeffs.mul` —
  the notion is stable under the ring operations.
* `Rigidity.RET.holoCoeffs_finset_sum`, `Rigidity.RET.holoCoeffs_finset_prod` — and under finite
  sums and products.
* `Rigidity.RET.holoCoeffs_const`, `Rigidity.RET.holoCoeffs_C` — the two kinds of atoms.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ} {p q : Y → ℂ[X]}

/-- **A family of polynomials indexed by the total space has holomorphic coefficients** when each
coefficient, read as a function of the point, is a holomorphic function on the total space. -/
def HoloCoeffs (f : Y → ℂ) (p : Y → ℂ[X]) : Prop :=
  ∀ k, IsHolo f fun y => (p y).coeff k

/-- A family which does not vary with the point has holomorphic coefficients: its coefficients are
constants. -/
theorem holoCoeffs_const (hf : IsLocalHomeomorph f) (r : ℂ[X]) :
    HoloCoeffs f fun _ : Y => r :=
  fun k y => isHoloAt_const hf (r.coeff k) y

/-- The constant polynomial with a holomorphic value has holomorphic coefficients. -/
theorem holoCoeffs_C (hf : IsLocalHomeomorph f) (hg : IsHolo f g) :
    HoloCoeffs f fun y => C (g y) := by
  intro k y
  by_cases hk : k = 0
  · subst hk
    simpa using hg y
  · simpa [coeff_C, hk] using isHoloAt_const hf 0 y

theorem HoloCoeffs.add (hp : HoloCoeffs f p) (hq : HoloCoeffs f q) :
    HoloCoeffs f fun y => p y + q y := by
  intro k y
  simpa using (hp k y).add (hq k y)

theorem HoloCoeffs.neg (hp : HoloCoeffs f p) : HoloCoeffs f fun y => -p y := by
  intro k y
  simpa using (hp k y).neg

theorem HoloCoeffs.sub (hp : HoloCoeffs f p) (hq : HoloCoeffs f q) :
    HoloCoeffs f fun y => p y - q y := by
  intro k y
  simpa using (hp k y).sub (hq k y)

/-- **A product of two families with holomorphic coefficients has holomorphic coefficients**: a
coefficient of the product is a finite sum of products of coefficients. -/
theorem HoloCoeffs.mul (hf : IsLocalHomeomorph f) (hp : HoloCoeffs f p) (hq : HoloCoeffs f q) :
    HoloCoeffs f fun y => p y * q y := by
  intro k y
  have hrw : (fun y : Y => (p y * q y).coeff k)
      = fun y : Y => ∑ x ∈ Finset.antidiagonal k, (p y).coeff x.1 * (q y).coeff x.2 :=
    funext fun y' => coeff_mul _ _ _
  rw [hrw]
  exact isHoloAt_finset_sum hf _ fun x _ => (hp x.1 y).mul (hq x.2 y)

/-- A finite sum of families with holomorphic coefficients has holomorphic coefficients. -/
theorem holoCoeffs_finset_sum (hf : IsLocalHomeomorph f) {ι : Type*} (s : Finset ι)
    {P : ι → Y → ℂ[X]} (h : ∀ i ∈ s, HoloCoeffs f (P i)) :
    HoloCoeffs f fun y => ∑ i ∈ s, P i y := by
  intro k y
  have hrw : (fun y : Y => (∑ i ∈ s, P i y).coeff k)
      = fun y : Y => ∑ i ∈ s, (P i y).coeff k :=
    funext fun y' => finset_sum_coeff s (fun i => P i y') k
  rw [hrw]
  exact isHoloAt_finset_sum hf _ fun i hi => h i hi k y

/-- A finite product of families with holomorphic coefficients has holomorphic coefficients. -/
theorem holoCoeffs_finset_prod (hf : IsLocalHomeomorph f) {ι : Type*} (s : Finset ι)
    {P : ι → Y → ℂ[X]} (h : ∀ i ∈ s, HoloCoeffs f (P i)) :
    HoloCoeffs f fun y => ∏ i ∈ s, P i y := by
  have hone : HoloCoeffs f (1 : Y → ℂ[X]) := holoCoeffs_const hf 1
  have hmul : ∀ a b : Y → ℂ[X], HoloCoeffs f a → HoloCoeffs f b → HoloCoeffs f (a * b) :=
    fun a b ha hb => ha.mul hf hb
  have hprod : HoloCoeffs f (∏ i ∈ s, P i) :=
    Finset.prod_induction P (HoloCoeffs f) hmul hone h
  have heq : (fun y : Y => ∏ i ∈ s, P i y) = ∏ i ∈ s, P i :=
    funext fun y => (Finset.prod_apply y s P).symm
  rw [heq]
  exact hprod

end Rigidity.RET

end
