/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Substituting a rational function for the parameter

A group of automorphisms of the line is a group of substitutions `u ↦ g(u)` of one rational
function for the parameter.  This file builds those substitutions and the criterion under which
they are automorphisms of `K(u)`.

Substituting a rational function `g` for the parameter is the `K`-algebra map `K(u) → K(u)`
determined by `u ↦ g`.  It exists exactly when `g` is transcendental over `K` — that is, when `g`
is not a constant — because then `p ↦ p(g)` sends nonzero polynomials to nonzero rational
functions and so extends to the fraction field.  Two substitutions compose to the identity as soon
as each takes the other's substituted function back to the parameter, which is a single equation
between rational functions: a `K`-algebra map out of `K(u)` is determined by its value at the
parameter.

The intended use is invariant theory: a finite group of such substitutions acts faithfully on
`K(u)`, and Artin's theorem (`Rigidity.RET.isGeometricGaloisCover_of_invariant_subfield`) turns
that action into a Galois extension whose base field is the field of invariant functions.

## Main definitions and results

* `Rigidity.RET.ratFuncSubst` — the substitution `u ↦ g` as a `K`-algebra map `K(u) → K(u)`,
  for `g` transcendental over `K`.
* `Rigidity.RET.ratFuncSubst_X` — it does send the parameter to `g`.
* `Rigidity.RET.ratFunc_algHom_ext` — a `K`-algebra map out of `K(u)` is determined by its value
  at the parameter.
* `Rigidity.RET.ratFuncSubstEquiv` — two mutually inverse substitutions form an automorphism of
  `K(u)`.
* `Rigidity.RET.transcendental_const_mul_X`, `Rigidity.RET.transcendental_inv_X` — the two
  substitutions that generate a dihedral group of automorphisms, `u ↦ c·u` and `u ↦ u⁻¹`, are
  legitimate: their substituted functions are transcendental.
-/

open Polynomial

namespace Rigidity.RET

variable {K : Type*} [Field K]

/-- **A `K`-algebra map out of `K(u)` is determined by its value at the parameter.**

Every rational function is a quotient of two polynomials in the parameter, and both a polynomial
and a quotient are built from the parameter by the field operations, which the map preserves. -/
theorem ratFunc_algHom_ext {L : Type*} [Field L] [Algebra K L]
    {f g : RatFunc K →ₐ[K] L} (h : f RatFunc.X = g RatFunc.X) : f = g := by
  have hpoly : ∀ p : K[X], f (algebraMap K[X] (RatFunc K) p) = g (algebraMap K[X] (RatFunc K) p) := by
    have : f.comp (IsScalarTower.toAlgHom K K[X] (RatFunc K))
        = g.comp (IsScalarTower.toAlgHom K K[X] (RatFunc K)) := by
      refine Polynomial.algHom_ext ?_
      simpa [RatFunc.algebraMap_X] using h
    intro p
    exact congrArg (fun φ => φ p) this
  refine AlgHom.ext fun x => ?_
  induction x using RatFunc.induction_on with
  | _ p q hq => rw [map_div₀, map_div₀, hpoly, hpoly]

/-- **Substituting a transcendental rational function for the parameter.**

The `K`-algebra map `K(u) → K(u)` with `u ↦ g`.  A polynomial in `g` vanishes only if it is the
zero polynomial, `g` being transcendental, so `p/q ↦ p(g)/q(g)` is well defined. -/
noncomputable def ratFuncSubst (g : RatFunc K) (hg : Transcendental K g) :
    RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (Polynomial.aeval g)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp hg))

@[simp]
theorem ratFuncSubst_X (g : RatFunc K) (hg : Transcendental K g) :
    ratFuncSubst g hg RatFunc.X = g := by
  have h := RatFunc.liftAlgHom_apply_div (S := K) (L := RatFunc K)
    (φ := Polynomial.aeval g)
    (hφ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp hg)) Polynomial.X 1
  simpa [ratFuncSubst, RatFunc.algebraMap_X] using h

/-- **Two mutually inverse substitutions are an automorphism of `K(u)`.**

If substituting `g` carries `g'` back to the parameter and substituting `g'` carries `g` back to
the parameter, the two substitutions are inverse to each other: a `K`-algebra map out of `K(u)` is
determined by its value at the parameter, and each composite fixes the parameter. -/
noncomputable def ratFuncSubstEquiv {g g' : RatFunc K} (hg : Transcendental K g)
    (hg' : Transcendental K g') (h : ratFuncSubst g hg g' = RatFunc.X)
    (h' : ratFuncSubst g' hg' g = RatFunc.X) : RatFunc K ≃ₐ[K] RatFunc K :=
  AlgEquiv.ofAlgHom (ratFuncSubst g hg) (ratFuncSubst g' hg')
    (ratFunc_algHom_ext (by simp [h]))
    (ratFunc_algHom_ext (by simp [h']))

@[simp]
theorem ratFuncSubstEquiv_apply {g g' : RatFunc K} (hg : Transcendental K g)
    (hg' : Transcendental K g') (h : ratFuncSubst g hg g' = RatFunc.X)
    (h' : ratFuncSubst g' hg' g = RatFunc.X) (x : RatFunc K) :
    ratFuncSubstEquiv hg hg' h h' x = ratFuncSubst g hg x :=
  rfl

/-- **A substitution acts on a polynomial by evaluating it at the substituted function.**  Both
sides are `K`-algebra maps out of `K[u]`, and they agree at the parameter. -/
@[simp]
theorem ratFuncSubst_algebraMap (g : RatFunc K) (hg : Transcendental K g) (p : K[X]) :
    ratFuncSubst g hg (algebraMap K[X] (RatFunc K) p) = Polynomial.aeval g p := by
  have h : (ratFuncSubst g hg).comp (IsScalarTower.toAlgHom K K[X] (RatFunc K))
      = Polynomial.aeval g := by
    refine Polynomial.algHom_ext ?_
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun φ => φ p) h

/-! ## The scaling and inversion substitutions -/

/-- **A nonzero constant multiple of the parameter is transcendental**, so `u ↦ c·u` is a
substitution. -/
theorem transcendental_const_mul_X {c : K} (hc : c ≠ 0) :
    Transcendental K (algebraMap K (RatFunc K) c * RatFunc.X) := by
  have hdeg : (Polynomial.C c * Polynomial.X : K[X]).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X c hc
  have hlead : (Polynomial.C c * Polynomial.X : K[X]).leadingCoeff ∈ nonZeroDivisors K := by
    have : (Polynomial.C c * Polynomial.X : K[X]).leadingCoeff = c := by
      simp [Polynomial.leadingCoeff, hdeg]
    rw [this]
    exact mem_nonZeroDivisors_of_ne_zero hc
  have h := (RatFunc.transcendental_X (K := K)).aeval (Polynomial.C c * Polynomial.X)
    (by rw [hdeg]; exact one_ne_zero) hlead
  simpa using h

/-- **The inverse of the parameter is transcendental**, so `u ↦ u⁻¹` is a substitution. -/
theorem transcendental_inv_X : Transcendental K (RatFunc.X : RatFunc K)⁻¹ := fun h =>
  RatFunc.transcendental_X (K := K) (IsAlgebraic.inv_iff.mp h)

/-- Inversion is an involution of the parameter: substituting `u⁻¹` into `u⁻¹` gives `u`. -/
theorem ratFuncSubst_inv_inv :
    ratFuncSubst (RatFunc.X : RatFunc K)⁻¹ transcendental_inv_X (RatFunc.X)⁻¹ = RatFunc.X := by
  rw [map_inv₀, ratFuncSubst_X, inv_inv]

/-- **The inversion `u ↦ u⁻¹` of `K(u)`.**  It exchanges the point `0` of the line with the point
at infinity. -/
noncomputable def ratFuncInv : RatFunc K ≃ₐ[K] RatFunc K :=
  ratFuncSubstEquiv transcendental_inv_X transcendental_inv_X
    ratFuncSubst_inv_inv ratFuncSubst_inv_inv

@[simp]
theorem ratFuncInv_X : ratFuncInv (RatFunc.X : RatFunc K) = (RatFunc.X)⁻¹ := by
  rw [ratFuncInv, ratFuncSubstEquiv_apply, ratFuncSubst_X]

/-- Inversion sends a polynomial to its evaluation at `u⁻¹`. -/
theorem ratFuncInv_algebraMap (p : K[X]) :
    ratFuncInv (algebraMap K[X] (RatFunc K) p) = Polynomial.aeval (RatFunc.X : RatFunc K)⁻¹ p :=
  ratFuncSubst_algebraMap _ transcendental_inv_X p

end Rigidity.RET
