/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Rigidity.RET.RatFuncSubst
import InverseGalois.Rigidity.RET.RatFuncGen

/-!
# The line as an extension of itself along a substitution

A transcendental rational function `g ∈ K(u)` presents the line as a finite extension of itself:
the subfield `K(g)` is again a rational function field, and `K(u)` is finite over it as soon as `u`
satisfies an equation with coefficients in `K(g)`.  The substitution `T ↦ g` is a `K`-algebra
embedding `φ : K(T) → K(u)`, and the covering field is `K(u)` with the base acting through `φ`.

Since the two fields are the same object, that action has to be installed on a type synonym,
`LineSubst φ`, exactly as the coordinate changes of `RET.Twist` are.  The difference is that `φ` is
now an embedding rather than an automorphism, so the extension is genuinely of finite degree
greater than one, and the type synonym carries an honest cover of the line.

This is how a cover of *genus zero* is written down: its function field is again a rational
function field `K(u)`, and the covering map is a rational function of the parameter.  The dihedral
covers `T = u^n + u^{-n}` are the first example.

## Main definitions

* `Rigidity.RET.LineSubst` — the line with the base acting through the substitution `φ`.
* `Rigidity.RET.LineSubst.param` — the parameter `u` of the covering line.

## Main results

* `Rigidity.RET.LineSubst.adjoin_param_eq_top` — the covering line is generated over the base by
  its parameter.
* `Rigidity.RET.LineSubst.finiteDimensional` — an integral parameter makes it a finite extension,
  and `Rigidity.RET.LineSubst.finrank_le_of_monic` bounds the degree by that of any monic equation
  the parameter satisfies.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

variable {K : Type*} [Field K]

/-- **The line, viewed as an extension of the line through a substitution.**  The field is `K(u)`
again, but a scalar `f : K(T)` acts on it as the rational function `φ f` of the parameter. -/
def LineSubst (_φ : RatFunc K →ₐ[K] RatFunc K) : Type _ := RatFunc K

namespace LineSubst

variable (φ : RatFunc K →ₐ[K] RatFunc K)

instance instField : Field (LineSubst φ) := inferInstanceAs (Field (RatFunc K))

instance instAlgebra : Algebra (RatFunc K) (LineSubst φ) :=
  (φ : RatFunc K →+* RatFunc K).toAlgebra

instance (priority := high) instSMul : SMul (RatFunc K) (LineSubst φ) := Algebra.toSMul

instance (priority := high) instModule : Module (RatFunc K) (LineSubst φ) := Algebra.toModule

/-- The integral model of the substituted line is the coordinate ring of the base, acting through
the substitution. -/
instance instAlgebraPoly : Algebra (Polynomial K) (LineSubst φ) :=
  ((algebraMap (RatFunc K) (LineSubst φ)).comp
    (algebraMap (Polynomial K) (RatFunc K))).toAlgebra

instance instTower : IsScalarTower (Polynomial K) (RatFunc K) (LineSubst φ) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The rational function underlying an element of the substituted line. -/
def toLine (x : LineSubst φ) : RatFunc K := x

/-- An element of the substituted line, from a rational function of the parameter. -/
def ofLine (x : RatFunc K) : LineSubst φ := x

variable {φ}

@[simp] theorem toLine_ofLine (x : RatFunc K) : toLine φ (ofLine φ x) = x := rfl

@[simp] theorem ofLine_toLine (x : LineSubst φ) : ofLine φ (toLine φ x) = x := rfl

theorem toLine_injective : Function.Injective (toLine φ) := fun _ _ h => h

@[simp] theorem toLine_add (x y : LineSubst φ) :
    toLine φ (x + y) = toLine φ x + toLine φ y := rfl

@[simp] theorem toLine_mul (x y : LineSubst φ) :
    toLine φ (x * y) = toLine φ x * toLine φ y := rfl

@[simp] theorem toLine_neg (x : LineSubst φ) : toLine φ (-x) = -toLine φ x := rfl

@[simp] theorem toLine_sub (x y : LineSubst φ) :
    toLine φ (x - y) = toLine φ x - toLine φ y := rfl

@[simp] theorem toLine_one : toLine φ 1 = 1 := rfl

@[simp] theorem toLine_zero : toLine φ 0 = 0 := rfl

@[simp] theorem toLine_pow (x : LineSubst φ) (m : ℕ) :
    toLine φ (x ^ m) = toLine φ x ^ m := rfl

@[simp] theorem toLine_inv (x : LineSubst φ) : toLine φ x⁻¹ = (toLine φ x)⁻¹ := rfl

/-- Scalars act on the substituted line through `φ`. -/
@[simp] theorem toLine_algebraMap (f : RatFunc K) :
    toLine φ (algebraMap (RatFunc K) (LineSubst φ) f) = φ f := rfl

/-- The integral model acts through `φ` as well. -/
@[simp] theorem toLine_algebraMap_poly (f : Polynomial K) :
    toLine φ (algebraMap (Polynomial K) (LineSubst φ) f)
      = φ (algebraMap (Polynomial K) (RatFunc K) f) := rfl

variable (φ)

/-- **The parameter `u` of the covering line.** -/
def param : LineSubst φ := ofLine φ (RatFunc.X : RatFunc K)

@[simp] theorem toLine_param : toLine φ (param φ) = (RatFunc.X : RatFunc K) := rfl

/-! ### Generation by the parameter -/

/-- **The covering line is generated over the base by its parameter.**  The base contributes the
constants, since the substitution fixes them, and the parameter is the remaining generator of a
rational function field. -/
theorem adjoin_param_eq_top :
    IntermediateField.adjoin (RatFunc K) {param φ} = ⊤ := by
  have hC : ∀ c : K, ofLine φ (algebraMap K (RatFunc K) c)
      ∈ IntermediateField.adjoin (RatFunc K) {param φ} := by
    intro c
    have hc : ofLine φ (algebraMap K (RatFunc K) c)
        = algebraMap (RatFunc K) (LineSubst φ) (algebraMap K (RatFunc K) c) :=
      (congrArg (ofLine φ) (φ.commutes c)).symm
    rw [hc]
    exact IntermediateField.algebraMap_mem _ _
  have hX : param φ ∈ IntermediateField.adjoin (RatFunc K) {param φ} :=
    IntermediateField.subset_adjoin _ _ rfl
  exact @ratFunc_intermediateField_eq_top K _ (RatFunc K) _ (instAlgebra φ) _ hC hX

/-! ### Finiteness -/

/-- **An integral parameter makes the substituted line a finite extension of the base.** -/
theorem finiteDimensional (h : IsIntegral (RatFunc K) (param φ)) :
    FiniteDimensional (RatFunc K) (LineSubst φ) := by
  haveI : FiniteDimensional (RatFunc K) ↥(IntermediateField.adjoin (RatFunc K) {param φ}) :=
    IntermediateField.adjoin.finiteDimensional h
  have hEq := adjoin_param_eq_top φ
  rw [hEq] at this
  exact (IntermediateField.topEquiv (F := RatFunc K)
    (E := LineSubst φ)).toLinearEquiv.finiteDimensional

/-- **The degree of the substituted line over the base is at most the degree of any monic equation
its parameter satisfies.** -/
theorem finrank_le_of_monic {p : Polynomial (RatFunc K)} (hp : p.Monic)
    (hroot : Polynomial.aeval (param φ) p = 0) :
    Module.finrank (RatFunc K) (LineSubst φ) ≤ p.natDegree := by
  have hint : IsIntegral (RatFunc K) (param φ) := ⟨p, hp, hroot⟩
  haveI : FiniteDimensional (RatFunc K) ↥(IntermediateField.adjoin (RatFunc K) {param φ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have h1 : Module.finrank (RatFunc K) ↥(IntermediateField.adjoin (RatFunc K) {param φ})
      = (minpoly (RatFunc K) (param φ)).natDegree := IntermediateField.adjoin.finrank hint
  have h2 : (minpoly (RatFunc K) (param φ)).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_natDegree
      (minpoly.degree_le_of_ne_zero (RatFunc K) (param φ) hp.ne_zero hroot)
  have h3 : Module.finrank (RatFunc K) (LineSubst φ)
      = Module.finrank (RatFunc K) ↥(IntermediateField.adjoin (RatFunc K) {param φ}) := by
    rw [adjoin_param_eq_top φ]
    exact (LinearEquiv.finrank_eq (IntermediateField.topEquiv (F := RatFunc K)
      (E := LineSubst φ)).toLinearEquiv).symm
  rw [h3, h1]
  exact h2

end LineSubst

end Rigidity.RET
