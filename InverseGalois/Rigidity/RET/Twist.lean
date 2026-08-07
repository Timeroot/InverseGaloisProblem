/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Unramified
import InverseGalois.Rigidity.RET.RatFuncSubst

/-!
# Changing the coordinate on the line, and the point at infinity

A cover of the line is recorded by its function field together with the integral model `ℚ̄[X] ⊆ M`
(`RET/TamePi1.lean`); that model addresses the points of the *affine* line only.  A change of
coordinate on the line — an automorphism `φ` of `ℚ̄(T)` over `ℚ̄` — moves the points around, and
carries a cover to a cover with the branch points moved accordingly.  Since the inversion
`T ↦ T⁻¹` exchanges `0` and the point at infinity, this is also what gives access to infinity:
a cover is unramified at infinity exactly when its inversion twist is unramified at `0`.

The twist is realized by a type synonym `Twist φ M`, carrying the same field `M` with the base
`ℚ̄(T)` acting through `φ`.  Its deck group is canonically the deck group of `M`, since an
automorphism of `M` is `ℚ̄(T)`-linear for one action exactly when it is for the other.

## Main definitions

* `Rigidity.RET.Twist` — `M` with the base acting through `φ`.
* `Rigidity.RET.Twist.autEquiv` — the deck groups of `M` and of its twist agree.
* `Rigidity.RET.invSubst` — the inversion `T ↦ T⁻¹` of `ℚ̄(T)`.
* `Rigidity.RET.LineCover.twist` — the twisted cover.
* `Rigidity.RET.LineCover.IsUnramifiedAtInfinity` — no non-trivial inertia over the point at
  infinity.
-/

open Polynomial

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace Rigidity.RET

open GeomAKLB

/-! ## The inversion of the parameter -/

/-- Inversion is an involution of the parameter: substituting `T⁻¹` into `T⁻¹` gives `T`. -/
theorem ratFuncSubst_inv_inv {K : Type*} [Field K] :
    ratFuncSubst (RatFunc.X : RatFunc K)⁻¹ transcendental_inv_X (RatFunc.X)⁻¹ = RatFunc.X := by
  rw [map_inv₀, ratFuncSubst_X, inv_inv]

/-- **The inversion `T ↦ T⁻¹` of `ℚ̄(T)`.**  It exchanges the point `0` of the line with the point
at infinity. -/
def invSubst : RatFunc k ≃ₐ[k] RatFunc k :=
  ratFuncSubstEquiv transcendental_inv_X transcendental_inv_X ratFuncSubst_inv_inv
    ratFuncSubst_inv_inv

@[simp] theorem invSubst_X : invSubst (RatFunc.X : RatFunc k) = (RatFunc.X)⁻¹ := by
  rw [invSubst, ratFuncSubstEquiv_apply, ratFuncSubst_X]

/-! ## The twist of a field over `ℚ̄(T)` by an automorphism of the base -/

/-- The field `M`, viewed as an extension of `ℚ̄(T)` through the coordinate change `φ`: a scalar
`f : ℚ̄(T)` acts on `Twist φ M` the way `φ f` acts on `M`. -/
def Twist (_φ : RatFunc k ≃+* RatFunc k) (M : Type) : Type := M

namespace Twist

variable (φ : RatFunc k ≃+* RatFunc k) (M : Type) [Field M]

instance instField : Field (Twist φ M) := inferInstanceAs (Field M)

variable [Algebra (RatFunc k) M]

instance instAlgebraRatFunc : Algebra (RatFunc k) (Twist φ M) :=
  ((algebraMap (RatFunc k) M).comp (φ : RatFunc k →+* RatFunc k)).toAlgebra

instance instAlgebraPoly : Algebra (Polynomial k) (Twist φ M) :=
  ((algebraMap (RatFunc k) (Twist φ M)).comp
    (algebraMap (Polynomial k) (RatFunc k))).toAlgebra

instance instTower : IsScalarTower (Polynomial k) (RatFunc k) (Twist φ M) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {φ M}

/-- The element of `M` underlying an element of the twist. -/
def toBase (x : Twist φ M) : M := x

/-- Scalars act on the twist through `φ`. -/
theorem algebraMap_apply (f : RatFunc k) :
    toBase (algebraMap (RatFunc k) (Twist φ M) f) = algebraMap (RatFunc k) M (φ f) := rfl

/-- Scalar multiplication on the twist is scalar multiplication by the transformed scalar. -/
theorem toBase_smul (f : RatFunc k) (x : Twist φ M) :
    toBase (f • x) = φ f • toBase x := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

variable (φ M)

/-- The twist has the same rank over the base as the original: the coordinate change is a
bijection of the base with itself, and the underlying additive group is unchanged. -/
theorem rank_eq : Module.rank (RatFunc k) (Twist φ M) = Module.rank (RatFunc k) M :=
  rank_eq_of_equiv_equiv (R := RatFunc k) (R' := RatFunc k) (M := Twist φ M) (M₁ := M)
    (fun f => φ f) (AddEquiv.refl M) φ.bijective (fun f x => toBase_smul f x)

instance instFiniteDimensional [FiniteDimensional (RatFunc k) M] :
    FiniteDimensional (RatFunc k) (Twist φ M) :=
  Module.rank_lt_aleph0_iff.mp (by rw [rank_eq]; exact Module.rank_lt_aleph0 (RatFunc k) M)

instance instIsGalois [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M] :
    IsGalois (RatFunc k) (Twist φ M) :=
  IsGalois.of_equiv_equiv (F := RatFunc k) (E := M) (M := RatFunc k) (N := Twist φ M)
    (f := φ.symm) (g := RingEquiv.refl M)
    (by ext f; show (algebraMap (RatFunc k) M) (φ (φ.symm f)) = _; rw [φ.apply_symm_apply]; rfl)

variable {φ M}

/-- An isomorphism of two extensions of `ℚ̄(T)` is one of their twists: linearity for the two
actions of the base is the same condition, up to the bijection `φ` of the base with itself. -/
def congr {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra (RatFunc k) M₁] [Algebra (RatFunc k) M₂]
    (e : M₁ ≃ₐ[RatFunc k] M₂) : Twist φ M₁ ≃ₐ[RatFunc k] Twist φ M₂ :=
  { (e.toRingEquiv : Twist φ M₁ ≃+* Twist φ M₂) with
    commutes' := fun f => e.commutes (φ f) }

@[simp] theorem toBase_congr {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra (RatFunc k) M₁]
    [Algebra (RatFunc k) M₂] (e : M₁ ≃ₐ[RatFunc k] M₂) (x : Twist φ M₁) :
    toBase (congr e x) = e (toBase x) := rfl

/-- An automorphism of `M` over `ℚ̄(T)` is one of the twist. -/
def aut (σ : M ≃ₐ[RatFunc k] M) : Twist φ M ≃ₐ[RatFunc k] Twist φ M := congr σ

@[simp] theorem toBase_aut (σ : M ≃ₐ[RatFunc k] M) (x : Twist φ M) :
    toBase (aut σ x) = σ (toBase x) := rfl

/-- Every scalar of the twist is a scalar of `M`, through the inverse coordinate change. -/
theorem algebraMap_symm (f : RatFunc k) :
    (algebraMap (RatFunc k) (Twist φ M)) (φ.symm f) = algebraMap (RatFunc k) M f := by
  show algebraMap (RatFunc k) M (φ (φ.symm f)) = algebraMap (RatFunc k) M f
  rw [φ.apply_symm_apply]

/-- An automorphism of the twist over `ℚ̄(T)` is one of `M`. -/
def unaut (τ : Twist φ M ≃ₐ[RatFunc k] Twist φ M) : M ≃ₐ[RatFunc k] M :=
  { (τ.toRingEquiv : M ≃+* M) with
    commutes' := fun f => by
      rw [← algebraMap_symm (φ := φ) (M := M) f]
      exact τ.commutes _ }

/-- **The deck group of the twist is the deck group.** -/
def autEquiv : (M ≃ₐ[RatFunc k] M) ≃* (Twist φ M ≃ₐ[RatFunc k] Twist φ M) where
  toFun := aut
  invFun := unaut
  left_inv _ := AlgEquiv.ext fun _ => rfl
  right_inv _ := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp] theorem autEquiv_apply (σ : M ≃ₐ[RatFunc k] M) (x : Twist φ M) :
    toBase ((autEquiv σ) x) = σ (toBase x) := rfl

end Twist

namespace LineCover

/-- **The cover in the coordinate `φ`.**  The same field, with the base acting through the
coordinate change; the branch points are moved by `φ`. -/
def twist (L : LineCover) (φ : RatFunc k ≃+* RatFunc k) : LineCover where
  M := Twist φ L.M
  field := Twist.instField φ L.M
  alg := Twist.instAlgebraRatFunc φ L.M
  algPoly := Twist.instAlgebraPoly φ L.M
  tower := Twist.instTower φ L.M
  findim := Twist.instFiniteDimensional φ L.M
  isGalois := Twist.instIsGalois φ L.M

@[simp] theorem twist_M (L : LineCover) (φ : RatFunc k ≃+* RatFunc k) :
    (L.twist φ).M = Twist φ L.M := rfl

/-- **A cover is unramified at the point at infinity** if the inversion twist, in which infinity
has become the point `0`, has no non-trivial inertia there. -/
def IsUnramifiedAtInfinity (L : LineCover) : Prop :=
  ∀ σ : (L.twist invSubst.toRingEquiv).deck,
    (L.twist invSubst.toRingEquiv).IsInertiaAt 0 σ → σ = 1

end LineCover

end Rigidity.RET
