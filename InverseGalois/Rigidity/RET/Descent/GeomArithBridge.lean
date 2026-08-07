/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.InertiaTransport
import InverseGalois.Rigidity.RET.Descent.FunctionFieldTower
import InverseGalois.Rigidity.RET.Descent.GeomAKLB
import InverseGalois.Rigidity.RET.Descent.ArithAKLB

/-!
# From the geometric integral model to the arithmetic one

The descent produces two integral models of the same cover, over two different bases:

* the **arithmetic** model `ℚ[X] ⊆ A = integralClosure ℚ[X] Ω` of a `ℚ(T)`-form `Ω`
  (`ArithAKLB`), carrying the action of `Gal(Ω / ℚ(T))`;
* the **geometric** model `ℚ̄[X] ⊆ B = integralClosure ℚ̄[X] Ω̄` of the compositum
  `Ω̄ = Ω · ℚ̄(T)` (`GeomAKLB`), carrying the action of `Gal(Ω̄ / ℚ̄(T))`.

The branch cycles are produced on the geometric side, where the constant field is algebraically
closed and the topology lives; they are consumed on the arithmetic side, where Fried's
branch-cycle formula and the descent to `ℚ` live.  This file builds the bridge between the two:
the coefficient-extension square

```
    ℚ[X]  ──────→  A = integralClosure ℚ[X] Ω
      │                        │
      │ coefficients           │ bridge
      ↓                        ↓
    ℚ̄[X]  ──────→  B = integralClosure ℚ̄[X] Ω̄
```

commutes, so an element of `A` is integral over `ℚ̄[X]` after transport into `Ω̄`, giving a ring map
`bridge : A →+* B`; the Galois actions are intertwined along it by restriction of automorphisms;
and therefore inertia upstairs contracts to inertia downstairs (`Rigidity.RET.mem_inertia_comap`).
Finally a geometric place `X - t` at a *rational* point `t = q` contracts to the arithmetic place
`X - q`, so the contracted prime lies over the place the arithmetic side expects.

The whole file is stated for abstract `Ω`, `Ω̄` linked only by an `Algebra Ω Ω̄` instance and the
`Prop` compatibility `algebraMap_comm` — no scalar-tower instance is assumed between the two
function fields, which keeps the caller free of the `RatFunc` instance diamonds.

## Main results

* `algebraMap_poly_comm` — the coefficient-extension square commutes.
* `bridge` — the induced ring map `integralClosure ℚ[X] Ω →+* integralClosure ℚ̄[X] Ω̄`.
* `bridge_smul` — the two Galois actions are intertwined along `bridge` by `restrictHom`.
* `mem_inertia_bridge` — geometric inertia contracts to arithmetic inertia.
* `comap_placeP_rat` — the geometric place at a rational point contracts to the arithmetic place.
* `liesOver_comap_bridge` — the contracted prime lies over the arithmetic place `X - q`.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Descent

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

attribute [local instance] GeomAKLB.instMSA ArithAKLB.instMSA

/-- The coefficient-extension map `ℚ[X] → ℚ̄[X]`. -/
abbrev coeffExt : ℚ[X] →+* (AlgebraicClosure ℚ)[X] :=
  Polynomial.mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))

section Bridge

variable (Ω Ωbar : Type) [Field Ω] [Field Ωbar]
  [Algebra (RatFunc ℚ) Ω] [Algebra ℚ[X] Ω] [IsScalarTower ℚ[X] (RatFunc ℚ) Ω]
  [Algebra (RatFunc GeomAKLB.k) Ωbar] [Algebra (AlgebraicClosure ℚ)[X] Ωbar]
  [IsScalarTower (AlgebraicClosure ℚ)[X] (RatFunc GeomAKLB.k) Ωbar]
  [Algebra Ω Ωbar]

/-- The compatibility linking the two models: the two ways of mapping `ℚ(T)` into `Ω̄` — through
`ℚ̄(T)` and through `Ω` — agree.  This is the only link assumed between the arithmetic and the
geometric side; stating it as an equation of `algebraMap`s rather than as a scalar-tower instance
avoids the `RatFunc` instance diamonds. -/
def IsCompositumOver : Prop :=
  ∀ q : RatFunc ℚ,
    algebraMap (RatFunc GeomAKLB.k) Ωbar
        (algebraMap (RatFunc ℚ) (RatFunc GeomAKLB.k) q)
      = algebraMap Ω Ωbar (algebraMap (RatFunc ℚ) Ω q)

variable {Ω Ωbar}

/-- **The coefficient-extension square commutes.**

Extending the coefficients of `p ∈ ℚ[X]` to `ℚ̄` and mapping into `Ω̄` is the same as mapping `p`
into `Ω` and then into `Ω̄`.  Both sides factor through the function fields, where the statement is
the assumed compatibility together with `algebraMap_ratFunc_closure_comp`. -/
theorem algebraMap_poly_comm (hc : IsCompositumOver Ω Ωbar) (p : ℚ[X]) :
    algebraMap (AlgebraicClosure ℚ)[X] Ωbar (coeffExt p)
      = algebraMap Ω Ωbar (algebraMap ℚ[X] Ω p) := by
  rw [IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ)[X] (RatFunc GeomAKLB.k) Ωbar,
    IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) Ω]
  rw [show algebraMap (AlgebraicClosure ℚ)[X] (RatFunc GeomAKLB.k) (coeffExt p)
      = algebraMap (RatFunc ℚ) (RatFunc GeomAKLB.k) (algebraMap ℚ[X] (RatFunc ℚ) p) from
    (algebraMap_ratFunc_closure_comp p).symm]
  exact hc _

/-- The ring-hom form of `algebraMap_poly_comm`, as `IsIntegral.map_of_comp_eq` wants it. -/
theorem algebraMap_poly_comm' (hc : IsCompositumOver Ω Ωbar) :
    (algebraMap (AlgebraicClosure ℚ)[X] Ωbar).comp coeffExt
      = (algebraMap Ω Ωbar).comp (algebraMap ℚ[X] Ω) :=
  RingHom.ext fun p => algebraMap_poly_comm hc p

/-- An element of `Ω` integral over `ℚ[X]` becomes, in `Ω̄`, integral over `ℚ̄[X]`. -/
theorem isIntegral_algebraMap_of_isIntegral (hc : IsCompositumOver Ω Ωbar) {x : Ω}
    (hx : IsIntegral ℚ[X] x) :
    IsIntegral (AlgebraicClosure ℚ)[X] (algebraMap Ω Ωbar x) :=
  hx.map_of_comp_eq coeffExt (algebraMap Ω Ωbar) (algebraMap_poly_comm' hc)

/-- **The bridge**: the arithmetic integral model maps into the geometric one, by transporting
elements along `Ω → Ω̄`. -/
def bridge (hc : IsCompositumOver Ω Ωbar) :
    ArithAKLB.Aring Ω →+* GeomAKLB.Bring Ωbar where
  toFun x := ⟨algebraMap Ω Ωbar (x : Ω), isIntegral_algebraMap_of_isIntegral hc x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp] theorem coe_bridge (hc : IsCompositumOver Ω Ωbar) (x : ArithAKLB.Aring Ω) :
    ((bridge hc x : GeomAKLB.Bring Ωbar) : Ωbar) = algebraMap Ω Ωbar (x : Ω) := rfl

end Bridge

/-! ## Intertwining the two Galois actions -/

section Action

variable {Ω Ωbar : Type} [Field Ω] [Field Ωbar]
  [Algebra (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc ℚ) Ω] [IsGalois (RatFunc ℚ) Ω]
  [Algebra ℚ[X] Ω] [IsScalarTower ℚ[X] (RatFunc ℚ) Ω]
  [Algebra (RatFunc GeomAKLB.k) Ωbar] [FiniteDimensional (RatFunc GeomAKLB.k) Ωbar]
  [IsGalois (RatFunc GeomAKLB.k) Ωbar] [Algebra (AlgebraicClosure ℚ)[X] Ωbar]
  [IsScalarTower (AlgebraicClosure ℚ)[X] (RatFunc GeomAKLB.k) Ωbar]
  [Algebra Ω Ωbar]

omit [FiniteDimensional (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc GeomAKLB.k) Ωbar] in
/-- The group homomorphism along which the actions are intertwined: a geometric automorphism of
`Ω̄`, restricted to the arithmetic form `Ω`.  It is supplied by the caller (in practice by the
comparison isomorphism of the compositum), together with the requirement `hres` that it really is
"restrict to `Ω`". -/
theorem bridge_smul (hc : IsCompositumOver Ω Ωbar)
    (ρ : (Ωbar ≃ₐ[RatFunc GeomAKLB.k] Ωbar) →* (Ω ≃ₐ[RatFunc ℚ] Ω))
    (hres : ∀ (τ : Ωbar ≃ₐ[RatFunc GeomAKLB.k] Ωbar) (x : Ω),
      algebraMap Ω Ωbar (ρ τ x) = τ (algebraMap Ω Ωbar x))
    (τ : Ωbar ≃ₐ[RatFunc GeomAKLB.k] Ωbar) (x : ArithAKLB.Aring Ω) :
    bridge hc (ρ τ • x) = τ • bridge hc x := by
  apply Subtype.ext
  rw [coe_bridge, ArithAKLB.coe_smul_arith, GeomAKLB.coe_smul_geom, coe_bridge, hres]

omit [FiniteDimensional (RatFunc ℚ) Ω] [FiniteDimensional (RatFunc GeomAKLB.k) Ωbar] in
/-- **Geometric inertia contracts to arithmetic inertia.**

If `τ` acts trivially modulo a prime `Q` of the geometric model, then its restriction `ρ τ` acts
trivially modulo the contracted prime `Q ∩ A` of the arithmetic model. -/
theorem mem_inertia_bridge (hc : IsCompositumOver Ω Ωbar)
    (ρ : (Ωbar ≃ₐ[RatFunc GeomAKLB.k] Ωbar) →* (Ω ≃ₐ[RatFunc ℚ] Ω))
    (hres : ∀ (τ : Ωbar ≃ₐ[RatFunc GeomAKLB.k] Ωbar) (x : Ω),
      algebraMap Ω Ωbar (ρ τ x) = τ (algebraMap Ω Ωbar x))
    (Q : Ideal (GeomAKLB.Bring Ωbar)) {τ : Ωbar ≃ₐ[RatFunc GeomAKLB.k] Ωbar}
    (hτ : τ ∈ GeomAKLB.geomInertia Ωbar Q) :
    ρ τ ∈ (Q.comap (bridge hc)).inertia (Ω ≃ₐ[RatFunc ℚ] Ω) :=
  Rigidity.RET.mem_inertia_comap (bridge hc) ρ (bridge_smul hc ρ hres) Q hτ

end Action

/-! ## Rational places contract to rational places -/

/-- The geometric place `X - q̄` of `ℚ̄[X]` at a **rational** point contracts, along coefficient
extension, to the arithmetic place `X - q` of `ℚ[X]`.

One inclusion is `coeffExt (X - C q) = X - C q̄`.  For the other, the contraction is a proper ideal
(coefficient extension is injective and `1 ∉ X - C q̄`), and `X - C q` generates a maximal ideal, so
the inclusion is an equality. -/
theorem comap_placeP_rat (q : ℚ) :
    (GeomAKLB.placeP (algebraMap ℚ GeomAKLB.k q)).comap coeffExt
      = Ideal.span {(X - C q : ℚ[X])} := by
  have hle : Ideal.span {(X - C q : ℚ[X])}
      ≤ (GeomAKLB.placeP (algebraMap ℚ GeomAKLB.k q)).comap coeffExt := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    have : coeffExt (X - C q) = (X - C (algebraMap ℚ GeomAKLB.k q) : GeomAKLB.k[X]) := by
      simp [coeffExt]
    rw [this]
    exact Ideal.mem_span_singleton_self _
  have hmax : (Ideal.span {(X - C q : ℚ[X])}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C _)
  have hne : (GeomAKLB.placeP (algebraMap ℚ GeomAKLB.k q)).comap coeffExt ≠ ⊤ := by
    intro htop
    have h1 : (1 : ℚ[X]) ∈ (GeomAKLB.placeP (algebraMap ℚ GeomAKLB.k q)).comap coeffExt := by
      rw [htop]; trivial
    rw [Ideal.mem_comap, map_one] at h1
    exact (GeomAKLB.placeP_max (algebraMap ℚ GeomAKLB.k q)).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  exact ((hmax.eq_of_le hne hle)).symm

section LiesOver

variable {Ω Ωbar : Type} [Field Ω] [Field Ωbar]
  [Algebra (RatFunc ℚ) Ω] [Algebra ℚ[X] Ω] [IsScalarTower ℚ[X] (RatFunc ℚ) Ω]
  [Algebra (RatFunc GeomAKLB.k) Ωbar] [Algebra (AlgebraicClosure ℚ)[X] Ωbar]
  [IsScalarTower (AlgebraicClosure ℚ)[X] (RatFunc GeomAKLB.k) Ωbar]
  [Algebra Ω Ωbar]

/-- The bridge is a map of `ℚ[X]`-algebras: extending coefficients and then including into the
geometric model is the same as including into the arithmetic model and bridging. -/
theorem bridge_algebraMap (hc : IsCompositumOver Ω Ωbar) (p : ℚ[X]) :
    bridge hc (algebraMap ℚ[X] (ArithAKLB.Aring Ω) p)
      = algebraMap (AlgebraicClosure ℚ)[X] (GeomAKLB.Bring Ωbar) (coeffExt p) := by
  apply Subtype.ext
  rw [coe_bridge]
  rw [show ((algebraMap ℚ[X] (ArithAKLB.Aring Ω) p : ArithAKLB.Aring Ω) : Ω)
      = algebraMap ℚ[X] Ω p from
    (IsScalarTower.algebraMap_apply ℚ[X] (ArithAKLB.Aring Ω) Ω p).symm]
  rw [show ((algebraMap (AlgebraicClosure ℚ)[X] (GeomAKLB.Bring Ωbar) (coeffExt p) :
        GeomAKLB.Bring Ωbar) : Ωbar)
      = algebraMap (AlgebraicClosure ℚ)[X] Ωbar (coeffExt p) from
    (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ)[X] (GeomAKLB.Bring Ωbar) Ωbar
      (coeffExt p)).symm]
  exact (algebraMap_poly_comm hc p).symm

/-- **A geometric prime over a rational point contracts to an arithmetic prime over the same
point.**  This is what makes the branch points of the descended model rational places of `ℚ[X]`. -/
theorem liesOver_comap_bridge (hc : IsCompositumOver Ω Ωbar) (q : ℚ)
    (Q : Ideal (GeomAKLB.Bring Ωbar))
    [Q.LiesOver (GeomAKLB.placeP (algebraMap ℚ GeomAKLB.k q))] :
    (Q.comap (bridge hc)).LiesOver (Ideal.span {(X - C q : ℚ[X])}) := by
  constructor
  have hover : GeomAKLB.placeP (algebraMap ℚ GeomAKLB.k q)
      = Q.comap (algebraMap (AlgebraicClosure ℚ)[X] (GeomAKLB.Bring Ωbar)) :=
    Ideal.LiesOver.over
  have hcomp : (Q.comap (bridge hc)).comap (algebraMap ℚ[X] (ArithAKLB.Aring Ω))
      = (Q.comap (algebraMap (AlgebraicClosure ℚ)[X] (GeomAKLB.Bring Ωbar))).comap coeffExt := by
    rw [Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    exact RingHom.ext fun p => bridge_algebraMap hc p
  rw [Ideal.under_def, hcomp, ← hover, comap_placeP_rat]

end LiesOver

end Rigidity.RET.Descent
