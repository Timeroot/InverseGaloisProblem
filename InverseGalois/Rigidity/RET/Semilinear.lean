/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.SubCover
import InverseGalois.Rigidity.RET.Twist

/-!
# Semilinear isomorphisms of covers, and where they move the branch points

A cover of the line is recorded by its function field together with the integral model `ℚ̄[X] ⊆ M`
(`RET/TamePi1.lean`), through which the points of the line are addressed.  An isomorphism of covers
in the strict sense is `ℚ̄(T)`-linear; but the isomorphisms the descent produces are only
*semilinear*: a `ℚ(T)`-automorphism of the arithmetic Galois closure moves the constants around by
an element of `Gal(ℚ̄/ℚ)`, so it commutes with the base only up to a coordinate change `φ` of
`ℚ̄(T)`.

Such a map is still perfectly good geometry.  As soon as the coordinate change preserves the
integral model — acting on it by a ring automorphism `ψ` of `ℚ̄[X]` (`PolyPreserving`) — it carries
places to places, inertia to inertia, and branch points to branch points, moved by `ψ`.  And for
the case at hand, a coordinate change coming from an automorphism of the *constants*
(`constSubst`), the branch points that get moved are the irrational ones: every **rational** point
stays where it is.  That is why the branch points of the rigidity method must be taken rational.

## Main definitions

* `Rigidity.RET.PolyPreserving` — the coordinate change restricts to `ψ` on the integral model.
* `Rigidity.RET.LineCover.SemiIso` — an isomorphism of covers, semilinear over a coordinate change.
* `Rigidity.RET.LineCover.SemiIso.bring` — the induced isomorphism of integral models.
* `Rigidity.RET.LineCover.SemiIso.deckEquiv` — the induced isomorphism of deck groups.
* `Rigidity.RET.LineCover.SemiIso.twist` — the same map, read in a new coordinate.
* `Rigidity.RET.constSubst` — the coordinate change induced by an automorphism of the constants.

## Main results

* `Rigidity.RET.LineCover.SemiIso.liesOver_map` — places go to places, over the moved point.
* `Rigidity.RET.LineCover.IsInertiaAt.semiIso` — inertia at `t` goes to inertia at the moved point.
* `Rigidity.RET.LineCover.IsUnramifiedOutside.semiIso'` — unramifiedness outside a set of points,
  with the set moved along.
* `Rigidity.RET.LineCover.IsUnramifiedOutside.semiIso` — unramifiedness outside a set of points
  stable under the move.
* `Rigidity.RET.constSubst_polyPreserving`, `Rigidity.RET.map_placeP_constSubst` — an automorphism
  of the constants preserves the integral model and moves the point `t` to `c t`.
* `Rigidity.RET.LineCover.IsUnramifiedOutside.semiIso_const` — a semilinear isomorphism over an
  automorphism of the constants preserves unramifiedness outside a set of **rational** points.
* `Rigidity.RET.LineCover.IsUnramifiedAtInfinity.semiIso_const` — and it preserves unramifiedness
  at the point at infinity.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral

/-! ## Coordinate changes preserving the integral model -/

/-- A coordinate change of the base **preserves the integral model**, acting on it as `ψ`: the
substitution `φ` carries a polynomial in `T` to the polynomial `ψ p`. -/
def PolyPreserving (φ : RatFunc k ≃+* RatFunc k) (ψ : Polynomial k ≃+* Polynomial k) : Prop :=
  ∀ p : Polynomial k,
    φ (algebraMap (Polynomial k) (RatFunc k) p) = algebraMap (Polynomial k) (RatFunc k) (ψ p)

variable {φ : RatFunc k ≃+* RatFunc k} {ψ : Polynomial k ≃+* Polynomial k}

/-- The inverse of a coordinate change preserving the integral model preserves it too. -/
theorem PolyPreserving.symm (h : PolyPreserving φ ψ) : PolyPreserving φ.symm ψ.symm := by
  intro p
  apply φ.injective
  rw [φ.apply_symm_apply, h (ψ.symm p), ψ.apply_symm_apply]

/-- Mapping an ideal along a ring isomorphism and back returns it. -/
theorem map_symm_map {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) (I : Ideal R) :
    Ideal.map f.symm (Ideal.map f I) = I := by
  ext p
  rw [← Ideal.symm_apply_mem_of_equiv_iff (f := f.symm),
    ← Ideal.symm_apply_mem_of_equiv_iff (f := f)]
  simp

/-- A coordinate change moving the point `t` to `t'` moves `t'` back to `t`. -/
theorem map_placeP_symm {ψ : Polynomial k ≃+* Polynomial k} {t t' : k}
    (hmove : Ideal.map ψ (placeP t) = placeP t') :
    Ideal.map ψ.symm (placeP t') = placeP t := by
  rw [← hmove]
  exact map_symm_map _ _

namespace LineCover

/-! ## Semilinear isomorphisms of covers -/

/-- An **isomorphism of covers, semilinear over the coordinate change `φ`**: a ring isomorphism of
the two function fields which intertwines the two actions of the base through `φ`. -/
structure SemiIso (L L' : LineCover) (φ : RatFunc k ≃+* RatFunc k) where
  /-- the underlying isomorphism of function fields. -/
  toRingEquiv : L.M ≃+* L'.M
  /-- scalars are carried along by the coordinate change. -/
  map_smul : ∀ (f : RatFunc k) (x : L.M), toRingEquiv (f • x) = φ f • toRingEquiv x

namespace SemiIso

variable {L L' : LineCover}

/-- Scalars are carried along by the coordinate change. -/
theorem map_algebraMap (e : SemiIso L L' φ) (f : RatFunc k) :
    e.toRingEquiv (algebraMap (RatFunc k) L.M f) = algebraMap (RatFunc k) L'.M (φ f) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, e.map_smul, map_one]

/-- The inverse of a semilinear isomorphism is semilinear over the inverse coordinate change. -/
def symm (e : SemiIso L L' φ) : SemiIso L' L φ.symm where
  toRingEquiv := e.toRingEquiv.symm
  map_smul f y := by
    apply e.toRingEquiv.injective
    rw [RingEquiv.apply_symm_apply, e.map_smul, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply]

@[simp] theorem symm_toRingEquiv (e : SemiIso L L' φ) :
    e.symm.toRingEquiv = e.toRingEquiv.symm := rfl

/-- The integral model is carried along by `ψ`. -/
theorem map_algebraMap_poly (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) (p : Polynomial k) :
    e.toRingEquiv (algebraMap (Polynomial k) L.M p) = algebraMap (Polynomial k) L'.M (ψ p) := by
  rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) L.M, e.map_algebraMap, h p,
    ← IsScalarTower.algebraMap_apply]

/-- The two integral models, compared as ring homomorphisms. -/
theorem algebraMap_comp (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) :
    (algebraMap (Polynomial k) L'.M).comp (ψ : Polynomial k →+* Polynomial k)
      = (e.toRingEquiv : L.M →+* L'.M).comp (algebraMap (Polynomial k) L.M) :=
  RingHom.ext fun p => (e.map_algebraMap_poly h p).symm

/-- **A semilinear isomorphism preserves integrality over the integral model**: the two integral
models differ by the ring automorphism `ψ` of `ℚ̄[X]`, which carries monic polynomials to monic
polynomials. -/
theorem isIntegral (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) {x : L.M}
    (hx : IsIntegral (Polynomial k) x) : IsIntegral (Polynomial k) (e.toRingEquiv x) :=
  IsIntegral.map_of_comp_eq (ψ : Polynomial k →+* Polynomial k)
    (e.toRingEquiv : L.M →+* L'.M) (e.algebraMap_comp h) hx

/-- **The integral models of two semilinearly isomorphic covers are isomorphic.** -/
def bring (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) : Bring L.M ≃+* Bring L'.M where
  toFun x := ⟨e.toRingEquiv (x : L.M), e.isIntegral h x.2⟩
  invFun y := ⟨e.symm.toRingEquiv (y : L'.M), e.symm.isIntegral h.symm y.2⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_bring (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) (x : Bring L.M) :
    ((e.bring h x : Bring L'.M) : L'.M) = e.toRingEquiv (x : L.M) := rfl

@[simp] theorem coe_bring_symm (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) (y : Bring L'.M) :
    (((e.bring h).symm y : Bring L.M) : L.M) = e.toRingEquiv.symm (y : L'.M) := rfl

/-- The isomorphism of integral models is the isomorphism of the inverse, inverted. -/
theorem bring_symm (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) :
    (e.bring h).symm = e.symm.bring h.symm := by
  ext y
  rfl

/-- The isomorphism of integral models is semilinear over `ψ`. -/
theorem bring_algebraMap (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) (p : Polynomial k) :
    e.bring h (algebraMap (Polynomial k) (Bring L.M) p)
      = algebraMap (Polynomial k) (Bring L'.M) (ψ p) :=
  Subtype.ext (by simpa using e.map_algebraMap_poly h p)

/-- The comparison of integral models, as a commuting square of ring homomorphisms. -/
theorem bring_comp (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) :
    ((e.bring h : Bring L.M ≃+* Bring L'.M) : Bring L.M →+* Bring L'.M).comp
        (algebraMap (Polynomial k) (Bring L.M))
      = (algebraMap (Polynomial k) (Bring L'.M)).comp (ψ : Polynomial k →+* Polynomial k) :=
  RingHom.ext fun p => e.bring_algebraMap h p

/-! ### Places -/

/-- **A semilinear isomorphism carries a place over `P` to a place over `ψ P`.** -/
theorem liesOver_map (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) (Q : Ideal (Bring L.M))
    (P : Ideal (Polynomial k)) [hQ : Q.LiesOver P] :
    (Ideal.map (e.bring h) Q).LiesOver (Ideal.map ψ P) := by
  constructor
  have hP : P = Ideal.comap (algebraMap (Polynomial k) (Bring L.M)) Q := hQ.over
  have hsym : ∀ p : Polynomial k, (e.bring h).symm (algebraMap (Polynomial k) (Bring L'.M) p)
      = algebraMap (Polynomial k) (Bring L.M) (ψ.symm p) := by
    intro p
    rw [bring_symm]
    exact e.symm.bring_algebraMap h.symm p
  show Ideal.map ψ P
      = Ideal.comap (algebraMap (Polynomial k) (Bring L'.M)) (Ideal.map (e.bring h) Q)
  ext p
  rw [← Ideal.symm_apply_mem_of_equiv_iff (f := ψ) (I := P), Ideal.mem_comap,
    ← Ideal.symm_apply_mem_of_equiv_iff (f := e.bring h) (I := Q), hsym p, hP, Ideal.mem_comap]

/-- A semilinear isomorphism carries a maximal place to a maximal place. -/
theorem isMaximal_map (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) (Q : Ideal (Bring L.M))
    [Q.IsMaximal] : (Ideal.map (e.bring h) Q).IsMaximal := by
  rw [← Ideal.comap_symm (e.bring h)]
  exact Ideal.comap_isMaximal_of_surjective _ (e.bring h).symm.surjective

/-! ### Deck transformations -/

/-- **A semilinear isomorphism conjugates deck transformations to deck transformations**: an
automorphism is linear over the base for one action exactly when its conjugate is for the other. -/
def conj (e : SemiIso L L' φ) (σ : L.deck) : L'.deck :=
  { (e.toRingEquiv.symm.trans σ.toRingEquiv).trans e.toRingEquiv with
    commutes' := fun f => by
      show e.toRingEquiv (σ (e.toRingEquiv.symm (algebraMap (RatFunc k) L'.M f))) = _
      rw [show e.toRingEquiv.symm (algebraMap (RatFunc k) L'.M f)
            = algebraMap (RatFunc k) L.M (φ.symm f) from e.symm.map_algebraMap f,
        σ.commutes, e.map_algebraMap, φ.apply_symm_apply] }

@[simp] theorem conj_apply (e : SemiIso L L' φ) (σ : L.deck) (x : L.M) :
    e.conj σ (e.toRingEquiv x) = e.toRingEquiv (σ x) := by
  show e.toRingEquiv (σ (e.toRingEquiv.symm (e.toRingEquiv x))) = _
  rw [e.toRingEquiv.symm_apply_apply]

theorem conj_apply' (e : SemiIso L L' φ) (σ : L.deck) (y : L'.M) :
    e.conj σ y = e.toRingEquiv (σ (e.toRingEquiv.symm y)) := rfl

@[simp] theorem conj_symm_conj (e : SemiIso L L' φ) (σ : L.deck) :
    e.symm.conj (e.conj σ) = σ := by
  ext x
  show e.toRingEquiv.symm (e.conj σ (e.toRingEquiv x)) = σ x
  rw [conj_apply, e.toRingEquiv.symm_apply_apply]

@[simp] theorem conj_conj_symm (e : SemiIso L L' φ) (τ : L'.deck) :
    e.conj (e.symm.conj τ) = τ := by
  ext y
  show e.toRingEquiv (e.symm.conj τ (e.toRingEquiv.symm y)) = τ y
  show e.toRingEquiv (e.toRingEquiv.symm (τ (e.toRingEquiv (e.toRingEquiv.symm y)))) = τ y
  rw [e.toRingEquiv.apply_symm_apply, e.toRingEquiv.apply_symm_apply]

theorem conj_mul (e : SemiIso L L' φ) (σ τ : L.deck) :
    e.conj (σ * τ) = e.conj σ * e.conj τ := by
  ext y
  show e.toRingEquiv (σ (τ (e.toRingEquiv.symm y))) = e.conj σ (e.conj τ y)
  rw [conj_apply']
  show _ = e.toRingEquiv (σ (e.toRingEquiv.symm (e.toRingEquiv (τ (e.toRingEquiv.symm y)))))
  rw [e.toRingEquiv.symm_apply_apply]

/-- **The deck groups of two semilinearly isomorphic covers agree.** -/
def deckEquiv (e : SemiIso L L' φ) : L.deck ≃* L'.deck where
  toFun := e.conj
  invFun := e.symm.conj
  left_inv := e.conj_symm_conj
  right_inv := e.conj_conj_symm
  map_mul' := e.conj_mul

@[simp] theorem deckEquiv_apply (e : SemiIso L L' φ) (σ : L.deck) : e.deckEquiv σ = e.conj σ := rfl

/-- The conjugate of a deck transformation acts on the integral model the way the original one
does. -/
theorem bring_smul (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) (σ : L.deck) (x : Bring L.M) :
    e.bring h (σ • x) = e.conj σ • e.bring h x := by
  apply Subtype.ext
  rw [coe_bring, coe_smul_geom, coe_smul_geom, coe_bring, conj_apply]

/-! ### Inertia -/

/-- **A semilinear isomorphism conjugates inertia to inertia.** -/
theorem mem_inertia_map (e : SemiIso L L' φ) (h : PolyPreserving φ ψ) {Q : Ideal (Bring L.M)}
    {σ : L.deck} (hσ : σ ∈ geomInertia L.M Q) :
    e.conj σ ∈ geomInertia L'.M (Ideal.map (e.bring h) Q) := by
  have hσ' : ∀ x : Bring L.M, σ • x - x ∈ Q := fun x => AddSubgroup.mem_inertia.mp hσ x
  refine AddSubgroup.mem_inertia.mpr fun y => ?_
  obtain ⟨x, rfl⟩ := (e.bring h).surjective y
  rw [← e.bring_smul h, ← map_sub]
  exact Ideal.mem_map_of_mem _ (hσ' x)

end SemiIso

/-- **Inertia at `t` goes to inertia at the moved point.** -/
theorem IsInertiaAt.semiIso {L L' : LineCover} (e : SemiIso L L' φ) (h : PolyPreserving φ ψ)
    {t t' : k} (hmove : Ideal.map ψ (placeP t) = placeP t')
    {σ : L.deck} (hσ : L.IsInertiaAt t σ) : L'.IsInertiaAt t' (e.conj σ) := by
  obtain ⟨Q, hQmax, hQover, hQin⟩ := hσ
  haveI := hQmax
  haveI := hQover
  refine ⟨Ideal.map (e.bring h) Q, e.isMaximal_map h Q, ?_, e.mem_inertia_map h hQin⟩
  have := e.liesOver_map h Q (placeP t)
  rwa [hmove] at this

/-- **Unramifiedness travels along a semilinear isomorphism**, with the branch locus moved along:
a point outside the new locus comes from a point outside the old one. -/
theorem IsUnramifiedOutside.semiIso' {L L' : LineCover} (e : SemiIso L L' φ)
    (h : PolyPreserving φ ψ) {move : k ≃ k}
    (hmove : ∀ t : k, Ideal.map ψ (placeP t) = placeP (move t))
    {S S' : Set k} (hS : ∀ t ∉ S', move.symm t ∉ S) (hL : L.IsUnramifiedOutside S) :
    L'.IsUnramifiedOutside S' := by
  intro t ht τ hτ
  have hmove' : Ideal.map ψ.symm (placeP t) = placeP (move.symm t) := by
    refine map_placeP_symm ?_
    have h1 := hmove (move.symm t)
    rwa [Equiv.apply_symm_apply] at h1
  have h2 : L.IsInertiaAt (move.symm t) (e.symm.conj τ) :=
    IsInertiaAt.semiIso e.symm h.symm hmove' hτ
  have h3 : e.symm.conj τ = 1 := hL _ (hS t ht) _ h2
  have h4 : e.conj (e.symm.conj τ) = e.conj 1 := by rw [h3]
  rw [SemiIso.conj_conj_symm] at h4
  rw [h4]
  exact e.deckEquiv.map_one

/-- **Unramifiedness travels along a semilinear isomorphism**, over a set of points stable under
the move. -/
theorem IsUnramifiedOutside.semiIso {L L' : LineCover} (e : SemiIso L L' φ)
    (h : PolyPreserving φ ψ) {move : k ≃ k}
    (hmove : ∀ t : k, Ideal.map ψ (placeP t) = placeP (move t))
    {S : Set k} (hS : ∀ t ∉ S, move.symm t ∉ S) (hL : L.IsUnramifiedOutside S) :
    L'.IsUnramifiedOutside S :=
  IsUnramifiedOutside.semiIso' e h hmove hS hL

/-! ### Changing the coordinate, and the point at infinity -/

namespace SemiIso

/-- **A semilinear isomorphism twists**: reading both covers in a new coordinate `φ₀` that commutes
with the semilinearity leaves the map semilinear over the same coordinate change. -/
def twist (e : SemiIso L L' φ) (φ₀ : RatFunc k ≃+* RatFunc k)
    (hcomm : ∀ f, φ (φ₀ f) = φ₀ (φ f)) : SemiIso (L.twist φ₀) (L'.twist φ₀) φ where
  toRingEquiv := (e.toRingEquiv : (L.twist φ₀).M ≃+* (L'.twist φ₀).M)
  map_smul f x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    show e.toRingEquiv (algebraMap (RatFunc k) L.M (φ₀ f)) = algebraMap (RatFunc k) L'.M (φ₀ (φ f))
    rw [e.map_algebraMap, hcomm]

end SemiIso

/-- **Unramifiedness at the point at infinity travels along a semilinear isomorphism** whose
coordinate change commutes with the inversion of the parameter and fixes the point `0` — the point
which the inversion exchanges with infinity. -/
theorem IsUnramifiedAtInfinity.semiIso {L L' : LineCover} (e : SemiIso L L' φ)
    (h : PolyPreserving φ ψ)
    (hcomm : ∀ f, φ (invSubst.toRingEquiv f) = invSubst.toRingEquiv (φ f))
    (hfix : Ideal.map ψ (placeP (0 : k)) = placeP 0)
    (hL : L.IsUnramifiedAtInfinity) : L'.IsUnramifiedAtInfinity := by
  intro τ hτ
  set e' := e.twist invSubst.toRingEquiv hcomm with he'
  have h1 : (L.twist invSubst.toRingEquiv).IsInertiaAt 0 (e'.symm.conj τ) :=
    IsInertiaAt.semiIso e'.symm h.symm (map_placeP_symm hfix) hτ
  have h2 := hL _ h1
  have h3 := congrArg e'.conj h2
  rw [SemiIso.conj_conj_symm] at h3
  rw [h3]
  exact e'.deckEquiv.map_one

end LineCover

/-! ## The coordinate change induced by an automorphism of the constants -/

/-- An automorphism of the constant field acts on the integral model of the line. -/
abbrev constSubstPoly (c : k ≃+* k) : Polynomial k ≃+* Polynomial k := Polynomial.mapEquiv c

/-- **The coordinate change induced by an automorphism of the constants**: it fixes the parameter
`T` and moves the coefficients by `c`. -/
def constSubst (c : k ≃+* k) : RatFunc k ≃+* RatFunc k :=
  IsFractionRing.ringEquivOfRingEquiv (A := Polynomial k) (B := Polynomial k)
    (K := RatFunc k) (L := RatFunc k) (constSubstPoly c)

/-- The coordinate change of the constants preserves the integral model, acting on it by `c` on
the coefficients. -/
theorem constSubst_polyPreserving (c : k ≃+* k) :
    PolyPreserving (constSubst c) (constSubstPoly c) := fun p =>
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (constSubstPoly c) p

/-- **An automorphism of the constants moves the point `t` to `c t`.** -/
theorem map_placeP_constSubst (c : k ≃+* k) (t : k) :
    Ideal.map (constSubstPoly c) (placeP t) = placeP (c t) := by
  have hXt : constSubstPoly c (X - C t) = X - C (c t) := by
    show Polynomial.map (c : k →+* k) (X - C t) = X - C (c t)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [placeP, placeP, Ideal.map_span, Set.image_singleton, hXt]

/-- **A ring map out of the field of rational functions is determined by its values on the
constants and at the parameter.** -/
theorem ratFunc_ringHom_ext {K L : Type*} [Field K] [Field L] {f g : RatFunc K →+* L}
    (hC : ∀ a : K, f (algebraMap K (RatFunc K) a) = g (algebraMap K (RatFunc K) a))
    (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  have hpoly : ∀ p : K[X],
      f (algebraMap K[X] (RatFunc K) p) = g (algebraMap K[X] (RatFunc K) p) := by
    have hcomp : f.comp (algebraMap K[X] (RatFunc K)) = g.comp (algebraMap K[X] (RatFunc K)) := by
      refine Polynomial.ringHom_ext ?_ ?_
      · intro a
        simpa [RatFunc.algebraMap_C] using hC a
      · simpa [RatFunc.algebraMap_X] using hX
    intro p
    exact congrArg (fun φ => φ p) hcomp
  refine RingHom.ext fun x => ?_
  induction x using RatFunc.induction_on with
  | _ p q hq => rw [map_div₀, map_div₀, hpoly, hpoly]

/-- The coordinate change of the constants acts on the constants by `c`. -/
theorem constSubst_algebraMap (c : k ≃+* k) (a : k) :
    constSubst c (algebraMap k (RatFunc k) a) = algebraMap k (RatFunc k) (c a) := by
  have h := constSubst_polyPreserving c (Polynomial.C a)
  simpa [RatFunc.algebraMap_C] using h

/-- The coordinate change of the constants fixes the parameter. -/
@[simp] theorem constSubst_X (c : k ≃+* k) : constSubst c (RatFunc.X : RatFunc k) = RatFunc.X := by
  have h := constSubst_polyPreserving c (Polynomial.X : Polynomial k)
  simpa [RatFunc.algebraMap_X] using h

/-- **An automorphism of the constants commutes with the inversion of the parameter**: it moves the
coefficients and leaves the parameter alone, so it does not disturb the point at infinity. -/
theorem constSubst_invSubst_comm (c : k ≃+* k) (f : RatFunc k) :
    constSubst c (invSubst f) = invSubst (constSubst c f) := by
  have key : (constSubst c : RatFunc k →+* RatFunc k).comp
        (invSubst.toRingEquiv : RatFunc k →+* RatFunc k)
      = (invSubst.toRingEquiv : RatFunc k →+* RatFunc k).comp
        (constSubst c : RatFunc k →+* RatFunc k) := by
    refine ratFunc_ringHom_ext ?_ ?_
    · intro a
      show constSubst c (invSubst (algebraMap k (RatFunc k) a))
        = invSubst (constSubst c (algebraMap k (RatFunc k) a))
      rw [invSubst.commutes, constSubst_algebraMap, invSubst.commutes]
    · show constSubst c (invSubst RatFunc.X) = invSubst (constSubst c RatFunc.X)
      rw [invSubst_X, constSubst_X, invSubst_X, map_inv₀, constSubst_X]
  exact congrArg (fun φ => φ f) key

/-- An automorphism of the constants fixes every rational point of the line. -/
theorem constSubst_fixes_rat (c : k ≃+* k) (q : ℚ) :
    c (algebraMap ℚ k q) = algebraMap ℚ k q := by
  rw [show algebraMap ℚ k q = (q : k) from eq_ratCast (algebraMap ℚ k) q, map_ratCast]

/-- **Unramifiedness outside a set of rational points survives a semilinear isomorphism over an
automorphism of the constants.**

This is the reason the rigidity method insists on *rational* branch points: the conjugates of a
cover by the arithmetic Galois group are branched over the conjugates of its branch points, and a
rational point is its own conjugate. -/
theorem LineCover.IsUnramifiedOutside.semiIso_const {L L' : LineCover} {c : k ≃+* k}
    (e : LineCover.SemiIso L L' (constSubst c)) {S : Set k}
    (hS : S ⊆ Set.range (algebraMap ℚ k)) (hL : L.IsUnramifiedOutside S) :
    L'.IsUnramifiedOutside S := by
  refine IsUnramifiedOutside.semiIso e (constSubst_polyPreserving c) (move := c.toEquiv)
    (fun t => map_placeP_constSubst c t) ?_ hL
  intro t ht hmem
  have hmem' : c.symm t ∈ S := hmem
  obtain ⟨q, hq⟩ := hS hmem'
  have hfix : c (algebraMap ℚ k q) = algebraMap ℚ k q := constSubst_fixes_rat c q
  rw [hq, c.apply_symm_apply] at hfix
  exact ht (by rw [hfix]; exact hmem')

/-- **Unramifiedness at the point at infinity survives a semilinear isomorphism over an
automorphism of the constants**: moving the coefficients around leaves the parameter, hence the
point at infinity, where it is. -/
theorem LineCover.IsUnramifiedAtInfinity.semiIso_const {L L' : LineCover} {c : k ≃+* k}
    (e : LineCover.SemiIso L L' (constSubst c)) (hL : L.IsUnramifiedAtInfinity) :
    L'.IsUnramifiedAtInfinity :=
  IsUnramifiedAtInfinity.semiIso e (constSubst_polyPreserving c)
    (fun f => constSubst_invSubst_comm c f) (by simpa using map_placeP_constSubst c 0) hL

/-! ## Automorphisms of the base fixing the parameter -/

/-- The image of a constant under any automorphism of `ℚ̄(T)` is algebraic over the constants: a
constant is algebraic over `ℚ`, and every ring map fixes `ℚ`. -/
theorem isAlgebraic_apply_const (φ : RatFunc k ≃+* RatFunc k) (a : k) :
    IsAlgebraic k (φ (algebraMap k (RatFunc k) a)) := by
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A := k) a
  refine ⟨p.map (algebraMap ℚ k), ?_, ?_⟩
  · simpa [Polynomial.map_eq_zero_iff (algebraMap ℚ k).injective] using hp0
  · set f : ℚ →+* RatFunc k := (algebraMap k (RatFunc k)).comp (algebraMap ℚ k) with hf
    have hφf : (φ : RatFunc k →+* RatFunc k).comp f = f := by
      refine RingHom.ext fun q => ?_
      show φ (f q) = f q
      rw [show f q = (q : RatFunc k) from eq_ratCast f q, map_ratCast]
    have hval : Polynomial.eval₂ f (algebraMap k (RatFunc k) a) p = 0 := by
      rw [hf, ← Polynomial.hom_eval₂, show Polynomial.eval₂ (algebraMap ℚ k) a p = 0 from hp,
        map_zero]
    have hcomp : (φ : RatFunc k →+* RatFunc k)
          (Polynomial.eval₂ f (algebraMap k (RatFunc k) a) p)
        = Polynomial.eval₂ ((φ : RatFunc k →+* RatFunc k).comp f)
            ((φ : RatFunc k →+* RatFunc k) (algebraMap k (RatFunc k) a)) p :=
      Polynomial.hom_eval₂ p f (φ : RatFunc k →+* RatFunc k) (algebraMap k (RatFunc k) a)
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hf, ← hφf,
      show φ (algebraMap k (RatFunc k) a)
        = (φ : RatFunc k →+* RatFunc k) (algebraMap k (RatFunc k) a) from rfl,
      ← hcomp, hval, map_zero]

/-- An element of an extension of an algebraically closed field which is algebraic over it is a
scalar. -/
theorem exists_const_of_isAlgebraic {L : Type*} [Field L] [Algebra k L] {x : L}
    (hx : IsAlgebraic k x) : ∃ a : k, algebraMap k L a = x := by
  have hi : IsIntegral k x := hx.isIntegral
  refine ⟨-((minpoly k x).coeff 0), ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic hi
  have hd : (minpoly k x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi)
  have h0 : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd, hq, Polynomial.C_1, one_mul, map_add,
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at h0
  rw [map_neg, ← h0]

/-- **An automorphism of `ℚ̄(T)` moves the constants among themselves.** -/
theorem exists_const_apply (φ : RatFunc k ≃+* RatFunc k) (a : k) :
    ∃ b : k, φ (algebraMap k (RatFunc k) a) = algebraMap k (RatFunc k) b :=
  (exists_const_of_isAlgebraic (isAlgebraic_apply_const φ a)).imp fun _ hb => hb.symm

/-- The automorphism of the constants underlying an automorphism of `ℚ̄(T)`. -/
noncomputable def constHom (φ : RatFunc k ≃+* RatFunc k) : k →+* k where
  toFun a := (exists_const_apply φ a).choose
  map_one' := (algebraMap k (RatFunc k)).injective (by
    rw [← (exists_const_apply φ 1).choose_spec, map_one, map_one])
  map_zero' := (algebraMap k (RatFunc k)).injective (by
    rw [← (exists_const_apply φ 0).choose_spec, map_zero, map_zero])
  map_mul' a b := (algebraMap k (RatFunc k)).injective (by
    rw [← (exists_const_apply φ (a * b)).choose_spec, map_mul, map_mul, map_mul,
      ← (exists_const_apply φ a).choose_spec, ← (exists_const_apply φ b).choose_spec])
  map_add' a b := (algebraMap k (RatFunc k)).injective (by
    rw [← (exists_const_apply φ (a + b)).choose_spec, map_add, map_add, map_add,
      ← (exists_const_apply φ a).choose_spec, ← (exists_const_apply φ b).choose_spec])

@[simp] theorem constHom_spec (φ : RatFunc k ≃+* RatFunc k) (a : k) :
    φ (algebraMap k (RatFunc k) a) = algebraMap k (RatFunc k) (constHom φ a) :=
  (exists_const_apply φ a).choose_spec

/-- **The automorphism of the constants underlying an automorphism of `ℚ̄(T)`.** -/
noncomputable def constEquiv (φ : RatFunc k ≃+* RatFunc k) : k ≃+* k where
  toFun := constHom φ
  invFun := constHom φ.symm
  left_inv a := (algebraMap k (RatFunc k)).injective (by
    rw [← constHom_spec, ← constHom_spec, φ.symm_apply_apply])
  right_inv a := (algebraMap k (RatFunc k)).injective (by
    rw [← constHom_spec, ← constHom_spec, φ.apply_symm_apply])
  map_mul' := map_mul _
  map_add' := map_add _

@[simp] theorem constEquiv_apply (φ : RatFunc k ≃+* RatFunc k) (a : k) :
    constEquiv φ a = constHom φ a := rfl

/-- **Every automorphism of `ℚ̄(T)` fixing the parameter is the coordinate change induced by an
automorphism of the constants.**  This is what makes the semilinearity of the descent's
isomorphisms harmless: the only coordinate changes it produces move the coefficients, and leave
every rational point of the line — and the point at infinity — where it is. -/
theorem eq_constSubst (φ : RatFunc k ≃+* RatFunc k) (hX : φ RatFunc.X = RatFunc.X) (f : RatFunc k) :
    φ f = constSubst (constEquiv φ) f := by
  have := ratFunc_ringHom_ext (f := (φ : RatFunc k →+* RatFunc k))
    (g := (constSubst (constEquiv φ) : RatFunc k →+* RatFunc k))
    (fun a => by rw [show ((φ : RatFunc k →+* RatFunc k)) (algebraMap k (RatFunc k) a)
        = φ (algebraMap k (RatFunc k) a) from rfl, constHom_spec,
      show ((constSubst (constEquiv φ) : RatFunc k →+* RatFunc k)) (algebraMap k (RatFunc k) a)
        = constSubst (constEquiv φ) (algebraMap k (RatFunc k) a) from rfl,
      constSubst_algebraMap, constEquiv_apply])
    (by
      show φ RatFunc.X = constSubst (constEquiv φ) RatFunc.X
      rw [hX, constSubst_X])
  exact congrArg (fun g => g f) this

end Rigidity.RET
