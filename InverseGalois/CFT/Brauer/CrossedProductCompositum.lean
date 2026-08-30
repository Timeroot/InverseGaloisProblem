/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductMul
import InverseGalois.CFT.Brauer.CrossedProductSimple
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.Group

/-!
# Base change of a crossed product to a field that is not intermediate

Let `E / K` be a finite Galois extension, let `M / K` be another extension, and let `N` be a field
containing both `E` and `M` and Galois over `M`.  When `E` and `M` are linearly disjoint over `K`
and generate `N`, restriction of automorphisms is an isomorphism `Gal(N/M) ≃ Gal(E/K)`; the
hypotheses below record exactly the data such an isomorphism provides, namely a multiplicative
bijection between the two Galois groups that is compatible with the embedding of `E` into `N`.

Transporting a multiplicative `2`-cocycle of `Gal(E/K)` with values in `Eˣ` along that bijection
gives a multiplicative `2`-cocycle of `Gal(N/M)` with values in `Nˣ`, and **extending scalars from
`K` to `M` carries the crossed product of `E / K` to the crossed product of `N / M`.**

The comparison map is the obvious one: the symbol `u σ` goes to the symbol attached to the
automorphism of `N` inducing `σ`, and the copy of `E` goes into the copy of `N`.  That is a
`K`-algebra homomorphism, so it extends to the base change; the base change of a central simple
algebra is simple, so the extension is injective; and the two Galois groups have the same order, so
the two sides have the same dimension over `M` and the extension is an isomorphism.

## Main definitions

* `InverseGalois.CFT.CrossedProduct.compositumCocycle`: the transported cocycle.
* `InverseGalois.CFT.CrossedProduct.compositumMap`: the comparison map between the two crossed
  products.

## Main results

* `InverseGalois.CFT.CrossedProduct.nonempty_algEquiv_compositum`: **extending scalars to `M`
  turns the crossed product of `E / K` into the crossed product of `N / M`.**
* `InverseGalois.CFT.CrossedProduct.baseChangeHom_mk_csa_compositum`: **base change on Brauer
  groups sends the class of a cocycle to the class of the transported cocycle.**

## Tags

crossed product, Brauer group, base change, compositum, linear disjointness, class field theory
-/

universe u

open groupCohomology Module

open scoped TensorProduct

namespace InverseGalois.CFT

namespace CrossedProduct

variable {K E M N : Type u} [Field K] [Field E] [Algebra K E]
variable [Field M] [Field N] [Algebra M N] [Algebra E N]
variable {e : Gal(N/M) ≃* Gal(E/K)} {f : Gal(E/K) × Gal(E/K) → Eˣ}

/-! ### The transported cocycle -/

variable (e f) in
/-- The cocycle of `Gal(N/M)` obtained from a cocycle of `Gal(E/K)` by transport along a
multiplicative bijection of the two Galois groups. -/
def compositumCocycle : Gal(N/M) × Gal(N/M) → Nˣ :=
  fun p => Units.map (algebraMap E N).toMonoidHom (f (e p.1, e p.2))

/-- The transported cocycle is the original one, read on the images of the two
automorphisms. -/
theorem compositumCocycle_apply (σ τ : Gal(N/M)) :
    compositumCocycle e f (σ, τ) = Units.map (algebraMap E N).toMonoidHom (f (e σ, e τ)) := rfl

/-- The transported cocycle, read on the automorphisms coming from `Gal(E/K)`. -/
theorem val_compositumCocycle_symm (σ τ : Gal(E/K)) :
    ((compositumCocycle e f (e.symm σ, e.symm τ) : Nˣ) : N)
      = algebraMap E N ((f (σ, τ) : Eˣ) : E) := by
  rw [compositumCocycle_apply, e.apply_symm_apply, e.apply_symm_apply]
  rfl

/-- The image of an automorphism acts on the copy of `E` inside `N` through the bijection. -/
theorem apply_symm_algebraMap
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x))
    (σ : Gal(E/K)) (b : E) : (e.symm σ) (algebraMap E N b) = algebraMap E N (σ b) := by
  rw [he, e.apply_symm_apply]

/-- The transported cocycle is equivariant for the two Galois actions. -/
theorem smul_units_map
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x))
    (σ : Gal(N/M)) (u : Eˣ) :
    σ • Units.map (algebraMap E N).toMonoidHom u
      = Units.map (algebraMap E N).toMonoidHom (e σ • u) :=
  Units.ext (he σ (u : E))

/-- The transport of a multiplicative `2`-cocycle is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_compositumCocycle
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x))
    (hf : IsMulCocycle₂ f) : IsMulCocycle₂ (compositumCocycle e f) := by
  intro σ τ ρ
  have hmap : ∀ u v : Eˣ, Units.map (algebraMap E N).toMonoidHom (u * v)
      = Units.map (algebraMap E N).toMonoidHom u * Units.map (algebraMap E N).toMonoidHom v :=
    fun u v => map_mul _ u v
  show Units.map (algebraMap E N).toMonoidHom (f (e (σ * τ), e ρ))
        * Units.map (algebraMap E N).toMonoidHom (f (e σ, e τ))
      = σ • Units.map (algebraMap E N).toMonoidHom (f (e τ, e ρ))
        * Units.map (algebraMap E N).toMonoidHom (f (e σ, e (τ * ρ)))
  rw [smul_units_map he, ← hmap, ← hmap, map_mul e, map_mul e]
  exact congrArg _ (hf (e σ) (e τ) (e ρ))

/-! ### The comparison map -/

variable (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ (compositumCocycle e f))

/-- The map from the crossed product of `E / K` to the crossed product of `N / M` sending the
symbol `u σ` to the symbol attached to the automorphism of `N` inducing `σ`. -/
noncomputable def compositumMap (x : CrossedProduct hf) : CrossedProduct hf' :=
  (Finsupp.mapDomain ⇑e.symm
    (Finsupp.mapRange ⇑(algebraMap E N) (map_zero _) (toFinsupp x)) : Gal(N/M) →₀ N)

/-- The coordinates of the image are the coordinates of the source, transported. -/
theorem toFinsupp_compositumMap (x : CrossedProduct hf) :
    toFinsupp (compositumMap hf hf' x)
      = Finsupp.mapDomain ⇑e.symm
        (Finsupp.mapRange ⇑(algebraMap E N) (map_zero _) (toFinsupp x)) := rfl

@[simp]
theorem compositumMap_single (σ : Gal(E/K)) (a : E) :
    compositumMap hf hf' (single hf σ a) = single hf' (e.symm σ) (algebraMap E N a) :=
  toFinsupp_injective <| by
    rw [toFinsupp_compositumMap, toFinsupp_single, toFinsupp_single, Finsupp.mapRange_single,
      Finsupp.mapDomain_single]

/-- The comparison map sends zero to zero. -/
theorem compositumMap_zero : compositumMap hf hf' 0 = 0 :=
  toFinsupp_injective <| by
    rw [toFinsupp_compositumMap, toFinsupp_zero, Finsupp.mapRange_zero, Finsupp.mapDomain_zero,
      toFinsupp_zero]

/-- The comparison map is additive. -/
theorem compositumMap_add (x y : CrossedProduct hf) :
    compositumMap hf hf' (x + y) = compositumMap hf hf' x + compositumMap hf hf' y :=
  toFinsupp_injective <| by
    rw [toFinsupp_compositumMap, toFinsupp_add, Finsupp.mapRange_add (map_add _),
      Finsupp.mapDomain_add, toFinsupp_add, toFinsupp_compositumMap, toFinsupp_compositumMap]

/-- The value of the transported cocycle at the unit, read inside `N`. -/
theorem val_inv_compositumCocycle_one :
    (((compositumCocycle e f (1, 1))⁻¹ : Nˣ) : N)
      = algebraMap E N ((((f (1, 1))⁻¹ : Eˣ)) : E) := by
  have h1 : compositumCocycle e f ((1 : Gal(N/M)), (1 : Gal(N/M)))
      = Units.map (algebraMap E N).toMonoidHom (f (1, 1)) := by
    rw [compositumCocycle_apply, map_one e]
  rw [h1, ← map_inv (Units.map (algebraMap E N).toMonoidHom) (f (1, 1))]
  rfl

/-- The comparison map sends the unit to the unit. -/
theorem compositumMap_one : compositumMap hf hf' 1 = 1 := by
  rw [one_def, one_def, compositumMap_single, map_one e.symm]
  exact single_congr (val_inv_compositumCocycle_one).symm

/-- The comparison map is compatible with the copies of `E` and of `N`. -/
theorem compositumMap_incl (c : E) :
    compositumMap hf hf' (incl hf c) = incl hf' (algebraMap E N c) := by
  rw [incl_eq_single, incl_eq_single, compositumMap_single, map_one e.symm]
  refine single_congr ?_
  rw [map_mul, val_inv_compositumCocycle_one]

/-- The comparison map is multiplicative. -/
theorem compositumMap_mul
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x))
    (x y : CrossedProduct hf) :
    compositumMap hf hf' (x * y) = compositumMap hf hf' x * compositumMap hf hf' y := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [zero_mul, compositumMap_zero, zero_mul]
  | add p q hp hq => rw [add_mul, compositumMap_add, hp, hq, compositumMap_add, add_mul]
  | single σ a =>
    induction y using CrossedProduct.induction_linear with
    | zero => rw [mul_zero, compositumMap_zero, mul_zero]
    | add p q hp hq => rw [mul_add, compositumMap_add, hp, hq, compositumMap_add, mul_add]
    | single τ b =>
      rw [single_mul_single, compositumMap_single, compositumMap_single, compositumMap_single,
        single_mul_single, map_mul e.symm, apply_symm_algebraMap he,
        val_compositumCocycle_symm]
      exact single_congr (by rw [map_mul (algebraMap E N), map_mul (algebraMap E N)])

/-- The comparison map, as a ring homomorphism. -/
noncomputable def compositumRingHom
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x)) :
    CrossedProduct hf →+* CrossedProduct hf' where
  toFun := compositumMap hf hf'
  map_one' := compositumMap_one hf hf'
  map_mul' := compositumMap_mul hf hf' he
  map_zero' := compositumMap_zero hf hf'
  map_add' := compositumMap_add hf hf'

/-! ### Base change -/

variable [Algebra K M] [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional M N]
  [IsGalois M N]

/-- The two Galois groups have the same order, so the two crossed products have the same dimension
over `M`. -/
theorem finrank_compositum_eq :
    finrank M (M ⊗[K] CrossedProduct hf) = finrank M (CrossedProduct hf') := by
  rw [Module.finrank_baseChange, finrank_eq, finrank_eq, Nat.card_congr e.toEquiv]

variable [Algebra K N] [IsScalarTower K M N] [IsScalarTower K E N]

/-- **Extending scalars to `M` turns the crossed product of `E / K` into the crossed product of
`N / M`.**  The comparison map is a `K`-algebra homomorphism, so it extends to the base change; the
base change of a central simple algebra is simple, so the extension is injective; and the two sides
have the same dimension over `M`. -/
theorem nonempty_algEquiv_compositum
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x)) :
    Nonempty ((M ⊗[K] CrossedProduct hf) ≃ₐ[M] CrossedProduct hf') := by
  letI : Algebra K (CrossedProduct hf') :=
    RingHom.toAlgebra' ((algebraMap M (CrossedProduct hf')).comp (algebraMap K M))
      fun k x => Algebra.commutes (algebraMap K M k) x
  haveI : IsScalarTower K M (CrossedProduct hf') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : CrossedProduct hf →ₐ[K] CrossedProduct hf' :=
    { compositumRingHom hf hf' he with
      commutes' := fun k => by
        show compositumMap hf hf' (incl hf (algebraMap K E k))
          = algebraMap M (CrossedProduct hf') (algebraMap K M k)
        rw [compositumMap_incl, algebraMap_eq, ← IsScalarTower.algebraMap_apply K E N,
          ← IsScalarTower.algebraMap_apply K M N] }
  let G : M ⊗[K] CrossedProduct hf →ₐ[M] CrossedProduct hf' :=
    Algebra.TensorProduct.lift (Algebra.ofId M (CrossedProduct hf')) g
      fun m x => Algebra.commutes m (g x)
  have hGinj : Function.Injective G := G.toRingHom.injective
  refine ⟨AlgEquiv.ofBijective G ⟨hGinj, ?_⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_compositum_eq hf hf') (f := G.toLinearMap)).1 hGinj

/-- **Base change on Brauer groups, computed on crossed products.**  Extending scalars to `M`
sends the class of a cocycle for `E / K` to the class of the transported cocycle for `N / M`. -/
theorem baseChangeHom_mk_csa_compositum
    (he : ∀ (σ : Gal(N/M)) (x : E), σ (algebraMap E N x) = algebraMap E N (e σ x)) :
    BrauerGroup.baseChangeHom M (⟦csa hf⟧ : BrauerGroup K) = (⟦csa hf'⟧ : BrauerGroup M) := by
  obtain ⟨eq⟩ := nonempty_algEquiv_compositum hf hf' he
  rw [BrauerGroup.baseChangeHom_mk]
  exact Quotient.sound (IsBrauerEquivalent.of_algEquiv eq)

end CrossedProduct

end InverseGalois.CFT
