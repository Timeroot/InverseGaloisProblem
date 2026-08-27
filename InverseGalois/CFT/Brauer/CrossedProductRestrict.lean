/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductSimple
import InverseGalois.CFT.Brauer.BaseChangeCentralizer
import InverseGalois.CFT.Brauer.BaseChange

/-!
# Restricting a crossed product to an intermediate field

Let `E / K` be a finite Galois extension, let `f` be a multiplicative `2`-cocycle of `Gal(E/K)`
with values in `Eˣ`, and let `M` be an intermediate field.  Restricting `f` along the inclusion
`Gal(E/M) → Gal(E/K)` gives a cocycle for `E / M`, and the crossed product it defines sits inside
the crossed product of `E / K` as the span of the symbols `u σ` with `σ` fixing `M`.

That subalgebra is exactly the centralizer of the copy of `M`: the symbol `u g` conjugates the
copy of `E` by `g`, so an element commutes with `M` precisely when every `g` in its support fixes
`M` pointwise.  Extending scalars to `M` therefore turns the crossed product of `E / K` into the
algebra of matrices over the crossed product of `E / M`, and on Brauer groups the restriction map
sends the class of a cocycle to the class of its restriction.

## Main definitions

* `InverseGalois.CFT.CrossedProduct.restrictCocycle`: the cocycle for `E / M` obtained by
  restriction.
* `InverseGalois.CFT.CrossedProduct.restrictRingHom`: the embedding of the crossed product of
  `E / M` into the crossed product of `E / K`.

## Main results

* `InverseGalois.CFT.CrossedProduct.range_restrictMap`: the image of the smaller crossed product
  is the centralizer of the copy of `M`.
* `InverseGalois.CFT.CrossedProduct.nonempty_algEquiv_matrix_restrict`: extending scalars to `M`
  turns the crossed product of `E / K` into matrices over the crossed product of `E / M`.
* `InverseGalois.CFT.CrossedProduct.baseChangeHom_mk_csa`: **the restriction map on Brauer groups
  sends the class of a cocycle to the class of its restriction.**

## Tags

crossed product, Brauer group, restriction, centralizer, class field theory
-/

universe u

open groupCohomology Module

open scoped TensorProduct

namespace InverseGalois.CFT

namespace CrossedProduct

variable {K E : Type u} [Field K] [Field E] [Algebra K E]
variable (M : Type u) [Field M] [Algebra K M] [Algebra M E] [IsScalarTower K M E]
variable {f : Gal(E/K) × Gal(E/K) → Eˣ}

/-! ### Automorphisms fixing the intermediate field -/

/-- Two `M`-automorphisms of `E` inducing the same `K`-automorphism are equal. -/
theorem restrictScalars_injective :
    Function.Injective (fun σ : Gal(E/M) => σ.restrictScalars K) := fun _ _ h =>
  AlgEquiv.ext fun x => congrArg (fun e : Gal(E/K) => e x) h

/-- The identity of `Gal(E/M)` induces the identity of `Gal(E/K)`. -/
theorem restrictScalars_one : (1 : Gal(E/M)).restrictScalars K = 1 := rfl

/-- Restriction of scalars is multiplicative. -/
theorem restrictScalars_mul (σ τ : Gal(E/M)) :
    (σ * τ).restrictScalars K = σ.restrictScalars K * τ.restrictScalars K := rfl

/-- The two actions on the units of `E` agree. -/
theorem restrictScalars_smul_units (σ : Gal(E/M)) (u : Eˣ) :
    σ.restrictScalars K • u = σ • u := rfl

/-- Restriction of scalars does not change the underlying map. -/
theorem restrictScalars_apply (σ : Gal(E/M)) (x : E) : (σ.restrictScalars K) x = σ x := rfl

/-! ### The restricted cocycle -/

/-- The restriction of a multiplicative `2`-cocycle of `Gal(E/K)` to the subgroup `Gal(E/M)` of
the automorphisms fixing an intermediate field `M`. -/
def restrictCocycle (f : Gal(E/K) × Gal(E/K) → Eˣ) : Gal(E/M) × Gal(E/M) → Eˣ :=
  fun p => f (p.1.restrictScalars K, p.2.restrictScalars K)

/-- The restricted cocycle is the original one, read on the induced automorphisms. -/
@[simp] theorem restrictCocycle_apply (f : Gal(E/K) × Gal(E/K) → Eˣ) (σ τ : Gal(E/M)) :
    restrictCocycle M f (σ, τ) = f (σ.restrictScalars K, τ.restrictScalars K) := rfl

/-- The restriction of a multiplicative `2`-cocycle is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_restrictCocycle (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (restrictCocycle M f) := fun σ τ ρ => by
  have h := hf (σ.restrictScalars K) (τ.restrictScalars K) (ρ.restrictScalars K)
  rw [← restrictScalars_mul, ← restrictScalars_mul, restrictScalars_smul_units] at h
  exact h

/-! ### The embedding of the smaller crossed product -/

variable (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ (restrictCocycle M f))

/-- The map from the crossed product of `E / M` to the crossed product of `E / K` sending the
symbol `u σ` to the symbol attached to the induced `K`-automorphism. -/
noncomputable def restrictMap (x : CrossedProduct hf') : CrossedProduct hf :=
  (Finsupp.mapDomain (fun σ : Gal(E/M) => σ.restrictScalars K) (toFinsupp x) : Gal(E/K) →₀ E)

/-- The coordinates of the image are the coordinates of the source, transported. -/
theorem toFinsupp_restrictMap (x : CrossedProduct hf') :
    toFinsupp (restrictMap M hf hf' x)
      = Finsupp.mapDomain (fun σ : Gal(E/M) => σ.restrictScalars K) (toFinsupp x) := rfl

/-- The embedding sends a symbol to a symbol. -/
@[simp] theorem restrictMap_single (σ : Gal(E/M)) (a : E) :
    restrictMap M hf hf' (single hf' σ a) = single hf (σ.restrictScalars K) a :=
  toFinsupp_injective <| by
    rw [toFinsupp_restrictMap, toFinsupp_single, toFinsupp_single, Finsupp.mapDomain_single]

/-- The embedding sends zero to zero. -/
theorem restrictMap_zero : restrictMap M hf hf' 0 = 0 :=
  toFinsupp_injective <| by
    rw [toFinsupp_restrictMap, toFinsupp_zero, Finsupp.mapDomain_zero, toFinsupp_zero]

/-- The embedding is additive. -/
theorem restrictMap_add (x y : CrossedProduct hf') :
    restrictMap M hf hf' (x + y) = restrictMap M hf hf' x + restrictMap M hf hf' y :=
  toFinsupp_injective <| by
    rw [toFinsupp_restrictMap, toFinsupp_add, Finsupp.mapDomain_add, toFinsupp_add,
      toFinsupp_restrictMap, toFinsupp_restrictMap]

/-- The embedding sends the unit to the unit. -/
theorem restrictMap_one : restrictMap M hf hf' 1 = 1 := by
  rw [one_def, one_def, restrictMap_single, restrictCocycle_apply, restrictScalars_one]

/-- The embedding is multiplicative. -/
theorem restrictMap_mul (x y : CrossedProduct hf') :
    restrictMap M hf hf' (x * y) = restrictMap M hf hf' x * restrictMap M hf hf' y := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [zero_mul, restrictMap_zero, zero_mul]
  | add p q hp hq => rw [add_mul, restrictMap_add, hp, hq, restrictMap_add, add_mul]
  | single σ a =>
    induction y using CrossedProduct.induction_linear with
    | zero => rw [mul_zero, restrictMap_zero, mul_zero]
    | add p q hp hq => rw [mul_add, restrictMap_add, hp, hq, restrictMap_add, mul_add]
    | single τ b =>
      rw [single_mul_single, restrictMap_single, restrictMap_single, restrictMap_single,
        single_mul_single, restrictCocycle_apply, restrictScalars_mul, restrictScalars_apply]

/-- The embedding is injective. -/
theorem restrictMap_injective : Function.Injective (restrictMap M hf hf') := by
  intro x y h
  refine toFinsupp_injective ?_
  exact Finsupp.mapDomain_injective (restrictScalars_injective M) (congrArg toFinsupp h)

/-- The embedding is compatible with the copies of `E`. -/
theorem restrictMap_incl (c : E) : restrictMap M hf hf' (incl hf' c) = incl hf c := by
  rw [incl_eq_single, incl_eq_single, restrictMap_single, restrictCocycle_apply,
    restrictScalars_one]

/-- The embedding of the crossed product of `E / M` into the crossed product of `E / K`. -/
noncomputable def restrictRingHom : CrossedProduct hf' →+* CrossedProduct hf where
  toFun := restrictMap M hf hf'
  map_one' := restrictMap_one M hf hf'
  map_mul' := restrictMap_mul M hf hf'
  map_zero' := restrictMap_zero M hf hf'
  map_add' := restrictMap_add M hf hf'

/-! ### The image is the centralizer of the intermediate field -/

/-- The image of the smaller crossed product commutes with the copy of `M`. -/
theorem restrictMap_commute (x : CrossedProduct hf') (m : M) :
    restrictMap M hf hf' x * incl hf (algebraMap M E m)
      = incl hf (algebraMap M E m) * restrictMap M hf hf' x := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [restrictMap_zero, zero_mul, mul_zero]
  | add p q hp hq => rw [restrictMap_add, add_mul, mul_add, hp, hq]
  | single σ a =>
    have hcom : (σ.restrictScalars K) (algebraMap M E m) = algebraMap M E m := σ.commutes m
    rw [restrictMap_single, single_mul_incl, hcom]

/-- An element of the crossed product of `E / K` commuting with the copy of `M` comes from the
crossed product of `E / M`. -/
theorem exists_eq_restrictMap (y : CrossedProduct hf)
    (hy : ∀ m : M, y * incl hf (algebraMap M E m) = incl hf (algebraMap M E m) * y) :
    ∃ x : CrossedProduct hf', restrictMap M hf hf' x = y := by
  classical
  have hrange : ↑(toFinsupp y).support ⊆
      Set.range (fun σ : Gal(E/M) => σ.restrictScalars K) := by
    intro g hg
    have hgne : toFinsupp y g ≠ 0 := Finsupp.mem_support_iff.1 hg
    have hfix : ∀ m : M, g (algebraMap M E m) = algebraMap M E m := by
      intro m
      have h := congrArg (fun z => toFinsupp z g) (hy m)
      simp only [toFinsupp_mul_incl, toFinsupp_incl_mul] at h
      have h2 : (g (algebraMap M E m) - algebraMap M E m) * toFinsupp y g = 0 := by
        linear_combination h
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact sub_eq_zero.1 h3
      · exact absurd h3 hgne
    exact ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hfix, AlgEquiv.ext fun _ => rfl⟩
  refine ⟨(Finsupp.comapDomain (fun σ : Gal(E/M) => σ.restrictScalars K) (toFinsupp y)
    ((restrictScalars_injective M).injOn) : Gal(E/M) →₀ E), toFinsupp_injective ?_⟩
  rw [toFinsupp_restrictMap]
  exact Finsupp.mapDomain_comapDomain _ (restrictScalars_injective M) (toFinsupp y) hrange

/-- **The image of the crossed product of `E / M` is the centralizer of the copy of `M`.** -/
theorem range_restrictMap :
    Set.range (restrictMap M hf hf')
      = Subalgebra.centralizer K (Set.range fun m : M => incl hf (algebraMap M E m)) := by
  ext y
  simp only [Set.mem_range, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
  constructor
  · rintro ⟨x, rfl⟩ _ ⟨m, rfl⟩
    exact (restrictMap_commute M hf hf' x m).symm
  · intro hy
    exact exists_eq_restrictMap M hf hf' y fun m => (hy _ ⟨m, rfl⟩).symm

/-! ### Base change to the intermediate field -/

variable [FiniteDimensional K E] [IsGalois K E]

/-- **Restriction of a crossed product.**  Extending scalars from `K` to an intermediate field
`M` turns the crossed product of `E / K` for a cocycle into the algebra of matrices over the
crossed product of `E / M` for the restricted cocycle. -/
theorem nonempty_algEquiv_matrix_restrict :
    Nonempty ((M ⊗[K] CrossedProduct hf) ≃ₐ[M]
      Matrix (Fin (finrank K M)) (Fin (finrank K M)) (CrossedProduct hf')) := by
  letI : Algebra K (CrossedProduct hf') :=
    RingHom.toAlgebra' ((incl hf').comp (algebraMap K E)) fun k x => by
      have hk : (incl hf') (algebraMap K E k)
          = algebraMap M (CrossedProduct hf') (algebraMap K M k) := by
        rw [algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      rw [RingHom.comp_apply, hk]
      exact Algebra.commutes _ _
  haveI : IsScalarTower K M (CrossedProduct hf') :=
    IsScalarTower.of_algebraMap_eq fun k => by
      show (incl hf') (algebraMap K E k)
        = algebraMap M (CrossedProduct hf') (algebraMap K M k)
      rw [algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  let g : CrossedProduct hf' →ₐ[K] CrossedProduct hf :=
    { restrictRingHom M hf hf' with
      commutes' := fun k => by
        show restrictMap M hf hf' ((incl hf') (algebraMap K E k))
          = algebraMap K (CrossedProduct hf) k
        rw [restrictMap_incl, algebraMap_eq, IsScalarTower.algebraMap_apply K M E] }
  have hginj : Function.Injective g := restrictMap_injective M hf hf'
  have hfun : (fun m : M => g (algebraMap M (CrossedProduct hf') m))
      = fun m : M => incl hf (algebraMap M E m) := funext fun m => by
    show restrictMap M hf hf' (algebraMap M (CrossedProduct hf') m) = _
    rw [algebraMap_eq, restrictMap_incl]
  have hgr : g.range = Subalgebra.centralizer K
      ((g.comp (IsScalarTower.toAlgHom K M (CrossedProduct hf'))).range :
        Set (CrossedProduct hf)) := by
    have hset : ((g.comp (IsScalarTower.toAlgHom K M (CrossedProduct hf'))).range :
        Set (CrossedProduct hf)) = Set.range fun m : M => incl hf (algebraMap M E m) := by
      rw [AlgHom.coe_range]
      exact congrArg Set.range hfun
    rw [hset]
    refine SetLike.ext' ?_
    rw [AlgHom.coe_range]
    exact range_restrictMap M hf hf'
  exact Centralizer.exists_algEquiv_matrix_of_range_eq_centralizer g hginj hgr

/-- **The restriction map on Brauer groups, computed on crossed products.**  Extending scalars to
an intermediate field sends the class of a cocycle to the class of its restriction. -/
theorem baseChangeHom_mk_csa [FiniteDimensional M E] [IsGalois M E] :
    BrauerGroup.baseChangeHom M (⟦csa hf⟧ : BrauerGroup K) = (⟦csa hf'⟧ : BrauerGroup M) := by
  haveI : FiniteDimensional K M := FiniteDimensional.left K M E
  have hd : finrank K M ≠ 0 := (Module.finrank_pos_iff.2 inferInstance).ne'
  obtain ⟨e⟩ := nonempty_algEquiv_matrix_restrict M hf hf'
  rw [BrauerGroup.baseChangeHom_mk]
  exact Quotient.sound (IsBrauerEquivalent.of_algEquiv_matrix hd e)

end CrossedProduct

end InverseGalois.CFT
