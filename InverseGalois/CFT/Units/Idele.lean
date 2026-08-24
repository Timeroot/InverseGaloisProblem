/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Prod
import InverseGalois.CFT.Tate.Restrict
import InverseGalois.CFT.Units.AdicSIdeles
import InverseGalois.CFT.Units.ArchimedeanIdeles
import InverseGalois.CFT.Units.LocalEmbedding

/-!
# The ideles of a number field

An idele of a number field is a unit of the completion at every place, subject to the requirement
that all but finitely many of the local components are units of the valuation ring.  This file
introduces that group as a subgroup of the product of all the local unit groups, carries the Galois
action over to it, and embeds the multiplicative group of the field in it diagonally.

The finiteness requirement is preserved by the Galois action because the transports between
completions are isometries and the action permutes the places; it holds for the diagonal image of an
element of the field because an element has nonzero order at only finitely many primes.

## Main definitions

* `InverseGalois.CFT.FullIdele`: the product of the local unit groups at all places.
* `InverseGalois.CFT.idele`: **the ideles**, the elements of that product that are units of the
  valuation ring at all but finitely many finite places.
* `InverseGalois.CFT.ideleAut`: **the action of a Galois automorphism on the ideles.**
* `InverseGalois.CFT.ideleDiag`: **the diagonal embedding of the units of the field into the
  ideles.**

## Main results

* `InverseGalois.CFT.unitVal_fullIdeleAut`: the Galois transports preserve the local valuations.
* `InverseGalois.CFT.ideleAut_pow_eq_one`: the action inherits the order of the automorphism.
* `InverseGalois.CFT.ideleDiag_injective`: the diagonal is injective.

## Tags

number field, idele, completion, unit, valuation, Galois action
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### The group of ideles -/

section Idele

variable (K : Type*) [Field K] [NumberField K]

/-- The product of the local unit groups at all places of a number field: the units of the
completion at every infinite place and at every finite one. -/
abbrev FullIdele : Type _ :=
  (∀ w : InfinitePlace K, Additive w.Completionˣ) ×
    (∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ)

/-- **The ideles of a number field**: the elements of the product of the local unit groups whose
component is a unit of the valuation ring at all but finitely many finite places. -/
def idele : AddSubgroup (FullIdele K) where
  carrier := {x | ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, unitVal (x.2 v) = 0}
  add_mem' {x y} hx hy := by
    show ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, unitVal ((x + y).2 v) = 0
    filter_upwards [hx, hy] with v hxv hyv
    show unitVal (x.2 v + y.2 v) = 0
    rw [map_add, hxv, hyv, add_zero]
  zero_mem' := by
    show ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      unitVal ((0 : FullIdele K).2 v) = 0
    filter_upwards with v
    exact map_zero _
  neg_mem' {x} hx := by
    show ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, unitVal ((-x).2 v) = 0
    filter_upwards [hx] with v hxv
    show unitVal (-x.2 v) = 0
    rw [map_neg, hxv, neg_zero]

theorem mem_idele {x : FullIdele K} :
    x ∈ idele K ↔ ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, unitVal (x.2 v) = 0 :=
  Iff.rfl

end Idele

/-! ### The Galois action -/

section Action

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]

/-- The action of a Galois automorphism on the product of the local unit groups, place by place. -/
noncomputable def fullIdeleAut (σ : Gal(K/k)) : FullIdele K ≃+ FullIdele K :=
  prodAut ((infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ)
    ((adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ)

theorem fullIdeleAut_symm (σ : Gal(K/k)) :
    (fullIdeleAut (k := k) (K := K) σ).symm = fullIdeleAut σ⁻¹ := by
  rw [fullIdeleAut, fullIdeleAut, map_inv, map_inv]
  rfl

/-- **The Galois transports preserve the local valuations**, the isomorphism between the completion
at a place and the completion at its image being an isometry. -/
theorem unitVal_fullIdeleAut (σ : Gal(K/k)) (x : FullIdele K) (v : HeightOneSpectrum (𝓞 K)) :
    unitVal ((fullIdeleAut (k := k) σ x).2 (σ • v)) = unitVal (x.2 v) := by
  show unitVal ((adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ x.2 (σ • v)) = _
  rw [FamilyAction.familyAut_apply_smul, unitVal_adicUnitsFamily_map]

/-- The ideles are stable under the Galois action: the places where the local component fails to be
a unit of the valuation ring are merely permuted. -/
theorem fullIdeleAut_mem_idele (σ : Gal(K/k)) {x : FullIdele K} (hx : x ∈ idele K) :
    fullIdeleAut (k := k) σ x ∈ idele K := by
  rw [mem_idele, Filter.eventually_cofinite] at hx ⊢
  refine (hx.image (fun v => σ • v)).subset fun v hv => ⟨σ⁻¹ • v, ?_, smul_inv_smul σ v⟩
  intro hc
  refine hv ?_
  rw [← smul_inv_smul σ v, unitVal_fullIdeleAut, hc]

/-- **The action of a Galois automorphism on the ideles.** -/
noncomputable def ideleAut (σ : Gal(K/k)) : ↥(idele K) ≃+ ↥(idele K) :=
  subgroupAut (fullIdeleAut (k := k) σ) (idele K) (fun _ hx => fullIdeleAut_mem_idele σ hx)
    (fun _ hx => by rw [fullIdeleAut_symm]; exact fullIdeleAut_mem_idele σ⁻¹ hx)

@[simp]
theorem coe_ideleAut (σ : Gal(K/k)) (x : ↥(idele K)) :
    ((ideleAut (k := k) σ x : ↥(idele K)) : FullIdele K)
      = fullIdeleAut (k := k) σ (x : FullIdele K) :=
  rfl

/-- **The action on the ideles inherits the order of the automorphism.** -/
theorem ideleAut_pow_eq_one (σ : Gal(K/k)) {n : ℕ} (hσ : σ ^ n = 1) :
    (ideleAut (k := k) (K := K) σ) ^ n = 1 := by
  refine subgroupAut_pow_eq_one _ _ ?_
  rw [fullIdeleAut]
  exact prodAut_pow_eq_one (by rw [← map_pow, hσ, map_one]) (by rw [← map_pow, hσ, map_one])

end Action

/-! ### The diagonal -/

section Diagonal

variable (K : Type*) [Field K] [NumberField K]

/-- The diagonal image of a unit of the field in the product of the local unit groups. -/
noncomputable def fullDiag : Additive Kˣ →+ FullIdele K where
  toFun u := (fun w => Additive.ofMul (infiniteUnitHom w u.toMul),
    fun v => Additive.ofMul (adicUnitHom v u.toMul))
  map_zero' := by
    refine Prod.ext (funext fun w => ?_) (funext fun v => ?_)
    · exact Additive.toMul.injective (Units.ext (by simp))
    · exact Additive.toMul.injective (Units.ext (by simp))
  map_add' u u' := by
    refine Prod.ext (funext fun w => ?_) (funext fun v => ?_)
    · exact Additive.toMul.injective (Units.ext (by simp))
    · exact Additive.toMul.injective (Units.ext (by simp))

@[simp]
theorem fullDiag_fst (u : Additive Kˣ) (w : InfinitePlace K) :
    (fullDiag K u).1 w = Additive.ofMul (infiniteUnitHom w u.toMul) := rfl

@[simp]
theorem fullDiag_snd (u : Additive Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (fullDiag K u).2 v = Additive.ofMul (adicUnitHom v u.toMul) := rfl

/-- The diagonal image of a unit of the field is an idele, an element of a number field having
nonzero order at only finitely many primes. -/
theorem fullDiag_mem_idele (u : Additive Kˣ) : fullDiag K u ∈ idele K := by
  rw [mem_idele]
  filter_upwards [ord_finite (R := 𝓞 K) (K := K) ((u.toMul : Kˣ) : K)] with v hv
  rw [fullDiag_snd, unitVal_adicUnitHom, hv, neg_zero]

/-- **The diagonal embedding of the units of the field into the ideles.** -/
noncomputable def ideleDiag : Additive Kˣ →+ ↥(idele K) where
  toFun u := ⟨fullDiag K u, fullDiag_mem_idele K u⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem coe_ideleDiag (u : Additive Kˣ) :
    ((ideleDiag K u : ↥(idele K)) : FullIdele K) = fullDiag K u := rfl

/-- The diagonal is injective, since a number field has an infinite place and embeds in the
completion there. -/
theorem ideleDiag_injective : Function.Injective (ideleDiag K) := by
  intro u u' h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have h1 := congrFun (congrArg Prod.fst (congrArg Subtype.val h)) w
  exact Additive.toMul.injective (infiniteUnitHom_injective w (Additive.toMul.injective h1))

end Diagonal

end InverseGalois.CFT
