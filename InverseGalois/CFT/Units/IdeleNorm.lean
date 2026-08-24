/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleFixed

/-!
# The norm map on the ideles

The norm of an idele of a Galois extension is the sum of its conjugates.  That sum is fixed by every
automorphism, an automorphism merely permuting the group; so it is the image of a unique idele of
the base field, and that idele is the norm.  This file records the norm map, and checks that the
norm map is compatible with the diagonal: the idele of the extension attached to a unit of the base
field is the image of the principal idele of that unit.

The compatibility with the diagonal is checked place by place, where it says that the structure map
of the completion at a place of the extension over the completion at the place below carries the
image of an element of the base field to its image in the extension; both sides are the image of the
same element of the base field, so the two maps agree on the base field, which is where the
diagonal lives.

For a cyclic group the sum of the conjugates is the norm of the Tate formalism, taken for the action
of a generator, because the powers of a generator below its order run through the group exactly
once.  That identification is what connects the norm map to the Tate cohomology of the idele class
group.

## Main definitions

* `InverseGalois.CFT.globalUnitsComap`: the units of the base field, viewed as units of the
  extension.
* `InverseGalois.CFT.ideleAutHom`: the Galois action on the ideles, as a homomorphism.
* `InverseGalois.CFT.galSum`: the sum of the conjugates of an idele.
* `InverseGalois.CFT.ideleNorm`: **the norm map from the ideles of a Galois extension to the ideles
  of the base field.**

## Main results

* `InverseGalois.CFT.ideleComap_ideleDiag`: **the diagonal commutes with the inclusion of the
  ideles of the base field.**
* `InverseGalois.CFT.ideleComap_ideleNorm`: **the norm of an idele, viewed among the ideles of the
  extension, is the sum of its conjugates.**
* `InverseGalois.CFT.galSum_eq_normHom`: for a cyclic group the sum of the conjugates is the norm
  of the Tate formalism, taken for a generator.

## Tags

number field, idele, norm map, Galois extension, Tate cohomology
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section IdeleNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ### The diagonal and the ideles of the base field -/

variable (k K) in
/-- **The units of the base field, viewed as units of the extension**, written additively. -/
noncomputable def globalUnitsComap : Additive kˣ →+ Additive Kˣ :=
  MonoidHom.toAdditive (Units.map (algebraMap k K).toMonoidHom)

variable (k K) in
omit [NumberField k] [NumberField K] in
@[simp]
theorem coe_globalUnitsComap (u : Additive kˣ) :
    ((Additive.toMul (globalUnitsComap k K u) : Kˣ) : K)
      = algebraMap k K ((Additive.toMul u : kˣ) : k) := rfl

/-! ### The Galois action as a homomorphism -/

omit [NumberField k] in
/-- The identity automorphism acts trivially on the product of the local unit groups. -/
theorem fullIdeleAut_one (x : FullIdele K) : fullIdeleAut (k := k) (1 : Gal(K/k)) x = x := by
  rw [fullIdeleAut, prodAut_apply, map_one, map_one]
  rfl

omit [NumberField k] in
/-- The action on the product of the local unit groups is multiplicative in the automorphism. -/
theorem fullIdeleAut_mul (σ τ : Gal(K/k)) (x : FullIdele K) :
    fullIdeleAut (k := k) (σ * τ) x = fullIdeleAut (k := k) σ (fullIdeleAut (k := k) τ x) := by
  rw [fullIdeleAut, prodAut_apply, map_mul, map_mul]
  rfl

omit [NumberField k] in
/-- The identity automorphism acts trivially on the ideles. -/
theorem ideleAut_one (x : ↥(idele K)) : ideleAut (k := k) (1 : Gal(K/k)) x = x :=
  Subtype.ext (fullIdeleAut_one (k := k) (x : FullIdele K))

omit [NumberField k] in
/-- The action on the ideles is multiplicative in the automorphism. -/
theorem ideleAut_mul (σ τ : Gal(K/k)) (x : ↥(idele K)) :
    ideleAut (k := k) (σ * τ) x = ideleAut (k := k) σ (ideleAut (k := k) τ x) :=
  Subtype.ext (fullIdeleAut_mul σ τ (x : FullIdele K))

variable (k K) in
omit [NumberField k] in
/-- **The Galois action on the ideles, as a homomorphism.** -/
noncomputable def ideleAutHom : Gal(K/k) →* AddAut ↥(idele K) where
  toFun := ideleAut (k := k)
  map_one' := AddEquiv.ext (ideleAut_one (k := k) (K := K))
  map_mul' σ τ := AddEquiv.ext (ideleAut_mul σ τ)

omit [NumberField k] in
/-- **A power of the action is the action of the power.** -/
theorem ideleAut_pow (σ : Gal(K/k)) (i : ℕ) :
    (ideleAut (k := k) (K := K) σ) ^ i = ideleAut (k := k) (σ ^ i) :=
  (map_pow (ideleAutHom k K) σ i).symm

variable [IsGalois k K]

variable (k K) in
/-- **The diagonal commutes with the inclusion of the ideles of the base field**: the idele of the
extension attached to a unit of the base field is the principal idele of that unit, read in the
extension. -/
theorem ideleComap_ideleDiag (u : Additive kˣ) :
    ideleComap k K (ideleDiag k u) = ideleDiag K (globalUnitsComap k K u) := by
  refine Subtype.ext (Prod.ext (funext fun w => ?_) (funext fun v => ?_))
  · refine Additive.toMul.injective (Units.ext ?_)
    show algebraMap (w.comap (algebraMap k K)).Completion w.Completion
        (infiniteCoe ((Additive.toMul u : kˣ) : k) (w.comap (algebraMap k K)))
      = infiniteCoe (algebraMap k K ((Additive.toMul u : kˣ) : k)) w
    rw [algebraMap_infiniteCompletion]
    exact infiniteCompletionComap_coe k w _
  · refine Additive.toMul.injective (Units.ext ?_)
    show algebraMap ((primeUnder (𝓞 k) v).adicCompletion k) (v.adicCompletion K)
        (adicCoe ((Additive.toMul u : kˣ) : k) (primeUnder (𝓞 k) v))
      = adicCoe (algebraMap k K ((Additive.toMul u : kˣ) : k)) v
    rw [algebraMap_adicCompletion]
    exact adicCompletionComap_coe (𝓞 k) v _

/-! ### The norm map -/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable (k K) in
/-- **The sum of the conjugates of an idele.** -/
noncomputable def galSum : ↥(idele K) →+ ↥(idele K) where
  toFun x := ∑ g : Gal(K/k), ideleAut (k := k) g x
  map_zero' := by
    simp only [map_zero]
    exact Finset.sum_const_zero
  map_add' x y := by
    simp only [map_add]
    exact Finset.sum_add_distrib

variable (k K) in
omit [IsGalois k K] in
theorem galSum_apply (x : ↥(idele K)) :
    galSum k K x = ∑ g : Gal(K/k), ideleAut (k := k) g x := rfl

variable (k K) in
omit [IsGalois k K] in
/-- **The sum of the conjugates of an idele is fixed by every automorphism**, an automorphism
merely permuting the Galois group. -/
theorem ideleAut_galSum (τ : Gal(K/k)) (x : ↥(idele K)) :
    ideleAut (k := k) τ (galSum k K x) = galSum k K x := by
  rw [galSum_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun g => (ideleAut_mul τ g x).symm

variable (k K) in
/-- **The sum of the conjugates of an idele is an idele of the base field.** -/
theorem galSum_mem_range (x : ↥(idele K)) : galSum k K x ∈ (ideleComap k K).range :=
  (mem_range_ideleComap_iff k K _).mpr fun τ => ideleAut_galSum k K τ x

variable (k K) in
/-- **The norm map on the ideles of a Galois extension**: the unique idele of the base field whose
image in the extension is the sum of the conjugates. -/
noncomputable def ideleNorm : ↥(idele K) →+ ↥(idele k) :=
  (AddMonoidHom.ofInjective (ideleComap_injective k K)).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict (galSum k K) (ideleComap k K).range (galSum_mem_range k K))

variable (k K) in
/-- **The norm of an idele, viewed among the ideles of the extension, is the sum of its
conjugates.** -/
@[simp]
theorem ideleComap_ideleNorm (x : ↥(idele K)) :
    ideleComap k K (ideleNorm k K x) = galSum k K x :=
  AddMonoidHom.apply_ofInjective_symm (ideleComap_injective k K)
    ⟨galSum k K x, galSum_mem_range k K x⟩

/-! ### The cyclic case -/

variable (k K) in
omit [IsGalois k K] in
/-- **For a cyclic Galois group the sum of the conjugates is the norm of the Tate formalism**, taken
for the action of a generator: the powers of a generator below its order run through the group
exactly once. -/
theorem galSum_eq_normHom {σ : Gal(K/k)} {n : ℕ} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)
    (hn : Nat.card Gal(K/k) = n) (x : ↥(idele K)) :
    galSum k K x = normHom (ideleAut (k := k) σ) n x := by
  have hord : orderOf σ = n := (orderOf_eq_card_of_forall_mem_zpowers hgen).trans hn
  have hlt : ∀ i : Fin n, (i : ℕ) ∈ Set.Iio (orderOf σ) := by
    intro i
    simp only [Set.mem_Iio, hord]
    exact i.isLt
  have hbij : Function.Bijective (fun i : Fin n => σ ^ (i : ℕ)) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j hij => ?_, ?_⟩
    · exact Fin.ext (pow_injOn_Iio_orderOf (hlt i) (hlt j) hij)
    · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hn]
  rw [galSum_apply, normHom_apply, ← Fin.sum_univ_eq_sum_range]
  exact (Fintype.sum_bijective _ hbij _ (fun g => ideleAut (k := k) g x)
    fun i => by rw [ideleAut_pow]).symm

variable (k K) in
/-- **For a cyclic Galois group the norm of an idele, viewed among the ideles of the extension, is
the norm of the Tate formalism.** -/
theorem ideleComap_ideleNorm_eq_normHom {σ : Gal(K/k)} {n : ℕ}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) (hn : Nat.card Gal(K/k) = n)
    (x : ↥(idele K)) :
    ideleComap k K (ideleNorm k K x) = normHom (ideleAut (k := k) σ) n x := by
  rw [ideleComap_ideleNorm, galSum_eq_normHom k K hgen hn]

end IdeleNorm

end InverseGalois.CFT
