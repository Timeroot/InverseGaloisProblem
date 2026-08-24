/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleFixed

/-!
# The norm map on the ideles of a cyclic extension

The norm of an idele of the extension is the sum of its conjugates.  For a cyclic Galois group that
sum is the norm of the Tate formalism, taken for the action of a generator, and it is fixed by the
generator, hence by the whole group; so it is the image of a unique idele of the base field.  This
file records that idele as the norm map, and checks that the norm map is compatible with the
diagonal: the idele of the extension attached to a unit of the base field is the image of the
principal idele of that unit.

The compatibility with the diagonal is checked place by place, where it says that the structure map
of the completion at a place of the extension over the completion at the place below carries the
image of an element of the base field to its image in the extension; both sides are the image of the
same element of the base field, so the two maps agree on the base field, which is where the
diagonal lives.

## Main definitions

* `InverseGalois.CFT.globalUnitsComap`: the units of the base field, viewed as units of the
  extension.
* `InverseGalois.CFT.ideleNorm`: **the norm map from the ideles of a cyclic extension to the ideles
  of the base field.**

## Main results

* `InverseGalois.CFT.ideleComap_ideleDiag`: **the diagonal commutes with the inclusion of the
  ideles of the base field.**
* `InverseGalois.CFT.ideleComap_ideleNorm`: **the norm of an idele, viewed among the ideles of the
  extension, is the sum of its conjugates.**

## Tags

number field, idele, norm map, cyclic extension, Tate cohomology
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

variable {σ : Gal(K/k)} {n : ℕ} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) (hσ : σ ^ n = 1)

include hgen hσ

variable (k K) in
/-- **The sum of the conjugates of an idele is an idele of the base field**: it is fixed by the
generator, hence by the whole Galois group. -/
theorem normHom_ideleAut_mem_range (x : ↥(idele K)) :
    normHom (ideleAut (k := k) σ) n x ∈ (ideleComap k K).range := by
  rw [mem_range_ideleComap_iff_of_zpowers k K hgen]
  refine (mem_ker_sigmaSubOne_iff _ _).mp ?_
  exact range_normHom_le_ker_sigmaSubOne (ideleAut (k := k) σ) (ideleAut_pow_eq_one σ hσ)
    ⟨x, rfl⟩

variable (k K) in
/-- **The norm map on the ideles of a cyclic extension**: the unique idele of the base field whose
image in the extension is the sum of the conjugates. -/
noncomputable def ideleNorm : ↥(idele K) →+ ↥(idele k) :=
  (AddMonoidHom.ofInjective (ideleComap_injective k K)).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict (normHom (ideleAut (k := k) σ) n) (ideleComap k K).range
      (normHom_ideleAut_mem_range k K hgen hσ))

variable (k K) in
/-- **The norm of an idele, viewed among the ideles of the extension, is the sum of its
conjugates.** -/
@[simp]
theorem ideleComap_ideleNorm (x : ↥(idele K)) :
    ideleComap k K (ideleNorm k K hgen hσ x) = normHom (ideleAut (k := k) σ) n x :=
  AddMonoidHom.apply_ofInjective_symm (ideleComap_injective k K)
    ⟨normHom (ideleAut (k := k) σ) n x, normHom_ideleAut_mem_range k K hgen hσ x⟩

end IdeleNorm

end InverseGalois.CFT
