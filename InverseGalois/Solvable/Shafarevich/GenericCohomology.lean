/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerCohomology
import InverseGalois.Solvable.Shafarevich.GenericHomology

/-!
# Killing cohomology classes seen from a subgroup of the operator group

The counting argument that annihilates finitely many cohomology classes with coefficients in a
layer of a generic operator group never looks at the group that acts: it only has to solve one
scalar equation for every value taken by the finitely many cocycles at hand.  So the group whose
cohomology is being killed need not be the operator group itself, and the coefficients need not be
a bare layer.

That extra freedom is what the argument is used for.  The classes to be killed are attached to a
finite family of subgroups of the operator group — the ones that arise as decomposition subgroups
of a finite family of places — and the coefficients are a layer tensored with a fixed module.  Both
are covered at once by running the count for an arbitrary homomorphism of a finite group into the
operator group and for coefficients in a layer tensored with a fixed representation, and by
counting the values of a cocycle on the smaller group.

## Main results

* `InverseGalois.Shafarevich.exists_genericShrink_res_cohomology_eq_zero` — **finitely many
  cohomology classes of a finite group acting through the operator group, in any single degree and
  with coefficients in a layer tensored with a fixed representation, are annihilated all at once by
  a surjective shrinking homomorphism**, provided the number of blocks is large enough.
* `InverseGalois.Shafarevich.exists_operatorHom_res_cohomology_eq_zero` — the same, stated with the
  rank chosen in advance of the classes.
* `InverseGalois.Shafarevich.exists_operatorHom_res_cohomology_eq_zero_of_finrank_le` — the same
  again, with the fixed representation chosen in advance only up to its dimension.

## Tags

Shafarevich's theorem, embedding problem, group cohomology, p-central series, decomposition group
-/

namespace InverseGalois.Shafarevich

open CategoryTheory

open scoped TensorProduct

section Count

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

/-- **Finitely many cohomology classes of a finite group acting through the operator group, with
coefficients in a layer tensored with a fixed representation, are annihilated all at once by a
surjective shrinking homomorphism.**  The number of scalar equations to be solved is the number of
classes, times the number of arguments of a cochain in the degree in question, times the dimension
of the coefficients downstairs; the number of blocks has to exceed that, times one more than the
level of the layer. -/
theorem exists_genericShrink_res_cohomology_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t c : ℕ} {H : Type} [Group H] [Finite H] (f : H →* U) (T : Rep (ZMod ℓ) U)
    [Module.Finite (ZMod ℓ) T]
    (hr : (j + 1) * (t * Nat.card H ^ c *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r)
    (x : Fin t → groupCohomology ((Action.res _ f).obj (genericLayerTensor U (r * n) S ℓ j T)) c) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, groupCohomology.map (MonoidHom.id H)
        ((Action.res _ f).map
          (operatorTensorRep (isOperatorHom_genericShrink U r n S a) ℓ j T)) c (x ν) = 0 := by
  choose z hz using fun ν =>
    (ModuleCat.epi_iff_surjective (groupCohomology.π
      ((Action.res _ f).obj (genericLayerTensor U (r * n) S ℓ j T)) c)).1 inferInstance (x ν)
  have hcard : Nat.card (Fin t × (Fin c → H)) = t * Nat.card H ^ c := by
    simp [Nat.card_prod, Nat.card_fun]
  have hr' : (j + 1) * (Nat.card (Fin t × (Fin c → H)) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r := by rwa [hcard]
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_rTensor_eq_zero U r n S hS T hr'
    fun q : Fin t × (Fin c → H) =>
      groupCohomology.iCocycles ((Action.res _ f).obj (genericLayerTensor U (r * n) S ℓ j T)) c
        (z q.1) q.2
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [← hz ν]
  exact map_π_eq_zero _ _ fun g => ha (ν, g)

end Count

section Prop6

variable (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S] [Finite S]

/-- **Proposition 6 with coefficients.**  For a large enough rank, finitely many cohomology classes
of a finite group acting through the operator group, in any single degree and with coefficients in
a layer tensored with a fixed representation, are annihilated all at once by a surjective
equivariant homomorphism onto the intended rank. -/
theorem exists_operatorHom_res_cohomology_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t c : ℕ} {H : Type} [Group H] [Finite H] (f : H →* U) (T : Rep (ZMod ℓ) U)
    [Module.Finite (ZMod ℓ) T] :
    ∃ m : ℕ, ∀ x : Fin t →
        groupCohomology ((Action.res _ f).obj (genericLayerTensor U m S ℓ j T)) c,
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ ν, groupCohomology.map (MonoidHom.id H)
          ((Action.res _ f).map (operatorTensorRep hα ℓ j T)) c (x ν) = 0 := by
  set r : ℕ := (j + 1) * (t * Nat.card H ^ c *
    Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) + 1 with hrdef
  have hr : (j + 1) * (t * Nat.card H ^ c *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r := by
    rw [hrdef]; exact Nat.lt_succ_self _
  refine ⟨r * n, fun x => ?_⟩
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_res_cohomology_eq_zero U r n S hS f T hr x
  exact ⟨genericShrink U r n S a, isOperatorHom_genericShrink U r n S a, hsurj, ha⟩

/-- **Proposition 6 with coefficients, the coefficients named last.**  Only the dimension of the
fixed representation enters the count, so a bound on that dimension is all that has to be known in
advance: for a large enough rank, finitely many cohomology classes of a finite group acting through
the operator group, in any single degree and with coefficients in a layer tensored with *any* fixed
representation of dimension at most the bound, are annihilated all at once by a surjective
equivariant homomorphism onto the intended rank. -/
theorem exists_operatorHom_res_cohomology_eq_zero_of_finrank_le {ℓ : ℕ} [Fact ℓ.Prime]
    (hS : IsPGroup ℓ S) {j t c d : ℕ} {H : Type} [Group H] [Finite H] (f : H →* U) :
    ∃ m : ℕ, ∀ (T : Rep (ZMod ℓ) U) [Module.Finite (ZMod ℓ) T],
      Module.finrank (ZMod ℓ) T ≤ d →
      ∀ x : Fin t → groupCohomology ((Action.res _ f).obj (genericLayerTensor U m S ℓ j T)) c,
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ ν, groupCohomology.map (MonoidHom.id H)
          ((Action.res _ f).map (operatorTensorRep hα ℓ j T)) c (x ν) = 0 := by
  set r : ℕ := (j + 1) * (t * Nat.card H ^ c *
    (Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j) * d)) + 1 with hrdef
  have hrlt : (j + 1) * (t * Nat.card H ^ c *
      (Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j) * d)) < r := by
    rw [hrdef]; exact Nat.lt_succ_self _
  refine ⟨r * n, ?_⟩
  intro T _ hT x
  have hr : (j + 1) * (t * Nat.card H ^ c *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j ⊗[ZMod ℓ] T)) < r := by
    refine lt_of_le_of_lt (Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) ?_)) hrlt
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_le_mul (le_refl _) hT
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_res_cohomology_eq_zero U r n S hS f T hr x
  exact ⟨genericShrink U r n S a, isOperatorHom_genericShrink U r n S a, hsurj, ha⟩

end Prop6

end InverseGalois.Shafarevich
