/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.InfiniteGalois

/-!
# Hilbert's theorem 90 for the decomposition group at an infinite place

The completion of a Galois extension of number fields at an archimedean place is a finite Galois
extension of the completion of the base at the place below, and every automorphism of it over the
completion of the base is induced by an element of the decomposition group there.  The
decomposition group is therefore the automorphism group of the completion, and Hilbert's theorem 90
for a finite extension of fields reads as a statement about the decomposition group: a one-cocycle
with values in the units of the completion is the coboundary of a single unit.

The same holds for an arbitrary subgroup of the decomposition group, which is the automorphism
group of the completion over the subfield it fixes, again a finite extension.

## Main definitions

* `InverseGalois.CFT.stabilizerToAlgEquivInfinite`: the automorphism of the completion attached to
  an element of the decomposition group.
* `InverseGalois.CFT.stabilizerAlgEquivInfinite`: **the decomposition group at an infinite place is
  the automorphism group of the completion there.**

## Main results

* `InverseGalois.CFT.isMulCoboundary₁_of_isMulCocycle₁_stabilizerInfinite`: **Hilbert's theorem 90
  for a subgroup of the decomposition group at an infinite place.**

## Tags

number field, infinite place, completion, decomposition group, Hilbert's theorem 90,
Galois cohomology
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

open MulAction NumberField groupCohomology

namespace InverseGalois.CFT

/-! ### The decomposition group as an automorphism group -/

section Stabilizer

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : InfinitePlace K)

variable (k) in
/-- **The automorphism of the completion attached to an element of the decomposition group.** -/
noncomputable def stabilizerToAlgEquivInfinite (σ : ↥(stabilizer Gal(K/k) w)) :
    w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion :=
  AlgEquiv.ofRingEquiv (f := infiniteCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2))
    (stabilizer_smul_algebraMap_infinite k w σ)

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
@[simp]
theorem stabilizerToAlgEquivInfinite_apply (σ : ↥(stabilizer Gal(K/k) w)) (z : w.Completion) :
    stabilizerToAlgEquivInfinite k w σ z = σ • z := rfl

variable (k) in
/-- **The decomposition group at an infinite place is the automorphism group of the completion
there.**  Every element of the decomposition group extends to the completion, and every
automorphism of the completion over the completion of the base is an isometry, hence restricts to
an automorphism of the extension fixing the place. -/
noncomputable def stabilizerAlgEquivInfinite : ↥(stabilizer Gal(K/k) w) ≃*
    (w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion) where
  toFun := stabilizerToAlgEquivInfinite k w
  invFun τ := ⟨restrictToBaseInfinite k w τ, restrictToBaseInfinite_mem_stabilizer k w τ⟩
  left_inv σ := by
    refine Subtype.ext (AlgEquiv.ext fun x => ?_)
    refine (algebraMap K w.Completion).injective ?_
    have hcoe : ∀ y : K, algebraMap K w.Completion y = infiniteCoe y w := fun _ => rfl
    rw [algebraMap_restrictToBaseInfinite k w (stabilizerToAlgEquivInfinite k w σ) x,
      stabilizerToAlgEquivInfinite_apply, hcoe, hcoe, stabilizer_smul_infiniteCompletion_def,
      infiniteCoe, infiniteCompletionAut_coe]
    rfl
  right_inv τ := AlgEquiv.ext fun z => infiniteCompletionAut_restrictToBaseInfinite k w τ z
  map_mul' σ τ := AlgEquiv.ext fun z => mul_smul σ τ z

variable (k) in
@[simp]
theorem stabilizerAlgEquivInfinite_apply (σ : ↥(stabilizer Gal(K/k) w)) (z : w.Completion) :
    stabilizerAlgEquivInfinite k w σ z = σ • z := rfl

end Stabilizer

/-! ### Hilbert's theorem 90 -/

section Hilbert90

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : InfinitePlace K)

/-- **The decomposition group at an infinite place acts on the units of the completion there.** -/
noncomputable instance instMulDistribMulActionStabilizerInfiniteUnits :
    MulDistribMulAction ↥(stabilizer Gal(K/k) w) (w.Completion)ˣ :=
  Units.mulDistribMulActionRight

/-- A shortcut instance for the action of a subgroup of the decomposition group at an infinite
place on the units of the completion there. -/
noncomputable instance instMulDistribMulActionSubgroupInfiniteUnits
    (S : Subgroup ↥(stabilizer Gal(K/k) w)) : MulDistribMulAction ↥S (w.Completion)ˣ :=
  Submonoid.mulDistribMulAction S.toSubmonoid

/-- A shortcut instance for the action of a subgroup of the decomposition group at an infinite
place on the units of the completion there. -/
noncomputable instance instMulActionSubgroupInfiniteUnits
    (S : Subgroup ↥(stabilizer Gal(K/k) w)) : MulAction ↥S (w.Completion)ˣ :=
  MulDistribMulAction.toMulAction

variable (k) in
omit [NumberField k] [NumberField K] [IsGalois k K] in
@[simp]
theorem val_stabilizer_smul_infiniteUnits (σ : ↥(stabilizer Gal(K/k) w)) (u : (w.Completion)ˣ) :
    ((σ • u : (w.Completion)ˣ) : w.Completion) = σ • (u : w.Completion) := rfl

set_option maxHeartbeats 4000000 in
variable (k) in
/-- **Hilbert's theorem 90 for a subgroup of the decomposition group at an infinite place.**  The
subgroup is the automorphism group of the completion over the subfield it fixes, and the completion
is a finite extension of that subfield. -/
theorem isMulCoboundary₁_of_isMulCocycle₁_stabilizerInfinite
    (S : Subgroup ↥(stabilizer Gal(K/k) w)) (e : ↥S → (w.Completion)ˣ) (he : IsMulCocycle₁ e) :
    IsMulCoboundary₁ e := by
  set Φ := stabilizerAlgEquivInfinite k w with hΦ
  set S' : Subgroup (w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion) :=
    S.map Φ.toMonoidHom with hS'
  set F := IntermediateField.fixedField S' with hF
  haveI : FiniteDimensional ↥F w.Completion :=
    FiniteDimensional.right (w.comap (algebraMap k K)).Completion ↥F w.Completion
  set Ψ : ↥S ≃* Gal(w.Completion/↥F) :=
    (S.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
      (IntermediateField.subgroupEquivAlgEquiv S') with hΨdef
  have hΨ : ∀ (σ : ↥S) (z : w.Completion),
      Ψ σ z = ((σ : ↥(stabilizer Gal(K/k) w))) • z := fun _ _ => rfl
  have hsmul : ∀ (σ : ↥S) (u : (w.Completion)ˣ), Ψ σ • u = σ • u := by
    intro σ u
    exact Units.ext (hΨ σ (u : w.Completion))
  have hsymm : ∀ (g : Gal(w.Completion/↥F)) (u : (w.Completion)ˣ), (Ψ.symm g) • u = g • u := by
    intro g u
    conv_rhs => rw [← Ψ.apply_symm_apply g]
    exact (hsmul (Ψ.symm g) u).symm
  have hcoc : IsMulCocycle₁ (fun g : Gal(w.Completion/↥F) => e (Ψ.symm g)) := by
    intro g h
    show e (Ψ.symm (g * h)) = g • e (Ψ.symm h) * e (Ψ.symm g)
    rw [map_mul, he, hsymm]
  obtain ⟨α, hα⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hcoc
  refine ⟨α, fun σ => ?_⟩
  have h : Ψ σ • α / α = e (Ψ.symm (Ψ σ)) := hα (Ψ σ)
  rwa [Ψ.symm_apply_apply, hsmul] at h

end Hilbert90

end InverseGalois.CFT
