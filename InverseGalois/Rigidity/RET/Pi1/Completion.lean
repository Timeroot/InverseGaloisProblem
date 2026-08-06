/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Finite continuous quotients of a profinite completion

A continuous homomorphism from the profinite completion `Â` of a group `A` to a *finite* discrete
group `H` is determined by its restriction along the unit `η : A → Â`, whose image is dense; since
the target is finite (hence discrete, and every subset closed), the range of the continuous map
already equals the range of the induced discrete homomorphism `A →* H`.  Consequently the finite
continuous quotients of `Â` are exactly the finite discrete quotients of `A`.

This is the general form of the dictionary used for `sphereCompletion` in
`RET.Pi1.SphereCompletion`; stating it for an arbitrary `A : GrpCat` lets the same dictionary be
applied to the fundamental group of a punctured plane (`RET.Pi1.Topological.Comparison`).

## Main results

* `Rigidity.RET.completion_surjective_iff` — a continuous hom `Â → H` is surjective iff the induced
  discrete hom `A →* H` is.
* `Rigidity.RET.exists_surjective_completion_iff` — `H` is a finite continuous quotient of `Â` iff
  it is a quotient of `A`.
-/

namespace Rigidity.RET

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory

universe u

variable {A : GrpCat.{u}} {H : Type u} [Group H] [Finite H]

/-- The discrete homomorphism `A →* H` induced by a continuous homomorphism from the profinite
completion of `A`, via the profinite-completion adjunction.  Its codomain is the (discrete, finite)
carrier of the profinite target, definitionally `H`. -/
noncomputable def completionInduced
    (f : profiniteCompletion.obj A ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) :
    A →* (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H) : Type u) :=
  (homEquiv A (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) f).hom

/-- The induced discrete hom is the composite of the continuous hom with the unit `η`. -/
theorem completionInduced_apply
    (f : profiniteCompletion.obj A ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) (x : A) :
    completionInduced f x = f (etaFn A x) := by
  simp only [completionInduced, homEquiv, Equiv.coe_fn_mk]
  rfl

/-- The range of a continuous hom from the completion equals the range of its induced discrete hom:
the completion is the closure of the dense image of `A`, and the target is finite discrete. -/
theorem completion_range_eq
    (f : profiniteCompletion.obj A ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) :
    Set.range (f : profiniteCompletion.obj A → _) = Set.range (completionInduced f) := by
  haveI : Finite (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H) : Type u) := ‹Finite H›
  apply le_antisymm
  · have hden : Dense (Set.range (etaFn A)) := ProfiniteGrp.ProfiniteCompletion.denseRange A
    have hcont : Continuous (f : profiniteCompletion.obj A → _) := f.hom.continuous
    calc Set.range (f : profiniteCompletion.obj A → _)
        = (f : profiniteCompletion.obj A → _) '' Set.univ := by rw [Set.image_univ]
      _ = (f : profiniteCompletion.obj A → _) '' closure (Set.range (etaFn A)) := by
            rw [hden.closure_eq]
      _ ⊆ closure ((f : profiniteCompletion.obj A → _) '' Set.range (etaFn A)) :=
            image_closure_subset_closure_image hcont
      _ = closure (Set.range (completionInduced f)) := by
            congr 1
            rw [← Set.range_comp]
            apply congrArg Set.range
            funext x
            exact (completionInduced_apply f x).symm
      _ = Set.range (completionInduced f) := (Set.toFinite _).isClosed.closure_eq
  · rintro _ ⟨x, rfl⟩
    exact ⟨etaFn A x, (completionInduced_apply f x).symm⟩

/-- **A continuous hom from the completion is surjective iff its induced discrete hom is.** -/
theorem completion_surjective_iff
    (f : profiniteCompletion.obj A ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) :
    Function.Surjective (f : profiniteCompletion.obj A → _)
      ↔ Function.Surjective (completionInduced f) := by
  rw [← Set.range_eq_univ, ← Set.range_eq_univ, completion_range_eq]

/-- **The finite-quotient dictionary for a profinite completion.**  A finite group `H` is a
continuous quotient of the profinite completion of `A` iff it is a quotient of `A` itself. -/
theorem exists_surjective_completion_iff :
    (∃ f : profiniteCompletion.obj A ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H),
        Function.Surjective (f : profiniteCompletion.obj A → _))
      ↔ (∃ φ : A →* H, Function.Surjective φ) := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨completionInduced f, (completion_surjective_iff f).mp hf⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨(homEquiv A (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H))).symm (GrpCat.ofHom φ), ?_⟩
    rw [completion_surjective_iff]
    have hind : completionInduced
        ((homEquiv A (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H))).symm (GrpCat.ofHom φ)) = φ := by
      simp only [completionInduced, Equiv.apply_symm_apply]
      rfl
    rw [hind]
    exact hφ

end Rigidity.RET
