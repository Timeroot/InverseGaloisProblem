/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Presentation
import InverseGalois.Rigidity.RET.Pi1.Completion

/-!
# The profinite completion of the sphere group and its finite quotients

The algebraic tame fundamental group of the `r`-punctured line is the profinite completion of the
sphere presentation group `Γ_r = ⟨x₀,…,x_{r-1} | x₀···x_{r-1} = 1⟩` (`SphereGroup r`).  This module
records that completion, `sphereCompletion r`, and establishes the dictionary between its **finite
continuous quotients** and the generating product-one tuples that a rigidity certificate records:

  continuous surjection `sphereCompletion r ↠ H`  ↔  generating product-one tuple `Fin r → H`.

A continuous homomorphism from the (compact) completion to a finite discrete group is determined by
its restriction to the dense image of `Γ_r`, so its range equals the range of the induced discrete
homomorphism `Γ_r →* H`; surjectivity therefore transfers between the two, and the discrete side is
the tuple dictionary of `Presentation` (`sphereHom_surjective_iff`).

## Main definitions / results

* `sphereCompletion r` — the profinite completion of `SphereGroup r`.
* `sphereCompletion_surjective_iff` — a continuous hom `sphereCompletion r → H` is surjective iff its
  induced discrete hom `SphereGroup r →* H` is.
* `exists_surjective_sphereCompletion_iff` — a continuous surjection onto a finite `H` exists iff a
  generating product-one tuple `Fin r → H` exists.
-/

namespace Rigidity.RET

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory

/-- **The profinite completion of the sphere group**: the algebraic tame fundamental group of the
`r`-punctured line, `π̂₁ = completion ⟨x₀,…,x_{r-1} | x₀···x_{r-1} = 1⟩`. -/
noncomputable def sphereCompletion (r : ℕ) : ProfiniteGrp :=
  profiniteCompletion.obj (GrpCat.of (SphereGroup r))

variable {r : ℕ} {H : Type} [Group H] [Finite H]

/-- The discrete homomorphism `SphereGroup r →* H` induced by a continuous homomorphism
`sphereCompletion r → H`, via the profinite-completion adjunction.  Its codomain is the (discrete,
finite) carrier of the profinite target, definitionally `H`. -/
noncomputable def sphereCompletionInduced
    (f : sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) :
    SphereGroup r →* (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H) : Type) :=
  completionInduced (A := GrpCat.of (SphereGroup r)) f

/-- The induced discrete hom is the composite of the continuous hom with the unit `η`. -/
theorem sphereCompletionInduced_apply
    (f : sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) (x : SphereGroup r) :
    sphereCompletionInduced f x = f (etaFn (GrpCat.of (SphereGroup r)) x) :=
  completionInduced_apply (A := GrpCat.of (SphereGroup r)) f x

/-- The range of a continuous hom from the completion equals the range of its induced discrete hom:
the completion is the closure of the dense image of `Γ_r`, and the target is finite discrete. -/
theorem sphereCompletion_range_eq
    (f : sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) :
    Set.range (f : sphereCompletion r → _) = Set.range (sphereCompletionInduced f) :=
  completion_range_eq (A := GrpCat.of (SphereGroup r)) f

/-- **A continuous hom from the completion is surjective iff its induced discrete hom is.** -/
theorem sphereCompletion_surjective_iff
    (f : sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H)) :
    Function.Surjective (f : sphereCompletion r → _)
      ↔ Function.Surjective (sphereCompletionInduced f) :=
  completion_surjective_iff (A := GrpCat.of (SphereGroup r)) f

/-- The product of the sphere group's generators is trivial (the defining relation). -/
theorem sphere_gens_prod_eq_one :
    (List.ofFn (fun i => PresentedGroup.of i : Fin r → SphereGroup r)).prod = 1 := by
  have h1 : (List.ofFn (fun i : Fin r => PresentedGroup.of i)).prod
      = PresentedGroup.mk (sphereRel r) ((List.ofFn (fun i : Fin r => FreeGroup.of i)).prod) := by
    rw [map_list_prod, List.map_ofFn]; rfl
  rw [h1]
  exact PresentedGroup.one_of_mem (by rfl)

omit [Finite H] in
/-- Every homomorphism out of the sphere group is the `sphereHom` of the tuple of its values on the
generators; in particular that tuple is product-one. -/
theorem eq_sphereHom (φ : SphereGroup r →* H) :
    ∃ hb : (List.ofFn (fun i => φ (PresentedGroup.of i))).prod = 1,
      sphereHom (fun i => φ (PresentedGroup.of i)) hb = φ := by
  have hb : (List.ofFn (fun i => φ (PresentedGroup.of i))).prod = 1 := by
    rw [show (List.ofFn (fun i => φ (PresentedGroup.of i)))
          = (List.ofFn (fun i => PresentedGroup.of i : Fin r → SphereGroup r)).map φ by
        rw [List.map_ofFn]; rfl,
      ← map_list_prod, sphere_gens_prod_eq_one, map_one]
  refine ⟨hb, ?_⟩
  apply PresentedGroup.ext
  intro i
  rw [sphereHom_of]

/-- **The finite-quotient dictionary for the tame π₁.**  A continuous surjection from
`sphereCompletion r` onto a finite group `H` exists iff `H` is generated by a product-one tuple of
length `r` — i.e. iff `H` is a quotient of the sphere group by the relation carried by a rigidity
certificate. -/
theorem exists_surjective_sphereCompletion_iff :
    (∃ f : sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H),
        Function.Surjective (f : sphereCompletion r → _))
      ↔ (∃ base : Fin r → H, (List.ofFn base).prod = 1
            ∧ Subgroup.closure (Set.range base) = ⊤) := by
  constructor
  · rintro ⟨f, hf⟩
    rw [sphereCompletion_surjective_iff] at hf
    obtain ⟨hb, hsh⟩ := eq_sphereHom (sphereCompletionInduced f)
    refine ⟨fun i => sphereCompletionInduced f (PresentedGroup.of i), hb, ?_⟩
    rw [← sphereHom_surjective_iff _ hb, hsh]; exact hf
  · rintro ⟨base, hb, hgen⟩
    refine ⟨(homEquiv (GrpCat.of (SphereGroup r))
              (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H))).symm (GrpCat.ofHom (sphereHom base hb)), ?_⟩
    rw [sphereCompletion_surjective_iff]
    have hind : sphereCompletionInduced
        ((homEquiv (GrpCat.of (SphereGroup r))
          (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H))).symm (GrpCat.ofHom (sphereHom base hb)))
        = sphereHom base hb := by
      simp only [sphereCompletionInduced, completionInduced, Equiv.apply_symm_apply]
      rfl
    rw [hind]
    exact (sphereHom_surjective_iff base hb).mpr hgen

omit [Finite H] in
/-- **The discrete tuple dictionary, existential form.**  A surjection `SphereGroup r ↠ H` exists iff
`H` is generated by a product-one `r`-tuple. -/
theorem exists_surjective_sphereGroup_iff :
    (∃ φ : SphereGroup r →* H, Function.Surjective φ)
      ↔ (∃ base : Fin r → H, (List.ofFn base).prod = 1
            ∧ Subgroup.closure (Set.range base) = ⊤) := by
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨hb, hsh⟩ := eq_sphereHom φ
    exact ⟨fun i => φ (PresentedGroup.of i), hb,
      (sphereHom_surjective_iff _ hb).1 (by rw [hsh]; exact hφ)⟩
  · rintro ⟨base, hb, hgen⟩
    exact ⟨sphereHom base hb, (sphereHom_surjective_iff base hb).2 hgen⟩

/-- **The profinite π₁ reformulation of the sphere-quotient condition.**  For a finite group `H`,
the two incarnations of "`H` is a quotient of the tame π₁ of the `r`-punctured line" agree: `H` is a
(discrete) quotient of the sphere group `SphereGroup r` iff `H` is a **finite continuous quotient**
of the profinite tame fundamental group `sphereCompletion r`.

This identifies the combinatorial input the rigidity certificate records — a surjection
`SphereGroup r ↠ H` — with the étale-π₁ datum of a continuous surjection from the profinite
fundamental group, the two sides related by the profinite-completion adjunction. -/
theorem exists_surjective_completion_iff_discrete :
    (∃ f : sphereCompletion r ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H),
        Function.Surjective (f : sphereCompletion r → _))
      ↔ (∃ φ : SphereGroup r →* H, Function.Surjective φ) := by
  rw [exists_surjective_sphereCompletion_iff, exists_surjective_sphereGroup_iff]

end Rigidity.RET
