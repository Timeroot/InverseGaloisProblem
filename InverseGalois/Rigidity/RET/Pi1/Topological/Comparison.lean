/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedPlane
import InverseGalois.Rigidity.RET.Pi1.CoverCompletion

/-!
# The Riemann Existence Theorem in topological fundamental-group language

Links **C** and **D** of `Pi1/GAGA_DREAM.md` are now proven: the topological fundamental group of
the plane punctured at a finite set `S` is the sphere presentation group `Γ_{|S|+1}`
(`Rigidity.RET.pi1_compl_mulEquiv_sphereGroup`), and `sphereCompletion r` is by definition the
profinite completion of `Γ_r`.  This module cashes that in, restating the covers correspondence with
the *honest topological object* — `π₁` of an actual punctured plane — in place of the presentation
group:

> A finite group `G` is realized by a geometric Galois cover of `ℙ¹_ℚ̄` **iff** it is a quotient of
> `π₁(ℂ ∖ S)` for some finite `S ⊂ ℂ`.

As with the presentation form, the `→` direction needs no geometry: `π₁(ℂ ∖ S)` is free of rank
`|S|`, so taking `|S|` large enough makes the right-hand side hold for every finite group.  What the
biconditional carries is the `←` direction — the comparison of the topological fundamental group
with the algebraic one (links **B** and **L**), i.e. GAGA.

## Main definitions / results

* `Rigidity.RET.pi1ComplCompletionIso` — `completion (π₁(ℂ ∖ S)) ≅ sphereCompletion (|S| + 1)`,
  links **C** and **D** composed.
* `Rigidity.RET.exists_pi1_compl_surjective` — every finite group is a quotient of `π₁(ℂ ∖ S)` for a
  suitable `S`.
* `Rigidity.RET.isGeometricGaloisCover_iff_pi1_compl` — the covers correspondence with the
  topological fundamental group of a punctured plane on the right.
* `Rigidity.RET.isGeometricGaloisCover_iff_pi1_compl_completion` — the same in profinite form: `G`
  is a finite continuous quotient of the profinite completion of `π₁(ℂ ∖ S)`.
-/

namespace Rigidity.RET

open ProfiniteGrp CategoryTheory

/-- Abbreviation for the fundamental group of the plane punctured at `S`, based at `z₀`. -/
abbrev Pi1Compl (S : Finset ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ (S : Set ℂ)) : Type :=
  FundamentalGroup {z : ℂ // z ∉ (S : Set ℂ)} ⟨z₀, hz₀⟩

/-- **Links C and D composed.**  The profinite completion of the topological fundamental group of
the plane punctured at `S` is the profinite tame fundamental group `sphereCompletion (|S| + 1)` of
the `(|S|+1)`-punctured sphere (the extra puncture being `∞`). -/
noncomputable def pi1ComplCompletionIso (S : Finset ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ (S : Set ℂ)) :
    profiniteCompletion.obj (GrpCat.of (Pi1Compl S z₀ hz₀)) ≅ sphereCompletion (S.card + 1) :=
  profiniteCompletion.mapIso
    (MulEquiv.toGrpIso (X := GrpCat.of (Pi1Compl S z₀ hz₀))
      (Y := GrpCat.of (SphereGroup (S.card + 1)))
      (pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some)

/-- A punctured plane with a prescribed number of punctures, and a basepoint off the real axis. -/
private noncomputable def stdPunctures (n : ℕ) : Finset ℂ :=
  (Finset.range n).image (fun k : ℕ => (k : ℂ))

private theorem stdPunctures_card (n : ℕ) : (stdPunctures n).card = n := by
  rw [stdPunctures, Finset.card_image_of_injective _ fun a b h => by exact_mod_cast h,
    Finset.card_range]

private theorem I_notMem_stdPunctures (n : ℕ) : Complex.I ∉ ((stdPunctures n : Finset ℂ) : Set ℂ) := by
  intro h
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h)
  have : (Complex.I).im = ((k : ℂ)).im := by rw [hk]
  simp at this

/-- **Every finite group is a quotient of the fundamental group of some punctured plane.**

`π₁(ℂ ∖ S)` is free of rank `|S|` (`pi1_compl_finset`), so `|S| = |G|` punctures already suffice.
The topological side of the covers correspondence therefore imposes no condition on a finite `G`;
compare `exists_sphereGroup_surjective`. -/
theorem exists_pi1_compl_surjective (G : Type) [Group G] [Finite G] :
    ∃ (S : Finset ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ (S : Set ℂ)) (φ : Pi1Compl S z₀ hz₀ →* G),
      Function.Surjective φ := by
  classical
  set e : Fin (Nat.card G) ≃ G := (Finite.equivFin G).symm with he
  refine ⟨stdPunctures (Nat.card G), Complex.I, I_notMem_stdPunctures _, ?_, ?_⟩
  · exact (FreeGroup.lift (fun i : Fin (stdPunctures (Nat.card G)).card =>
      e (Fin.cast (stdPunctures_card (Nat.card G)) i))).comp
      (pi1_compl_finset (stdPunctures (Nat.card G)) Complex.I
        (I_notMem_stdPunctures _)).some.toMonoidHom
  · intro g
    refine ⟨(pi1_compl_finset (stdPunctures (Nat.card G)) Complex.I
      (I_notMem_stdPunctures _)).some.symm
        (FreeGroup.of (Fin.cast (stdPunctures_card (Nat.card G)).symm (e.symm g))), ?_⟩
    simp

/-- **The covers correspondence, with the topological fundamental group of a punctured plane.**

A finite group is realized by a geometric Galois cover of `ℙ¹_ℚ̄` iff it is a quotient of
`π₁(ℂ ∖ S)` for some finite `S`.  This is `riemann_existence_cover` transported across link **C**
(`pi1_compl_mulEquiv_sphereGroup`): the presentation group `Γ_{|S|+1}` on the right is replaced by
the fundamental group it presents. -/
theorem isGeometricGaloisCover_iff_pi1_compl {G : Type} [Group G] [Finite G] :
    IsGeometricGaloisCover G ↔
      ∃ (S : Finset ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ (S : Set ℂ)) (φ : Pi1Compl S z₀ hz₀ →* G),
        Function.Surjective φ := by
  refine ⟨fun _ => exists_pi1_compl_surjective G, ?_⟩
  rintro ⟨S, z₀, hz₀, φ, hφ⟩
  refine riemann_existence_cover_mpr ⟨S.card + 1,
    φ.comp (pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some.symm.toMonoidHom, ?_⟩
  exact hφ.comp (pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some.symm.surjective

/-- **The covers correspondence in profinite topological form.**  A finite group is realized by a
geometric Galois cover of `ℙ¹_ℚ̄` iff it is a finite continuous quotient of the profinite completion
of the fundamental group of a punctured plane.

This is the statement an étale-`π₁` development targets: the left-hand side is algebraic geometry
over `ℚ̄`, the right-hand side is the profinite completion of a genuinely topological group, and the
gap between them is exactly GAGA together with base change (links **B** and **L**). -/
theorem isGeometricGaloisCover_iff_pi1_compl_completion {G : Type} [Group G] [Finite G] :
    IsGeometricGaloisCover G ↔
      ∃ (S : Finset ℂ) (z₀ : ℂ) (hz₀ : z₀ ∉ (S : Set ℂ))
        (f : profiniteCompletion.obj (GrpCat.of (Pi1Compl S z₀ hz₀)) ⟶
          ProfiniteGrp.ofFiniteGrp (FiniteGrp.of G)),
        Function.Surjective (f : profiniteCompletion.obj (GrpCat.of (Pi1Compl S z₀ hz₀)) → _) := by
  rw [isGeometricGaloisCover_iff_pi1_compl]
  refine exists_congr fun S => exists_congr fun z₀ => exists_congr fun hz₀ => ?_
  exact (exists_surjective_completion_iff (A := GrpCat.of (Pi1Compl S z₀ hz₀)) (H := G)).symm

end Rigidity.RET
