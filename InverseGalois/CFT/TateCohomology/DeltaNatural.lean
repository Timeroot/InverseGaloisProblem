/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Graded

/-!
# The connecting map of the complete cohomology is natural

A map between two short exact sequences of representations induces a map of the two long exact
sequences of complete cohomology.  The squares built from the maps of the terms commute because the
maps of the terms are functorial in each degree; the squares built from the connecting maps commute
for a different reason in each of the five ranges in which the connecting map is defined.

Above degree zero and below degree minus two the connecting map is the one of the ordinary
cohomology or homology, and the square is the naturality of the connecting map of a map of short
exact sequences of complexes.  Out of degree zero the connecting map is the descent of the ordinary
one to the invariants modulo the norms, so the square follows from that same naturality once the
comparison of the cohomology in degree zero with the invariants is known to be natural.  Out of
degree minus two the connecting map is the corestriction of the ordinary one to the classes killed
by the norm, and the square follows in the same way from the naturality of the comparison of the
homology in degree zero with the coinvariants.

Out of degree minus one the connecting map is the snake of the ladder of the norms, and there is no
ordinary connecting map behind it.  A class in that degree is the class of a vector of the middle
whose norm comes from the sub; the map of sequences carries such a vector to another one, since it
carries the vector of the sub witnessing the norm to a witness for the image.  Both the source and
the target of the snake are computed from that vector, and both computations commute with the map,
the second one because the sub of the target is embedded.

## Main results

* `InverseGalois.CFT.Tate.deltaMid_naturality`: **the connecting map in degree minus one commutes
  with a map of short exact sequences.**
* `InverseGalois.CFT.Tate.tateδ_naturality_apply`, `InverseGalois.CFT.Tate.tateδ_naturality`:
  **the connecting map of the complete cohomology commutes with a map of short exact sequences**,
  in every integer degree.

## Tags

Tate cohomology, connecting homomorphism, naturality, long exact sequence
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  {X Y : ShortComplex (Rep k G)} (hX : X.ShortExact) (hY : Y.ShortExact) (φ : X ⟶ Y)

/-! ### The two commuting squares of the map of sequences -/

omit [Finite G] in
/-- The square of the sub and the middle commutes on vectors. -/
theorem comm₁₂_apply (a : X.X₁) :
    Y.f.hom.hom (φ.τ₁.hom.hom a) = φ.τ₂.hom.hom (X.f.hom.hom a) := by
  have h := congrArg (fun m : X.X₁ ⟶ Y.X₂ => m.hom.hom a) φ.comm₁₂
  simpa using h

omit [Finite G] in
/-- The square of the middle and the quotient commutes on vectors. -/
theorem comm₂₃_apply (b : X.X₂) :
    Y.g.hom.hom (φ.τ₂.hom.hom b) = φ.τ₃.hom.hom (X.g.hom.hom b) := by
  have h := congrArg (fun m : X.X₂ ⟶ Y.X₃ => m.hom.hom b) φ.comm₂₃
  simpa using h

/-! ### The connecting maps of the ordinary cohomology and homology -/

section Ordinary

omit [Finite G]

/-- **The connecting map of the ordinary cohomology commutes with a map of short exact
sequences.** -/
theorem groupCohomology_δ_naturality (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology.δ hX i j hij ≫ groupCohomology.map (MonoidHom.id G) φ.τ₁ j
      = groupCohomology.map (MonoidHom.id G) φ.τ₃ i ≫ groupCohomology.δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((groupCohomology.cochainsFunctor k G).mapShortComplex.map φ)
    (groupCohomology.map_cochainsFunctor_shortExact hX)
    (groupCohomology.map_cochainsFunctor_shortExact hY) i j hij

theorem groupCohomology_map_δ_apply (i j : ℕ) (hij : i + 1 = j) (z : groupCohomology X.X₃ i) :
    groupCohomology.map (MonoidHom.id G) φ.τ₁ j (groupCohomology.δ hX i j hij z)
      = groupCohomology.δ hY i j hij (groupCohomology.map (MonoidHom.id G) φ.τ₃ i z) := by
  have h := congrArg (fun m : groupCohomology X.X₃ i ⟶ groupCohomology Y.X₁ j => m z)
    (groupCohomology_δ_naturality hX hY φ i j hij)
  simpa only [CategoryTheory.comp_apply] using h

/-- **The connecting map of the ordinary homology commutes with a map of short exact
sequences.** -/
theorem groupHomology_δ_naturality (i j : ℕ) (hij : j + 1 = i) :
    groupHomology.δ hX i j hij ≫ groupHomology.map (MonoidHom.id G) φ.τ₁ j
      = groupHomology.map (MonoidHom.id G) φ.τ₃ i ≫ groupHomology.δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((groupHomology.chainsFunctor k G).mapShortComplex.map φ)
    (groupHomology.map_chainsFunctor_shortExact hX)
    (groupHomology.map_chainsFunctor_shortExact hY) i j hij

theorem groupHomology_map_δ_apply (i j : ℕ) (hij : j + 1 = i) (z : groupHomology X.X₃ i) :
    groupHomology.map (MonoidHom.id G) φ.τ₁ j (groupHomology.δ hX i j hij z)
      = groupHomology.δ hY i j hij (groupHomology.map (MonoidHom.id G) φ.τ₃ i z) := by
  have h := congrArg (fun m : groupHomology X.X₃ i ⟶ groupHomology Y.X₁ j => m z)
    (groupHomology_δ_naturality hX hY φ i j hij)
  simpa only [CategoryTheory.comp_apply] using h

end Ordinary

/-! ### The two junctions -/

/-- **The connecting map out of degree zero commutes with a map of short exact sequences.** -/
theorem H0toH1_naturality (w : H0 X.X₃.ρ) :
    groupCohomology.map (MonoidHom.id G) φ.τ₁ 1 (H0toH1 hX w)
      = H0toH1 hY (H0map φ.τ₃.hom.hom (hom_equivariant φ.τ₃) w) := by
  obtain ⟨z, rfl⟩ := H0mk_surjective X.X₃.ρ w
  rw [H0toH1_H0mk, H0map_H0mk, H0toH1_H0mk, ← map_H0Iso_inv φ.τ₃ z]
  exact groupCohomology_map_δ_apply hX hY φ 0 1 rfl _

/-- **The connecting map into degree minus one commutes with a map of short exact sequences.** -/
theorem H1toHm1_naturality (z : groupHomology X.X₃ 1) :
    Hm1map φ.τ₁.hom.hom (hom_equivariant φ.τ₁) (H1toHm1 hX z)
      = H1toHm1 hY (groupHomology.map (MonoidHom.id G) φ.τ₃ 1 z) := by
  refine Subtype.ext ?_
  rw [Hm1map_coe, H1toHm1_coe, H1toHm1_coe, ← map_homology_H0Iso_hom φ.τ₁,
    groupHomology_map_δ_apply hX hY φ 1 0 rfl]

/-! ### The snake of the ladder of the norms -/

section Snake

/-- A vector of the middle whose norm comes from the sub is carried to another such vector. -/
theorem mem_normSource_map (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    φ.τ₂.hom.hom (b : X.X₂) ∈ normSource Y.X₂.ρ Y.f.hom.hom := by
  obtain ⟨a, ha⟩ := mem_normSource_iff.1 b.2
  refine mem_normSource_iff.2 ⟨φ.τ₁.hom.hom a, ?_⟩
  rw [comm₁₂_apply φ a, ha]
  exact map_normMap φ.τ₂.hom.hom (hom_equivariant φ.τ₂) (b : X.X₂)

/-- The vectors of the middle whose norm comes from the sub, carried along the map of sequences. -/
def normSourceMap (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) : ↥(normSource Y.X₂.ρ Y.f.hom.hom) :=
  ⟨φ.τ₂.hom.hom (b : X.X₂), mem_normSource_map φ b⟩

/-- The class in degree minus one attached to such a vector is carried along the map of
sequences. -/
theorem toHm1_normSourceMap (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    Hm1map φ.τ₃.hom.hom (hom_equivariant φ.τ₃)
        (toHm1 X.f.hom.hom X.g.hom.hom (hom_equivariant X.g) (shortExact_range_eq_ker hX) b)
      = toHm1 Y.f.hom.hom Y.g.hom.hom (hom_equivariant Y.g) (shortExact_range_eq_ker hY)
        (normSourceMap φ b) := by
  refine Subtype.ext ?_
  rw [Hm1map_coe, toHm1_coe, toHm1_coe, Coinvariants.map_mk]
  exact congrArg (Coinvariants.mk Y.X₃.ρ) (comm₂₃_apply φ (b : X.X₂)).symm

/-- The class in degree zero attached to such a vector is carried along the map of sequences. -/
theorem toH0_normSourceMap (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    H0map φ.τ₁.hom.hom (hom_equivariant φ.τ₁)
        (toH0 X.f.hom.hom (hom_equivariant X.f) (shortExact_injective hX) b)
      = toH0 Y.f.hom.hom (hom_equivariant Y.f) (shortExact_injective hY) (normSourceMap φ b) := by
  rw [toH0_apply, H0map_H0mk, toH0_apply]
  refine congrArg (H0mk Y.X₁.ρ) (Subtype.ext ?_)
  rw [invariantsMap_coe, normDescentInv_coe, normDescentInv_coe]
  refine shortExact_injective hY ?_
  rw [comm₁₂_apply φ, f_normDescent, f_normDescent]
  exact map_normMap φ.τ₂.hom.hom (hom_equivariant φ.τ₂) (b : X.X₂)

/-- The snake of the ladder of the norms is computed from a vector of the middle whose norm comes
from the sub. -/
theorem deltaMid_toHm1 (b : ↥(normSource X.X₂.ρ X.f.hom.hom)) :
    deltaMid hX (toHm1 X.f.hom.hom X.g.hom.hom (hom_equivariant X.g)
        (shortExact_range_eq_ker hX) b)
      = toH0 X.f.hom.hom (hom_equivariant X.f) (shortExact_injective hX) b :=
  delta_toHm1 X.f.hom.hom (hom_equivariant X.f) X.g.hom.hom (hom_equivariant X.g)
    (shortExact_injective hX) (shortExact_surjective hX) (shortExact_range_eq_ker hX) b

/-- **The connecting map in degree minus one commutes with a map of short exact sequences.** -/
theorem deltaMid_naturality (u : Hm1 X.X₃.ρ) :
    H0map φ.τ₁.hom.hom (hom_equivariant φ.τ₁) (deltaMid hX u)
      = deltaMid hY (Hm1map φ.τ₃.hom.hom (hom_equivariant φ.τ₃) u) := by
  obtain ⟨b, rfl⟩ := toHm1_surjective X.f.hom.hom X.g.hom.hom (hom_equivariant X.g)
    (shortExact_surjective hX) (shortExact_range_eq_ker hX) u
  rw [deltaMid_toHm1 hX b, toHm1_normSourceMap hX hY φ b,
    deltaMid_toHm1 hY (normSourceMap φ b), toH0_normSourceMap hX hY φ b]

end Snake

/-! ### Every degree -/

/-- **The connecting map of the complete cohomology commutes with a map of short exact sequences**,
in every integer degree. -/
theorem tateδ_naturality_apply (n : ℤ) (w : ↥(tateModule X.X₃ n)) :
    tateMap φ.τ₁ (n + 1) (tateδ hX n w) = tateδ hY n (tateMap φ.τ₃ n w) := by
  match n with
  | .ofNat 0 => exact H0toH1_naturality hX hY φ w
  | .ofNat (m + 1) => exact groupCohomology_map_δ_apply hX hY φ (m + 1) (m + 2) rfl w
  | .negSucc 0 => exact deltaMid_naturality hX hY φ w
  | .negSucc 1 => exact H1toHm1_naturality hX hY φ w
  | .negSucc (m + 2) => exact groupHomology_map_δ_apply hX hY φ (m + 2) (m + 1) rfl w

/-- **The square of the connecting maps of the complete cohomology attached to a map of short exact
sequences commutes**, in every integer degree. -/
theorem tateδ_naturality (n : ℤ) :
    tateδ hX n ≫ tateMap φ.τ₁ (n + 1) = tateMap φ.τ₃ n ≫ tateδ hY n :=
  ModuleCat.hom_ext (LinearMap.ext fun w => tateδ_naturality_apply hX hY φ n w)

end

end InverseGalois.CFT.Tate
