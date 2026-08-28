/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CentralLift
import InverseGalois.CFT.GroupCohomology.CoprimeSplit

/-!
# Descending a solved embedding problem along a subgroup of coprime index

An embedding problem is a surjection `π : Γ → H` of finite groups together with a surjection
`f : G → H` whose kernel is central; a solution is a homomorphism `Γ → G` lifting `π`.  If the
problem is solved after restricting `π` to a subgroup `U` of `Γ` whose index is coprime to the
order of the kernel, then it is solved over `Γ` itself.

The mechanism is the pullback `E = Γ ×_H G`, a central extension of `Γ` by the kernel of `f`.  A
solution over `U` is exactly a section of that extension over `U`, and a section over a subgroup of
coprime index extends to a section over the whole group by the transfer argument of
`InverseGalois.CFT.exists_splitting_of_coprime_index`.

This is the group-theoretic form of the descent from `ℚ(μ_ℓ)` back to `ℚ`: the Kummer-theoretic
solution of a central embedding problem with kernel of order `ℓ` needs the `ℓ`-th roots of unity in
the base, and the degree of that adjunction divides `ℓ - 1`.

## Main results

* `InverseGalois.CFT.exists_hom_comp_eq_of_coprime_index`: **an embedding problem with central
  kernel that is solved over a subgroup of coprime index is solved.**
* `InverseGalois.CFT.exists_surjective_hom_comp_eq_of_coprime_index`: the solution is surjective
  when the kernel lies in the Frattini subgroup.

## Tags

embedding problem, central extension, transfer, coprime index, descent
-/

namespace InverseGalois.CFT

open Subgroup

variable {Γ G H : Type*} [Group Γ] [Group G] [Group H] [Finite Γ] [Finite G]

/-- The pullback `Γ ×_H G` of an embedding problem, realised as the subgroup of the product on
which the two maps to `H` agree. -/
def embeddingPullback (f : G →* H) (π : Γ →* H) : Subgroup (Γ × G) :=
  (π.comp (MonoidHom.fst Γ G)).eqLocus (f.comp (MonoidHom.snd Γ G))

omit [Finite Γ] [Finite G] in
theorem mem_embeddingPullback {f : G →* H} {π : Γ →* H} {p : Γ × G} :
    p ∈ embeddingPullback f π ↔ π p.1 = f p.2 :=
  Iff.rfl

/-- The projection of the pullback onto the first factor. -/
def embeddingPullbackFst (f : G →* H) (π : Γ →* H) : ↥(embeddingPullback f π) →* Γ :=
  (MonoidHom.fst Γ G).comp (embeddingPullback f π).subtype

omit [Finite Γ] [Finite G] in
@[simp]
theorem embeddingPullbackFst_apply {f : G →* H} {π : Γ →* H} (p : ↥(embeddingPullback f π)) :
    embeddingPullbackFst f π p = (p : Γ × G).1 :=
  rfl

omit [Finite Γ] [Finite G] in
/-- The projection of the pullback onto the first factor is surjective when `f` is. -/
theorem surjective_embeddingPullbackFst {f : G →* H} (hf : Function.Surjective f)
    (π : Γ →* H) : Function.Surjective (embeddingPullbackFst f π) := by
  intro x
  obtain ⟨g, hg⟩ := hf (π x)
  exact ⟨⟨(x, g), by rw [mem_embeddingPullback, hg]⟩, rfl⟩

/-- The kernel of the projection of the pullback onto the first factor is the kernel of `f`. -/
noncomputable def embeddingPullbackKerEquiv (f : G →* H) (π : Γ →* H) :
    ↥f.ker ≃* ↥(embeddingPullbackFst f π).ker where
  toFun z := ⟨⟨(1, (z : G)), by
    rw [mem_embeddingPullback]
    show π 1 = f (z : G)
    rw [map_one, MonoidHom.mem_ker.mp z.2]⟩, rfl⟩
  invFun w := ⟨((w : ↥(embeddingPullback f π)) : Γ × G).2, by
    have hmem := (w : ↥(embeddingPullback f π)).2
    rw [mem_embeddingPullback] at hmem
    have hone : ((w : ↥(embeddingPullback f π)) : Γ × G).1 = 1 := w.2
    rw [MonoidHom.mem_ker, ← hmem, hone, map_one]⟩
  left_inv z := rfl
  right_inv w := by
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
    exact w.2.symm
  map_mul' z z' := Subtype.ext (Subtype.ext (Prod.ext (one_mul 1).symm rfl))

omit [Finite Γ] [Finite G] in
/-- The kernel of the projection of the pullback onto the first factor is central. -/
theorem embeddingPullbackKer_le_center {f : G →* H} (hZ : f.ker ≤ Subgroup.center G)
    (π : Γ →* H) :
    (embeddingPullbackFst f π).ker ≤ Subgroup.center ↥(embeddingPullback f π) := by
  intro w hw
  have hmem := (w : ↥(embeddingPullback f π)).2
  rw [mem_embeddingPullback] at hmem
  have h1 : ((w : ↥(embeddingPullback f π)) : Γ × G).1 = 1 := hw
  have hker : ((w : ↥(embeddingPullback f π)) : Γ × G).2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, ← hmem, h1, map_one]
  rw [Subgroup.mem_center_iff]
  intro x
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show ((x : Γ × G).1) * ((w : Γ × G).1) = ((w : Γ × G).1) * ((x : Γ × G).1)
    rw [h1, one_mul, mul_one]
  · show ((x : Γ × G).2) * ((w : Γ × G).2) = ((w : Γ × G).2) * ((x : Γ × G).2)
    exact (Subgroup.mem_center_iff.1 (hZ hker)) _

/-- **An embedding problem with central kernel that is solved over a subgroup whose index is
coprime to the order of the kernel is solved.**  A solution over the subgroup is a section of the
pullback extension over that subgroup, and the transfer extends it to a section over the whole
group. -/
theorem exists_hom_comp_eq_of_coprime_index
    {f : G →* H} (hf : Function.Surjective f) (hZ : f.ker ≤ Subgroup.center G)
    (π : Γ →* H) {U : Subgroup Γ} (hcop : Nat.Coprime U.index (Nat.card ↥f.ker))
    (s : ↥U →* G) (hs : ∀ u : ↥U, f (s u) = π u) :
    ∃ ψ : Γ →* G, ∀ x, f (ψ x) = π x := by
  classical
  have hcard : Nat.card ↥(embeddingPullbackFst f π).ker = Nat.card ↥f.ker :=
    (Nat.card_congr (embeddingPullbackKerEquiv f π).toEquiv).symm
  obtain ⟨σ, hσ⟩ := exists_splitting_of_coprime_index (embeddingPullbackFst f π)
    (surjective_embeddingPullbackFst hf π) (embeddingPullbackKer_le_center hZ π)
    (U := U) (by rwa [hcard])
    ((U.subtype.prod s).codRestrict (embeddingPullback f π)
      (fun u => by rw [mem_embeddingPullback]; exact (hs u).symm))
    (fun _ => rfl)
  refine ⟨((MonoidHom.snd Γ G).comp (embeddingPullback f π).subtype).comp σ, fun x => ?_⟩
  have hmem := (σ x).2
  rw [mem_embeddingPullback] at hmem
  have hfst : ((σ x : ↥(embeddingPullback f π)) : Γ × G).1 = x := hσ x
  show f ((σ x : ↥(embeddingPullback f π)) : Γ × G).2 = π x
  rw [← hmem, hfst]

/-- **An embedding problem with a central kernel inside the Frattini subgroup that is solved over a
subgroup whose index is coprime to the order of the kernel has a surjective solution.** -/
theorem exists_surjective_hom_comp_eq_of_coprime_index
    {f : G →* H} (hf : Function.Surjective f) (hZ : f.ker ≤ Subgroup.center G)
    (hfr : f.ker ≤ frattini G) {π : Γ →* H} (hπ : Function.Surjective π)
    {U : Subgroup Γ} (hcop : Nat.Coprime U.index (Nat.card ↥f.ker))
    (s : ↥U →* G) (hs : ∀ u : ↥U, f (s u) = π u) :
    ∃ ψ : Γ →* G, Function.Surjective ψ ∧ ∀ x, f (ψ x) = π x := by
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_of_coprime_index hf hZ π hcop s hs
  exact ⟨ψ, surjective_of_le_frattini hfr hπ hψ, hψ⟩

end InverseGalois.CFT
