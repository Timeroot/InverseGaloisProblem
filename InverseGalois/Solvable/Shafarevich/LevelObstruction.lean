/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.EmbeddingClass
import InverseGalois.Solvable.Shafarevich.LayerSection
import InverseGalois.Solvable.Shafarevich.LevelSolution

/-!
# What a solution at one level buys for the step to the next

A solution at one level of the filtration carries two pieces of data beyond being a surjection: it
projects onto the fixed base realization, and it is trivial on a prescribed family of subgroups
wherever the base realization is.  Together those two say that the projection onto the operator
group is injective on each member of the family and has a prescribed image there, which is exactly
the input the shrinking count consumes: a subgroup on which the projection is injective is carried
isomorphically onto a subgroup downstairs settled by the base realization alone, so the count may
be run before the solution at the level is chosen, and the number of letters it asks for does not
depend on which solution is produced.

Running the count therefore turns a solution at one level, for every number of letters, into a
single solution at that level whose lifting obstruction to the next level dies on every member of
the family: the class of the extension one layer gives already dies on the images of those
subgroups, and an obstruction which is inflated from a class already trivial upstairs is trivial.
The obstruction of the step is thus an everywhere locally trivial class, and what is left of the
step is to make such classes vanish.

Both statements are proved here, the first over an arbitrary abstract group, since nothing about a
Galois group is used until the obstruction itself is formed.

## Main results

* `InverseGalois.Shafarevich.exists_operatorHom_forall_exists_subgroup_resH2_extensionClass_eq_one`
  — **a homomorphism over the operator group which is trivial on a family of subgroups wherever the
  operator map is meets, after one shrinking, a subgroup over which the extension of the layer
  splits.**
* `InverseGalois.Shafarevich.exists_levelSolution_liftObstructionClass_mem_sha2` — **solutions at
  one level for every number of letters give a single solution whose obstruction to the next level
  is everywhere locally trivial.**

## Tags

Shafarevich's theorem, embedding problem, obstruction, p-central series, decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

attribute [local instance] genericQuotAction

/-! ### Splitting over the image of a completely decomposed subgroup -/

/-- **A homomorphism over the operator group which is trivial on a family of subgroups wherever the
operator map is meets, after one shrinking, a subgroup over which the extension given by one layer
splits.**

The family of subgroups downstairs is the image of the given one under the operator map, and it is
settled before the count is run; the subgroups upstairs are produced afterwards by whatever
homomorphism over the operator map one happens to have.  Being trivial on a member of the family
wherever the operator map is says precisely that the projection is injective there, so the member
is carried isomorphically onto its image downstairs. -/
theorem exists_operatorHom_forall_exists_subgroup_resH2_extensionClass_eq_one (ℓ : ℕ)
    [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U] [DiscreteTopology U]
    (n : ℕ) (S : Type) [Group S] [Finite S] (hS : IsPGroup ℓ S) (j : ℕ) {Γ : Type*} [Group Γ]
    (φ : Γ →* U) {t : ℕ} (D : Fin t → Subgroup Γ)
    (σn : (layerExtension ℓ (genericAut U n S) j).Section) :
    ∃ m : ℕ, ∀ Φ : Γ →* GenericQuot ℓ U m S j,
      (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) →
      (∀ (ν : Fin t), ∀ x ∈ D ν, φ x = 1 → Φ x = 1) →
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ A ∈ Set.range D, ∃ H : Subgroup (GenericQuot ℓ U n S j),
          (∀ d : ↥A, ((layerSemidirectMap ℓ hα j).comp Φ) (d : Γ) ∈ H) ∧
            resH2 H (extensionClass (layerExtension ℓ (genericAut U n S) j)
              (smul_eq_conjActHom_genericLayer ℓ U n S j) σn) = 1 := by
  obtain ⟨m, hm⟩ := exists_operatorHom_forall_resH2_extensionClass_subgroup_eq_one ℓ U n S hS j t
    (fun ν => (D ν).map φ) σn
  refine ⟨m, fun Φ hright hloc => ?_⟩
  have hcomp : (SemidirectProduct.rightHom : GenericQuot ℓ U m S j →* U).comp Φ = φ :=
    MonoidHom.ext hright
  have hinj : ∀ (ν : Fin t), ∀ x ∈ (D ν).map Φ,
      SemidirectProduct.rightHom x = (1 : U) → x = 1 := by
    intro ν x hx hx1
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
    exact hloc ν d hd ((hright d).symm.trans hx1)
  have hmap : ∀ ν : Fin t, ((D ν).map Φ).map
      (SemidirectProduct.rightHom : GenericQuot ℓ U m S j →* U) = (D ν).map φ := by
    intro ν
    rw [Subgroup.map_map, hcomp]
  obtain ⟨α, hα, hαsurj, hkill⟩ := hm (fun ν => (D ν).map Φ) hinj hmap
  refine ⟨α, hα, hαsurj, ?_⟩
  rintro _ ⟨ν, rfl⟩
  exact ⟨((D ν).map Φ).map (layerSemidirectMap ℓ hα j),
    fun d => Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ d.2), hkill ν⟩

/-! ### The obstruction of the step is everywhere locally trivial -/

/-- **Solutions at one level of the filtration for every number of letters give a single solution
whose obstruction to the next level is everywhere locally trivial.**

The count which makes the class of the extension die on the prescribed family asks for some number
of letters; a solution is available at that number, and the count then produces a surjection onto
the group with fewer letters over which the class does die.  The obstruction of the step is
inflated from that class, so it dies on the family too, and the whole of what is left of the step
is to make an everywhere locally trivial class vanish. -/
theorem exists_levelSolution_liftObstructionClass_mem_sha2 (ℓ : ℕ) [Fact ℓ.Prime] (U : Type)
    [Group U] [Finite U] [TopologicalSpace U] [DiscreteTopology U] (n : ℕ) (S : Type) [Group S]
    [Finite S] (hS : IsPGroup ℓ S) (j : ℕ) {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (φ : Gal(Ω/k) →* U) [MulDistribMulAction Gal(Ω/k) ↥(layerSub ℓ (Generic U n S) j)] {t : ℕ}
    (D : Fin t → Subgroup Gal(Ω/k)) (σn : (layerExtension ℓ (genericAut U n S) j).Section)
    (h : ∀ m : ℕ, LevelSolution ℓ U S φ (Set.range D) m j) :
    ∃ Φ : Gal(Ω/k) →* GenericQuot ℓ U n S j, Function.Surjective Φ ∧ IsSmoothHom Φ ∧
      (∀ x, SemidirectProduct.rightHom (Φ x) = φ x) ∧
      (∀ A ∈ Set.range D, ∀ x ∈ A, φ x = 1 → Φ x = 1) ∧
      ∀ (hact : ∀ (x : Gal(Ω/k)) (v : ↥(layerSub ℓ (Generic U n S) j)),
            x • v = (layerExtension ℓ (genericAut U n S) j).conjActHom (Φ x) v)
          (hker : IsOpenNormal Φ.ker),
        liftObstructionClass (layerExtension ℓ (genericAut U n S) j) Φ hact hker σn
          ∈ sha2 ↥(layerSub ℓ (Generic U n S) j) (Set.range D) := by
  obtain ⟨m, hm⟩ :=
    exists_operatorHom_forall_exists_subgroup_resH2_extensionClass_eq_one ℓ U n S hS j φ D σn
  obtain ⟨Φ₀, hsurj, hsm, hright, hloc⟩ := h m
  obtain ⟨α, hα, hαsurj, hres⟩ := hm Φ₀ hright fun ν => hloc (D ν) ⟨ν, rfl⟩
  refine ⟨(layerSemidirectMap ℓ hα j).comp Φ₀,
    (layerSemidirectMap_surjective ℓ hα j hαsurj).comp hsurj,
    isSmoothHom_comp hsm (isSmoothHom_of_continuous continuous_of_discreteTopology),
    fun x => hright x, ?_, fun hact hker => ?_⟩
  · rintro _ ⟨ν, rfl⟩ x hx hx1
    show layerSemidirectMap ℓ hα j (Φ₀ x) = 1
    rw [hloc (D ν) ⟨ν, rfl⟩ x hx hx1, _root_.map_one]
  · exact liftObstructionClass_mem_sha2_of_extensionClass
      (layerExtension ℓ (genericAut U n S) j) ((layerSemidirectMap ℓ hα j).comp Φ₀)
      (smul_eq_conjActHom_genericLayer ℓ U n S j) hact hker σn hres

end InverseGalois.Shafarevich
