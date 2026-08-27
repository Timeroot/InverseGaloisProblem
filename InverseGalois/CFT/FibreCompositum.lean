/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.RestrictLE

/-!
# The compositum of two solutions of one embedding problem

Two surjections `π₁ : G → G₁` and `π₂ : G → G₂` with trivially intersecting kernels present `G` as
a subgroup of `G₁ × G₂`, and when both quotients are further mapped onto a common group `H` by
maps that agree on `G`, that subgroup lies in the fibre product of `G₁` and `G₂` over `H`.  If the
kernels together are the kernel of the map to `H`, the two descriptions agree: `G` *is* the fibre
product.

The point of this description is that it is inherited by Galois groups.  If `E₁` and `E₂` are two
Galois extensions of a common Galois subextension `A`, with groups `G₁` and `G₂` over the group `H`
of `A`, then the Galois group of the compositum `E₁ ⊔ E₂` embeds in `G₁ × G₂` with image inside the
fibre product, and it surjects onto `G₁`.  A subgroup of the fibre product surjecting onto `G₁` is
everything as soon as the kernel of `π₁` consists of non-generating elements, which is the case in
the situation the Scholz–Reichardt induction produces, where both kernels lie in the Frattini
subgroup.  So the compositum of two solutions of the same embedding problem solves the problem
posed by the fibre product.

## Main definitions

* `InverseGalois.CFT.fibreProduct`: the fibre product of two groups over a common quotient.

## Main results

* `InverseGalois.CFT.range_prod_eq_fibreProduct`: **two surjections whose kernels intersect
  trivially and together exhaust the kernel of the map to the common quotient present the source as
  the fibre product.**
* `InverseGalois.CFT.eq_range_prod_of_le`: a subgroup of that fibre product surjecting onto the
  first factor is everything, when the kernel of the first surjection lies in the Frattini
  subgroup.
* `InverseGalois.CFT.exists_galEquiv_sup`: **the compositum of two solutions of one embedding
  problem realizes the fibre product**, compatibly with both of them.

## Tags

fibre product, compositum, embedding problem, Frattini subgroup, Galois group
-/

namespace InverseGalois.CFT

open Subgroup

section Group

variable {G G₁ G₂ H : Type*} [Group G] [Group G₁] [Group G₂] [Group H]
  {π₁ : G →* G₁} {π₂ : G →* G₂} {f₁ : G₁ →* H} {f₂ : G₂ →* H}

/-- The fibre product of two groups over a common quotient: the pairs whose two components have
the same image. -/
def fibreProduct (f₁ : G₁ →* H) (f₂ : G₂ →* H) : Subgroup (G₁ × G₂) :=
  (f₁.comp (MonoidHom.fst G₁ G₂)).eqLocus (f₂.comp (MonoidHom.snd G₁ G₂))

theorem mem_fibreProduct {x : G₁ × G₂} : x ∈ fibreProduct f₁ f₂ ↔ f₁ x.1 = f₂ x.2 :=
  Iff.rfl

/-- Two maps to a common quotient that agree on the source send the source into the fibre
product. -/
theorem range_prod_le_fibreProduct (hcomm : f₁.comp π₁ = f₂.comp π₂) :
    (π₁.prod π₂).range ≤ fibreProduct f₁ f₂ := by
  rintro _ ⟨g, rfl⟩
  show f₁ (π₁ g) = f₂ (π₂ g)
  exact DFunLike.congr_fun hcomm g

/-- When the two kernels together exhaust the kernel of the map to the common quotient, the kernel
of the second map to the quotient is the image of the first kernel. -/
theorem ker_eq_map_ker (hπ₂ : Function.Surjective π₂) (hcomm : f₁.comp π₁ = f₂.comp π₂)
    (hsup : (f₁.comp π₁).ker = π₁.ker ⊔ π₂.ker) : f₂.ker = π₁.ker.map π₂ := by
  have h1 : (f₂.comp π₂).ker = π₁.ker ⊔ π₂.ker := by rw [← hcomm]; exact hsup
  have h2 : f₂.ker = (f₂.comp π₂).ker.map π₂ := by
    rw [← MonoidHom.comap_ker, Subgroup.map_comap_eq_self_of_surjective hπ₂]
  have h3 : π₂.ker.map π₂ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  rw [h2, h1, Subgroup.map_sup, h3, sup_bot_eq]

/-- **Two surjections whose kernels intersect trivially and together exhaust the kernel of the map
to a common quotient present the source as the fibre product.** -/
theorem range_prod_eq_fibreProduct (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂)
    (hcomm : f₁.comp π₁ = f₂.comp π₂) (hsup : (f₁.comp π₁).ker = π₁.ker ⊔ π₂.ker) :
    (π₁.prod π₂).range = fibreProduct f₁ f₂ := by
  refine le_antisymm (range_prod_le_fibreProduct hcomm) ?_
  intro x hx
  rw [mem_fibreProduct] at hx
  obtain ⟨g, hg1⟩ := hπ₁ x.1
  have hcg : f₁ (π₁ g) = f₂ (π₂ g) := DFunLike.congr_fun hcomm g
  have hz : (π₂ g)⁻¹ * x.2 ∈ f₂.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hx, ← hg1, hcg, inv_mul_cancel]
  rw [ker_eq_map_ker hπ₂ hcomm hsup] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨g * w, Prod.ext ?_ ?_⟩
  · show π₁ (g * w) = x.1
    rw [map_mul, MonoidHom.mem_ker.mp hw, mul_one, hg1]
  · show π₂ (g * w) = x.2
    rw [map_mul, hwz, mul_inv_cancel_left]

/-- **A subgroup of the fibre product surjecting onto the first factor is everything**, when the
kernel of the first surjection consists of non-generating elements. -/
theorem eq_range_prod_of_le [Finite G] (hfr : π₁.ker ≤ frattini G)
    {U : Subgroup (G₁ × G₂)} (hle : U ≤ (π₁.prod π₂).range)
    (hfst : ∀ g₁ : G₁, ∃ x ∈ U, (x : G₁ × G₂).1 = g₁) : U = (π₁.prod π₂).range := by
  refine le_antisymm hle ?_
  have hV : U.comap (π₁.prod π₂) ⊔ π₁.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, hxU, hx1⟩ := hfst (π₁ g)
    obtain ⟨w, hw⟩ := hle hxU
    have hwV : w ∈ U.comap (π₁.prod π₂) := by
      rw [Subgroup.mem_comap, hw]
      exact hxU
    have hw1 : π₁ w = π₁ g := by
      rw [← hx1, ← hw]
      rfl
    have hmem : w⁻¹ * g ∈ π₁.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hw1, inv_mul_cancel]
    have hg := Subgroup.mul_mem_sup hwV hmem
    rwa [mul_inv_cancel_left] at hg
  have htop : U.comap (π₁.prod π₂) = ⊤ :=
    frattini_nongenerating (eq_top_iff.mpr (hV.ge.trans (sup_le_sup_left hfr _)))
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ U.comap (π₁.prod π₂) := by rw [htop]; trivial
  exact hg

end Group

section Field

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **Restricting an automorphism to the field it already lives on does nothing.** -/
theorem galRestrictLE_refl {E : IntermediateField F L} [Normal F ↥E] (σ : Gal(↥E/F)) :
    galRestrictLE le_rfl σ = σ := by
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [coe_galRestrictLE le_rfl σ x]

/-- Restricting an automorphism of a compositum to the two factors, which are normal over the
base, determines it. -/
theorem galRestrictLE_prod_injective (A B : IntermediateField F L) [Normal F ↥A] [Normal F ↥B] :
    Function.Injective ((galRestrictLE (le_sup_left : A ≤ A ⊔ B)).prod
      (galRestrictLE (le_sup_right : B ≤ A ⊔ B))) :=
  galRestrictProd_injective A B

variable {A E₁ E₂ : IntermediateField F L}

/-- **The compositum of two solutions of one embedding problem realizes the fibre product of the
two solving groups**, compatibly with both solutions. -/
theorem exists_galEquiv_sup {G G₁ G₂ H : Type*} [Group G] [Group G₁] [Group G₂] [Group H]
    [Finite G] {π₁ : G →* G₁} {π₂ : G →* G₂} (hπ₁ : Function.Surjective π₁)
    (hπ₂ : Function.Surjective π₂) {f₁ : G₁ →* H} {f₂ : G₂ →* H} (hcomm : f₁.comp π₁ = f₂.comp π₂)
    (hinf : π₁.ker ⊓ π₂.ker = ⊥) (hsup : (f₁.comp π₁).ker = π₁.ker ⊔ π₂.ker)
    (hfr : π₁.ker ≤ frattini G) (h₁ : A ≤ E₁) (h₂ : A ≤ E₂) [Normal F ↥A] [IsGalois F ↥E₁]
    [IsGalois F ↥E₂] [FiniteDimensional F ↥E₁] [FiniteDimensional F ↥E₂] (e : Gal(↥A/F) ≃* H)
    (e₁ : Gal(↥E₁/F) ≃* G₁) (e₂ : Gal(↥E₂/F) ≃* G₂)
    (he₁ : ∀ σ, f₁ (e₁ σ) = e (galRestrictLE h₁ σ))
    (he₂ : ∀ σ, f₂ (e₂ σ) = e (galRestrictLE h₂ σ)) :
    ∃ ψ : Gal(↥(E₁ ⊔ E₂)/F) ≃* G,
      (∀ σ, π₁ (ψ σ) = e₁ (galRestrictLE (le_sup_left : E₁ ≤ E₁ ⊔ E₂) σ)) ∧
      (∀ σ, π₂ (ψ σ) = e₂ (galRestrictLE (le_sup_right : E₂ ≤ E₁ ⊔ E₂) σ)) := by
  classical
  set r₁ := galRestrictLE (le_sup_left : E₁ ≤ E₁ ⊔ E₂) with hr₁
  set r₂ := galRestrictLE (le_sup_right : E₂ ≤ E₁ ⊔ E₂) with hr₂
  set u : Gal(↥(E₁ ⊔ E₂)/F) →* G₁ × G₂ :=
    (e₁.toMonoidHom.comp r₁).prod (e₂.toMonoidHom.comp r₂) with hu_def
  have hu : Function.Injective u := by
    intro σ τ hστ
    refine galRestrictLE_prod_injective E₁ E₂ (Prod.ext ?_ ?_)
    · exact e₁.injective (congrArg Prod.fst hστ)
    · exact e₂.injective (congrArg Prod.snd hστ)
  have hv : Function.Injective (π₁.prod π₂) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_prod, hinf]
  have hrange : u.range = (π₁.prod π₂).range := by
    refine eq_range_prod_of_le hfr ?_ ?_
    · rw [range_prod_eq_fibreProduct hπ₁ hπ₂ hcomm hsup]
      rintro _ ⟨σ, rfl⟩
      show f₁ (e₁ (r₁ σ)) = f₂ (e₂ (r₂ σ))
      rw [he₁, he₂, hr₁, hr₂, galRestrictLE_galRestrictLE, galRestrictLE_galRestrictLE]
    · intro g₁
      obtain ⟨σ, hσ⟩ := galRestrictLE_surjective (le_sup_left : E₁ ≤ E₁ ⊔ E₂) (e₁.symm g₁)
      refine ⟨u σ, ⟨σ, rfl⟩, ?_⟩
      show e₁ (r₁ σ) = g₁
      rw [hr₁, hσ, e₁.apply_symm_apply]
  refine ⟨((MonoidHom.ofInjective hu).trans (MulEquiv.subgroupCongr hrange)).trans
    (MonoidHom.ofInjective hv).symm, ?_, ?_⟩ <;> intro σ
  · exact congrArg Prod.fst (MonoidHom.apply_ofInjective_symm hv _)
  · exact congrArg Prod.snd (MonoidHom.apply_ofInjective_symm hv _)

end Field

end InverseGalois.CFT
