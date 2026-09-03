/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyOrbit
import InverseGalois.CFT.TateCohomology.Functorial
import InverseGalois.CFT.TateCohomology.Shapiro
import InverseGalois.CFT.Units.IdeleRep

/-!
# The sections of a family over an orbit are coinduced

A family of modules indexed by a set on which a group acts transitively is determined by the module
at one chosen base point together with the action there of the stabiliser of that point.  The
identification is the one that arithmetic uses without naming it: a section is remembered by the
function on the group sending an element to the value, at the base point, of the translated section.
That function is equivariant for the stabiliser, every equivariant function arises from exactly one
section, and translating a section translates the function; so the sections of the family are the
representation coinduced from the module at the base point.

Coinduction is transparent to complete cohomology, and the two statements together compute the
complete cohomology of the sections of a family over a transitive orbit as the complete cohomology
of the stabiliser of a base point with coefficients in the module there.  For the family of local
factors of the group of ideles at the places above a place of the base field, the stabiliser is the
decomposition group and the module is the local factor at one place above it: this is the reason the
cohomology of the ideles is a product of local contributions, one for each place of the base field.

## Main definitions

* `InverseGalois.CFT.orbitSectionsRep`: the sections of a family, as a representation of the group.
* `InverseGalois.CFT.orbitStabRep`: the module at the base point, as a representation of the
  stabiliser of that point.

## Main results

* `InverseGalois.CFT.orbitCoindEquiv`: **the sections of a family over a transitive orbit are the
  functions equivariant for the stabiliser of the base point.**
* `InverseGalois.CFT.orbitCoindIso`: **the sections of a family over a transitive orbit are
  coinduced from the stabiliser of the base point.**
* `InverseGalois.CFT.orbitTateEquiv`: **the complete cohomology of the sections of a family over a
  transitive orbit is the complete cohomology of the stabiliser of the base point with coefficients
  in the module there.**

## Tags

Tate cohomology, Shapiro's lemma, coinduced representation, orbit, decomposition group, idele
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

noncomputable section

variable {G X : Type} [Group G] [MulAction G X] (x₀ : X)
  (htrans : ∀ y : X, ∃ g : G, g • y = x₀)
  {M : X → Type} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)

/-! ### The two representations -/

/-- The sections of a family, as a representation of the group. -/
def orbitSectionsRep : Rep ℤ G := repOfAddAut F.familyAut

@[simp]
theorem orbitSectionsRep_ρ_apply (g : G) (u : ∀ x, M x) :
    (orbitSectionsRep F).ρ g u = F.familyAut g u := rfl

/-- The module at the base point, as a representation of the stabiliser of that point. -/
def orbitStabRep : Rep ℤ ↥(stabilizer G x₀) :=
  repOfAddAut (stabAut x₀ (fun s : ↥(stabilizer G x₀) => s.2) F)

theorem orbitStabRep_ρ_apply (s : ↥(stabilizer G x₀)) (a : M x₀) :
    (orbitStabRep x₀ F).ρ s a = F.transport (s.2 : (s : G) • x₀ = x₀) a := rfl

/-! ### The equivariant function attached to a section -/

/-- The function on the group sending an element to the value at the base point of the translated
section. -/
def orbitCoindFun (u : ∀ x, M x) : G → M x₀ := fun g => F.familyAut g u x₀

/-- **The function attached to a section is equivariant for the stabiliser of the base point.** -/
theorem orbitCoindFun_mem (u : ∀ x, M x) :
    orbitCoindFun x₀ F u ∈ Representation.coindV (stabilizer G x₀).subtype
      (orbitStabRep x₀ F).ρ := by
  intro s g
  show F.familyAut ((s : G) * g) u x₀ = (orbitStabRep x₀ F).ρ s (F.familyAut g u x₀)
  rw [map_mul, AddAut.mul_apply, orbitStabRep_ρ_apply]
  exact F.familyAut_apply_eq_transport (s.2 : (s : G) • x₀ = x₀) _

/-- The equivariant function attached to a section, as a map of additive groups. -/
def orbitCoindHom : (∀ x, M x) →+
    ↥(Representation.coindV (stabilizer G x₀).subtype (orbitStabRep x₀ F).ρ) where
  toFun u := ⟨orbitCoindFun x₀ F u, orbitCoindFun_mem x₀ F u⟩
  map_zero' := Subtype.ext (funext fun g => congrFun (map_zero (F.familyAut g)) x₀)
  map_add' u v := Subtype.ext (funext fun g => congrFun (map_add (F.familyAut g) u v) x₀)

theorem orbitCoindHom_coe (u : ∀ x, M x) (g : G) :
    (orbitCoindHom x₀ F u).val g = F.familyAut g u x₀ := rfl

/-! ### The identification -/

include htrans in
/-- **A section is determined by the values at the base point of its translates**, when the action
on the index set is transitive. -/
theorem orbitCoindHom_injective : Function.Injective (orbitCoindHom x₀ F) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  refine funext fun x => ?_
  obtain ⟨g, hg⟩ := htrans x
  have h : F.familyAut g u x₀ = 0 := congrFun (congrArg Subtype.val hu) g
  rw [F.familyAut_apply_eq_transport hg u] at h
  exact (map_eq_zero_iff (F.transport hg) (F.transport hg).injective).1 h

include htrans in
/-- **Every function equivariant for the stabiliser of the base point comes from a section**, when
the action on the index set is transitive.  The section takes at an index the value transported back
from the base point along a group element carrying the index there; the equivariance makes the
result independent of that element. -/
theorem orbitCoindHom_surjective : Function.Surjective (orbitCoindHom x₀ F) := by
  rintro ⟨f, hf⟩
  have hf' := (Tate.mem_coindV_iff (orbitStabRep x₀ F).ρ f).1 hf
  choose c hc using htrans
  refine ⟨fun y => (F.transport (hc y)).symm (f (c y)), Subtype.ext (funext fun h => ?_)⟩
  have hh : h • (h⁻¹ • x₀) = x₀ := smul_inv_smul h x₀
  have hs : (h * (c (h⁻¹ • x₀))⁻¹) • x₀ = x₀ := by
    rw [mul_smul, inv_smul_eq_iff.2 (hc (h⁻¹ • x₀)).symm, hh]
  have h₃ : ((h * (c (h⁻¹ • x₀))⁻¹) * c (h⁻¹ • x₀)) • (h⁻¹ • x₀) = x₀ := by
    rw [inv_mul_cancel_right]
    exact hh
  have hfh : f h = F.transport hs (f (c (h⁻¹ • x₀))) := by
    have hcv := hf' ⟨_, hs⟩ (c (h⁻¹ • x₀))
    rw [inv_mul_cancel_right] at hcv
    rw [hcv, orbitStabRep_ρ_apply]
  have hb : f (c (h⁻¹ • x₀))
      = F.transport (hc (h⁻¹ • x₀))
          ((F.transport (hc (h⁻¹ • x₀))).symm (f (c (h⁻¹ • x₀)))) :=
    ((F.transport (hc (h⁻¹ • x₀))).apply_symm_apply _).symm
  show F.familyAut h _ x₀ = f h
  rw [F.familyAut_apply_eq_transport hh, hfh]
  conv_rhs => rw [hb]
  rw [F.transport_trans (hc (h⁻¹ • x₀)) hs h₃]
  exact (F.transport_congr (inv_mul_cancel_right h (c (h⁻¹ • x₀))) h₃ hh _).symm

/-- **The sections of a family over a transitive orbit are the functions equivariant for the
stabiliser of the base point.** -/
def orbitCoindEquiv : (∀ x, M x) ≃ₗ[ℤ]
    ↥(Representation.coindV (stabilizer G x₀).subtype (orbitStabRep x₀ F).ρ) :=
  (AddEquiv.ofBijective (orbitCoindHom x₀ F)
    ⟨orbitCoindHom_injective x₀ htrans F, orbitCoindHom_surjective x₀ htrans F⟩).toIntLinearEquiv

theorem orbitCoindEquiv_apply (u : ∀ x, M x) (g : G) :
    (orbitCoindEquiv x₀ htrans F u).val g = F.familyAut g u x₀ := rfl

/-- **The sections of a family over a transitive orbit are coinduced from the stabiliser of the
base point.** -/
def orbitCoindIso :
    orbitSectionsRep F ≅ Rep.coind (stabilizer G x₀).subtype (orbitStabRep x₀ F) :=
  Action.mkIso (orbitCoindEquiv x₀ htrans F).toModuleIso fun g => by
    ext u h
    show F.familyAut h (F.familyAut g u) x₀ = F.familyAut (h * g) u x₀
    rw [map_mul, AddAut.mul_apply]

variable [Finite G]

/-- **The complete cohomology of the sections of a family over a transitive orbit is the complete
cohomology of the stabiliser of the base point with coefficients in the module there.** -/
def orbitTateEquiv (n : ℤ) :
    tateModule (orbitSectionsRep F) n ≃ₗ[ℤ] tateModule (orbitStabRep x₀ F) n :=
  (tateMapIso (orbitCoindIso x₀ htrans F) n).toLinearEquiv.trans
    (tateShapiroEquiv (orbitStabRep x₀ F) n)

end

end InverseGalois.CFT
