/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Graded
import InverseGalois.CFT.TateCohomology.Induced

/-!
# The functions on a group have no complete cohomology

The representation on the functions from a group to a module that translates the argument is the
one coinduced from the trivial subgroup: the condition of equivariance for the trivial subgroup is
empty, so the coinduced module is the whole of the functions on the group, and the two actions
translate the argument in the same way.  Shapiro's lemma therefore computes the cohomology of the
functions on the group as the cohomology of the trivial group, which vanishes above degree zero.
For a finite group the coinduced and the induced representation agree, so the same argument
computes the homology.  Together with the vanishing of the two middle groups this says that the
complete cohomology of the functions on the group vanishes in every integer degree.

A short exact sequence whose middle term has no complete cohomology therefore has a bijective
connecting map in every degree: this is the mechanism of dimension shifting, which moves a
statement about the complete cohomology in one degree to the neighbouring degree.

## Main definitions

* `InverseGalois.CFT.Tate.coindBotIso`: the identification of the functions on the group with the
  representation coinduced from the trivial subgroup.

## Main results

* `InverseGalois.CFT.Tate.isZero_tateModule_inducedRep`: **the complete cohomology of the functions
  on the group vanishes in every integer degree.**
* `InverseGalois.CFT.Tate.bijective_tateδ`: **the connecting map of a short exact sequence whose
  middle term has no complete cohomology is bijective.**

## Tags

Tate cohomology, coinduced representation, Shapiro's lemma, dimension shifting
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G M : Type u} [CommRing k] [Group G] [AddCommGroup M] [Module k M]

/-! ### Coinduction from the trivial subgroup -/

/-- Every function on the group is equivariant for the trivial subgroup. -/
theorem coindV_bot_eq_top :
    Representation.coindV (⊥ : Subgroup G).subtype
        (Rep.trivial k ↥(⊥ : Subgroup G) M).ρ = ⊤ := by
  refine eq_top_iff.2 fun f _ g h => ?_
  obtain ⟨g, hg⟩ := g
  rw [Subgroup.mem_bot] at hg
  subst hg
  simp

/-- **The functions equivariant for the trivial subgroup are all of the functions on the group.** -/
def coindBotEquiv :
    ↥(Representation.coindV (⊥ : Subgroup G).subtype
      (Rep.trivial k ↥(⊥ : Subgroup G) M).ρ) ≃ₗ[k] (G → M) :=
  (LinearEquiv.ofEq _ _ coindV_bot_eq_top).trans Submodule.topEquiv

theorem coindBotEquiv_apply
    (f : ↥(Representation.coindV (⊥ : Subgroup G).subtype
      (Rep.trivial k ↥(⊥ : Subgroup G) M).ρ)) :
    coindBotEquiv f = (f : G → M) := rfl

/-- **The functions on the group are coinduced from the trivial subgroup.** -/
def coindBotIso :
    Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k ↥(⊥ : Subgroup G) M)
      ≅ Rep.of (inducedRep k G M) :=
  Action.mkIso (coindBotEquiv (k := k) (G := G) (M := M)).toModuleIso fun _ => by
    ext f x
    rfl

/-! ### The vanishing -/

/-- **The cohomology of the functions on the group vanishes above degree zero.** -/
theorem isZero_groupCohomology_inducedRep (n : ℕ) :
    Limits.IsZero (groupCohomology (Rep.of (inducedRep k G M)) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
      (Rep.trivial k ↥(⊥ : Subgroup G) M) n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (coindBotIso (k := k) (G := G) (M := M)).symm ≪≫
      groupCohomology.coindIso _ (n + 1))

variable [Finite G]

/-- **The homology of the functions on a finite group vanishes above degree zero.** -/
theorem isZero_groupHomology_inducedRep (n : ℕ) :
    Limits.IsZero (groupHomology (Rep.of (inducedRep k G M)) (n + 1)) := by
  classical
  refine (isZero_groupHomology_succ_of_subsingleton
      (A := Rep.trivial k ↥(⊥ : Subgroup G) M) n).of_iso ?_
  refine (groupHomology.functor k G (n + 1)).mapIso
      ((coindBotIso (k := k) (G := G) (M := M)).symm ≪≫
        (Rep.indCoindIso (Rep.trivial k ↥(⊥ : Subgroup G) M)).symm) ≪≫ ?_
  exact groupHomology.indIso _ _ (n + 1)

instance subsingleton_H0_inducedRep : Subsingleton (H0 (inducedRep k G M)) :=
  ⟨fun a b => by rw [H0_inducedRep_eq_zero a, H0_inducedRep_eq_zero b]⟩

instance subsingleton_Hm1_inducedRep : Subsingleton (Hm1 (inducedRep k G M)) :=
  ⟨fun a b => by rw [Hm1_inducedRep_eq_zero a, Hm1_inducedRep_eq_zero b]⟩

/-- **The complete cohomology of the functions on a finite group vanishes in every integer
degree.** -/
theorem isZero_tateModule_inducedRep (n : ℤ) :
    Limits.IsZero (tateModule (Rep.of (inducedRep k G M)) n) := by
  match n with
  | .ofNat 0 => exact ModuleCat.isZero_of_subsingleton (ModuleCat.of k (H0 (inducedRep k G M)))
  | .ofNat (m + 1) => exact isZero_groupCohomology_inducedRep m
  | .negSucc 0 => exact ModuleCat.isZero_of_subsingleton (ModuleCat.of k (Hm1 (inducedRep k G M)))
  | .negSucc (m + 1) => exact isZero_groupHomology_inducedRep m

/-! ### Dimension shifting -/

section Shift

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℤ)

/-- **The connecting map is injective as soon as the middle term has nothing in that degree.** -/
theorem injective_tateδ (h : Limits.IsZero (tateModule X.X₂ n)) :
    Function.Injective (tateδ hX n) := by
  intro a b hab
  obtain ⟨x, hx⟩ := (tateExact_map_δ hX n (a - b)).1 (by rw [map_sub, hab, sub_self])
  have hzero : (tateMap X.g n) x = 0 := by
    rw [h.eq_zero_of_src (tateMap X.g n)]
    simp
  rw [hzero] at hx
  exact sub_eq_zero.1 hx.symm

/-- **The connecting map is surjective as soon as the middle term has nothing in the next
degree.** -/
theorem surjective_tateδ (h : Limits.IsZero (tateModule X.X₂ (n + 1))) :
    Function.Surjective (tateδ hX n) := by
  intro y
  refine (tateExact_δ_map hX n y).1 ?_
  rw [h.eq_zero_of_tgt (tateMap X.f (n + 1))]
  simp

/-- **The connecting map of a short exact sequence whose middle term has no complete cohomology is
bijective.** -/
theorem bijective_tateδ (h : Limits.IsZero (tateModule X.X₂ n))
    (h' : Limits.IsZero (tateModule X.X₂ (n + 1))) :
    Function.Bijective (tateδ hX n) :=
  ⟨injective_tateδ hX n h, surjective_tateδ hX n h'⟩

end Shift

end

end InverseGalois.CFT.Tate
