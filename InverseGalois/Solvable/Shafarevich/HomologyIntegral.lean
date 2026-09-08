/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelCoverOperator

/-!
# First homology does not notice which ring the coefficients are written over

Global duality over a number field is run with coefficients that are abelian groups, that is with
modules over the integers, while the ladder that builds a solvable extension carries coefficients
that are vector spaces over the field with a prime number of elements.  The two first homologies are
objects of different categories, so a class produced by the one cannot literally be handed to the
other.

They are nevertheless computed by the same formulas.  The first homology of a group with
coefficients in a representation is the quotient of the kernel of the map sending a formal
combination of group elements with coefficients to the sum of the translates minus the coefficients,
by the image of the map coming from pairs of group elements; and both of those maps are written
purely in terms of the action and the addition.  Writing a representation over a ring of prime
characteristic over the integers instead changes neither map, so the cycles and the boundaries are
literally the same subsets of the same abelian group.

That is enough, and no comparison map between the two homologies is needed.  A class over the
integers is the class of some cycle, because the projection from the cycles onto the homology is
surjective; the very same cycle is a cycle over the smaller ring, and gives a class there.  If that
class dies under a map of coefficients, the image of the cycle is a boundary over the smaller ring,
hence a boundary over the integers, hence the class one started with dies too.  So one class over
the smaller ring governs the class over the integers for every map of the coefficients at once.

## Main definitions

* `InverseGalois.Shafarevich.intRep` — a representation of prime characteristic, read over the
  integers.
* `InverseGalois.Shafarevich.intRepMap` — a map of such representations, read over the integers.
* `InverseGalois.Shafarevich.HasIntegralShaTateCover` — the covering of the operator group, with
  the homology class asked for over the integers.

## Main results

* `InverseGalois.Shafarevich.mem_cycles₁_intRep`, `InverseGalois.Shafarevich.mem_boundaries₁_intRep`
  — the cycles and the boundaries in degree one do not depend on the ring.
* `InverseGalois.Shafarevich.exists_h1_map_eq_zero` — **a class of first homology over the smaller
  ring whose death under any map of the coefficients forces the death of a given class over the
  integers.**
* `InverseGalois.Shafarevich.hasOperatorShaTateCover_of_hasIntegralShaTateCover` — **a covering by
  integral homology classes is a covering by homology classes of prime characteristic.**

## Tags

group homology, change of rings, Poitou-Tate, Shafarevich's theorem
-/

namespace InverseGalois.Shafarevich

open CategoryTheory Finsupp groupHomology InverseGalois.CFT

/-! ### A representation of prime characteristic, read over the integers -/

section IntRep

variable {ℓ : ℕ} {G : Type} [Group G]

/-- **A representation over the integers modulo a number, read over the integers.**  The underlying
abelian group is unchanged; only the scalars are forgotten. -/
noncomputable def intRep (A : Rep (ZMod ℓ) G) : Rep ℤ G :=
  Rep.of (V := ↥A.V)
    { toFun := fun g => (A.ρ g).toAddMonoidHom.toIntLinearMap
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp }

@[simp]
theorem intRep_ρ_apply (A : Rep (ZMod ℓ) G) (g : G) (a : ↥A.V) :
    (intRep A).ρ g a = A.ρ g a := rfl

/-- **A map of representations of prime characteristic, read over the integers.** -/
noncomputable def intRepMap {A B : Rep (ZMod ℓ) G} (ψ : A ⟶ B) : intRep A ⟶ intRep B where
  hom := ModuleCat.ofHom ψ.hom.hom.toAddMonoidHom.toIntLinearMap
  comm g := ModuleCat.hom_ext (LinearMap.ext fun x => Rep.hom_comm_apply ψ g x)

@[simp]
theorem intRepMap_hom_apply {A B : Rep (ZMod ℓ) G} (ψ : A ⟶ B) (a : ↥A.V) :
    (intRepMap ψ).hom a = ψ.hom a := rfl

end IntRep

/-! ### The cycles and the boundaries in degree one are the same subsets -/

section Chains

variable {ℓ : ℕ} {G : Type} [Group G] (A : Rep (ZMod ℓ) G)

/-- The map whose kernel cuts out the one-cycles does not depend on the ring. -/
theorem d₁₀_intRep (x : G →₀ ↥A.V) : d₁₀ (intRep A) x = d₁₀ A x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single g a => rw [d₁₀_single, d₁₀_single, intRep_ρ_apply]

/-- The map whose image cuts out the one-boundaries does not depend on the ring. -/
theorem d₂₁_intRep (x : G × G →₀ ↥A.V) : d₂₁ (intRep A) x = d₂₁ A x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single g a => rw [d₂₁_single, d₂₁_single, intRep_ρ_apply]

/-- **The one-cycles do not depend on the ring the coefficients are written over.** -/
theorem mem_cycles₁_intRep (x : G →₀ ↥A.V) : x ∈ cycles₁ (intRep A) ↔ x ∈ cycles₁ A := by
  show d₁₀ (intRep A) x = 0 ↔ d₁₀ A x = 0
  rw [d₁₀_intRep]

/-- **The one-boundaries do not depend on the ring the coefficients are written over.** -/
theorem mem_boundaries₁_intRep (x : G →₀ ↥A.V) :
    x ∈ boundaries₁ (intRep A) ↔ x ∈ boundaries₁ A := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, d₂₁_intRep A y⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (d₂₁_intRep A y).symm⟩

/-- The one-chains carried along a map of the coefficients do not depend on the ring. -/
theorem chainsMap₁_intRep {B : Rep (ZMod ℓ) G} (ψ : A ⟶ B) (x : G →₀ ↥A.V) :
    chainsMap₁ (A := intRep A) (B := intRep B) (MonoidHom.id G) (intRepMap ψ) x
      = chainsMap₁ (A := A) (B := B) (MonoidHom.id G) ψ x := rfl

end Chains

/-! ### One class of prime characteristic governs a class over the integers -/

section Govern

variable {ℓ : ℕ} {G : Type} [Group G]

/-- **A class of first homology over the ring of prime characteristic whose death under any map of
the coefficients forces the death of a given class over the integers.**  The class is the class of
any cycle representing the integral one, and it works because the cycles and the boundaries are the
same subsets on both sides. -/
theorem exists_h1_map_eq_zero (A : Rep (ZMod ℓ) G) (z : groupHomology.H1 (intRep A)) :
    ∃ x : groupHomology.H1 A, ∀ (B : Rep (ZMod ℓ) G) (ψ : A ⟶ B),
      groupHomology.map (B := B) (MonoidHom.id G) ψ 1 x = 0 →
        groupHomology.map (B := intRep B) (MonoidHom.id G) (intRepMap ψ) 1 z = 0 := by
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H1π (intRep A))).1
    inferInstance z
  refine ⟨groupHomology.H1π A ⟨c.1, (mem_cycles₁_intRep A c.1).1 c.2⟩, fun B ψ hψ => ?_⟩
  rw [← hc, H1π_comp_map_apply]
  refine (H1π_eq_zero_iff _).2 ?_
  rw [coe_mapCycles₁, chainsMap₁_intRep, mem_boundaries₁_intRep]
  rw [H1π_comp_map_apply] at hψ
  have h := (H1π_eq_zero_iff _).1 hψ
  rwa [coe_mapCycles₁] at h

end Govern

/-! ### The covering asked for over the integers -/

/-- **Every everywhere locally trivial class of the layer comes from a first homology class of the
operator group over the integers, compatibly with shrinking.**

This is the covering in the shape global duality supplies it: the homology of a finite group with
coefficients an abelian group, with no reference to the ring of prime characteristic the ladder
carries its coefficients over. -/
def HasIntegralShaTateCover (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U]
    [TopologicalSpace U] (N : ℕ) (S : Type) [Group S] [Finite S] (j : ℕ) {k Ω : Type*} [Field k]
    [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U) (T : Set (Subgroup Gal(Ω/k)))
    (W : Rep (ZMod ℓ) U) : Prop :=
  letI := galLayerAction ℓ U N S j φ
  ∀ ε ∈ sha2 ↥(layerSub ℓ (Generic U N S) j) T,
    ∃ z : groupHomology.H1 (intRep (genericLayerTensor U N S ℓ j W)),
      ∀ (n : ℕ) (α : Generic U N S →* Generic U n S) (hα : IsOperatorHom α),
        groupHomology.map (B := intRep (genericLayerTensor U n S ℓ j W)) (MonoidHom.id U)
            (intRepMap (operatorTensorRep hα ℓ j W)) 1 z = 0 →
          letI := galLayerAction ℓ U n S j φ
          coeffH2 (layerSubMap ℓ α j)
            (layerSubMap_smul_comm φ (fun _ _ => rfl) (fun _ _ => rfl) hα) ε = 1

/-- **A covering by integral homology classes is a covering by homology classes of prime
characteristic.**  Replace the integral class by the class of any cycle representing it. -/
theorem hasOperatorShaTateCover_of_hasIntegralShaTateCover (ℓ : ℕ) [Fact ℓ.Prime] (U : Type)
    [Group U] [Finite U] [TopologicalSpace U] (N : ℕ) (S : Type) [Group S] [Finite S] (j : ℕ)
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U)
    (T : Set (Subgroup Gal(Ω/k))) (W : Rep (ZMod ℓ) U)
    (h : HasIntegralShaTateCover ℓ U N S j φ T W) :
    HasOperatorShaTateCover ℓ U N S j φ T W := by
  intro ε hε
  obtain ⟨z, hz⟩ := h ε hε
  obtain ⟨x, hx⟩ := exists_h1_map_eq_zero (genericLayerTensor U N S ℓ j W) z
  exact ⟨x, fun n α hα hkill =>
    hz n α hα (hx (genericLayerTensor U n S ℓ j W) (operatorTensorRep hα ℓ j W) hkill)⟩

end InverseGalois.Shafarevich
