/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TensorOrbit
import InverseGalois.CFT.Profinite.KummerRep

/-!
# From everywhere locally trivial classes to coefficients in the units of a set of places

The everywhere locally trivial classes at the level of a normal subextension are read by twisted
Kummer theory inside the first cohomology of a finite group with coefficients in the units of that
subextension tensored with the homomorphisms of the roots of unity into the kernel of a lifting
problem.  Separately, a class of that cohomology whose valuation is a coboundary at every place,
on the subgroup fixing that place, comes from the units of a finite set of places.  This file joins
the two: **an everywhere locally trivial class comes from the units of a finite set of places.**

The two statements are about different groups, and the passage between them is arithmetic.  Local
triviality is triviality of the restriction to a genuine decomposition subgroup of the Galois group
of the base, with coefficients restricted along it; the theorem about valuations wants triviality of
the plain restriction to the subgroup of the finite quotient fixing a place.  What bridges them is a
dictionary at each place: a decomposition subgroup whose image covers the subgroup fixing that
place, and a homomorphism out of the first cohomology there which computes the valuation of a
twisted Kummer class at that place.  With the dictionary in hand, an element trivialising the class
on the decomposition subgroup is carried by the homomorphism to an element trivialising the
valuation, which is exactly what the theorem about valuations consumes.

## Main definitions

* `InverseGalois.CFT.HasLocalOrdHom`: **the dictionary at a place** — a decomposition subgroup
  covering the subgroup fixing the place, and an equivariant homomorphism out of the first
  cohomology there which computes the valuation of a twisted Kummer class.

## Main results

* `InverseGalois.CFT.mem_range_tensorSubInclRep_of_mem_kummerSha1`: **an everywhere locally trivial
  class, read with the units of the subextension as coefficients, comes from the units of the set
  of places where the valuation is not taken.**

## Tags

Galois cohomology, local-global principle, Kummer theory, S-unit, decomposition group
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory groupCohomology TensorProduct

section Bridge

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {K : IntermediateField k Ω}
variable {M : Type} [CommGroup M] [MulDistribMulAction Gal(Ω/↥K) M] {ι : M →* (↥K)ˣ}
variable {p : ℕ} [NeZero p] [MulDistribMulAction Gal(Ω/k) M]
variable {E : Type} [CommGroup E] [MulDistribMulAction Gal(Ω/k) E]
variable (h : IsKummerData ↥K Ω M ι p) (htriv : ∀ (σ : Gal(Ω/k)) (m : M), σ • m = m)
variable (htrivE : ∀ (x : ↥K.fixingSubgroup) (e : E), x • e = e)
variable {J : Type} [Fintype J] [DecidableEq J] (α : E ≃* (J → M))
variable (hEp : ∀ e : E, e ^ p = 1) [Normal k ↥K] [IsCyclic M]
variable (hfix : ∀ (σ : Gal(Ω/k)) (m : M),
  σ • Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) (ι m))
variable [ActsTrivially K.fixingSubgroup (M →* E)]
variable {X : Type} [MulAction (Gal(Ω/k) ⧸ K.fixingSubgroup) X] [DecidableEq X]
variable (g : Additive (↥K)ˣ →+ (X →₀ ℤ))

/-- **The dictionary at a place.**  A place has the dictionary when some subgroup of the family —
in the arithmetic situation, the decomposition subgroup of a prime above it — has an image in the
quotient covering the subgroup fixing the place, and carries an equivariant homomorphism out of the
first cohomology of the part of it fixing the subextension which computes, on a twisted Kummer
class, the valuation of that class at the place. -/
def HasLocalOrdHom (S : Set (Subgroup Gal(Ω/k))) (x : X) : Prop :=
  ∃ D ∈ S,
    (∀ ρ : Gal(Ω/k) ⧸ K.fixingSubgroup, ρ • x = x → ∃ σ ∈ D, (QuotientGroup.mk σ : _) = ρ) ∧
    ∃ μ : SmoothH1 ↥(K.fixingSubgroup.subgroupOf D) E →* (M →* E),
      (∀ (σ : ↥D) (z : SmoothH1 ↥(K.fixingSubgroup.subgroupOf D) E),
        μ (σ • z) = (σ : Gal(Ω/k)) • μ z) ∧
      ∀ t : Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E),
        μ (resSubH1 K.fixingSubgroup D
            (Additive.toMul (kummerTwistEquiv h htriv htrivE α hEp t)))
          = Additive.toMul (tensorVal (M →* E) g t x)

variable (B : Subgroup (↥K)ˣ) [IsStableSubgroup (Gal(Ω/k) ⧸ K.fixingSubgroup) B]
variable [Finite (Gal(Ω/k) ⧸ K.fixingSubgroup)]

/-- **An everywhere locally trivial class, read with the units of the subextension as coefficients,
comes from the units of the set of places where the valuation is not taken.**  A cocycle
representing the class is trivialised on each decomposition subgroup of the family; the dictionary
at a place carries the element which trivialises it there to an element which trivialises the
valuation of the cocycle at that place, and a cocycle whose valuation is a coboundary at every
place has, after a correction by a coboundary, values in the kernel of the valuation. -/
theorem mem_range_tensorSubInclRep_of_mem_kummerSha1
    (hop : IsOpen (K.fixingSubgroup : Set Gal(Ω/k))) (S : Set (Subgroup Gal(Ω/k)))
    (hg : Function.Surjective g)
    (hB : ∀ a : (↥K)ˣ, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Gal(Ω/k) ⧸ K.fixingSubgroup) (a : (↥K)ˣ) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hlocal : ∀ x : X, HasLocalOrdHom h htriv htrivE α hEp g S x)
    {y : Multiplicative ↥(H1 (Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
      (Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E))))}
    (hy : y ∈ kummerSha1 h htriv htrivE α hEp hfix hop S) :
    ∃ w : H1 (Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
        (Additive ↥B ⊗[ℤ] Additive (M →* E))),
      (groupCohomology.map (MonoidHom.id (Gal(Ω/k) ⧸ K.fixingSubgroup))
        (A := Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
          (Additive ↥B ⊗[ℤ] Additive (M →* E)))
        (tensorSubInclRep (Gal(Ω/k) ⧸ K.fixingSubgroup) (M →* E) B) 1).hom w
        = Multiplicative.toAdd y := by
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨u, hu, hs, rfl⟩ := smoothH1Mk_surjective z
  have hesymm : ∀ (σ : Gal(Ω/k) ⧸ K.fixingSubgroup) (s : SmoothH1 ↥K.fixingSubgroup E),
      (kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul (σ • s))
        = σ • (kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul s) := by
    intro σ s
    refine (kummerTwistEquiv h htriv htrivE α hEp).injective ?_
    rw [AddEquiv.apply_symm_apply, kummerTwistEquiv_smul h htriv htrivE α hEp hfix,
      AddEquiv.apply_symm_apply]
    rfl
  have hccoc : ∀ σ τ : Gal(Ω/k) ⧸ K.fixingSubgroup,
      (kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul (u (σ * τ)))
        = σ • (kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul (u τ))
          + (kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul (u σ)) := by
    intro σ τ
    rw [hu σ τ, _root_.ofMul_mul, map_add, hesymm]
  have hcoc : (fun q => (kummerTwistEquiv h htriv htrivE α hEp).symm (Additive.ofMul (u q))) ∈
      cocycles₁ (Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
        (Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E))) :=
    (mem_cocycles₁_iff (A := Rep.ofDistribMulAction ℤ (Gal(Ω/k) ⧸ K.fixingSubgroup)
      (Additive (↥K)ˣ ⊗[ℤ] Additive (M →* E))) _).2 hccoc
  rw [show ((kummerSmoothH1Equiv h htriv htrivE α hEp hfix hop :
        SmoothH1 (Gal(Ω/k) ⧸ K.fixingSubgroup) (SmoothH1 ↥K.fixingSubgroup E) →* _))
        (smoothH1Mk u hu hs)
      = kummerSmoothH1Equiv h htriv htrivE α hEp hfix hop (smoothH1Mk u hu hs) from rfl,
    kummerSmoothH1Equiv_smoothH1Mk h htriv htrivE α hEp hfix hop hu hs hcoc]
  refine LinearMap.mem_range.1
    (mem_range_map_tensorSubInclRep_of_forall_stabilizer (M →* E) g B hg hB hgeq _ hcoc ?_)
  intro x
  obtain ⟨D, hD, hstab, μ, hμ, hdict⟩ := hlocal x
  have hw : IsMulCocycle₁ (fun σ : ↥D =>
      resSubH1 K.fixingSubgroup D (u (QuotientGroup.mk (σ : Gal(Ω/k))))) :=
    isMulCocycle₁_coeffMap₁ (resSubH1 K.fixingSubgroup D) (resSubH1_smul D)
      (isMulCocycle₁_comap₁ D.subtype (fun _ _ => rfl)
        (isMulCocycle₁_comap₁ (QuotientGroup.mk' K.fixingSubgroup) (fun _ _ => rfl) hu))
  have hws : IsSmooth₁ (fun σ : ↥D =>
      resSubH1 K.fixingSubgroup D (u (QuotientGroup.mk (σ : Gal(Ω/k))))) :=
    IsSmooth₁.coeffMap₁ (resSubH1 K.fixingSubgroup D) ((isSmoothHom_subtype D).isSmooth₁
      ((isSmoothHom_mk' K.fixingSubgroup hop).isSmooth₁ hs))
  have h1 : smoothH1Mk _ hw hws = 1 := mem_sha1Level.1 hz D hD
  obtain ⟨b, hb⟩ := (smoothH1Mk_eq_one_iff hw hws).1 h1
  refine ⟨Additive.ofMul (μ b), fun ρ hρ => ?_⟩
  obtain ⟨σ, hσD, rfl⟩ := hstab ρ hρ
  have hval : Additive.toMul (tensorVal (M →* E) g
      ((kummerTwistEquiv h htriv htrivE α hEp).symm
        (Additive.ofMul (u (QuotientGroup.mk σ)))) x)
      = (σ : Gal(Ω/k)) • μ b / μ b := by
    rw [← hdict]
    have hrw : Additive.toMul (kummerTwistEquiv h htriv htrivE α hEp
        ((kummerTwistEquiv h htriv htrivE α hEp).symm
          (Additive.ofMul (u (QuotientGroup.mk σ)))))
        = u (QuotientGroup.mk σ) := by
      rw [AddEquiv.apply_symm_apply]
      rfl
    rw [hrw, ← congrFun hb ⟨σ, hσD⟩, map_div, hμ ⟨σ, hσD⟩ b]
  refine Additive.toMul.injective ?_
  rw [hval]
  show _ = ((QuotientGroup.mk σ : Gal(Ω/k) ⧸ K.fixingSubgroup) • μ b) / μ b
  rw [quotientMk_smul]

end Bridge

end InverseGalois.CFT
