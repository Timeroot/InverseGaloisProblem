/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.CoverField

/-!
# The geometric fundamental group of the punctured line

The automorphism group of the cover field over `S` is the **geometric fundamental group** of the
affine line over `ℚ̄` punctured at `S` (and at infinity): a profinite group whose finite continuous
quotients are exactly the deck groups of the covers unramified outside `S`.

This file constructs that group and proves the dictionary between it and the covers, in both
directions.  A cover unramified outside `S` sits inside the cover field, and restriction of
automorphisms to it is a surjection onto its deck group with open kernel; conversely such a finite
quotient is cut out by an open normal subgroup, whose fixed field is a finite Galois subextension of
the cover field, hence lies inside a single cover, and is itself the field of a subcover.

Continuity is expressed by openness of the kernel — for a finite discrete target that is exactly
continuity, and it avoids having to name a topology on the target group.

## Main definitions

* `Rigidity.RET.geomPi1` — the geometric fundamental group of the line punctured at `S`.

## Main results

* `Rigidity.RET.exists_surjective_of_isDeckGroupOver` — a group occurring over `S` is a finite
  quotient of `geomPi1 S` by a homomorphism with open kernel.
* `Rigidity.RET.isDeckGroupOver_of_surjective` — such a finite quotient of `geomPi1 S` occurs
  over `S`.
* `Rigidity.RET.isDeckGroupOver_iff_exists_surjective` — the two are the same thing.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

attribute [local instance] GeomAKLB.instMSA GeomAKLB.instIntegral GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instDedekindB GeomAKLB.instTorsionFree
  GeomAKLB.instFaithful

/-- **The geometric fundamental group of the line punctured at `S`**: the automorphism group of the
compositum of every cover unramified outside `S` and at infinity, with its Krull topology. -/
abbrev geomPi1 (S : Set k) : Type :=
  (coverField S : Type) ≃ₐ[RatFunc k] (coverField S : Type)

/-- Composing a homomorphism with an isomorphism does not change its kernel. -/
private theorem ker_comp_mulEquiv {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (ψ : B ≃* C) : (ψ.toMonoidHom.comp f).ker = f.ker := by
  ext a
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]

/-! ### Covers give continuous finite quotients -/

/-- **Restriction of automorphisms to a finite normal subextension of the cover field** is a
surjection with open kernel, the subgroup fixing that subextension. -/
theorem exists_surjective_of_subextension {S : Set k} {G : Type} [Group G] [Finite G]
    (A : IntermediateField (RatFunc k) (coverField S : Type))
    [FiniteDimensional (RatFunc k) (A : Type)] [Normal (RatFunc k) (A : Type)]
    (ψ : ((A : Type) ≃ₐ[RatFunc k] (A : Type)) ≃* G) :
    ∃ φ : geomPi1 S →* G, Function.Surjective φ ∧ IsOpen (φ.ker : Set (geomPi1 S)) := by
  refine ⟨ψ.toMonoidHom.comp (AlgEquiv.restrictNormalHom A), fun g => ?_, ?_⟩
  · obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := RatFunc k) (K₁ := (A : Type)) (E := (coverField S : Type)) (ψ.symm g)
    refine ⟨σ, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hσ,
      MulEquiv.apply_symm_apply]
  · rw [ker_comp_mulEquiv, IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_isOpen A

/-- **A group occurring over `S` is a finite quotient of the geometric fundamental group**, by a
homomorphism with open kernel.  The cover realizing the group embeds in the cover field, and the
homomorphism is restriction of automorphisms to that copy of it. -/
theorem exists_surjective_of_isDeckGroupOver {S : Set k} {G : Type} [Group G] [Finite G]
    (h : IsDeckGroupOver S G) :
    ∃ φ : geomPi1 S →* G, Function.Surjective φ ∧ IsOpen (φ.ker : Set (geomPi1 S)) := by
  obtain ⟨L, ⟨e⟩, hout, hinf⟩ := h
  -- The cover, transported into the algebraic closure of the line, is a cover field over `S`,
  have hcf : IsCoverFieldOver S L.image := ⟨L, ⟨L.imageEquiv⟩, hout, hinf⟩
  have hle : L.image ≤ coverField S := hcf.le_coverField
  haveI := hcf.finiteDimensional
  haveI := hcf.normal
  -- hence a finite normal subextension of the cover field, and a copy of the cover.
  haveI := LinearEquiv.finiteDimensional (IntermediateField.restrict_algEquiv hle).toLinearEquiv
  haveI := Normal.of_algEquiv (IntermediateField.restrict_algEquiv hle)
  exact exists_surjective_of_subextension (IntermediateField.restrict hle)
    ((AlgEquiv.autCongr
      (L.imageEquiv.trans (IntermediateField.restrict_algEquiv hle)).symm).trans e)

/-! ### Continuous finite quotients come from covers -/

/-- A normal intermediate field of a cover unramified outside `S` and at infinity realizes its own
automorphism group over `S`. -/
theorem isDeckGroupOver_of_mulEquiv_sub {S : Set k} {G : Type} [Group G] [Finite G]
    {L : LineCover} (hout : L.IsUnramifiedOutside S) (hinf : L.IsUnramifiedAtInfinity)
    (B : IntermediateField (RatFunc k) L.M) [Normal (RatFunc k) (B : Type)]
    (ψ : ((B : Type) ≃ₐ[RatFunc k] (B : Type)) ≃* G) : IsDeckGroupOver S G :=
  ⟨L.sub B, ⟨ψ⟩, hout.sub B, hinf.sub B⟩

/-- **A finite Galois subextension of the cover field over `S` realizes its automorphism group
over `S`.**  It lies inside a single cover field, hence is a normal subextension of an honest
cover, and so is cut out by a subcover. -/
theorem isDeckGroupOver_of_mulEquiv_subextension {S : Set k} {G : Type} [Group G] [Finite G]
    (E : IntermediateField (RatFunc k) (coverField S : Type))
    [FiniteDimensional (RatFunc k) (E : Type)] [Normal (RatFunc k) (E : Type)]
    (ψ : ((E : Type) ≃ₐ[RatFunc k] (E : Type)) ≃* G) : IsDeckGroupOver S G := by
  -- `E`, viewed in the algebraic closure of the line, is finite over the line,
  haveI := LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv E).toLinearEquiv
  -- so it lies inside a single cover field, the field of a cover `L'`.
  obtain ⟨E', hE', hle'⟩ :=
    exists_isCoverFieldOver_of_le (S := S) (IntermediateField.lift E) (IntermediateField.lift_le E)
  obtain ⟨L', ⟨e'⟩, hout', hinf'⟩ := hE'
  haveI := LinearEquiv.finiteDimensional e'.toLinearEquiv
  haveI : IsGalois (RatFunc k) (E' : Type) := IsGalois.of_algEquiv e'
  have μ : (E : Type) ≃ₐ[RatFunc k]
      ((IntermediateField.restrict hle' : IntermediateField (RatFunc k) (E' : Type)) : Type) :=
    (IntermediateField.liftAlgEquiv E).trans (IntermediateField.restrict_algEquiv hle')
  -- Transported into the cover itself, `E` becomes a normal intermediate field.
  have ν := IntermediateField.intermediateFieldMap e'.symm (IntermediateField.restrict hle')
  haveI := Normal.of_algEquiv (μ.trans ν)
  exact isDeckGroupOver_of_mulEquiv_sub hout' hinf' _
    ((AlgEquiv.autCongr (μ.trans ν).symm).trans ψ)

/-- **A finite quotient of the geometric fundamental group by a homomorphism with open kernel occurs
over `S`.**  The fixed field of the kernel is a finite Galois subextension of the cover field, and
the quotient is its automorphism group. -/
theorem isDeckGroupOver_of_surjective {S : Set k} {G : Type} [Group G] [Finite G]
    (φ : geomPi1 S →* G) (hφ : Function.Surjective φ)
    (hopen : IsOpen (φ.ker : Set (geomPi1 S))) : IsDeckGroupOver S G := by
  -- The kernel is an open, hence closed, normal subgroup; let `E` be its fixed field.
  have hclosed : IsClosed (φ.ker : Set (geomPi1 S)) := Subgroup.isClosed_of_isOpen _ hopen
  have hfix : (IntermediateField.fixedField φ.ker).fixingSubgroup = φ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨φ.ker, hclosed⟩
  -- Being open, the kernel cuts out a finite subextension.
  haveI : FiniteDimensional (RatFunc k)
      ((IntermediateField.fixedField φ.ker : IntermediateField (RatFunc k)
        (coverField S : Type)) : Type) := by
    refine (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField φ.ker)).mp ?_
    rw [hfix]
    exact hopen
  -- Being normal, it cuts out a Galois one, whose automorphism group is the quotient.
  refine isDeckGroupOver_of_mulEquiv_subextension (IntermediateField.fixedField φ.ker) ?_
  exact (InfiniteGalois.normalAutEquivQuotient ⟨φ.ker, hclosed⟩).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

/-- **The finite quotients of the geometric fundamental group are the groups occurring over `S`.**
-/
theorem isDeckGroupOver_iff_exists_surjective {S : Set k} (G : Type) [Group G] [Finite G] :
    IsDeckGroupOver S G ↔
      ∃ φ : geomPi1 S →* G, Function.Surjective φ ∧ IsOpen (φ.ker : Set (geomPi1 S)) :=
  ⟨exists_surjective_of_isDeckGroupOver, fun ⟨_, hφ, hopen⟩ =>
    isDeckGroupOver_of_surjective _ hφ hopen⟩

end Rigidity.RET
