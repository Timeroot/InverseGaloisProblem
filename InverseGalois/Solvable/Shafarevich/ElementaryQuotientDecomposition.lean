/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.GlobalPowRepresentatives
import InverseGalois.CFT.Profinite.FixingSubgroup
import InverseGalois.CFT.Profinite.Krull
import InverseGalois.CFT.Units.DecompositionClosed
import InverseGalois.Solvable.Shafarevich.ElementaryQuotient

/-!
# The finite elementary quotient of a decomposition subgroup

The ladder of the descending central series asks each member of its finite family of subgroups to
have a finite elementary quotient, and in the arithmetic those members are decomposition subgroups
of an algebraic closure of a number field, cut down by the open normal subgroup the base
realization defines.  This file supplies the condition for them.

The counting is done over a finite Galois level chosen to contain the roots of unity of the prime
and to fix no more than the open subgroup does.  Over that level the elements of the closure fixed
by the part of the decomposition subgroup lying above it have finitely many power classes, so that
part carries only finitely many smooth characters of the prime order; and the part has finite index
in the whole, because the quotient is carried faithfully into the Galois group of the level, so the
whole carries only finitely many as well.

Reading an automorphism over an intermediate field as one over the base is what makes the two
descriptions of the smaller subgroup agree: the reading is injective with image the subgroup fixing
the field, it does not change the effect on an element, and it moves an ideal of the integers the
same way, so it matches the stabilizers of a prime on the two sides.

## Main results

* `InverseGalois.Shafarevich.exists_galSubHom_eq`: **every automorphism fixing an intermediate field
  is one over that field, read over the base.**
* `InverseGalois.Shafarevich.mem_stabilizer_galSubHom_iff`: **stabilizing a prime is the same
  condition on the two sides.**
* `InverseGalois.Shafarevich.mem_inertia_galSubHom_iff`: **inertia at a prime is read the same way
  on the two sides.**
* `InverseGalois.Shafarevich.finite_quotient_fixingSubgroup_subgroupOf`: **the part of a subgroup
  fixing a finite Galois level has finite index in it.**
* `InverseGalois.Shafarevich.hasFiniteElementaryQuotient_stabilizer_inf`: **a decomposition subgroup
  cut down by an open normal subgroup has a finite elementary quotient.**

## Tags

Shafarevich's theorem, decomposition group, Kummer theory, local field, smooth character
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT MulAction NumberField

open scoped Pointwise

/-! ### Reading an automorphism over an intermediate field as one over the base -/

section Bridge

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (K : IntermediateField k Ω)

omit [IsGalois k Ω] in
/-- An automorphism over an intermediate field fixes that field, read over the base. -/
theorem galSubHom_mem_fixingSubgroup (τ : Gal(Ω/↥K)) : galSubHom K τ ∈ K.fixingSubgroup := by
  rw [← coe_fixingSubgroupEquiv_symm]
  exact ((IntermediateField.fixingSubgroupEquiv K).symm τ).2

omit [IsGalois k Ω] in
/-- Every automorphism fixing an intermediate field is one over that field, read over the base. -/
theorem exists_galSubHom_eq {σ : Gal(Ω/k)} (hσ : σ ∈ K.fixingSubgroup) :
    ∃ τ : Gal(Ω/↥K), galSubHom K τ = σ := by
  refine ⟨IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩, ?_⟩
  rw [← coe_fixingSubgroupEquiv_symm]
  exact congrArg Subtype.val
    ((IntermediateField.fixingSubgroupEquiv K).symm_apply_apply ⟨σ, hσ⟩)

omit [IsGalois k Ω] in
/-- An automorphism over an intermediate field moves an ideal of the integers the same way over the
base. -/
theorem smul_ideal_galSubHom (τ : Gal(Ω/↥K)) (I : Ideal (𝓞 Ω)) :
    galSubHom K τ • I = τ • I := by
  have h : ∀ b : 𝓞 Ω, (galSubHom K τ)⁻¹ • b = τ⁻¹ • b := by
    intro b
    rw [← _root_.map_inv (galSubHom K) τ]
    exact Subtype.ext rfl
  refine Ideal.ext fun b => ?_
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem, h]

omit [IsGalois k Ω] in
/-- Stabilizing a prime is the same condition over an intermediate field and over the base. -/
theorem mem_stabilizer_galSubHom_iff (τ : Gal(Ω/↥K)) (P : Ideal (𝓞 Ω)) :
    galSubHom K τ ∈ stabilizer Gal(Ω/k) P ↔ τ ∈ stabilizer Gal(Ω/↥K) P := by
  rw [mem_stabilizer_iff, mem_stabilizer_iff, smul_ideal_galSubHom]

omit [IsGalois k Ω] in
/-- An automorphism over a level acts on the integers of the whole extension the way it does read
over the base field. -/
theorem smul_ringOfIntegers_galSubHom (τ : Gal(Ω/↥K)) (b : 𝓞 Ω) :
    galSubHom K τ • b = τ • b := Subtype.ext rfl

omit [IsGalois k Ω] in
/-- An automorphism over a level acts on the units of the whole extension the way it does read over
the base field. -/
theorem smul_units_galSubHom (τ : Gal(Ω/↥K)) (β : Ωˣ) : galSubHom K τ • β = τ • β :=
  Units.ext rfl

omit [IsGalois k Ω] in
/-- Inertia at a prime is read the same way over the base field and over a level. -/
theorem mem_inertia_galSubHom_iff (τ : Gal(Ω/↥K)) (P : Ideal (𝓞 Ω)) :
    galSubHom K τ ∈ Ideal.inertia Gal(Ω/k) P ↔ τ ∈ Ideal.inertia Gal(Ω/↥K) P := by
  simp only [AddSubgroup.mem_inertia]
  exact forall_congr' fun b => by rw [smul_ringOfIntegers_galSubHom]

omit [IsGalois k Ω] in
/-- The quotient of a subgroup by the part of it fixing a finite Galois level is finite, that
quotient being carried into the Galois group of the level. -/
theorem finite_quotient_fixingSubgroup_subgroupOf (A : Subgroup Gal(Ω/k))
    [FiniteDimensional k ↥K] [Normal k ↥K] :
    Finite (↥A ⧸ K.fixingSubgroup.subgroupOf A) := by
  set ψ : ↥A →* Gal(↥K/k) :=
    (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K).comp A.subtype with hψ
  have hker : K.fixingSubgroup.subgroupOf A = ψ.ker := by
    refine Subgroup.ext fun x => ?_
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hψ, MonoidHom.coe_comp,
      Function.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker]
  rw [hker]
  haveI : Finite ↥ψ.range := Subtype.finite
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).symm.toEquiv

end Bridge

/-! ### The finite elementary quotient of a decomposition subgroup -/

section Decomposition

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω]

/-- **A decomposition subgroup of an algebraic closure of a number field, cut down by an open
normal subgroup, has a finite elementary quotient.** -/
theorem hasFiniteElementaryQuotient_stabilizer_inf {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥)
    {N : Subgroup Gal(Ω/k)} (hN : IsOpenNormal N) :
    HasFiniteElementaryQuotient ℓ (stabilizer Gal(Ω/k) P ⊓ N) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : NeZero ((ℓ : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne ℓ)⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω ℓ
  -- a finite Galois level whose fixing subgroup lies in the open subgroup and which has the root
  obtain ⟨L, hLfin, -, hLN⟩ := exists_fixingSubgroup_le hN
  haveI := hLfin
  obtain ⟨t, ht⟩ : L.FG := IntermediateField.essFiniteType_iff.1 inferInstance
  obtain ⟨M, hMfin, hMgal, hsM⟩ :=
    exists_isGalois_level_subset k (insert ξ (↑t : Set Ω)) (t.finite_toSet.insert ξ)
  haveI := hMfin
  haveI := hMgal
  have hξM : ξ ∈ M := hsM (Set.mem_insert _ _)
  have hLM : L ≤ M := by
    rw [← ht]
    exact IntermediateField.adjoin_le_iff.2 fun y hy => hsM (Set.mem_insert_of_mem _ hy)
  have hfixle : M.fixingSubgroup ≤ N := fun σ hσ =>
    hLN ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y (hLM hy))
  have hle : stabilizer Gal(Ω/k) P ⊓ M.fixingSubgroup ≤ stabilizer Gal(Ω/k) P ⊓ N :=
    inf_le_inf_left _ hfixle
  -- the quotient of the one by the other is finite
  have hsub : (stabilizer Gal(Ω/k) P ⊓ M.fixingSubgroup).subgroupOf
        (stabilizer Gal(Ω/k) P ⊓ N)
      = M.fixingSubgroup.subgroupOf (stabilizer Gal(Ω/k) P ⊓ N) := by
    refine Subgroup.ext fun x => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨(Subgroup.mem_inf.1 x.2).1, h⟩⟩
  haveI : Finite (↥(stabilizer Gal(Ω/k) P ⊓ N) ⧸
      (stabilizer Gal(Ω/k) P ⊓ M.fixingSubgroup).subgroupOf (stabilizer Gal(Ω/k) P ⊓ N)) := by
    rw [hsub]
    exact finite_quotient_fixingSubgroup_subgroupOf M _
  -- the subgroup over the level is closed
  have hclosed : IsClosed ((stabilizer Gal(Ω/k) P ⊓ M.fixingSubgroup : Subgroup Gal(Ω/k)) :
      Set Gal(Ω/k)) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_stabilizer_ideal (k := k) P).inter
      (Subgroup.isClosed_of_isOpen _ M.fixingSubgroup_isOpen)
  -- it fixes the roots of unity, which lie in the level
  have hμ : ∀ ζ : Ωˣ, ζ ^ ℓ = 1 →
      ∀ σ : ↥(stabilizer Gal(Ω/k) P ⊓ M.fixingSubgroup), σ • ζ = ζ := by
    intro ζ hζ σ
    have hval : ((ζ : Ω)) ^ ℓ = 1 := by
      have h := congrArg (fun u : Ωˣ => (u : Ω)) hζ
      simpa using h
    obtain ⟨j, -, hj⟩ := hξ.eq_pow_of_pow_eq_one hval
    have hfix : (σ : Gal(Ω/k)) ξ = ξ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Subgroup.mem_inf.1 σ.2).2 ξ hξM
    refine Units.ext ?_
    show (σ : Gal(Ω/k)) (ζ : Ω) = (ζ : Ω)
    rw [← hj, _root_.map_pow, hfix]
  -- the representatives, taken over the level
  haveI : NumberField ↥M := NumberField.of_module_finite k ↥M
  haveI : IsGalois ↥M Ω := IsGalois.tower_top_of_isGalois k ↥M Ω
  obtain ⟨T, hTfin, -, hT⟩ :=
    exists_finite_pow_representatives_stabilizer (k := ↥M) (Ω := Ω) (NeZero.ne ℓ) hP
  have hrep : ∀ x : Ω, x ≠ 0 →
      (∀ σ : ↥(stabilizer Gal(Ω/k) P ⊓ M.fixingSubgroup), (σ : Gal(Ω/k)) x = x) →
      ∃ a ∈ T, ∃ c : Ω,
        (∀ σ : ↥(stabilizer Gal(Ω/k) P ⊓ M.fixingSubgroup), (σ : Gal(Ω/k)) c = c) ∧
          x = a * c ^ ℓ := by
    intro x hx0 hxfix
    have hmemA' : ∀ τ : Gal(Ω/↥M), τ ∈ stabilizer Gal(Ω/↥M) P →
        galSubHom M τ ∈ stabilizer Gal(Ω/k) P ⊓ M.fixingSubgroup := by
      intro τ hτ
      rw [Subgroup.mem_inf]
      exact ⟨(mem_stabilizer_galSubHom_iff M τ P).2 hτ, galSubHom_mem_fixingSubgroup M τ⟩
    obtain ⟨a, haT, c, hcfix, hxc⟩ := hT x hx0 fun τ => hxfix ⟨_, hmemA' τ τ.2⟩
    refine ⟨a, haT, c, fun σ => ?_, hxc⟩
    obtain ⟨τ, hτ⟩ := exists_galSubHom_eq M (Subgroup.mem_inf.1 σ.2).2
    have hτP : τ ∈ stabilizer Gal(Ω/↥M) P :=
      (mem_stabilizer_galSubHom_iff M τ P).1 (hτ ▸ (Subgroup.mem_inf.1 σ.2).1)
    have h := hcfix ⟨τ, hτP⟩
    rw [← hτ]
    exact h
  exact hasFiniteElementaryQuotient_of_finite_smoothZModChar
    (finite_smoothZModChar_of_le hle
      (finite_smoothZModChar_of_finite_pow_representatives hξ hclosed hμ hTfin hrep))

end Decomposition

end InverseGalois.Shafarevich
