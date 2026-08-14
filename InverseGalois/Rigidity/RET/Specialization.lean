/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Statement
import InverseGalois.Rigidity.RET.Cayley
import InverseGalois.Core.Basic
import InverseGalois.Hilbert.RegularExtension
import InverseGalois.Rigidity.RET.GeometricIrreducibility

/-!
# Step (B) — specialization `ℚ(T) → ℚ` (Hilbert irreducibility)

The rigidity method's second recognizable theorem: a **regular** Galois extension of `ℚ(T)` with
group `G` (`IsRegularInverseGalois G`, the output of the branch-cycle descent) specializes to a
genuine Galois extension of `ℚ` with the same group at infinitely many rational values of `T`,
giving `IsInverseGalois G`.  This is Hilbert's irreducibility theorem.

This is **not** an axiom — it is a theorem we owe.  Regularity (`algebraicClosure ℚ L = ⊥`) is
exactly the hypothesis that makes the specialized group stay all of `G`: it forces the resolvent to
be absolutely irreducible, so Hilbert irreducibility keeps the Galois group full.

## Architecture: proven Hilbert descent + isolated model-translation gaps

The repository already contains the **polynomial-model form** of this theorem,
`IsInverseGalois.of_regular_family` (`InverseGalois/Hilbert/RegularExtension.lean`), which runs the
proven Hilbert-irreducibility descent (`hilbert_irreducibility_theorem`) on an explicit regular
monic family `F ∈ ℚ[T][X]` with an absolutely irreducible resolvent.  So the *only* thing step (B)
additionally needs is the **model translation**: turning the *abstract* regular Galois extension
`L / ℚ(T)` into such a family.

This file makes that split explicit:

* `IsRegularInverseGalois.isInverseGalois` — the headline theorem — is **fully proven** from the
  bundle `exists_regular_family` by feeding it to `of_regular_family` and transporting along the
  group isomorphism.
* `exists_regular_family` — the **model translation** (task L4): from the abstract extension produce
  a monic `ℚ[T][X]` family with the full `of_regular_family` hypothesis bundle.  This is where the
  work lives; it is decomposed below.

## The model translation (decomposition of `exists_regular_family`)

Take the regular representation `G ↪ Sₙ`, `n = |G|` (`cayleyPerm`); then `H = range ≅ G` and the
family and resolvent **coincide** — both are the minimal polynomial of a primitive element:

1. **Primitive element** (`Field.exists_primitive_element`): `L = ℚ(T)⟮α⟯`, `α` abstract.
2. **Clear denominators** (`IsAlgebraic.exists_integral_multiple`): replace `α` by `β = y • α`
   (`y ∈ ℚ[T]`, `y ≠ 0`) *integral* over `ℚ[T]`, generating the same field.
3. **Monic model** (`minpoly.isIntegrallyClosed_eq_field_fractions'`, `ℚ[T]` integrally closed):
   `F := minpoly ℚ[T] β ∈ ℚ[T][X]` is monic of degree `[L : ℚ(T)] = |G|`, and
   `minpoly ℚ(T) β = F.map (algebraMap ℚ[T] ℚ(T))`.
4. **Irreducible over `ℚ[T]`** (`Monic.irreducible_iff_irreducible_map_fraction_map`): from
   irreducibility of the minimal polynomial over `ℚ(T)`.
5. **Root certificate** (`hroot`): the resolvent *is* `F`, and `F(t)` has a root in its own
   splitting field — trivial.
6. **Cofinite separability** (`hFsep`): `F` is separable over `ℚ(T)` (char `0`), so its
   discriminant is a nonzero element of `ℚ[T]`, vanishing at only finitely many `t`.
7. **Absolute irreducibility** (`hGabs`) — the *regularity teeth* (**genuine gap**
   `absIrreducible_family_of_regular`): `algebraicClosure ℚ L = ⊥` means `L` is geometrically
   connected, so `F` stays irreducible after base change to `ℚ̄`.
8. **Landing certificate** (`hland`) — the *reduction map* (**genuine gap**
   `landing_family_of_regular`): for a good specialization `t`, `Gal(F(t)) ↪ G`, the specialization
   homomorphism into the generic Galois group.

Steps 1–6 are provable algebra (this file discharges them / hands them to the ATP); steps 7 and 8
are the two genuine arithmetic-geometry bridges Mathlib currently lacks (geometric integrality
under base change, and reduction of the Galois group under specialization).  The fully-worked `Aₙ`
development (`InverseGalois/Hilbert/AlternatingFamily*`,
`abs_irreducible_of_geometric_galois_alternating_odd`) is the template for both.

## Main results

* `IsRegularInverseGalois.isInverseGalois` — **step (B)**: a regular `ℚ(T)` realization of `G`
  yields an inverse-Galois realization over `ℚ`.  Proven from `exists_regular_family`.
* `exists_regular_family` — the model translation (decomposition above).
-/

open Polynomial

noncomputable section

section SpecCore

open UniqueFactorizationMonoid
open scoped Pointwise


attribute [local instance] Ideal.Quotient.field

variable
  (L : Type) [Field L] [Algebra (RatFunc ℚ) L] [FiniteDimensional (RatFunc ℚ) L]
  [IsGalois (RatFunc ℚ) L] [Algebra ℚ L] [IsScalarTower ℚ (RatFunc ℚ) L]
  [Algebra (Polynomial ℚ) L] [IsScalarTower (Polynomial ℚ) (RatFunc ℚ) L]

/-! ## Integral model `A = ℚ[T] ⊆ B = integralClosure A L`, and the place `P = (T - t)`. -/

/-- Integral closure of `ℚ[T]` in `L`; the ring `B` of the classical argument. -/
abbrev Bring : Type := integralClosure (Polynomial ℚ) L

noncomputable local instance instMSA :
    MulSemiringAction (L ≃ₐ[RatFunc ℚ] L) (Bring L) :=
  IsIntegralClosure.MulSemiringAction (Polynomial ℚ) (RatFunc ℚ) L (Bring L)

local instance instIsFrac : IsFractionRing (Bring L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial ℚ) (RatFunc ℚ) L (Bring L)

local instance instIGG : IsGaloisGroup (L ≃ₐ[RatFunc ℚ] L) (Polynomial ℚ) (Bring L) :=
  IsGaloisGroup.of_isFractionRing (L ≃ₐ[RatFunc ℚ] L) (Polynomial ℚ) (Bring L) (RatFunc ℚ) L

local instance instFinite : Module.Finite (Polynomial ℚ) (Bring L) :=
  IsIntegralClosure.finite (Polynomial ℚ) (RatFunc ℚ) L (Bring L)

local instance instFaithful : FaithfulSMul (Polynomial ℚ) (Bring L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have hAL : Function.Injective (algebraMap (Polynomial ℚ) L) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial ℚ) (RatFunc ℚ) L]
    exact (algebraMap (RatFunc ℚ) L).injective.comp
      (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))
  intro x y hxy
  apply hAL
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) (Bring L) L,
    IsScalarTower.algebraMap_apply (Polynomial ℚ) (Bring L) L, hxy]

/-- The place `P = (T - t)` of `ℚ[T]`. -/
abbrev placeP (t : ℤ) : Ideal (Polynomial ℚ) := Ideal.span {(X - C (t:ℚ) : Polynomial ℚ)}

instance placeP_max (t : ℤ) : (placeP t).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C _)

/-! ## Extra instances for the ramification computation. -/

local instance instDedekindB : IsDedekindDomain (Bring L) :=
  integralClosure.isDedekindDomain (Polynomial ℚ) (RatFunc ℚ) L

set_option synthInstance.maxHeartbeats 400000 in
local instance instTorsionFree : Module.IsTorsionFree (Polynomial ℚ) (Bring L) := inferInstance

local instance instFiniteGal : Finite (L ≃ₐ[RatFunc ℚ] L) := inferInstance

/-! ## The two genuine textbook gaps, isolated as named lemmas. -/

/-! **GAP (A) — unramified place ⟹ trivial inertia.**
When `specialize F t` is separable, the place `P = (T - t)` is unramified in `B`, hence the inertia
group `I_Q` of any prime `Q ∣ P` is trivial (as a subgroup of the decomposition group).

This is the genuine arithmetic-geometry crux: separability of `specialize F t` is equivalent to
`disc F` not vanishing at `t`, which is exactly the condition that `P` does not ramify.  The Mathlib
route would go through `Ideal.card_inertia_eq_ramificationIdxIn` together with a proof that the
ramification index `ramificationIdxIn P B = 1`; the latter connection (separable specialization ⟺
unramified) is not currently in Mathlib. -/
omit [Algebra ℚ L] [IsScalarTower ℚ (RatFunc ℚ) L] in
/-- **Residual sub-crux of GAP (A).**
The conductor of the integral generator `β` is coprime to the place `P = (T - t)` whenever the
specialization `specialize F t` is separable.  Mathematically: `F'(β) ∈ 𝔠 = conductor ℚ[T] β` (via
`conductor_mul_differentIdeal`), so `𝔠.comap ℚ[T]` contains a Galois-invariant multiple of `F'(β)`
whose value at `t` is (up to sign) `disc (specialize F t) ≠ 0`; hence `𝔠.comap ⊄ (T - t)`, i.e. the
two ideals are coprime (as `(T-t)` is maximal). -/
theorem conductor_coprime_of_separable
    (β : L) (hβint : IsIntegral (Polynomial ℚ) β)
    (hβtop : IntermediateField.adjoin (RatFunc ℚ) {β} = ⊤)
    (F : Polynomial (Polynomial ℚ)) (hF_def : F = minpoly (Polynomial ℚ) β)
    (t : ℤ) (hsep : (specialize F t).Separable) :
    (conductor (Polynomial ℚ) (⟨β, hβint⟩ : Bring L)).comap (algebraMap (Polynomial ℚ) (Bring L))
        ⊔ placeP t = ⊤ := by
  classical
  -- Monic / integrality data for `F` and `β`.
  have hFmonic : F.Monic := by rw [hF_def]; exact minpoly.monic hβint
  have hβK : IsIntegral (RatFunc ℚ) β := hβint.tower_top
  have hFK : minpoly (RatFunc ℚ) β = F.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
    rw [hF_def]; exact minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc ℚ) hβint
  have hadj : Algebra.adjoin (RatFunc ℚ) {β} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβK.isAlgebraic, hβtop,
        IntermediateField.top_toSubalgebra]
  -- The integral generator and its minimal polynomial.
  set xβ : Bring L := ⟨β, hβint⟩ with hxβ
  have hcoe : (algebraMap (Bring L) L) xβ = β := rfl
  have hminpoly : minpoly (Polynomial ℚ) xβ = F := by
    rw [hF_def, ← minpoly.algebraMap_eq (IsFractionRing.injective (Bring L) L) xβ, hcoe]
  -- The Galois-conductor generator `y = F'(β) ∈ 𝔠` (from `conductor_mul_differentIdeal`).
  set y : Bring L := aeval xβ (derivative (minpoly (Polynomial ℚ) xβ)) with hy_def
  have hcmd := conductor_mul_differentIdeal (Polynomial ℚ) (RatFunc ℚ) L xβ
    (by rw [hcoe]; exact hadj)
  rw [← hy_def] at hcmd
  have hy_cond : y ∈ conductor (Polynomial ℚ) xβ := by
    have hmem : y ∈ conductor (Polynomial ℚ) xβ * differentIdeal (Polynomial ℚ) (Bring L) := by
      rw [hcmd]; exact Ideal.mem_span_singleton_self y
    exact Ideal.mul_le_right hmem
  have hbLy : algebraMap (Bring L) L y = aeval β (derivative F) := by
    rw [hy_def, hminpoly, ← hcoe]
    exact (aeval_algHom_apply (IsScalarTower.toAlgHom (Polynomial ℚ) (Bring L) L) xβ
      (derivative F)).symm
  -- The resultant `dres = Res(F, F') ∈ ℚ[T]`; its specialization is the discriminant.
  set dres : Polynomial ℚ :=
    resultant F (derivative F) F.natDegree (derivative F).natDegree with hdres_def
  -- `F` maps to a monic polynomial that splits over `L` (as `L/ℚ(T)` is normal).
  have hFLmonic : (F.map (algebraMap (Polynomial ℚ) L)).Monic := hFmonic.map _
  have hFLsplits : (F.map (algebraMap (Polynomial ℚ) L)).Splits := by
    have hn := Normal.splits (inferInstance : Normal (RatFunc ℚ) L) β
    rwa [hFK, Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at hn
  -- `σ ↦ σ β` is injective, and its image is exactly the multiset of roots of `F` in `L`.
  have hinj : Function.Injective (fun σ : L ≃ₐ[RatFunc ℚ] L => σ β) := by
    intro σ τ hστ
    have hEq : (σ : L →ₐ[RatFunc ℚ] L) = (τ : L →ₐ[RatFunc ℚ] L) := by
      refine AlgHom.ext_of_adjoin_eq_top hadj ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hστ
    exact AlgEquiv.ext (fun x => DFunLike.congr_fun hEq x)
  have hTnodup : (Finset.univ.val.map (fun σ : L ≃ₐ[RatFunc ℚ] L => σ β)).Nodup :=
    Multiset.Nodup.map hinj Finset.univ.nodup
  have hcard_gal : Fintype.card (L ≃ₐ[RatFunc ℚ] L) = (minpoly (RatFunc ℚ) β).natDegree := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
        ← IntermediateField.finrank_top', ← hβtop,
        IntermediateField.adjoin.finrank hβK]
  have hFLdeg : (F.map (algebraMap (Polynomial ℚ) L)).natDegree
      = (minpoly (RatFunc ℚ) β).natDegree := by
    rw [hFmonic.natDegree_map, hFK, hFmonic.natDegree_map]
  have hTcard : (Finset.univ.val.map (fun σ : L ≃ₐ[RatFunc ℚ] L => σ β)).card
      = Fintype.card (L ≃ₐ[RatFunc ℚ] L) := by
    rw [Multiset.card_map]; rfl
  have hFLrootsCard : (F.map (algebraMap (Polynomial ℚ) L)).roots.card
      = Fintype.card (L ≃ₐ[RatFunc ℚ] L) := by
    rw [← hFLsplits.natDegree_eq_card_roots, hFLdeg, ← hcard_gal]
  have hsubset : (Finset.univ.val.map (fun σ : L ≃ₐ[RatFunc ℚ] L => σ β))
      ⊆ (F.map (algebraMap (Polynomial ℚ) L)).roots := by
    intro a ha
    rw [Multiset.mem_map] at ha
    obtain ⟨σ, _, rfl⟩ := ha
    have haev : aeval (σ β) F = σ (aeval β F) :=
      aeval_algHom_apply ((σ : L →ₐ[RatFunc ℚ] L).restrictScalars (Polynomial ℚ)) β F
    rw [Polynomial.mem_roots hFLmonic.ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map,
        ← Polynomial.aeval_def, haev, hF_def, minpoly.aeval, map_zero]
  have hset_eq : (F.map (algebraMap (Polynomial ℚ) L)).roots
      = Finset.univ.val.map (fun σ : L ≃ₐ[RatFunc ℚ] L => σ β) := by
    refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
    · exact (Multiset.le_iff_subset hTnodup).mpr hsubset
    · exact (hFLrootsCard.trans hTcard.symm).le
  -- The Galois product of `F'(β)` equals the image of the resultant in `L`.
  have hgalprod : (∏ σ : L ≃ₐ[RatFunc ℚ] L, σ (aeval β (derivative F)))
      = algebraMap (Polynomial ℚ) L dres := by
    have hR : algebraMap (Polynomial ℚ) L dres
        = ((F.map (algebraMap (Polynomial ℚ) L)).roots.map
            (fun α => aeval α (derivative F))).prod := by
      rw [hdres_def, ← resultant_map_map F (derivative F) F.natDegree (derivative F).natDegree
            (algebraMap (Polynomial ℚ) L),
          show F.natDegree = (F.map (algebraMap (Polynomial ℚ) L)).natDegree from
            (hFmonic.natDegree_map _).symm,
          resultant_eq_prod_eval (F.map (algebraMap (Polynomial ℚ) L))
            ((derivative F).map (algebraMap (Polynomial ℚ) L)) (derivative F).natDegree
            Polynomial.natDegree_map_le hFLsplits,
          hFLmonic.leadingCoeff, one_pow, one_mul]
      refine congrArg Multiset.prod (Multiset.map_congr rfl (fun α _ => ?_))
      rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [hR, Finset.prod_eq_multiset_prod, hset_eq, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl (fun σ _ => ?_))
    exact (aeval_algHom_apply ((σ : L →ₐ[RatFunc ℚ] L).restrictScalars (Polynomial ℚ)) β
      (derivative F)).symm
  -- Hence the resultant, pulled back to `B`, lies in the conductor (Galois product route).
  have hprodB :
      (∏ σ : L ≃ₐ[RatFunc ℚ] L, galRestrict (Polynomial ℚ) (RatFunc ℚ) L (Bring L) σ y)
        = algebraMap (Polynomial ℚ) (Bring L) dres := by
    apply IsFractionRing.injective (Bring L) L
    rw [map_prod, ← IsScalarTower.algebraMap_apply (Polynomial ℚ) (Bring L) L]
    simp_rw [algebraMap_galRestrict_apply]
    rw [hbLy]
    exact hgalprod
  have hdres_mem : algebraMap (Polynomial ℚ) (Bring L) dres ∈ conductor (Polynomial ℚ) xβ := by
    rw [← hprodB, ← Finset.mul_prod_erase Finset.univ
        (fun σ => galRestrict (Polynomial ℚ) (RatFunc ℚ) L (Bring L) σ y) (Finset.mem_univ 1)]
    simp only [map_one, AlgEquiv.one_apply]
    exact Ideal.mul_mem_right _ _ hy_cond
  -- Separability of `specialize F t` ⟹ the discriminant does not vanish at `t`.
  have hBne : dres.eval (t : ℚ) ≠ 0 := by
    intro hzero
    have hspecmonic : (specialize F t).Monic := by
      simp only [specialize]; exact hFmonic.map _
    set FE : Polynomial (AlgebraicClosure ℚ) :=
      (specialize F t).map (algebraMap ℚ (AlgebraicClosure ℚ)) with hFE_def
    have hFEmonic : FE.Monic := by rw [hFE_def]; exact hspecmonic.map _
    have hFEsep : FE.Separable := by rw [hFE_def]; exact hsep.map
    have hFEsplits : FE.Splits := IsAlgClosed.splits FE
    have hFEne : FE ≠ 0 := hFEmonic.ne_zero
    have hgE_def : derivative FE
        = (derivative (specialize F t)).map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      rw [hFE_def, Polynomial.derivative_map]
    have hFEdeg : FE.natDegree = F.natDegree := by
      rw [hFE_def, hspecmonic.natDegree_map]
      simp only [specialize]
      rw [hFmonic.natDegree_map]
    have hcompute : algebraMap ℚ (AlgebraicClosure ℚ) (dres.eval (t : ℚ))
        = (FE.roots.map (derivative FE).eval).prod := by
      have h0 : algebraMap ℚ (AlgebraicClosure ℚ) (dres.eval (t : ℚ))
          = ((algebraMap ℚ (AlgebraicClosure ℚ)).comp
              (Polynomial.evalRingHom (t : ℚ))) dres := rfl
      have hFmapψ : F.map ((algebraMap ℚ (AlgebraicClosure ℚ)).comp
            (Polynomial.evalRingHom (t : ℚ))) = FE := by
        rw [hFE_def]; simp only [specialize]; rw [Polynomial.map_map]
      have hgmapψ : (derivative F).map ((algebraMap ℚ (AlgebraicClosure ℚ)).comp
            (Polynomial.evalRingHom (t : ℚ))) = derivative FE := by
        rw [hgE_def]; simp only [specialize]; rw [Polynomial.derivative_map, Polynomial.map_map]
      rw [h0, hdres_def, ← resultant_map_map F (derivative F) F.natDegree (derivative F).natDegree
            ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (Polynomial.evalRingHom (t : ℚ))),
          hFmapψ, hgmapψ, ← hFEdeg,
          resultant_eq_prod_eval FE (derivative FE) (derivative F).natDegree ?hg hFEsplits,
          hFEmonic.leadingCoeff, one_pow, one_mul]
      case hg => rw [← hgmapψ]; exact Polynomial.natDegree_map_le
    rw [hzero, map_zero] at hcompute
    have hzero_mem := Multiset.prod_eq_zero_iff.mp hcompute.symm
    rw [Multiset.mem_map] at hzero_mem
    obtain ⟨α, hαroot, hαder⟩ := hzero_mem
    have hαFE : FE.eval α = 0 := (Polynomial.mem_roots hFEne).mp hαroot
    have hcop0 : IsCoprime FE (derivative FE) := hFEsep
    have hcop : IsCoprime (FE.eval α) ((derivative FE).eval α) := by
      simpa only [Polynomial.coe_evalRingHom] using hcop0.map (Polynomial.evalRingHom α)
    rw [hαFE, hαder] at hcop
    exact (isCoprime_zero_left.mp hcop).ne_zero rfl
  -- Assemble: if the two ideals were not coprime, `(T - t)` would contain the discriminant.
  by_contra hne
  have hle : (conductor (Polynomial ℚ) xβ).comap (algebraMap (Polynomial ℚ) (Bring L))
      ≤ placeP t := by
    have heq := (placeP_max t).eq_of_le hne le_sup_right
    exact le_sup_left.trans heq.ge
  have hmem : dres ∈ (conductor (Polynomial ℚ) xβ).comap (algebraMap (Polynomial ℚ) (Bring L)) :=
    Ideal.mem_comap.mpr hdres_mem
  have hdt : dres ∈ placeP t := hle hmem
  rw [placeP, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot] at hdt
  exact hBne hdt

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
omit [Algebra ℚ L] [IsScalarTower ℚ (RatFunc ℚ) L] in
theorem inertia_trivial_of_separable
    (β : L) (hβint : IsIntegral (Polynomial ℚ) β)
    (hβtop : IntermediateField.adjoin (RatFunc ℚ) {β} = ⊤)
    (F : Polynomial (Polynomial ℚ)) (hF_def : F = minpoly (Polynomial ℚ) β)
    (_hFmap : minpoly (RatFunc ℚ) β = F.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)))
    (t : ℤ) (hsep : (specialize F t).Separable)
    (Q : Ideal (Bring L)) [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    (Q.inertia (L ≃ₐ[RatFunc ℚ] L)).subgroupOf
      (MulAction.stabilizer (L ≃ₐ[RatFunc ℚ] L) Q) = ⊥ := by
  classical
  haveI : Q.IsPrime := ‹Q.IsMaximal›.isPrime
  -- residue-field instances (char 0 ⟹ perfect ⟹ separable residue).
  haveI : CharZero (Polynomial ℚ ⧸ placeP t) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (Polynomial ℚ ⧸ placeP t)).injective
  haveI : Algebra.IsSeparable (Polynomial ℚ ⧸ placeP t) (Bring L ⧸ Q) := inferInstance
  -- basic nonvanishing facts.
  have hPbot : placeP t ≠ ⊥ := by
    rw [placeP, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero _
  have hmapne : Ideal.map (algebraMap (Polynomial ℚ) (Bring L)) (placeP t) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (Polynomial ℚ) (Bring L))).not.mpr hPbot
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hPbot Q
  have hQirr : Irreducible Q := (Ideal.prime_of_isPrime hQne inferInstance).irreducible
  -- `Q` divides `P·B`, hence is a normalized factor of it.
  have hQdvd : Q ∣ Ideal.map (algebraMap (Polynomial ℚ) (Bring L)) (placeP t) := by
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← Ideal.under_def]
    exact le_of_eq (Ideal.over_def Q (placeP t))
  have hJ : Q ∈ normalizedFactors (Ideal.map (algebraMap (Polynomial ℚ) (Bring L)) (placeP t)) := by
    rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hmapne]
    exact ⟨hQirr, normalize_eq Q, hQdvd⟩
  -- the integral generator, as an element of `B`, and its minimal polynomial.
  set xβ : Bring L := ⟨β, hβint⟩ with hxβ
  have hxint : IsIntegral (Polynomial ℚ) xβ := integralClosure.isIntegral xβ
  have hcoe : (algebraMap (Bring L) L) xβ = β := rfl
  have hminpoly : minpoly (Polynomial ℚ) xβ = F := by
    rw [hF_def, ← minpoly.algebraMap_eq (IsFractionRing.injective (Bring L) L) xβ, hcoe]
  -- coprimality of conductor and place (the residual sub-crux).
  have hx := conductor_coprime_of_separable L β hβint hβtop F hF_def t hsep
  -- `(minpoly xβ).map (mk (T-t))` is squarefree because `specialize F t` is separable.
  -- We transport squarefreeness across the ring isomorphism `ℚ[X]/(T-t) ≅ ℚ` on coefficients.
  -- `φRH : ℚ[X]/(T-t) →+* ℚ` sends `mk g` to `g(t)`; `ψRH` is its inverse.
  -- Build the ring iso `ℚ[X]/(T-t) ≅ ℚ` via the first isomorphism theorem for `eval t`,
  -- deliberately avoiding the `AlgEquiv` (whose `ℚ`-algebra instance clashes with the
  -- `DivisionRing.toRatAlgebra` structure on the quotient field).
  have hker : RingHom.ker (Polynomial.evalRingHom (t : ℚ)) = placeP t :=
    Polynomial.ker_evalRingHom (t : ℚ)
  set φE : (Polynomial ℚ ⧸ placeP t) ≃+* ℚ :=
    (Ideal.quotEquivOfEq hker).symm.trans
      (RingHom.quotientKerEquivOfRightInverse
        (f := Polynomial.evalRingHom (t : ℚ)) (g := fun a : ℚ => Polynomial.C a)
        (fun a => Polynomial.eval_C)) with hφE
  set φRH : (Polynomial ℚ ⧸ placeP t) →+* ℚ := φE.toRingHom with hφRH
  set ψRH : ℚ →+* (Polynomial ℚ ⧸ placeP t) := φE.symm.toRingHom with hψRH
  have hcomp : φRH.comp (Ideal.Quotient.mk (placeP t)) = Polynomial.evalRingHom (t : ℚ) := by
    refine RingHom.ext fun g => ?_
    show φE (Ideal.Quotient.mk (placeP t) g) = g.eval (t : ℚ)
    rw [hφE, RingEquiv.trans_apply, Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfRightInverse.apply, RingHom.kerLift_mk]
    rfl
  have hid : ψRH.comp φRH = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    simp [hφRH, hψRH]
  have htrans : ((minpoly (Polynomial ℚ) xβ).map (Ideal.Quotient.mk (placeP t))).map φRH
      = specialize F t := by
    rw [Polynomial.map_map, hcomp, hminpoly]; rfl
  have hsqfree : Squarefree
      ((minpoly (Polynomial ℚ) xβ).map (Ideal.Quotient.mk (placeP t))) := by
    intro x hx
    have hu : IsUnit (x.map φRH) := by
      apply hsep.squarefree
      rw [← htrans, ← Polynomial.map_mul]
      exact Polynomial.map_dvd _ hx
    have hback : (x.map φRH).map ψRH = x := by
      rw [Polynomial.map_map, hid, Polynomial.map_id]
    have h2 := hu.map (Polynomial.mapRingHom ψRH)
    rwa [Polynomial.coe_mapRingHom, hback] at h2
  -- the Kummer–Dedekind factor corresponding to `Q`.
  have hd_mem :
      (↑(KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
          (placeP_max t) hPbot hx hxint ⟨Q, hJ⟩) : Polynomial (Polynomial ℚ ⧸ placeP t))
      ∈ normalizedFactors ((minpoly (Polynomial ℚ) xβ).map (Ideal.Quotient.mk (placeP t))) :=
    (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
      (placeP_max t) hPbot hx hxint ⟨Q, hJ⟩).2
  -- ramification index = multiplicity of `Q` = multiplicity of the factor = 1.
  have hcount :
      (normalizedFactors (Ideal.map (algebraMap (Polynomial ℚ) (Bring L)) (placeP t))).count Q
        = 1 := by
    have hemult :
        emultiplicity Q (Ideal.map (algebraMap (Polynomial ℚ) (Bring L)) (placeP t)) = 1 := by
      rw [KummerDedekind.emultiplicity_factors_map_eq_emultiplicity
            (placeP_max t) hPbot hx hxint hJ]
      refine le_antisymm ?_ ?_
      · rcases (squarefree_iff_emultiplicity_le_one
            ((minpoly (Polynomial ℚ) xβ).map (Ideal.Quotient.mk (placeP t)))).mp hsqfree
            (↑(KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
                (placeP_max t) hPbot hx hxint ⟨Q, hJ⟩)) with h | h
        · exact h
        · exact absurd h (irreducible_of_normalized_factor _ hd_mem).not_isUnit
      · exact pow_dvd_iff_le_emultiplicity.mp (by simpa using dvd_of_mem_normalizedFactors hd_mem)
    rw [emultiplicity_eq_count_normalizedFactors hQirr hmapne, normalize_eq] at hemult
    exact_mod_cast hemult
  -- assemble: trivial inertia ⟺ ramification index 1.
  suffices hbot : Q.inertia (L ≃ₐ[RatFunc ℚ] L) = ⊥ by
    rw [hbot, Subgroup.bot_subgroupOf]
  rw [Subgroup.eq_bot_iff_card,
    Ideal.card_inertia_eq_ramificationIdxIn (placeP t) hPbot Q,
    Ideal.ramificationIdxIn_eq_ramificationIdx (placeP t) Q (L ≃ₐ[RatFunc ℚ] L),
    Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hmapne inferInstance hQne]
  exact hcount

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
omit [IsScalarTower ℚ (RatFunc ℚ) L] in
/-- **GAP (B), genuine content: the residue field is a splitting field.**
The residue field `B/Q`, regarded as a `ℚ`-algebra (equivalently a `κ(P)`-algebra, since
`κ(P) = ℚ[T]/(T-t) ≅ ℚ`), is a splitting field of `specialize F t` over `ℚ`.

This is exactly the Kummer–Dedekind root-tracking statement: the reductions mod `Q` of the roots of
`F` (which lie in `B`) are the roots of `specialize F t`, they are distinct by separability, and
because `β` generates `L` over `ℚ(T)` its reduction already generates `B/Q` over `κ(P)`.  This is the
part not packaged in Mathlib; it needs the conductor-coprimality sub-crux
`conductor_coprime_of_separable` shared with GAP (A). -/
theorem bQuot_isSplittingField_specialize
    (β : L) (hβint : IsIntegral (Polynomial ℚ) β)
    (hβtop : IntermediateField.adjoin (RatFunc ℚ) {β} = ⊤)
    (F : Polynomial (Polynomial ℚ)) (hF_def : F = minpoly (Polynomial ℚ) β)
    (hFmap : minpoly (RatFunc ℚ) β = F.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)))
    (t : ℤ) (hsep : (specialize F t).Separable)
    (Q : Ideal (Bring L)) [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    IsSplittingField ℚ (Bring L ⧸ Q) (specialize F t) := by
  classical
  haveI : Q.IsPrime := ‹Q.IsMaximal›.isPrime
  set xβ : Bring L := ⟨β, hβint⟩ with hxβ
  have hxint : IsIntegral (Polynomial ℚ) xβ := integralClosure.isIntegral xβ
  have hcoe : (algebraMap (Bring L) L) xβ = β := rfl
  have hminpoly : minpoly (Polynomial ℚ) xβ = F := by
    rw [hF_def, ← minpoly.algebraMap_eq (IsFractionRing.injective (Bring L) L) xβ, hcoe]
  have hFmonic : F.Monic := hminpoly ▸ minpoly.monic hxint
  -- coprimality (GAP A sub-crux), folded to `xβ`
  have hx := conductor_coprime_of_separable L β hβint hβtop F hF_def t hsep
  rw [← hxβ] at hx
  have h_alg : Function.Injective
      (algebraMap (↥(Algebra.adjoin (Polynomial ℚ) {xβ})) (Bring L)) :=
    FaithfulSMul.algebraMap_injective _ _
  -- `P·B ≤ Q`
  have hPBle : Ideal.map (algebraMap (Polynomial ℚ) (Bring L)) (placeP t) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def]
    exact le_of_eq (Ideal.over_def Q (placeP t))
  -- `algebraMap (X - C t) ∈ Q`
  have hmemQ : algebraMap (Polynomial ℚ) (Bring L) (X - C (t : ℚ)) ∈ Q := by
    have h1 : (X - C (t : ℚ)) ∈ placeP t := Ideal.mem_span_singleton_self _
    rw [Ideal.over_def Q (placeP t), Ideal.under_def, Ideal.mem_comap] at h1
    exact h1
  -- key compatibility square `κ(P) ≅ ℚ`
  have hCt : ((Ideal.Quotient.mk Q).comp (algebraMap (Polynomial ℚ) (Bring L))).comp
      (Polynomial.C) = algebraMap ℚ (Bring L ⧸ Q) := Subsingleton.elim _ _
  have hfX : (Polynomial.evalRingHom (t : ℚ)) X = (t : ℚ) := by simp
  have hπ : (algebraMap ℚ (Bring L ⧸ Q)).comp (Polynomial.evalRingHom (t : ℚ))
      = (Ideal.Quotient.mk Q).comp (algebraMap (Polynomial ℚ) (Bring L)) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    have e1 : Ideal.Quotient.mk Q (algebraMap (Polynomial ℚ) (Bring L) X)
        = Ideal.Quotient.mk Q (algebraMap (Polynomial ℚ) (Bring L) (C (t : ℚ))) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmemQ
    show (algebraMap ℚ (Bring L ⧸ Q)) ((Polynomial.evalRingHom (t : ℚ)) X)
        = (Ideal.Quotient.mk Q) (algebraMap (Polynomial ℚ) (Bring L) X)
    rw [hfX, e1, ← hCt]
    rfl
  -- polynomial identity: `specialize F t` mapped to `B/Q` equals `(F over B)` mapped by `mk Q`
  have hpoly : (specialize F t).map (algebraMap ℚ (Bring L ⧸ Q))
      = (F.map (algebraMap (Polynomial ℚ) (Bring L))).map (Ideal.Quotient.mk Q) := by
    show (F.map (Polynomial.evalRingHom (t : ℚ))).map (algebraMap ℚ (Bring L ⧸ Q))
        = (F.map (algebraMap (Polynomial ℚ) (Bring L))).map (Ideal.Quotient.mk Q)
    rw [Polynomial.map_map, hπ, ← Polynomial.map_map]
  -- `F` splits over `L` (Galois ⟹ normal)
  have hFsplitsL : Splits (F.map (algebraMap (Polynomial ℚ) L)) := by
    have hN : Splits ((minpoly (RatFunc ℚ) β).map (algebraMap (RatFunc ℚ) L)) :=
      Normal.splits inferInstance β
    rwa [hFmap, Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq (Polynomial ℚ) (RatFunc ℚ) L] at hN
  have hpM : (F.map (algebraMap (Polynomial ℚ) L)).Monic := hFmonic.map _
  -- the roots of `F` over `L` are integral, hence live in `B`
  have hint : ∀ a ∈ (F.map (algebraMap (Polynomial ℚ) L)).roots,
      IsIntegral (Polynomial ℚ) a := by
    intro a ha
    refine ⟨F, hFmonic, ?_⟩
    rw [← Polynomial.eval_map]
    exact (Polynomial.mem_roots'.mp ha).2
  obtain ⟨rootsB, hrootsB⟩ :
      ∃ m : Multiset (Bring L), m =
        (F.map (algebraMap (Polynomial ℚ) L)).roots.attach.map
          (fun a => (⟨a.1, hint a.1 a.2⟩ : Bring L)) := ⟨_, rfl⟩
  have hmapι : rootsB.map (algebraMap (Bring L) L)
      = (F.map (algebraMap (Polynomial ℚ) L)).roots := by
    rw [hrootsB, Multiset.map_map]
    rw [show ((algebraMap (Bring L) L) ∘
        (fun a : {x // x ∈ (F.map (algebraMap (Polynomial ℚ) L)).roots} =>
          (⟨a.1, hint a.1 a.2⟩ : Bring L)))
        = (fun a => a.1) from rfl]
    exact Multiset.attach_map_val _
  -- `F` over `B` is a product of monic linear factors
  have hL : F.map (algebraMap (Polynomial ℚ) L)
      = (rootsB.map (fun b => X - C ((algebraMap (Bring L) L) b))).prod := by
    rw [hFsplitsL.eq_prod_roots_of_monic hpM, ← hmapι, Multiset.map_map]
    rfl
  have hFB : F.map (algebraMap (Polynomial ℚ) (Bring L))
      = (rootsB.map (fun b => X - C b)).prod := by
    apply Polynomial.map_injective (algebraMap (Bring L) L)
      (IsFractionRing.injective (Bring L) L)
    have hLHS : (F.map (algebraMap (Polynomial ℚ) (Bring L))).map (algebraMap (Bring L) L)
        = F.map (algebraMap (Polynomial ℚ) L) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq (Polynomial ℚ) (Bring L) L]
    have hRHS : ((rootsB.map (fun b => X - C b)).prod).map (algebraMap (Bring L) L)
        = (rootsB.map (fun b => X - C ((algebraMap (Bring L) L) b))).prod := by
      rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro b _
      simp [Function.comp, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hLHS, hRHS]; exact hL
  -- assemble the two `IsSplittingField` obligations
  refine ⟨?_, ?_⟩
  · -- splits
    rw [hpoly]
    refine Splits.map ?_ (Ideal.Quotient.mk Q)
    rw [hFB]
    refine Splits.multisetProd (fun g hg => ?_)
    obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hg
    have hb := Splits.X_add_C (R := Bring L) (-b)
    rwa [map_neg, ← sub_eq_add_neg] at hb
  · -- roots generate `B/Q` over `ℚ`
    have haevalβ : aeval xβ F = 0 := by
      rw [← hminpoly]; exact minpoly.aeval (Polynomial ℚ) xβ
    have hβroot : Ideal.Quotient.mk Q xβ ∈ (specialize F t).rootSet (Bring L ⧸ Q) := by
      rw [Polynomial.mem_rootSet']
      refine ⟨?_, ?_⟩
      · rw [hpoly]
        exact ((hFmonic.map (algebraMap (Polynomial ℚ) (Bring L))).map
          (Ideal.Quotient.mk Q)).ne_zero
      · rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpoly, Polynomial.eval_map,
          Polynomial.eval₂_hom, Polynomial.eval_map, ← Polynomial.aeval_def, haevalβ, map_zero]
    have hgen : ∀ r : Polynomial ℚ,
        Ideal.Quotient.mk Q (algebraMap (Polynomial ℚ) (Bring L) r)
        = algebraMap ℚ (Bring L ⧸ Q) ((Polynomial.evalRingHom (t : ℚ)) r) := by
      intro r
      have h := DFunLike.congr_fun hπ r
      simpa [RingHom.comp_apply] using h.symm
    have hsurjg : Function.Surjective
        (fun a : ↥(Algebra.adjoin (Polynomial ℚ) {xβ}) =>
          Ideal.Quotient.mk Q (↑a : Bring L)) := by
      intro y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨z, hz⟩ := (quotAdjoinEquivQuotMap hx h_alg).surjective
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap (Polynomial ℚ) (Bring L)) (placeP t)) b)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [quotAdjoinEquivQuotMap_apply_mk] at hz
      refine ⟨a, ?_⟩
      show Ideal.Quotient.mk Q (↑a : Bring L) = Ideal.Quotient.mk Q b
      rw [Ideal.Quotient.eq] at hz ⊢
      exact hPBle hz
    have hadjβ : Algebra.adjoin ℚ {Ideal.Quotient.mk Q xβ} = ⊤ := by
      rw [Algebra.eq_top_iff]
      intro y
      obtain ⟨a, rfl⟩ := hsurjg y
      show Ideal.Quotient.mk Q (↑a : Bring L) ∈ Algebra.adjoin ℚ {Ideal.Quotient.mk Q xβ}
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ a.2
      · intro w hwmem
        rw [Set.mem_singleton_iff.mp hwmem]
        exact Algebra.self_mem_adjoin_singleton _ _
      · intro r
        rw [hgen r]
        exact Subalgebra.algebraMap_mem _ _
      · intro u v _ _ hu hv
        rw [map_add]; exact add_mem hu hv
      · intro u v _ _ hu hv
        rw [map_mul]; exact mul_mem hu hv
    refine top_le_iff.mp ?_
    rw [← hadjβ]
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hβroot)

set_option synthInstance.maxHeartbeats 400000 in
omit [IsScalarTower ℚ (RatFunc ℚ) L] in
/-- **GAP (B) — residue identification.**
The Galois group of the specialized polynomial `specialize F t` embeds into the residue-field Galois
group `Gal(κ(Q)/κ(P)) = Gal((B/Q)/(ℚ[T]/P))`.

Mathematically: `κ(P) = ℚ[T]/(T-t) ≅ ℚ`, the reductions mod `Q` of the roots of `F` in `B` are the
roots of `specialize F t`, and separability makes them distinct; so `B/Q` contains a splitting field
of `specialize F t` over `ℚ` and the restriction map identifies `Gal(specialize F t)` with a
subgroup of the residue Galois group.  Formalizing this requires tracking the roots of `F` through
reduction mod `Q`, which is not packaged in Mathlib. -/
theorem residue_gal_embedding
    (β : L) (hβint : IsIntegral (Polynomial ℚ) β)
    (hβtop : IntermediateField.adjoin (RatFunc ℚ) {β} = ⊤)
    (F : Polynomial (Polynomial ℚ)) (hF_def : F = minpoly (Polynomial ℚ) β)
    (hFmap : minpoly (RatFunc ℚ) β = F.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)))
    (t : ℤ) (hsep : (specialize F t).Separable)
    (Q : Ideal (Bring L)) [Q.IsMaximal] [Q.LiesOver (placeP t)] :
    ∃ j : (specialize F t).Gal →*
      ((Bring L ⧸ Q) ≃ₐ[Polynomial ℚ ⧸ placeP t] (Bring L ⧸ Q)), Function.Injective j := by
  classical
  -- `κ(P) = ℚ[T]/(T-t) ≅ ℚ`, so `algebraMap ℚ κ(P)` is surjective.
  have hsurj : Function.Surjective (algebraMap ℚ (Polynomial ℚ ⧸ placeP t)) := fun r =>
    ⟨Polynomial.quotientSpanXSubCAlgEquiv (t : ℚ) r,
      (Polynomial.quotientSpanXSubCAlgEquiv_symm_apply (t : ℚ) _).symm.trans
        ((Polynomial.quotientSpanXSubCAlgEquiv (t : ℚ)).symm_apply_apply r)⟩
  -- GAP (B) genuine content: `B/Q` is a splitting field of `specialize F t` over `ℚ`.
  haveI hSF : IsSplittingField ℚ (Bring L ⧸ Q) (specialize F t) :=
    bQuot_isSplittingField_specialize L β hβint hβtop F hF_def hFmap t hsep Q
  -- Hence `Gal(specialize F t) ≃* (B/Q ≃ₐ[ℚ] B/Q)` by conjugating with the splitting-field iso.
  let ε : (specialize F t).Gal ≃* ((Bring L ⧸ Q) ≃ₐ[ℚ] (Bring L ⧸ Q)) :=
    (IsSplittingField.algEquiv (Bring L ⧸ Q) (specialize F t)).autCongr.symm
  -- A `ℚ`-algebra automorphism of `B/Q` is automatically a `κ(P)`-algebra automorphism, since
  -- `algebraMap ℚ κ(P)` is surjective; this gives an injective monoid hom into the target.
  let toK : ((Bring L ⧸ Q) ≃ₐ[ℚ] (Bring L ⧸ Q)) →*
      ((Bring L ⧸ Q) ≃ₐ[Polynomial ℚ ⧸ placeP t] (Bring L ⧸ Q)) :=
    { toFun := fun e => AlgEquiv.ofRingEquiv (f := (e : (Bring L ⧸ Q) ≃+* (Bring L ⧸ Q))) (fun r => by
        obtain ⟨q, rfl⟩ := hsurj r
        rw [← IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ ⧸ placeP t) (Bring L ⧸ Q)]
        exact e.commutes q)
      map_one' := by ext x; rfl
      map_mul' := fun a b => by ext x; rfl }
  have htoK_inj : Function.Injective toK := by
    intro a b hab
    exact AlgEquiv.ext fun x => (AlgEquiv.ext_iff.mp hab x)
  exact ⟨toK.comp ε.toMonoidHom, htoK_inj.comp ε.injective⟩

/-! ## The genuine mathematical core, assembled from the two gaps. -/

set_option synthInstance.maxHeartbeats 400000 in
omit [IsScalarTower ℚ (RatFunc ℚ) L] in
/-- **The heart of Hilbert-irreducibility specialization.**
For a separable specialization `t`, the Galois group of `specialize F t` over `ℚ` embeds into the
generic Galois group `Gal(L / ℚ(T))`.

Choose the place `P = (T - t)` and a prime `Q` of `B = integralClosure ℚ[T] L` lying over `P`.
`GAP (A)` gives trivial inertia `I_Q`, so the decomposition group
`D_Q = stabilizer Q ↪ Gal(L/ℚ(T))` maps isomorphically onto the residue Galois group
`Gal(κ(Q)/κ(P))`; `GAP (B)` embeds `Gal(specialize F t)` into that residue Galois group.  Composing
these produces the desired injection. -/
theorem specialization_gal_embeds
    (β : L) (hβint : IsIntegral (Polynomial ℚ) β)
    (hβtop : IntermediateField.adjoin (RatFunc ℚ) {β} = ⊤)
    (F : Polynomial (Polynomial ℚ)) (hF_def : F = minpoly (Polynomial ℚ) β)
    (_hFmonic : F.Monic)
    (hFmap : minpoly (RatFunc ℚ) β = F.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)))
    (t : ℤ) (hsep : (specialize F t).Separable) :
    ∃ g : (specialize F t).Gal →* (L ≃ₐ[RatFunc ℚ] L), Function.Injective g := by
  classical
  -- A prime `Q` of `B` lying over `P = (T - t)`.
  obtain ⟨Q, hQmax, hQlo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := Bring L) (placeP t)
  haveI := hQmax
  haveI := hQlo
  haveI : Q.IsPrime := hQmax.isPrime
  -- residue-field instances: `κ(P) = ℚ[T]/(T-t) ≅ ℚ` is char 0 (hence perfect), `B/Q` separable.
  haveI : CharZero (Polynomial ℚ ⧸ placeP t) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (Polynomial ℚ ⧸ placeP t)).injective
  haveI : Algebra.IsSeparable (Polynomial ℚ ⧸ placeP t) (Bring L ⧸ Q) := inferInstance
  -- GAP (A): trivial inertia.
  have hI := inertia_trivial_of_separable L β hβint hβtop F hF_def hFmap t hsep Q
  -- GAP (B): residue identification.
  obtain ⟨j, hj⟩ := residue_gal_embedding L β hβint hβtop F hF_def hFmap t hsep Q
  -- Composition: `Gal(F(t)) ↪ Gal(κ(Q)/κ(P)) ≃ D_Q/I_Q ≃ D_Q ↪ Gal(L/ℚ(T))`.
  let e1 := (Ideal.Quotient.stabilizerQuotientInertiaEquiv (L ≃ₐ[RatFunc ℚ] L) (placeP t) Q).symm
  let e2 := (QuotientGroup.quotientMulEquivOfEq hI).trans QuotientGroup.quotientBot
  let sub : MulAction.stabilizer (L ≃ₐ[RatFunc ℚ] L) Q →* (L ≃ₐ[RatFunc ℚ] L) :=
    (MulAction.stabilizer (L ≃ₐ[RatFunc ℚ] L) Q).subtype
  refine ⟨sub.comp (e2.toMonoidHom.comp (e1.toMonoidHom.comp j)), ?_⟩
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact Subtype.val_injective.comp (e2.injective.comp (e1.injective.comp hj))

end SpecCore

set_option maxHeartbeats 800000 in
/-- **Model translation** (task L4): from an abstract regular Galois realization of `G` over `ℚ(T)`,
produce the explicit `of_regular_family` hypothesis bundle — a permutation degree `n`, a subgroup
`H ≤ Sₙ` isomorphic to `G`, and a monic `ℚ[T][X]` family `F` with resolvent `Gp` satisfying all the
regularity/landing/root certificates that `IsInverseGalois.of_regular_family` consumes.

This isolates *all* of step (B)'s remaining content into a single existence statement.  Its proof
(see the module docstring) is the primitive-element / integral-closure construction, whose only
non-algebraic ingredients are the two arithmetic-geometry bridges `absIrreducible_family_of_regular`
(the regularity teeth) and `landing_family_of_regular` (the reduction map). -/
theorem exists_regular_family {G : Type} [Group G] [Finite G]
    (h : IsRegularInverseGalois G) :
    ∃ (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) (_e : H ≃* G)
      (F Gp : Polynomial (Polynomial ℚ)),
      F.Monic ∧ F.natDegree = n ∧ Gp.Monic ∧ Gp.natDegree = Nat.card H ∧
      Irreducible Gp ∧
      Irreducible (Gp.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
      {t : ℤ | ¬ (specialize F t).Separable}.Finite ∧
      (∀ t : ℤ, (specialize F t).Separable →
          ∃ g' : (specialize F t).Gal →* H, Function.Injective g') ∧
      (∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize Gp t) = 0) := by
  obtain ⟨L, _fL, _aL, _fdL, _galL, _aQL, _stL, hreg, ⟨φ⟩⟩ := h
  -- Permutation model: the regular (Cayley) representation `G ↪ Sₙ`, `n = |G|`.
  set n : ℕ := Nat.card G with hn
  set φG : G →* Equiv.Perm (Fin n) := Rigidity.cayley G with hφG_def
  have hφG : Function.Injective φG := Rigidity.cayley_injective
  set H : Subgroup (Equiv.Perm (Fin n)) := φG.range with hH_def
  set e : H ≃* G := (MonoidHom.ofInjective hφG).symm with he_def
  have hcardH : Nat.card H = n := by rw [Nat.card_congr e.toEquiv]
  -- Numeric backbone: `[L : ℚ(T)] = |Gal| = |G| = n`.
  have hcardGal : Nat.card (L ≃ₐ[RatFunc ℚ] L) = n := Nat.card_congr φ.toEquiv
  have hfinrank : Module.finrank (RatFunc ℚ) L = n := by
    rw [← hcardGal, IsGalois.card_aut_eq_finrank]
  -- A primitive element `α` for `L / ℚ(T)`, then an integral multiple `β` over `ℚ[T]`.
  letI : Algebra (Polynomial ℚ) L :=
    ((algebraMap (RatFunc ℚ) L).comp (algebraMap (Polynomial ℚ) (RatFunc ℚ))).toAlgebra
  haveI : IsScalarTower (Polynomial ℚ) (RatFunc ℚ) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (RatFunc ℚ) L
  have hαalg : IsAlgebraic (Polynomial ℚ) α := by
    have hα_alg_rat : IsAlgebraic (RatFunc ℚ) α := by
      exact ((Algebra.IsIntegral.of_finite (RatFunc ℚ) L).isAlgebraic).isAlgebraic α
    obtain ⟨p, hp_ne, hp_root⟩ := hα_alg_rat
    haveI : IsFractionRing (Polynomial ℚ) (RatFunc ℚ) := by infer_instance
    have hcoeff : ∀ i ∈ p.support, ∃ (b : Polynomial ℚ), b ≠ 0 ∧
        ∃ (a : Polynomial ℚ), algebraMap (Polynomial ℚ) (RatFunc ℚ) a = b * p.coeff i := by
      intro i hi
      have hsurj := IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial ℚ)) (p.coeff i)
      obtain ⟨x, hx⟩ := hsurj
      refine ⟨x.2, ?_, x.1, ?_⟩
      · exact mem_nonZeroDivisors_iff_ne_zero.mp x.2.property
      · have hmk : IsLocalization.mk' (RatFunc ℚ) x.1 x.2 = p.coeff i := by simpa using hx
        rw [← hmk]
        have hne : (algebraMap (Polynomial ℚ) (RatFunc ℚ) (x.2 : Polynomial ℚ)) ≠ 0 := by
          intro h
          have h0 : (algebraMap (Polynomial ℚ) (RatFunc ℚ) 0 : RatFunc ℚ) = 0 := by simp
          have := (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)) (h.trans h0.symm)
          exact absurd this (mem_nonZeroDivisors_iff_ne_zero.mp x.2.property)
        have hmk_def : IsLocalization.mk' (RatFunc ℚ) x.1 x.2 =
            algebraMap (Polynomial ℚ) (RatFunc ℚ) x.1 / algebraMap (Polynomial ℚ) (RatFunc ℚ) (x.2 : Polynomial ℚ) := by
          have hspec : IsLocalization.mk' (RatFunc ℚ) x.1 x.2 * algebraMap (Polynomial ℚ) (RatFunc ℚ) (x.2 : Polynomial ℚ) =
              algebraMap (Polynomial ℚ) (RatFunc ℚ) x.1 := by
            exact IsLocalization.mk'_spec _ _ _
          rw [← hspec, mul_div_cancel_right₀ _ hne]
        rw [hmk_def]
        field_simp
        rfl
    choose! b hb_ne hb using hcoeff
    let d := p.support.prod (fun i => b i)
    have hd_ne : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hb_ne i hi)
    have hcommon : ∀ i ∈ p.support, ∃ (c_i : Polynomial ℚ),
        algebraMap (Polynomial ℚ) (RatFunc ℚ) c_i = d * p.coeff i := by
      intro i hi
      obtain ⟨a_i, ha_i⟩ := hb i hi
      use a_i * (∏ j ∈ p.support \ {i}, b j)
      have hprod_eq : ∏ j ∈ p.support, (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (b j) =
          (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (b i) * (∏ j ∈ p.support \ {i}, (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (b j)) := by
        rw [Finset.sdiff_singleton_eq_erase, ← Finset.mul_prod_erase _ _ hi]
      have hd_prod : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) d =
          ∏ j ∈ p.support, (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (b j) := by
        simp [d]
      simp only [map_mul]
      rw [ha_i, show (↑d : RatFunc ℚ) = (algebraMap (Polynomial ℚ) (RatFunc ℚ)) d from rfl, hd_prod, hprod_eq, show (↑(b i) : RatFunc ℚ) = (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (b i) from rfl]
      rw [show (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (∏ j ∈ p.support \ {i}, b j) = ∏ j ∈ p.support \ {i}, (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (b j) from (map_prod (algebraMap (Polynomial ℚ) (RatFunc ℚ)) _ _)]
      ring
    choose! c hc using hcommon
    let q : Polynomial (Polynomial ℚ) :=
      ∑ i ∈ p.support, c i • Polynomial.X ^ i
    have hcoeff_q : ∀ i ∈ p.support, (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (q.coeff i) = ↑d * p.coeff i := by
      intro i hi
      have hci' := hc i hi
      have hcoeff_ci : ∀ j ∈ p.support, (c j • Polynomial.X ^ j).coeff i = if j = i then c i else 0 := by
        intro j hj
        simp [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        by_cases hij : i = j <;> simp [hij, eq_comm]
      have hqi : q.coeff i = ∑ j ∈ p.support, (if j = i then c i else 0) := by
        simp [q]
      rw [hqi, Finset.sum_ite_eq']
      simp [hi]
      exact hci'
    have hq_ne : q ≠ 0 := by
      intro hq_zero
      apply hp_ne
      obtain ⟨i, hi⟩ := p.support.nonempty_of_ne_empty (by
        intro h; exact hp_ne (Polynomial.ext fun j => by
          by_contra hj; exact absurd (Polynomial.mem_support_iff.mpr hj) (by rw [h]; simp)))
      have := hcoeff_q i hi
      rw [hq_zero, Polynomial.coeff_zero, map_zero] at this
      have hd_ne' : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) d ≠ 0 := by
        intro h
        exact hd_ne ((IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)) (h.trans (map_zero _).symm))
      have : p.coeff i = 0 := by
        have h2 : (↑d : RatFunc ℚ) * p.coeff i = 0 := this.symm
        exact (mul_eq_zero.mp h2).resolve_left hd_ne'
      exact absurd hi (by simpa [Polynomial.mem_support_iff] using this)
    have halg_factor : ∀ r : Polynomial ℚ, (algebraMap (Polynomial ℚ) L) r = (algebraMap (RatFunc ℚ) L) ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) r) := by
      intro r; rfl
    have hq_root : (aeval α) q = 0 := by
      simp only [q]
      have haeval_step : ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℚ),
          (aeval (α : L)) (∑ i ∈ s, (f i : Polynomial ℚ) • (Polynomial.X : Polynomial (Polynomial ℚ)) ^ i) =
          ∑ i ∈ s, (algebraMap (Polynomial ℚ) L) (f i) * α ^ i := by
        intro s f; induction s using Finset.cons_induction with
        | empty => simp
        | cons a t hat ih =>
          simp [Algebra.smul_def]
      rw [haeval_step p.support c]
      rw [Finset.sum_congr rfl (fun i hi => by rw [halg_factor (c i), hc i hi])]
      simp only [map_mul]
      have key : (∑ x ∈ p.support, (algebraMap (RatFunc ℚ) L) ↑d * (algebraMap (RatFunc ℚ) L) (p.coeff x) * α ^ x) =
          (algebraMap (RatFunc ℚ) L) ↑d * (∑ x ∈ p.support, (algebraMap (RatFunc ℚ) L) (p.coeff x) * α ^ x) := by
        simp [mul_assoc, Finset.mul_sum]
      rw [key]
      have heval_eq : (∑ x ∈ p.support, (algebraMap (RatFunc ℚ) L) (p.coeff x) * α ^ x) = (aeval α) p := by
        simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      rw [heval_eq, hp_root, mul_zero]
    exact ⟨q, hq_ne, hq_root⟩
  obtain ⟨y, hy0, hβint⟩ := hαalg.exists_integral_multiple
  set β : L := y • α with hβ_def
  have hβtop : IntermediateField.adjoin (RatFunc ℚ) {β} = ⊤ := by
    have hy0' : (algebraMap (Polynomial ℚ) (RatFunc ℚ) y) ≠ 0 := by
      set k : RatFunc ℚ := algebraMap (Polynomial ℚ) (RatFunc ℚ) y
      have hinj := IsFractionRing.injective (R := Polynomial ℚ) (K := RatFunc ℚ)
      exact fun h => hy0 (hinj (by simp [k, h]))
    -- The scalar c = (algebraMap y)⁻¹ in RatFunc ℚ
    set c : RatFunc ℚ := ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) y)⁻¹
    -- β = y • α, so α = c • β (as elements of L)
    have hα_eq : α = c • β := by
      simp only [c, hβ_def, Algebra.smul_def]
      have : (algebraMap (Polynomial ℚ) L) y = (algebraMap (RatFunc ℚ) L) ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) y) := by
        exact rfl
      rw [this]
      rw [← mul_assoc]
      rw [show (algebraMap (RatFunc ℚ) L) ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) y)⁻¹ *
          (algebraMap (RatFunc ℚ) L) ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) y) = 1 from by
        rw [← map_mul, inv_mul_cancel₀ hy0', map_one]]
      simp
    have hα_mem : α ∈ IntermediateField.adjoin (RatFunc ℚ) {β} := by
      rw [hα_eq]
      exact SMulMemClass.smul_mem c (IntermediateField.subset_adjoin (RatFunc ℚ) {β} (Set.mem_singleton β))
    have hle : IntermediateField.adjoin (RatFunc ℚ) {α} ≤ IntermediateField.adjoin (RatFunc ℚ) {β} := by
      exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hα_mem)
    rw [hα] at hle
    exact le_antisymm le_top hle
  -- The monic model `F ∈ ℚ[T][X]` and its image over `ℚ(T)`.
  set F : Polynomial (Polynomial ℚ) := minpoly (Polynomial ℚ) β with hF_def
  have hFmonic : F.Monic := minpoly.monic hβint
  have hFmap : minpoly (RatFunc ℚ) β = F.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
    rw [hF_def]
    -- Use the fact that ℚ[X] is integrally closed and RatFunc ℚ is its fraction field
    have hint : IsIntegral (Polynomial ℚ) β := hβint
    have hintK : IsIntegral (RatFunc ℚ) β := by
      rcases hint with ⟨p, hp_mono, hp_eval⟩
      exact ⟨p.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)), Polynomial.Monic.map _ hp_mono, by
        change eval₂ (algebraMap (RatFunc ℚ) L) β (Polynomial.map (algebraMap ℚ[X] (RatFunc ℚ)) p) = 0
        rw [Polynomial.eval₂_map]
        exact hp_eval⟩
    exact minpoly.isIntegrallyClosed_eq_field_fractions' (K := RatFunc ℚ) hint
  have hFdeg : F.natDegree = n := by
    set_option synthInstance.maxHeartbeats 200000 in
    have hβint' : IsIntegral (RatFunc ℚ) β := hβint.tower_top
    have hfr : Module.finrank (RatFunc ℚ) ↥(IntermediateField.adjoin (RatFunc ℚ) {β} : IntermediateField (RatFunc ℚ) L) =
        (minpoly (RatFunc ℚ) β).natDegree := by
      exact IntermediateField.adjoin.finrank hβint'
    rw [hβtop, IntermediateField.finrank_top'] at hfr
    have : F.natDegree = (minpoly (RatFunc ℚ) β).natDegree := by
      rw [hFmap, Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
      simp [hFmonic.leadingCoeff]
    rw [this, ← hfr, hfinrank]
  have hFirr : Irreducible F := by
    rw [hFmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc ℚ)]
    rw [← hFmap]
    have hint2 : IsIntegral (RatFunc ℚ) β := by
      rcases hβint with ⟨p, hpmonic, hpzero⟩
      exact ⟨p.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)), hpmonic.map _, by
        rw [Polynomial.eval₂_map]
        exact hpzero⟩
    exact minpoly.irreducible hint2
  -- (7) Absolute irreducibility — the regularity teeth. GENUINE GAP (geometric integrality).
  have hFabs : Irreducible (F.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
    -- Gauss reduction: for the monic `F.map (ℚ → ℚ̄)`, irreducibility over `ℚ̄[T]` is equivalent
    -- to irreducibility of its image over the fraction field `ℚ̄(T) = FractionRing (ℚ̄[T])`.
    -- That image is `F.map toClosureFrac`, the base change of `minpoly ℚ[T] β` to `ℚ̄(T)`.
    have hmonicFK : (F.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).Monic :=
      hFmonic.map _
    rw [hmonicFK.irreducible_iff_irreducible_map_fraction_map
        (K := FractionRing (Polynomial (AlgebraicClosure ℚ)))]
    -- The double coefficient map `F ↦ (F.map (ℚ→ℚ̄)).map (localisation)` collapses to the single
    -- `Rigidity.RET.toClosureFrac : ℚ[T] → ℚ̄(T)`, base change on coefficients then localisation.
    have heq : (F.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).map
        (algebraMap (Polynomial (AlgebraicClosure ℚ))
          (FractionRing (Polynomial (AlgebraicClosure ℚ))))
        = F.map Rigidity.RET.toClosureFrac := by
      rw [Polynomial.map_map]; rfl
    rw [heq]
    -- Irreducibility over `ℚ̄(T)` from regularity (`hreg : algebraicClosure ℚ L = ⊥`) via linear
    -- disjointness of `L` and `ℚ̄(T)` over `ℚ(T)` — the geometric-integrality teeth.
    exact Rigidity.RET.irreducible_map_toClosureFrac_of_regular hreg β hβtop F hFmap
  -- (6) Cofinite separability of the specializations.
  have hFsep : {t : ℤ | ¬ (specialize F t).Separable}.Finite := by
    -- F over RatFunc ℚ is separable (char 0, irreducible)
    have hβint_rat : IsIntegral (RatFunc ℚ) β := by
      haveI : Module.Finite (RatFunc ℚ) L := _fdL
      have halg' : Algebra.IsAlgebraic (RatFunc ℚ) L := Algebra.IsAlgebraic.of_finite _ _
      have : ∀ x : L, IsAlgebraic (RatFunc ℚ) x := fun x => halg'.isAlgebraic x
      exact (this β).isIntegral
    have hsep_rat : (minpoly (RatFunc ℚ) β).Separable := by
      exact (minpoly.irreducible hβint_rat).separable
    -- So F and F' are coprime in RatFunc ℚ [X]
    have hcoprime : IsCoprime (F.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)))
        ((Polynomial.derivative F).map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) := by
      have hsep_rat' : (minpoly (RatFunc ℚ) β).Separable := hsep_rat
      rw [hFmap] at hsep_rat'
      obtain ⟨a, b, hab⟩ := hsep_rat'
      rw [Polynomial.derivative_map] at hab
      exact ⟨a, b, hab⟩
    -- F is monic and separable over RatFunc ℚ, so F and F' are coprime in RatFunc ℚ[X].
    -- Clearing denominators, ∃ A B : ℚ[X][X] and 0 ≠ D : ℚ[X] with A*F + B*F' = C(D).
    -- For t with D(t) ≠ 0, specialize F t is coprime with its derivative over ℚ, hence separable.
    -- D ≠ 0 implies finitely many integer roots.
    -- Step 1: Get a Bézout relation over ℚ[X] with nonzero right-hand side.
    -- Step 1: Clear denominators to get a Bézout relation over ℚ[X] with nonzero RHS.
    obtain ⟨u, v, huv⟩ := hcoprime
    -- Clear denominators for u, v ∈ RatFunc ℚ[X]
    have h_clear_denom : ∀ p : Polynomial (RatFunc ℚ),
        ∃ w0 : Polynomial ℚ, w0 ≠ 0 ∧ ∃ A : Polynomial (Polynomial ℚ),
          Polynomial.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) A =
              p * Polynomial.C (algebraMap (Polynomial ℚ) (RatFunc ℚ) w0) := by
      intro p
      induction' p using Polynomial.induction_on' with p q ihp ihq n a
      · obtain ⟨w0, hw0, A, hA⟩ := ihp
        obtain ⟨w1, hw1, B, hB⟩ := ihq
        use w0 * w1
        simp_all
        use A * Polynomial.C w1 + B * Polynomial.C w0
        simp [*, add_mul, mul_comm, mul_left_comm]
      · obtain ⟨w0, hw0⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial ℚ)) a
        refine ⟨w0.2, ?_, ?_⟩
        · simp_all
        · simp_all [← Polynomial.C_mul_X_pow_eq_monomial]
          use Polynomial.C w0.1 * Polynomial.X ^ n
          simp [← hw0, mul_assoc]
    obtain ⟨w0, hw0ne, A, hA⟩ := h_clear_denom u
    obtain ⟨w1, hw1ne, B, hB⟩ := h_clear_denom v
    have hbezout : ∃ (A' B' : Polynomial (Polynomial ℚ)) (w0' : Polynomial ℚ),
        w0' ≠ 0 ∧ A' * F + B' * Polynomial.derivative F = Polynomial.C w0' := by
      refine ⟨A * Polynomial.C w1, B * Polynomial.C w0, w0 * w1,
        mul_ne_zero hw0ne hw1ne, ?_⟩
      apply Polynomial.map_injective (algebraMap (Polynomial ℚ) (RatFunc ℚ))
        (IsFractionRing.injective _ _)
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
      rw [hA, hB]
      have hgoal : u * Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w0) * Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w1) * Polynomial.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) F +
          v * Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w1) * Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w0) * Polynomial.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Polynomial.derivative F) =
          Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) (w0 * w1)) := by
        have h1 : Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) (w0 * w1)) =
            Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w0) *
            Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w1) := by
          rw [← Polynomial.C_mul, map_mul]
        rw [h1]
        have huv' : (u * Polynomial.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) F +
          v * Polynomial.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Polynomial.derivative F)) *
          (Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w0) * Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w1)) =
          Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w0) * Polynomial.C ((algebraMap (Polynomial ℚ) (RatFunc ℚ)) w1) := by
          rw [huv]; simp
        ring_nf at huv' ⊢
        exact huv'
      rw [hgoal]
    -- Step 2: For t with w0'.eval (↑t) ≠ 0, specialize F t is separable.
    obtain ⟨A', B', w0', hw0'ne, hAB'⟩ := hbezout
    have hsep_of_ne : ∀ t : ℤ, (Polynomial.eval (↑t : ℚ) w0') ≠ 0 → (specialize F t).Separable := by
      intro t ht
      have hspecialize : Polynomial.C (Polynomial.eval (↑t : ℚ) w0') =
          Polynomial.map (Polynomial.evalRingHom (↑t : ℚ)) A' * specialize F t +
          Polynomial.map (Polynomial.evalRingHom (↑t : ℚ)) B' * Polynomial.derivative (specialize F t) := by
        unfold specialize at *
        have h1 := congr_arg (Polynomial.map (Polynomial.evalRingHom (↑t : ℚ))) hAB'
        simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at h1
        rw [← Polynomial.derivative_map] at h1
        exact h1.symm
      -- C(eval t w0') is a unit, so specialize F t and its derivative are coprime
      have hcunit : IsUnit (Polynomial.C (Polynomial.eval (↑t : ℚ) w0') : Polynomial ℚ) := by
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ht)
      have hcop : IsCoprime (specialize F t) (Polynomial.derivative (specialize F t)) := by
        rcases hcunit.exists_left_inv with ⟨u, hu⟩
        exact ⟨u * Polynomial.map (Polynomial.evalRingHom (↑t : ℚ)) A',
              u * Polynomial.map (Polynomial.evalRingHom (↑t : ℚ)) B', by
          calc u * Polynomial.map (Polynomial.evalRingHom (↑t : ℚ)) A' * specialize F t +
                  u * Polynomial.map (Polynomial.evalRingHom (↑t : ℚ)) B' * Polynomial.derivative (specialize F t)
              = u * (Polynomial.map (Polynomial.evalRingHom (↑t : ℚ)) A' * specialize F t +
                      Polynomial.map (Polynomial.evalRingHom (↑t : ℚ)) B' * Polynomial.derivative (specialize F t)) := by ring
            _ = u * Polynomial.C (Polynomial.eval (↑t : ℚ) w0') := by rw [hspecialize.symm]
            _ = 1 := by rw [← hu, mul_comm]⟩
      have hne : specialize F t ≠ 0 := (specialize_monic F hFmonic t).ne_zero
      rw [PerfectField.separable_iff_squarefree (K := ℚ)]
      intro a ha
      by_cases ha0 : a = 0
      · exfalso; exact hne (by simpa [ha0] using ha)
      · by_contra hnu
        have ha_div_f : a ∣ specialize F t := dvd_trans (dvd_mul_right _ _) ha
        have ha_div_fp : a ∣ Polynomial.derivative (specialize F t) := by
          obtain ⟨q, hq⟩ := ha
          rw [hq]
          have : Polynomial.derivative (a * a * q) = a * (2 * Polynomial.derivative a * q + a * Polynomial.derivative q) := by
            simp [Polynomial.derivative_mul]; ring
          rw [this]
          exact ⟨_, rfl⟩
        obtain ⟨u, v, huv⟩ := hcop
        have ha_div_one : a ∣ 1 := by
          have : a ∣ u * specialize F t + v * Polynomial.derivative (specialize F t) :=
            dvd_add (ha_div_f.mul_left u) (ha_div_fp.mul_left v)
          rw [huv] at this
          exact this
        exact hnu (isUnit_of_dvd_one ha_div_one)
    -- Step 3: {t : ℤ | ¬ separable} ⊆ {t : ℤ | w0'.eval (↑t) = 0}
    have hsubset : {t : ℤ | ¬ (specialize F t).Separable} ⊆ {t : ℤ | Polynomial.eval (↑t : ℚ) w0' = 0} := by
      intro t ht; by_contra hne; exact ht (hsep_of_ne t hne)
    -- Step 4: {t : ℤ | w0'.eval (↑t) = 0} is finite
    have hroots_finite : Set.Finite {t : ℤ | Polynomial.eval (↑t : ℚ) w0' = 0} := by
      let S := {t : ℤ | Polynomial.eval (↑t : ℚ) w0' = 0}
      have hinj : Function.Injective (Int.cast : ℤ → ℚ) := Int.cast_injective
      have hinjS : Set.InjOn (Int.cast : ℤ → ℚ) S := hinj.injOn
      have hfin_image : Set.Finite ((fun t : ℤ => (t : ℚ)) '' S) := by
        refine Set.Finite.subset (w0'.roots.toFinset.finite_toSet) ?_
        intro q hq
        obtain ⟨t, ht, rfl⟩ := hq
        exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots hw0'ne |>.mpr ht)
      have hfin_S : Set.Finite S := by
        have hinjOn : Set.InjOn (Int.cast : ℤ → ℚ) ((fun t : ℤ => (t : ℚ)) ⁻¹' ((fun t : ℤ => (t : ℚ)) '' S)) := by
          intro x hx y hy h
          simp only [Set.mem_preimage, Set.mem_image] at hx hy
          obtain ⟨a, ha, ha'⟩ := hx
          obtain ⟨b, hb, hb'⟩ := hy
          have hab : a = b := hinjS ha hb (by rw [ha', hb', h])
          rw [hab] at ha'
          exact hinj (ha'.symm.trans hb')
        exact (hfin_image.preimage hinjOn).subset (fun t ht => by simp [Set.mem_preimage, Set.mem_image, ht])
      exact hfin_S
    exact hroots_finite.subset hsubset
  -- (8) Landing certificate — the reduction of the Galois group. GENUINE GAP (specialization map).
  have hland : ∀ t : ℤ, (specialize F t).Separable →
      ∃ g' : (specialize F t).Gal →* H, Function.Injective g' := by
    intro t hsep
    -- The generic Galois group is identified with `H` via `ψ := φ.trans e.symm`.
    obtain ⟨g, hg⟩ :=
      specialization_gal_embeds L β hβint hβtop F hF_def hFmonic hFmap t hsep
    exact ⟨((φ.trans e.symm).toMonoidHom).comp g,
      (EquivLike.injective (φ.trans e.symm)).comp hg⟩
  -- (5) Root certificate: the resolvent is `F` itself, which has a root in its splitting field.
  have hroot : ∀ t : ℤ, ∃ a : (specialize F t).SplittingField, (aeval a) (specialize F t) = 0 := by
    intro t
    have hmonic : (specialize F t).Monic := specialize_monic F hFmonic t
    have hdeg : 0 < (specialize F t).natDegree := by
      rw [specialize_monic_natDegree F hFmonic t, hFdeg]
      exact Nat.card_pos
    let p := specialize F t
    -- p splits over its splitting field, and has positive degree, so it has a root there.
    have hisspl : Polynomial.IsSplittingField ℚ p.SplittingField p := inferInstance
    have hsplits' := hisspl.splits  -- (map f p).Splits (old-style)
    have hdeg' : (map (algebraMap ℚ p.SplittingField) p).degree ≠ 0 := by
      rw [Polynomial.degree_map]
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
      exact mod_cast hdeg.ne'
    obtain ⟨a, ha⟩ := Polynomial.Splits.exists_eval_eq_zero hsplits' hdeg'
    have : aeval a p = 0 := by
      simpa [Polynomial.eval_map] using ha
    exact ⟨a, this⟩
  exact ⟨n, H, e, F, F, hFmonic, hFdeg, hFmonic, hFdeg.trans hcardH.symm,
    hFirr, hFabs, hFsep, hland, hroot⟩

/-- **Specialization / Hilbert irreducibility** (step (B) of the honest cut): a group that occurs
as the Galois group of a *regular* extension of `ℚ(T)` occurs as the Galois group of an extension
of `ℚ`.

This is a theorem, not an axiom.  It is now **proven** from the model translation
`exists_regular_family` (which carries all the outstanding content) via the repository's proven
Hilbert-irreducibility descent `IsInverseGalois.of_regular_family` and transport of the
inverse-Galois property along the group isomorphism `H ≃* G` (`IsInverseGalois.of_mulEquiv`). -/
theorem IsRegularInverseGalois.isInverseGalois {G : Type} [Group G] [Finite G]
    (h : IsRegularInverseGalois G) : IsInverseGalois G := by
  obtain ⟨n, H, e, F, Gp, hFm, hFd, hGm, hGd, hGirr, hGabs, hFsep, hland, hroot⟩ :=
    exists_regular_family h
  exact (IsInverseGalois.of_regular_family H F Gp hFm hFd hGm hGd hGirr hGabs hFsep hland hroot).of_mulEquiv e

end

