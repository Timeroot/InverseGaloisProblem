/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Frobenius Lifting Infrastructure

This file builds the algebraic number theory infrastructure needed for the
Frobenius lifting lemma: given a monic f ∈ ℤ[X] with f irreducible over ℚ
and squarefree mod p, there exists σ in the Galois group whose action on
roots has the same cycle type as the Frobenius on mod-p roots.

## Key constructions

1. Roots of monic integer polynomials are algebraic integers
2. Reduction map from roots in the splitting field to roots mod p
3. Existence of the Frobenius element via decomposition groups
4. Cycle type preservation under equivariant bijections
-/

open Polynomial NumberField Classical Pointwise

noncomputable section

/-!
## Part 1: Splitting field setup and root integrality
-/

/-- The splitting field of a polynomial over ℚ is a number field. -/
instance Polynomial.SplittingField.numberField (f : Polynomial ℚ) :
    NumberField f.SplittingField := ⟨⟩

/-- A root of a monic polynomial with integer coefficients is an algebraic integer. -/
lemma isIntegral_root_of_monic_intPoly {K : Type*} [Field K] [Algebra ℚ K]
    (f : ℤ[X]) (hf : f.Monic) (α : K)
    (hα : Polynomial.aeval α (f.map (Int.castRingHom ℚ)) = 0) :
    IsIntegral ℤ α := by
  refine ⟨f, hf, ?_⟩
  rw [← eq_comm, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] at *
  simp_all [Polynomial.coeff_map]

/-- Roots of a monic integer polynomial in a field extension lie in the ring of integers. -/
lemma root_mem_ringOfIntegers {K : Type*} [Field K] [Algebra ℚ K]
    (f : ℤ[X]) (hf : f.Monic) (α : K)
    (hα : α ∈ (f.map (Int.castRingHom ℚ)).rootSet K) :
    ∃ (β : 𝓞 K), (β : K) = α := by
  obtain ⟨β, hβ⟩ := isIntegral_root_of_monic_intPoly f hf α
    (by rw [Polynomial.mem_rootSet] at hα; exact hα.2)
  exact ⟨⟨α, ⟨β, hβ.1, hβ.2⟩⟩, rfl⟩

/-!
## Part 2: Prime ideal above p and reduction map
-/

section ReductionMap

variable {p : ℕ} [hp : Fact (Nat.Prime p)]
variable {K : Type*} [Field K] [Algebra ℚ K] [NumberField K]

private instance : (Ideal.span {(p : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
  exact Nat.prime_iff_prime_int.mp hp.out

/-- There exists a maximal ideal of 𝓞 K above the prime p. -/
lemma exists_maximal_ideal_above :
    ∃ (P : Ideal (𝓞 K)), P.IsMaximal ∧
      Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ P := by
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Ideal.nonempty_primesOver (Ideal.span {(p : ℤ)}) (S := 𝓞 K)
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Int.natCast_ne_zero.mpr hp.out.ne_zero)
  refine ⟨Q, ?_, ?_⟩
  · exact Ideal.IsPrime.isMaximal hQ1 (Ideal.ne_bot_of_liesOver_of_ne_bot hne Q)
  · rw [hQ2.over]; exact Ideal.map_comap_le

/-- The residue field 𝓞 K / P has characteristic p for P above (p). -/
lemma residue_field_charP (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ P) :
    CharP (𝓞 K ⧸ P) p := by
  have hp_mem : (algebraMap ℤ (𝓞 K)) (p : ℤ) ∈ P :=
    hP (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))
  have hp_zero : (p : 𝓞 K ⧸ P) = 0 := by
    rw [show (p : 𝓞 K ⧸ P) = Ideal.Quotient.mk P ((algebraMap ℤ (𝓞 K)) (p : ℤ)) from by
      push_cast; rfl]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp_mem
  exact (CharP.charP_iff_prime_eq_zero hp.out).mpr hp_zero

/-- The residue field is finite. -/
instance residue_field_finite (P : Ideal (𝓞 K)) [P.IsMaximal] :
    Finite (𝓞 K ⧸ P) :=
  instFiniteQuotientRingOfIntegersIdealOfNumberFieldOfIsMaximal

end ReductionMap

/-!
## Part 3: Reduction sends roots to roots
-/

section RootReduction

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- If α ∈ 𝓞 K is a root of f.map (ℤ→ℚ), then the reduction of α modulo P
is a root of f.map (ℤ→𝓞K/P) in the residue field. -/
lemma reduction_of_root_is_root
    {K : Type*} [Field K] [Algebra ℚ K] [NumberField K]
    (f : ℤ[X]) (P : Ideal (𝓞 K)) [P.IsMaximal]
    (α : 𝓞 K) (hα : Polynomial.aeval (α : K) (f.map (Int.castRingHom ℚ)) = 0) :
    Polynomial.aeval (Ideal.Quotient.mk P α) (f.map (Int.castRingHom (𝓞 K ⧸ P))) = 0 := by
  have h0 : Polynomial.eval₂ (Int.castRingHom (𝓞 K)) α f = 0 := by
    apply_fun (algebraMap (𝓞 K) K) using Subtype.val_injective
    rw [map_zero, Polynomial.hom_eval₂]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map] at hα
    have : (algebraMap ℚ K).comp (Int.castRingHom ℚ) =
      (algebraMap (𝓞 K) K).comp (Int.castRingHom (𝓞 K)) := by ext n; simp
    rwa [← this]
  simp only [Polynomial.aeval_def, Polynomial.eval₂_map]
  have : (algebraMap (𝓞 K ⧸ P) (𝓞 K ⧸ P)).comp (Int.castRingHom (𝓞 K ⧸ P)) =
    (Ideal.Quotient.mk P).comp (Int.castRingHom (𝓞 K)) := by ext n; simp
  rw [this, ← Polynomial.hom_eval₂ f (Int.castRingHom (𝓞 K)) (Ideal.Quotient.mk P) α,
    h0, map_zero]

end RootReduction

/-!
## Part 4: Frobenius element existence

The key deep result: for the splitting field of a monic ℤ[X] polynomial
over ℚ, there exists a Galois automorphism that acts as the Frobenius
(x ↦ x^p) on the residue field modulo a chosen prime above p.

In this case, since the base field is ℚ with ring of integers ℤ,
the residue field ℤ/pℤ = 𝔽_p, so the Frobenius x ↦ x^p fixes 𝔽_p
and is indeed an element of Aut(κ_Q/𝔽_p).
-/

section FrobeniusElement

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Fermat's little theorem for integer casts: in any ring of characteristic p,
(n : R)^p = (n : R) for all integers n. -/
lemma intCast_pow_eq_intCast (R : Type*) [CommRing R] [CharP R p] (n : ℤ) :
    (Int.cast n : R) ^ p = (Int.cast n : R) := by
  have h : (p : ℤ) ∣ (n ^ p - n) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; simp [ZMod.pow_card]
  obtain ⟨k, hk⟩ := h
  have key : ((n ^ p : ℤ) : R) - ((n : ℤ) : R) = 0 := by
    rw [← Int.cast_sub, hk, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]
  simp only [Int.cast_pow] at key
  exact sub_eq_zero.mp key

/-- Q lies over (p) given the containment Ideal.map ℤ→𝓞L (p) ≤ Q. -/
lemma liesOver_of_map_le (L : Type*) [CommRing L] [Algebra ℤ L]
    (Q : Ideal L) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ L) (Ideal.span {(p : ℤ)}) ≤ Q) :
    Q.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  have h1 : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ L) Q :=
    Ideal.map_le_iff_le_comap.mp hQ
  have h2 : (Ideal.span {(p : ℤ)}).IsMaximal := by
    apply (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.out.ne_zero) |>.mpr
      (Nat.prime_iff_prime_int.mp hp.out)).isMaximal
    exact Ideal.span_singleton_eq_bot.not.mpr (Int.natCast_ne_zero.mpr hp.out.ne_zero)
  have h4 : Ideal.comap (algebraMap ℤ L) Q ≠ ⊤ :=
    Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›)
  show Ideal.span {(p : ℤ)} = Ideal.under ℤ Q
  unfold Ideal.under; exact h2.eq_of_le h4 h1

/-
**Frobenius element existence.**

For the splitting field L of f over ℚ and a maximal ideal Q of 𝓞 L above p,
there exists σ ∈ Gal(L/ℚ) such that for all x ∈ 𝓞 L:
  π(σ(x)) = π(x)^p
where π is the reduction modulo Q. -/

/-- The ring of integers of a Galois extension L/ℚ has the property that
its fixed points under the Galois group are exactly ℤ. -/
private instance isInvariant_ringOfIntegers (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L] [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ (𝓞 L) (L ≃ₐ[ℚ] L) := by
  constructor
  intro b hb
  have h_fixed : (b : L) ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[ℚ] L)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    show σ (b : L) = (b : L)
    have : ((σ • b : 𝓞 L) : L) = σ (b : L) := rfl
    rw [← this]; exact congrArg Subtype.val (hb σ)
  rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at h_fixed
  obtain ⟨q, hq⟩ := h_fixed
  have hq_int : IsIntegral ℤ q := by
    have : IsIntegral ℤ ((algebraMap ℚ L) q) := hq ▸ b.2
    rwa [isIntegral_algebraMap_iff (algebraMap ℚ L).injective] at this
  rw [IsIntegrallyClosed.isIntegral_iff] at hq_int
  obtain ⟨n, hn⟩ := hq_int
  refine ⟨n, ?_⟩
  ext
  show (algebraMap ℤ L) n = (b : L)
  have : (algebraMap ℤ L) n = (algebraMap ℚ L) ((algebraMap ℤ ℚ) n) := by
    simp [RingHom.algebraMap_toAlgebra]
  rw [this, hn, hq]

private instance charP_quotient_int :
    CharP (ℤ ⧸ Ideal.span {(p : ℤ)}) p := by
  constructor; intro n
  rw [show (n : ℤ ⧸ Ideal.span {(p : ℤ)}) = Ideal.Quotient.mk _ (n : ℤ) from rfl]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨fun h => Int.natCast_dvd_natCast.mp h, fun h => Int.natCast_dvd_natCast.mpr h⟩

/-- The Frobenius endomorphism x ↦ x^p on the residue field 𝓞_L/Q,
viewed as an algebra automorphism over ℤ/(p). -/
private def frobeniusResidueField
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ Q)
    [Q.LiesOver (Ideal.span {(p : ℤ)})] :
    (𝓞 L ⧸ Q) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 L ⧸ Q) := by
  haveI : CharP (𝓞 L ⧸ Q) p := residue_field_charP Q hQ
  haveI : Finite (𝓞 L ⧸ Q) := residue_field_finite Q
  haveI : ExpChar (𝓞 L ⧸ Q) p := ExpChar.prime hp.out
  haveI : Fintype (𝓞 L ⧸ Q) := Fintype.ofFinite _
  haveI : ExpChar (ℤ ⧸ Ideal.span {(p : ℤ)}) p := ExpChar.prime hp.out
  exact AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective (frobenius (𝓞 L ⧸ Q) p)
      ⟨frobenius_inj (𝓞 L ⧸ Q) p,
       Finite.surjective_of_injective (frobenius_inj (𝓞 L ⧸ Q) p)⟩)
    (fun a => by
      show (algebraMap _ (𝓞 L ⧸ Q) a) ^ p = algebraMap _ _ a
      rw [← map_pow]; congr 1
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact (by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; simp [ZMod.pow_card]))

private lemma frobeniusResidueField_apply
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ Q)
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (x : 𝓞 L ⧸ Q) :
    frobeniusResidueField L Q hQ x = x ^ p := by
  simp [frobeniusResidueField, AlgEquiv.ofRingEquiv, RingEquiv.ofBijective, frobenius_def]

private lemma smul_eq_galRestrict
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (x : 𝓞 L) :
    (σ • x : 𝓞 L) = galRestrict ℤ ℚ L (𝓞 L) σ x := by
  ext
  change σ (x : L) = ((galRestrict ℤ ℚ L (𝓞 L) σ x : 𝓞 L) : L)
  simp [galRestrict, galRestrictHom, galRestrict']

lemma exists_frobenius_element_over_Q
    (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L] [IsGalois ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (hQ : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ Q) :
    ∃ σ : L ≃ₐ[ℚ] L, ∀ (x : 𝓞 L),
      Ideal.Quotient.mk Q (galRestrict ℤ ℚ L (𝓞 L) σ x) =
      (Ideal.Quotient.mk Q x) ^ p := by
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_map_le (𝓞 L) Q hQ
  let frob := frobeniusResidueField L Q hQ
  obtain ⟨⟨σ, hσ_stab⟩, hσ⟩ :=
    Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) Q frob
  refine ⟨σ, fun x => ?_⟩
  rw [← smul_eq_galRestrict]
  rw [show Ideal.Quotient.mk Q (σ • x) =
    Ideal.Quotient.stabilizerHom Q (Ideal.span {(p : ℤ)}) (L ≃ₐ[ℚ] L) ⟨σ, hσ_stab⟩
      (Ideal.Quotient.mk Q x) from by
    simp [Ideal.Quotient.stabilizerHom]]
  rw [hσ]
  exact frobeniusResidueField_apply L Q hQ _

end FrobeniusElement

/-!
## Part 5: Equivariant bijections preserve cycle type
-/

/-- `permCongr` preserves cycle type. -/
lemma permCongr_cycleType {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) :
    (Equiv.permCongr e σ).cycleType = σ.cycleType := by
  convert Equiv.Perm.cycleType_extendDomain
    (f := e.trans (Equiv.Set.univ β).symm) (g := σ) using 1

/-- If two permutations on finite types are conjugate via an equiv,
they have the same cycle type. -/
lemma cycleType_eq_of_conjugate {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    (h : ∀ x, e (σ x) = τ (e x)) :
    σ.cycleType = τ.cycleType := by
  have : τ = Equiv.permCongr e σ := by
    ext x; have := h (e.symm x); simp at this; exact this.symm
  rw [this, permCongr_cycleType]

/-- The auxiliary permutation from galActionAux. -/
def galActionAux_perm {F : Type*} [Field F] (p : Polynomial F) (σ : p.Gal) :
    Equiv.Perm (p.rootSet p.SplittingField) :=
  letI := Polynomial.Gal.galActionAux p
  MulAction.toPerm σ

/-- galActionAux_perm maps a root x to σ(x). -/
lemma galActionAux_perm_val {F : Type*} [Field F] (p : Polynomial F) (σ : p.Gal)
    (x : p.rootSet p.SplittingField) :
    ((galActionAux_perm p σ) x : p.SplittingField) = σ (x : p.SplittingField) := by
  simp [galActionAux_perm, MulAction.toPerm, Polynomial.Gal.galActionAux]
  rfl

/-- galActionHom equals permCongr of the auxiliary action. -/
lemma galActionHom_eq_permCongr {F : Type*} [Field F] (p : Polynomial F)
    (E : Type*) [Field E] [Algebra F E] [Fact (p.map (algebraMap F E)).Splits]
    (σ : p.Gal) :
    Polynomial.Gal.galActionHom p E σ =
    Equiv.permCongr (Polynomial.Gal.rootsEquivRoots p E) (galActionAux_perm p σ) := by
  ext ⟨x, hx⟩
  simp only [Polynomial.Gal.galActionHom, MulAction.toPermHom_apply, Equiv.permCongr_apply]
  have h := Polynomial.Gal.smul_def p E σ (⟨x, hx⟩ : p.rootSet E)
  apply_fun (fun y => (y : E)) at h
  exact h

/-- The cycle type of galActionHom is independent of the target field.
In particular, galActionHom p ℂ σ and galActionHom p SplittingField σ
have the same cycle type. This follows from the definition of the MulAction
on rootSet(p, E) via rootsEquivRoots. -/
lemma galActionHom_cycleType_eq {F : Type*} [Field F] (p : Polynomial F)
    (E : Type*) [Field E] [Algebra F E] [Fact (p.map (algebraMap F E)).Splits]
    (σ : p.Gal) :
    (@Polynomial.Gal.galActionHom _ _ p E _ _ ‹_› σ).cycleType =
    (@Polynomial.Gal.galActionHom _ _ p p.SplittingField _ _ ⟨Polynomial.SplittingField.splits p⟩ σ).cycleType := by
  haveI : Fact (p.map (algebraMap F p.SplittingField)).Splits := ⟨Polynomial.SplittingField.splits p⟩
  rw [galActionHom_eq_permCongr p E σ, galActionHom_eq_permCongr p p.SplittingField σ,
      permCongr_cycleType, permCongr_cycleType]

end
