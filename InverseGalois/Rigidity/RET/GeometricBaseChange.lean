/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Local.PuiseuxAssembly

/-!
# Base change of an equation along an extension of an algebraically closed field

An irreducible equation over an algebraically closed field stays irreducible after its constants
are enlarged.  Applied to the equation of a cover of the line, whose constants are the algebraic
numbers, this says that the complexified equation is still irreducible — the geometric statement
that a cover which does not split over the algebraic numbers does not split over the complex
numbers either.

The argument is a specialization argument.  A factorization of the base-changed equation is
normalized so that both factors are monic, and only finitely many constants of the large field
occur among their coefficients.  Those constants generate a finitely generated subalgebra of the
large field, and Zariski's lemma sends such a subalgebra back into an algebraically closed base
field: a maximal ideal has a residue field that is finite over the base, hence equal to it.
Reducing the factorization along that retraction produces a factorization of the original equation
into two monic factors of positive degree.

## Main results

* `Rigidity.RET.exists_ringHom_of_fg` — a finitely generated subalgebra of an extension of an
  algebraically closed field retracts onto the base field.
* `Rigidity.RET.irreducible_map_mapRingHom_of_isAlgClosed` — enlarging the constants of an
  irreducible equation over an algebraically closed field preserves irreducibility.
* `Rigidity.RET.irreducible_complexEquation` — the equation of a cover of the line stays
  irreducible with complex coefficients.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

/-- **A finitely generated subalgebra of an extension of an algebraically closed field retracts
onto the base field.**

A maximal ideal of the subalgebra has a residue field which is a finitely generated algebra over
the base, hence finite over it by Zariski's lemma; an algebraically closed field has no proper
integral extension, so that residue field is the base field itself. -/
theorem exists_ringHom_of_fg {k Ω : Type*} [Field k] [IsAlgClosed k] [Field Ω] [Algebra k Ω]
    (A : Subalgebra k Ω) (hA : A.FG) :
    ∃ ψ : A →+* k, ∀ c : k, ψ (algebraMap k A c) = c := by
  classical
  haveI : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType A).1 hA
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  haveI := hm
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  haveI : Algebra.IsIntegral k (A ⧸ m) := Algebra.IsIntegral.of_finite k _
  have hbij : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  set e : k ≃+* (A ⧸ m) := RingEquiv.ofBijective (algebraMap k (A ⧸ m)) hbij with he
  refine ⟨((e.symm : (A ⧸ m) ≃+* k) : (A ⧸ m) →+* k).comp (Ideal.Quotient.mk m), fun c => ?_⟩
  show e.symm (Ideal.Quotient.mk m (algebraMap k A c)) = c
  have hc : Ideal.Quotient.mk m (algebraMap k A c) = e c := rfl
  rw [hc, e.symm_apply_apply]

/-- **Enlarging the constants of an irreducible equation over an algebraically closed field
preserves irreducibility.** -/
theorem irreducible_map_mapRingHom_of_isAlgClosed
    {k Ω : Type*} [Field k] [IsAlgClosed k] [Field Ω] [Algebra k Ω]
    {p : Polynomial (Polynomial k)} (hm : p.Monic) (hp : Irreducible p) :
    Irreducible (p.map (Polynomial.mapRingHom (algebraMap k Ω))) := by
  classical
  have hφinj : Function.Injective (Polynomial.mapRingHom (algebraMap k Ω)) :=
    Polynomial.map_injective _ (algebraMap k Ω).injective
  set φ : Polynomial k →+* Polynomial Ω := Polynomial.mapRingHom (algebraMap k Ω) with hφ
  have hpm : (p.map φ).Monic := hm.map φ
  have hdeg : (p.map φ).natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hφinj p
  have hn : p.natDegree ≠ 0 := fun h => hp.not_isUnit (hm.isUnit_iff.2 (hm.natDegree_eq_zero.1 h))
  constructor
  · intro hu
    exact hn (by rw [← hdeg]; exact Polynomial.natDegree_eq_zero_of_isUnit hu)
  · intro a b hab
    by_contra hcon
    push_neg at hcon
    obtain ⟨hane, hbne⟩ := hcon
    -- normalize the two factors to be monic
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hab, hpm.leadingCoeff]
    obtain ⟨u, hu⟩ : IsUnit a.leadingCoeff := IsUnit.of_mul_eq_one _ hlc
    have hbl : b.leadingCoeff = ↑u⁻¹ := by
      have h1 : (↑u : Polynomial Ω) * b.leadingCoeff = 1 := by rw [hu]; exact hlc
      have h2 := congrArg (fun x => (↑u⁻¹ : Polynomial Ω) * x) h1
      simpa [← mul_assoc] using h2
    set q : Polynomial (Polynomial Ω) := Polynomial.C (↑u⁻¹ : Polynomial Ω) * a with hq
    set r : Polynomial (Polynomial Ω) := Polynomial.C (↑u : Polynomial Ω) * b with hr
    have hqr : q * r = p.map φ := by
      rw [hq, hr, hab,
        show Polynomial.C (↑u⁻¹ : Polynomial Ω) * a * (Polynomial.C (↑u : Polynomial Ω) * b)
          = Polynomial.C (↑u⁻¹ : Polynomial Ω) * Polynomial.C (↑u : Polynomial Ω) * (a * b) by
          ring, ← Polynomial.C_mul]
      simp
    have hqmonic : q.Monic := by
      rw [Polynomial.Monic, hq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, ← hu]
      simp
    have hrmonic : r.Monic := by
      rw [Polynomial.Monic, hr, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hbl]
      simp
    have hqne : q ≠ 1 := by
      intro h
      refine hane ?_
      have ha : a = Polynomial.C (↑u : Polynomial Ω) * q := by
        rw [hq, ← mul_assoc, ← Polynomial.C_mul]; simp
      rw [ha, h, mul_one]
      exact Polynomial.isUnit_C.2 u.isUnit
    have hrne : r ≠ 1 := by
      intro h
      refine hbne ?_
      have hb : b = Polynomial.C (↑u⁻¹ : Polynomial Ω) * r := by
        rw [hr, ← mul_assoc, ← Polynomial.C_mul]; simp
      rw [hb, h, mul_one]
      exact Polynomial.isUnit_C.2 u⁻¹.isUnit
    have hqdeg : q.natDegree ≠ 0 := fun h => hqne (hqmonic.natDegree_eq_zero.1 h)
    have hrdeg : r.natDegree ≠ 0 := fun h => hrne (hrmonic.natDegree_eq_zero.1 h)
    -- the finitely many constants of the large field occurring in the two factors
    set S : Finset Ω :=
      (q.support.biUnion fun i => (q.coeff i).support.image fun j => (q.coeff i).coeff j) ∪
        (r.support.biUnion fun i => (r.coeff i).support.image fun j => (r.coeff i).coeff j)
      with hS
    set A : Subalgebra k Ω := Algebra.adjoin k (S : Set Ω) with hAdef
    have hmemq : ∀ i j, (q.coeff i).coeff j ∈ A := by
      intro i j
      by_cases h : (q.coeff i).coeff j = 0
      · rw [h]; exact zero_mem _
      · refine Algebra.subset_adjoin ?_
        rw [hS]
        refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, ?_, ?_⟩)
        · exact Polynomial.mem_support_iff.2 fun hz => h (by rw [hz]; simp)
        · exact Finset.mem_image_of_mem _ (Polynomial.mem_support_iff.2 h)
    have hmemr : ∀ i j, (r.coeff i).coeff j ∈ A := by
      intro i j
      by_cases h : (r.coeff i).coeff j = 0
      · rw [h]; exact zero_mem _
      · refine Algebra.subset_adjoin ?_
        rw [hS]
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, ?_, ?_⟩)
        · exact Polynomial.mem_support_iff.2 fun hz => h (by rw [hz]; simp)
        · exact Finset.mem_image_of_mem _ (Polynomial.mem_support_iff.2 h)
    -- lift the factorization to the subalgebra generated by those constants
    set ι : A →+* Ω := (Subalgebra.val A).toRingHom with hι
    have hιinj : Function.Injective ι := Subtype.val_injective
    set Φ : Polynomial A →+* Polynomial Ω := Polynomial.mapRingHom ι with hΦ
    have hΦinj : Function.Injective Φ := Polynomial.map_injective _ hιinj
    have hlift : ∀ f : Polynomial (Polynomial Ω), (∀ i j, (f.coeff i).coeff j ∈ A) →
        f ∈ Polynomial.lifts Φ := by
      intro f hf
      refine (Polynomial.lifts_iff_coeff_lifts f).2 fun i => ?_
      have hmem : f.coeff i ∈ Polynomial.lifts ι :=
        (Polynomial.lifts_iff_coeff_lifts (f.coeff i)).2 fun j => ⟨⟨_, hf i j⟩, rfl⟩
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, hc⟩
    obtain ⟨Q, hQmap, hQdeg, hQmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic (hlift q hmemq) hqmonic
    obtain ⟨R, hRmap, hRdeg, hRmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic (hlift r hmemr) hrmonic
    have hbase : p.map (Polynomial.mapRingHom (algebraMap k A)) = Q * R := by
      refine Polynomial.map_injective Φ hΦinj ?_
      rw [Polynomial.map_mul, hQmap, hRmap, hqr, Polynomial.map_map]
      congr 1
      refine RingHom.ext fun x => ?_
      show (x.map (algebraMap k A)).map ι = x.map (algebraMap k Ω)
      rw [Polynomial.map_map]
      congr 1
    -- specialize the constants back to the algebraically closed base field
    obtain ⟨ψ, hψ⟩ := exists_ringHom_of_fg A (hAdef ▸ Subalgebra.fg_adjoin_finset S)
    have hret : (Polynomial.mapRingHom ψ).comp (Polynomial.mapRingHom (algebraMap k A))
        = RingHom.id (Polynomial k) := by
      refine RingHom.ext fun x => ?_
      show (x.map (algebraMap k A)).map ψ = x
      rw [Polynomial.map_map, show ψ.comp (algebraMap k A) = RingHom.id k from RingHom.ext hψ,
        Polynomial.map_id]
    have hfin : p = Q.map (Polynomial.mapRingHom ψ) * R.map (Polynomial.mapRingHom ψ) := by
      have hc := congrArg (Polynomial.map (Polynomial.mapRingHom ψ)) hbase
      rw [Polynomial.map_mul] at hc
      rw [← hc, Polynomial.map_map, hret, Polynomial.map_id]
    rcases hp.isUnit_or_isUnit hfin with h1 | h1
    · refine hqdeg ?_
      rw [← hQdeg, ← hQmonic.natDegree_map (Polynomial.mapRingHom ψ),
        (hQmonic.map (Polynomial.mapRingHom ψ)).isUnit_iff.1 h1, Polynomial.natDegree_one]
    · refine hrdeg ?_
      rw [← hRdeg, ← hRmonic.natDegree_map (Polynomial.mapRingHom ψ),
        (hRmonic.map (Polynomial.mapRingHom ψ)).isUnit_iff.1 h1, Polynomial.natDegree_one]

/-- **The equation of a cover of the line stays irreducible with complex coefficients.** -/
theorem irreducible_complexEquation {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω]
    [Algebra (Polynomial k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω] [Algebra k ℂ]
    {α : Ω} (hα : IsIntegral (Polynomial k) α) : Irreducible (complexEquation α) :=
  irreducible_map_mapRingHom_of_isAlgClosed (minpoly.monic hα) (minpoly.irreducible hα)

end Rigidity.RET

end
