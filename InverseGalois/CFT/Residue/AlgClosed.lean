/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The residue field of an algebraic closure

An algebraic closure of a number field has no places of its own, but its ring of integers has
nonzero primes, and the quotient by one of them is a field: the ring of integers is integral over
the integers, so the prime below is a nonzero prime of a principal ideal domain, hence maximal, and
maximality goes up along an integral extension.

That field is an algebraic closure of a finite field.  Being algebraically closed is the only part
which needs the ambient field to be: a monic polynomial over the quotient lifts to a monic
polynomial over the ring of integers, that one has a root in the ambient field, the root is
integral over the ring of integers and therefore over the integers, so it already lies in the ring
of integers, and its class is a root of the polynomial one started with.  The base is finite
because the prime below it in the ring of integers of the number field is nonzero, hence maximal,
and the residue fields of a number ring are finite.

## Main results

* `InverseGalois.CFT.isMaximal_prime_ringOfIntegers` — a nonzero prime of the ring of integers of
  an arbitrary field is maximal.
* `InverseGalois.CFT.isAlgClosed_quotient_ringOfIntegers` — **the residue field of the ring of
  integers of an algebraically closed field is algebraically closed.**
* `InverseGalois.CFT.finite_quotient_under_ringOfIntegers` — **the residue field of the number
  field below is finite.**

## Tags

number field, ring of integers, residue field, algebraically closed field, decomposition group
-/

namespace InverseGalois.CFT

open NumberField Polynomial

attribute [local instance] Ideal.Quotient.field

/-! ### The prime and the prime below it -/

section Prime

variable {Ω : Type*} [Field Ω]

/-- **A nonzero prime of the ring of integers of an arbitrary field is maximal.**  The prime below
it in the integers is nonzero because the ring of integers is the integral closure of the integers,
hence maximal, and maximality goes up along an integral extension. -/
theorem isMaximal_prime_ringOfIntegers (P : Ideal (𝓞 Ω)) [P.IsPrime] (hP : P ≠ ⊥) :
    P.IsMaximal := by
  have h1 : Ideal.comap (algebraMap ℤ (𝓞 Ω)) P ≠ ⊥ :=
    Ideal.IsIntegralClosure.comap_ne_bot (A := 𝓞 Ω) (R := ℤ) Ω hP
  haveI : (Ideal.comap (algebraMap ℤ (𝓞 Ω)) P).IsPrime := Ideal.comap_isPrime _ _
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (Ideal.IsPrime.isMaximal ‹_› h1)

variable (k : Type*) [Field k] [NumberField k] [Algebra k Ω]

omit [NumberField k] in
/-- The prime of the number field below a nonzero prime of the ring of integers of an extension is
nonzero. -/
theorem under_ringOfIntegers_ne_bot (P : Ideal (𝓞 Ω)) (hP : P ≠ ⊥) : P.under (𝓞 k) ≠ ⊥ :=
  Ideal.under_ne_bot (𝓞 k) hP

/-- The prime of the number field below a nonzero prime of the ring of integers of an extension is
maximal. -/
theorem isMaximal_under_ringOfIntegers (P : Ideal (𝓞 Ω)) [P.IsPrime] (hP : P ≠ ⊥) :
    (P.under (𝓞 k)).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (under_ringOfIntegers_ne_bot k P hP)

/-- **The residue field of the number field below a nonzero prime of the ring of integers of an
extension is finite**, the prime below being a nonzero prime of a number ring. -/
theorem finite_quotient_under_ringOfIntegers (P : Ideal (𝓞 Ω)) [P.IsPrime] (hP : P ≠ ⊥) :
    Finite (𝓞 k ⧸ P.under (𝓞 k)) :=
  haveI := isMaximal_under_ringOfIntegers k P hP
  inferInstance

end Prime

/-! ### The residue field of an algebraically closed field -/

section AlgClosed

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]

/-- **The residue field of the ring of integers of an algebraically closed field at a maximal
prime is algebraically closed.**

A monic polynomial over the quotient lifts to a monic polynomial of the same degree over the ring
of integers; that one has a root in the ambient field, the root is integral over the ring of
integers and therefore over the integers, so it already lies in the ring of integers, and its class
is a root of the polynomial one started with. -/
theorem isAlgClosed_quotient_ringOfIntegers (P : Ideal (𝓞 Ω)) [P.IsMaximal] :
    IsAlgClosed (𝓞 Ω ⧸ P) := by
  refine IsAlgClosed.of_exists_root _ fun f hfm hfirr => ?_
  have hfd : f.natDegree ≠ 0 := fun h =>
    not_irreducible_one (hfm.natDegree_eq_zero.1 h ▸ hfirr)
  have hlift : f ∈ Polynomial.lifts (Ideal.Quotient.mk P) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨(Ideal.Quotient.mk_surjective (f.coeff n)).choose,
      (Ideal.Quotient.mk_surjective (f.coeff n)).choose_spec⟩
  obtain ⟨g, hgmap, hgdeg, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hfm
  set G : Polynomial Ω := g.map (algebraMap (𝓞 Ω) Ω) with hG
  have hGm : G.Monic := hgm.map _
  have hGdeg : G.natDegree = f.natDegree := by rw [hG, hgm.natDegree_map, hgdeg]
  have hdeg0 : G.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hGm.ne_zero, hGdeg]
    exact_mod_cast hfd
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root G hdeg0
  have hint : IsIntegral (𝓞 Ω) α := ⟨g, hgm, by simpa [hG, Polynomial.eval_map, aeval_def] using hα⟩
  obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 Ω) (R := ℤ) (B := Ω)).1
    (isIntegral_trans α hint)
  refine ⟨Ideal.Quotient.mk P b, ?_⟩
  have hgb : g.eval b = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 Ω) Ω
    rw [_root_.map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← hG, hb]
    exact hα
  show Polynomial.eval (Ideal.Quotient.mk P b) f = 0
  rw [← hgmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hgb, _root_.map_zero]

end AlgClosed

end InverseGalois.CFT
