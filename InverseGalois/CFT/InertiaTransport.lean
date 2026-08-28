/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.TameRamification

/-!
# Total ramification is an isomorphism invariant

A prime of a Galois number field is totally ramified exactly when its inertia subgroup is the whole
Galois group, and equally when its ramification index is the degree of the field.  In the second
form the property visibly only depends on the isomorphism class: contracting a prime along an
isomorphism of the rings of integers preserves both the rational prime below it and the
ramification index, and an isomorphism of fields preserves the degree.

This is what allows a field built inside one algebraic closure — a subfield of a cyclotomic field,
say — to be moved into another ambient field without losing the ramification data that it was built
to have.

## Main results

* `InverseGalois.CFT.inertia_eq_top_of_algEquiv`: **a number field isomorphic to one totally
  ramified at a prime is itself totally ramified there.**

## Tags

inertia subgroup, ramification index, totally ramified, number field
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {E F : Type*} [Field E] [NumberField E] [IsGalois ℚ E] [Field F] [NumberField F]
  [IsGalois ℚ F] {p : ℕ}

/-- **Total ramification transports along an isomorphism of number fields.**  A prime of the target
contracts to a prime of the source lying over the same rational prime and with the same
ramification index, and the two fields have the same degree, so the two inertia subgroups have the
order of their respective Galois groups at the same time. -/
theorem inertia_eq_top_of_algEquiv (e : E ≃ₐ[ℚ] F) (hp : p.Prime)
    (h : ∀ (P : Ideal (𝓞 E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)})),
      Ideal.inertia Gal(E/ℚ) P = ⊤)
    (Q : Ideal (𝓞 F)) [Q.IsPrime] [hQo : Q.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.inertia Gal(F/ℚ) Q = ⊤ := by
  set f := mapAlgEquivInt (e : E ≃+* F) with hf
  set P : Ideal (𝓞 E) := Ideal.comap (f : 𝓞 E →+* 𝓞 F) Q with hP
  have hPp : P.IsPrime := Ideal.comap_isPrime _ _
  have hPo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    have hunder : P.under ℤ = Q.under ℤ := by
      rw [Ideal.under, Ideal.under, hP, Ideal.comap_comap]
      congr 1
      exact Subsingleton.elim _ _
    rw [hunder]
    exact hQo.over
  haveI := hPp
  haveI := hPo
  have hidx : Ideal.ramificationIdx (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) P =
      Ideal.ramificationIdx (algebraMap ℤ (𝓞 F)) (Ideal.span {(p : ℤ)}) Q :=
    Ideal.ramificationIdx_comap_eq (Ideal.span {(p : ℤ)}) f Q
  rw [← inertia_eq_top_iff_card_eq_finrank, card_inertia_eq_ramificationIdx_span hp Q, ← hidx,
    ← card_inertia_eq_ramificationIdx_span hp P, h P hPp hPo, Subgroup.card_top,
    IsGalois.card_aut_eq_finrank]
  exact e.toLinearEquiv.finrank_eq

end InverseGalois.CFT
