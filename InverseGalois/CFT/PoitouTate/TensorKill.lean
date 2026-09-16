/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TensorShrink

/-!
# A finite family of coefficients whose death kills a class

A class in the first cohomology of a finite group with coefficients in a tensor product is killed
by a homomorphism of the **second** factor as soon as that homomorphism kills finitely many
prescribed elements of that factor, and the list of elements can be named before the homomorphism
is.  The reason is that the left factor is spanned by finitely many elements: a cocycle has one
value at each element of the group, each value is a combination of the members of the spanning
family against coefficients in the right factor, and a homomorphism killing all of those
coefficients kills every value of the cocycle.

That order — the list first, the homomorphism afterwards — is the order a counting argument needs.
A shrinking of the coefficients can be made to kill a prescribed finite list of elements, of a
length fixed in advance by the size of the group and the size of the spanning family, but it cannot
be asked to kill a whole cohomology group.  Stating the conclusion as a list of elements rather than
as a class also keeps it free of the action the coefficients carry, because an element of the module
does not know which action is meant.

## Main results

* `InverseGalois.CFT.exists_sum_tmul_of_span`: **an element of a tensor product is a combination of
  a spanning family of the left factor against coefficients in the right.**
* `InverseGalois.CFT.exists_kill_family_of_span`: **a finite family of elements of the second
  factor, of a size the group and the spanning family alone decide, whose death under an
  equivariant homomorphism kills a prescribed class.**

## Tags

group cohomology, tensor product, spanning family, shrinking, counting argument
-/

namespace InverseGalois.CFT

open CategoryTheory TensorProduct groupCohomology

/-! ### Coordinates along a spanning family -/

section Span

variable {R : Type*} [CommRing R] {A X : Type*} [AddCommGroup A] [Module R A] [AddCommGroup X]
  [Module R X] {d : ℕ}

/-- **An element of a tensor product is a combination of a spanning family of the left factor
against coefficients in the right factor.**  No basis is asked for, only a spanning family, so the
left factor is allowed torsion. -/
theorem exists_sum_tmul_of_span (b : Fin d → A) (hb : Submodule.span R (Set.range b) = ⊤)
    (z : A ⊗[R] X) : ∃ w : Fin d → X, z = ∑ i, b i ⊗ₜ[R] w i := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a x =>
    have ha : a ∈ Submodule.span R (Set.range b) := by rw [hb]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
    refine ⟨fun i => c i • x, ?_⟩
    calc a ⊗ₜ[R] x = (∑ i, c i • b i) ⊗ₜ[R] x := by rw [hc]
      _ = ∑ i, b i ⊗ₜ[R] (c i • x) := by
            rw [TensorProduct.sum_tmul]
            exact Finset.sum_congr rfl fun i _ => TensorProduct.smul_tmul _ _ _
  | add z z' hz hz' =>
    obtain ⟨w, rfl⟩ := hz
    obtain ⟨w', rfl⟩ := hz'
    refine ⟨w + w', ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.tmul_add _ _ _).symm

end Span

/-! ### The family cut out by a class -/

section Kill

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C : Type} [CommGroup C] [MulDistribMulAction Q C]

/-- **A finite family of elements of the second factor whose death under an equivariant
homomorphism kills the class of a prescribed cocycle.**  The family is indexed by the group times
the spanning family of the left factor: the cocycle has one value at each element of the group, and
each value is read in the coordinates the spanning family provides.

The group the homomorphism lands in is quantified over inside the conclusion, after the family is
named: the family is read in the second factor alone and knows nothing of where it is sent, so a
single family answers for every target at once. -/
theorem exists_kill_family_of_span_cocycle {d : ℕ} (b : Fin d → Additive A)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) (c : Q → Additive A ⊗[ℤ] Additive C)
    (hcoc : c ∈ cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))) :
    ∃ x : Q × Fin d → C,
      ∀ (C' : Type) [CommGroup C'] [MulDistribMulAction Q C'] (φ : C →* C')
        (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w), (∀ ν, φ (x ν) = 1) →
        (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ hφ) 1).hom
          (H1π (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)) ⟨c, hcoc⟩) = 0 := by
  choose v hv using fun q => exists_sum_tmul_of_span b hb (c q)
  refine ⟨fun ν => (v ν.1 ν.2).toMul, fun C' _ _ φ hφ hkill => ?_⟩
  have hzero : ∀ q, tensorCoeff A φ (c q) = 0 := by
    intro q
    rw [hv q, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : φ (v q i).toMul = 1 := hkill (q, i)
    show b i ⊗ₜ[ℤ] Additive.ofMul (φ (v q i).toMul) = 0
    rw [h1]
    exact TensorProduct.tmul_zero _ _
  have hmap : mapCocycles₁ (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ hφ)
      (⟨c, hcoc⟩ : cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)))
      = 0 := Subtype.ext (funext hzero)
  rw [H1π_comp_map_apply, hmap]
  exact map_zero _

/-- **A finite family of elements of the second factor, of a size the group and the spanning family
alone decide, whose death under an equivariant homomorphism kills a prescribed class.**  Every class
is the class of a cocycle, and the reading of the map of the coefficients on cohomology is the
reading on cocycles. -/
theorem exists_kill_family_of_span {d : ℕ} (b : Fin d → Additive A)
    (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (y : H1 (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))) :
    ∃ x : Q × Fin d → C,
      ∀ (C' : Type) [CommGroup C'] [MulDistribMulAction Q C'] (φ : C →* C')
        (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w), (∀ ν, φ (x ν) = 1) →
        (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ hφ) 1).hom y = 0 := by
  induction y using H1_induction_on with
  | @h z => exact exists_kill_family_of_span_cocycle b hb _ z.2

end Kill

end InverseGalois.CFT
