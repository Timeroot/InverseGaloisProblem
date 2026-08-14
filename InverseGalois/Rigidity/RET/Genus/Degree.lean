/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Residue

/-!
# The degree of a place

A point of a curve over a field which is not algebraically closed can carry more than one value of
a function: its residue field can be a proper extension of the constants.  The *degree* of a place
measures that, as the dimension of the residue field over the constants; over an algebraically
closed constant field every place has degree one, and the degree of a divisor is then just the sum
of its multiplicities.

Read from a chart, the degree of a place is the dimension over the constants of the quotient of the
chart by the prime under the place.  This does not depend on the chart: the residue field of a
place is intrinsic to it, so two charts see the same field, and they see it with the same
constants because the constants sit inside `F` before either chart is chosen.

## Main definitions

* `Rigidity.RET.primeDeg` — the degree of a prime of a chart, over a field of constants.

## Main results

* `Rigidity.RET.primeDeg_eq_of_placeSubring_eq` — primes of different charts giving the same place
  have the same degree.
-/

open IsDedekindDomain

noncomputable section


namespace Rigidity.RET

variable {F : Type*} [Field F]

/-! ## Comparing the residue fields of equal places -/

/-- **Equal places have the same residue field.** -/
def residueFieldCongr : ∀ {A A' : ValuationSubring F}, A = A' →
    (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A')
  | _, _, rfl => RingEquiv.refl _

theorem residueFieldCongr_residue {A A' : ValuationSubring F} (h : A = A') (x : A) (x' : A')
    (hx : (x : F) = (x' : F)) :
    residueFieldCongr h (IsLocalRing.residue A x) = IsLocalRing.residue A' x' := by
  subst h
  obtain rfl : x = x' := Subtype.ext hx
  rfl

/-! ## The degree of a prime of a chart -/

variable (k : Type*) [Field k]
variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra k B]

/-- **The degree of a prime of a chart**: the dimension over the constants of the field of values
that the functions of the chart take at the prime. -/
def primeDeg (v : HeightOneSpectrum B) : ℕ := Module.finrank k (B ⧸ v.asIdeal)

variable {k}
variable {B₁ B₂ : Type*} [CommRing B₁] [IsDedekindDomain B₁] [Algebra k B₁]
  [CommRing B₂] [IsDedekindDomain B₂] [Algebra k B₂]
variable [Algebra k F] [Algebra B₁ F] [IsFractionRing B₁ F] [IsScalarTower k B₁ F]
  [Algebra B₂ F] [IsFractionRing B₂ F] [IsScalarTower k B₂ F]

/-- **The degree of a place does not depend on the chart it is read in.** -/
theorem primeDeg_eq_of_placeSubring_eq {v₁ : HeightOneSpectrum B₁} {v₂ : HeightOneSpectrum B₂}
    (h : placeSubring F v₁ = placeSubring F v₂) : primeDeg k v₁ = primeDeg k v₂ := by
  set e : (B₁ ⧸ v₁.asIdeal) ≃+* (B₂ ⧸ v₂.asIdeal) :=
    ((residueFieldEquiv F v₁).trans (residueFieldCongr h)).trans (residueFieldEquiv F v₂).symm
    with he
  have hconst : ∀ c : k, e (algebraMap k (B₁ ⧸ v₁.asIdeal) c)
      = algebraMap k (B₂ ⧸ v₂.asIdeal) c := by
    intro c
    have hval : ((toPlaceSubring F v₁ (algebraMap k B₁ c) : placeSubring F v₁) : F)
        = ((toPlaceSubring F v₂ (algebraMap k B₂ c) : placeSubring F v₂) : F) := by
      rw [coe_toPlaceSubring, coe_toPlaceSubring, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    have hstep : residueFieldCongr h (chartResidue F v₁ (algebraMap k B₁ c))
        = chartResidue F v₂ (algebraMap k B₂ c) :=
      residueFieldCongr_residue h _ _ hval
    have h₁ : algebraMap k (B₁ ⧸ v₁.asIdeal) c
        = Ideal.Quotient.mk v₁.asIdeal (algebraMap k B₁ c) := rfl
    have h₂ : algebraMap k (B₂ ⧸ v₂.asIdeal) c
        = Ideal.Quotient.mk v₂.asIdeal (algebraMap k B₂ c) := rfl
    rw [he, h₁, h₂, RingEquiv.trans_apply, RingEquiv.trans_apply, residueFieldEquiv_mk, hstep,
      ← residueFieldEquiv_mk F v₂ (algebraMap k B₂ c), RingEquiv.symm_apply_apply]
  exact (AlgEquiv.ofRingEquiv (f := e) hconst).toLinearEquiv.finrank_eq

end Rigidity.RET
