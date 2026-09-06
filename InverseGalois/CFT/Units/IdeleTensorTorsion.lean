/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorPExact
import InverseGalois.CFT.Units.IdeleClassSES
import InverseGalois.CFT.Units.IdeleClassTorsionSES

/-!
# The idele sequence tensored with coefficients killed by a prime

Tensoring the sequence of the units, the ideles and the idele classes with a representation flat
over the integers leaves it exact, and that is what the theory of tori needs.  Coefficients killed
by a prime are not flat, and the failure is exactly one map: the principal ideles need not stay
injective after tensoring.

They do, and the reason is the Hasse principle for powers.  Tensoring with coefficients killed by a
prime does not distinguish a module from its reduction modulo that prime, so the question is
whether a unit of the field whose principal idele is a power of an idele is itself a power in the
field.  Wang's theorem says it is, for a prime exponent and with no hypothesis on the roots of
unity, so the reduction of the principal ideles modulo the prime is injective and the tensored
sequence stays short exact.

The same statement for the elements killed by the prime needs nothing at all: there the middle term
is itself killed by the prime, and an injection into a module killed by a prime survives any
tensoring.

## Main results

* `InverseGalois.CFT.injective_modNsmulHom_globalUnitsToIdele`: **the principal ideles stay
  injective modulo a prime.**
* `InverseGalois.CFT.tensorSeq_ideleClassShortComplex_shortExact_of_nsmul`: **the units, the ideles
  and the idele classes stay short exact after tensoring with coefficients killed by a prime.**
* `InverseGalois.CFT.tensorSeq_ideleClassTorsionShortComplex_shortExact`: **the elements killed by a
  prime of the units, of the ideles and of the idele classes stay short exact after tensoring with
  any coefficients.**

## Tags

number field, idele, idele class group, tensor product, Hasse principle, short exact sequence
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K]
  {p : ℕ} (hp : p.Prime)

/-! ### The principal ideles modulo a prime -/

include hp in
/-- **The principal ideles stay injective modulo a prime.**  A unit of the field whose principal
idele is a power of an idele is a power in every completion, so Wang's theorem makes it a power in
the field. -/
theorem injective_modNsmulHom_globalUnitsToIdele :
    Function.Injective (modNsmulHom (globalUnitsToIdele k K) p).hom.hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (nsmulLinear ℤ p ↥(globalUnitsRep k K).V)) x
  have hx' : Submodule.mkQ (LinearMap.range (nsmulLinear ℤ p ↥(ideleRep k K).V))
      ((globalUnitsToIdele k K).hom.hom u) = 0 := hx
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx'
  obtain ⟨z, hz⟩ := hx'
  have hz' : ideleDiag K u = (p : ℤ) • z := by
    rw [natCast_zsmul]
    exact hz.symm
  obtain ⟨y, hy⟩ := exists_zsmul_eq_of_ideleDiag_eq_zsmul hp u z hz'
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨y, by rw [nsmulLinear_apply, ← natCast_zsmul]; exact hy⟩

/-! ### The tensored sequences -/

include hp in
/-- **The units, the ideles and the idele classes stay short exact after tensoring with
coefficients killed by a prime.** -/
theorem tensorSeq_ideleClassShortComplex_shortExact_of_nsmul (W : Rep ℤ Gal(K/k))
    (hW : ∀ w : ↥W.V, p • w = 0) :
    (tensorSeq W (ideleClassShortComplex k K)).ShortExact :=
  haveI : Fact p.Prime := ⟨hp⟩
  tensorSeq_shortExact_of_injective_modNsmul (ideleClassShortComplex_shortExact k K) W hW
    (injective_modNsmulHom_globalUnitsToIdele hp)

include hp in
/-- **The elements killed by a prime of the units, of the ideles and of the idele classes stay
short exact after tensoring with any coefficients.**  The middle term is killed by the prime, and
an injection into a module killed by a prime has a retraction that survives the tensoring. -/
theorem tensorSeq_ideleClassTorsionShortComplex_shortExact (W : Rep ℤ Gal(K/k)) :
    (tensorSeq W (ideleClassTorsionShortComplex k K (p : ℤ))).ShortExact :=
  haveI : Fact p.Prime := ⟨hp⟩
  tensorSeq_shortExact_of_nsmul (p := p) (ideleClassTorsionShortComplex_shortExact k K hp) W
    fun b => by
      rw [← natCast_zsmul]
      refine Subtype.ext ?_
      push_cast
      exact mem_torsionBy.1 b.2

end

end InverseGalois.CFT
