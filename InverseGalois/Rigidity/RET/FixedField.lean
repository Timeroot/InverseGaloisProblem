/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Hilbert.Analytic.Luroth
import InverseGalois.Rigidity.RET.BaseTransport

/-!
# Groups of automorphisms of a rational function field

A finite group `Γ` acting faithfully on `k(T)` by ring automorphisms fixing the constants is the
Galois group of `k(T)` over its fixed field: this is Artin's theorem, which Mathlib provides for
the fixed subfield of any faithful finite action.  Over `k(T)` the fixed field is more than an
abstract Galois base — by Lüroth's theorem (`RatFunc.luroth`) it is again a rational function
field, since it is an intermediate field of `k(T)/k` other than `k` itself; it is not `k` because
`k(T)` is not finite over `k`.

So a finite group of automorphisms of `k(T)` realizes itself as the Galois group of a degree
`|Γ|` extension `k(T)/k(w)` whose base is a copy of `k(T)`.  Over `ℚ` this is exactly a regular
realization: the extension field is `ℚ(T)`, whose constants are just `ℚ`, and the base is
identified with `ℚ(T)` by `IsRegularInverseGalois.of_ratFunc_ext`.

Every subgroup of the Möbius group acts this way, so the theorem turns explicit fractional linear
substitutions into regular inverse Galois groups.

## Main results

* `Rigidity.RET.fixedField` — the fixed field, as an intermediate field of `k(T)/k`.
* `Rigidity.RET.autHom_bijective` — Artin's theorem: `Γ` is the full Galois group.
* `Rigidity.RET.exists_ringEquiv_fixedField` — Lüroth: the fixed field is a copy of `k(T)`.
* `IsRegularInverseGalois.of_faithful_smul` — a finite group acting faithfully on `ℚ(T)` is a
  regular inverse Galois group.
* `IsRegularInverseGalois.of_injective_ringAut` — the same, for a group presented as an injective
  family of ring automorphisms.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-- The scalar action underlying a semiring action on a field of rational functions, named to
short-circuit the generic search (which unfolds the field of rational functions all the way down
to the polynomial ring before finding the obvious answer). -/
instance (priority := high) smulOfMulSemiringAction {k : Type*} [Field k] {Γ : Type*} [Monoid Γ]
    [MulSemiringAction Γ (RatFunc k)] : SMul Γ (RatFunc k) :=
  (inferInstance : MulAction Γ (RatFunc k)).toSMul

variable (k : Type*) [Field k]

/-- The variable is not a constant. -/
theorem X_not_mem_bot : (RatFunc.X : RatFunc k) ∉ (⊥ : IntermediateField k (RatFunc k)) := by
  rw [RatFunc.mem_bot_iff]
  rintro ⟨c, hc⟩
  rw [← RatFunc.algebraMap_C, ← RatFunc.algebraMap_X] at hc
  exact Polynomial.X_ne_C c (IsFractionRing.injective (Polynomial k) (RatFunc k) hc).symm

variable {k} {Γ : Type*} [Group Γ] [MulSemiringAction Γ (RatFunc k)]
  (hfix : ∀ (g : Γ) (c : k), g • RatFunc.C c = RatFunc.C c)

/-- **The fixed field** of a group of automorphisms of `k(T)` fixing the constants, as an
intermediate field of `k(T)/k`. -/
def fixedField : IntermediateField k (RatFunc k) :=
  (FixedPoints.subfield Γ (RatFunc k)).toIntermediateField (fun x g => hfix g x)

variable [Finite Γ] [FaithfulSMul Γ (RatFunc k)]

instance finiteDimensional_fixedField : FiniteDimensional ↥(fixedField hfix) (RatFunc k) :=
  (inferInstance : FiniteDimensional ↥(FixedPoints.subfield Γ (RatFunc k)) (RatFunc k))

instance isGalois_fixedField : IsGalois ↥(fixedField hfix) (RatFunc k) :=
  (inferInstance : IsGalois ↥(FixedPoints.subfield Γ (RatFunc k)) (RatFunc k))

omit [Finite Γ] in
/-- **Artin's degree formula**: `k(T)` has degree `|Γ|` over the fixed field. -/
theorem finrank_fixedField [Fintype Γ] :
    Module.finrank ↥(fixedField hfix) (RatFunc k) = Fintype.card Γ :=
  FixedPoints.finrank_eq_card Γ (RatFunc k)

omit [FaithfulSMul Γ (RatFunc k)] in
/-- The fixed field is strictly larger than the constants: it has finite index in `k(T)`, whereas
`k(T)` is infinite over `k`, the variable being transcendental. -/
theorem fixedField_ne_bot : fixedField hfix ≠ ⊥ := by
  intro hbot
  haveI : FiniteDimensional k ↥(fixedField hfix) := by rw [hbot]; infer_instance
  haveI : FiniteDimensional k (RatFunc k) :=
    FiniteDimensional.trans k ↥(fixedField hfix) (RatFunc k)
  exact RatFunc.transcendental_of_not_mem_bot RatFunc.X (X_not_mem_bot k)
    (Algebra.IsAlgebraic.isAlgebraic _)

omit [FaithfulSMul Γ (RatFunc k)] in
/-- **Lüroth's theorem applied to the fixed field**: it is again a field of rational functions. -/
theorem exists_ringEquiv_fixedField : Nonempty (RatFunc k ≃+* ↥(fixedField hfix)) := by
  obtain ⟨w, hw⟩ := RatFunc.luroth (fixedField hfix) (fixedField_ne_bot hfix)
  have hw' : w ∉ (⊥ : IntermediateField k (RatFunc k)) := by
    intro hmem
    exact fixedField_ne_bot hfix (by rw [hw, IntermediateField.adjoin_simple_eq_bot_iff.mpr hmem])
  obtain ⟨e, -⟩ := RatFunc.exists_algEquiv_ratFunc w hw'
  exact ⟨(e.trans (IntermediateField.equivOfEq hw.symm)).toRingEquiv⟩

/-- A group element, read as an automorphism of `k(T)` over the fixed field. -/
def toAutFixedField (g : Γ) : RatFunc k ≃ₐ[↥(fixedField hfix)] RatFunc k :=
  AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv Γ (RatFunc k) g) (fun x => x.2 g)

/-- The group, mapped into the Galois group of `k(T)` over its fixed field. -/
def autHom : Γ →* (RatFunc k ≃ₐ[↥(fixedField hfix)] RatFunc k) where
  toFun := toAutFixedField hfix
  map_one' := by ext x; exact one_smul Γ x
  map_mul' g h := by ext x; exact mul_smul g h x

/-- **Artin's theorem**: a faithful finite group of automorphisms of `k(T)` is the whole Galois
group of `k(T)` over its fixed field.  Injectivity is faithfulness; surjectivity is the count, the
number of automorphisms of a Galois extension being its degree, which is `|Γ|`. -/
theorem autHom_bijective : Function.Bijective (autHom hfix) := by
  haveI : Fintype Γ := Fintype.ofFinite Γ
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨fun g h hgh => eq_of_smul_eq_smul (α := RatFunc k) (fun a => ?_), ?_⟩
  · exact congrArg (fun φ : RatFunc k ≃ₐ[↥(fixedField hfix)] RatFunc k => φ a) hgh
  · rw [Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank ↥(fixedField hfix) (RatFunc k), finrank_fixedField hfix]

/-- The Galois group of `k(T)` over the fixed field, identified with `Γ`. -/
def autMulEquiv : Γ ≃* (RatFunc k ≃ₐ[↥(fixedField hfix)] RatFunc k) :=
  MulEquiv.ofBijective (autHom hfix) (autHom_bijective hfix)

end Rigidity.RET

namespace IsRegularInverseGalois

/-- **A finite group of automorphisms of `ℚ(T)` is a regular inverse Galois group.**

The group is the Galois group of `ℚ(T)` over its fixed field (Artin), the fixed field is another
copy of `ℚ(T)` (Lüroth), and `ℚ(T)` has no constants beyond `ℚ`; transporting the base along the
identification (`IsRegularInverseGalois.of_ratFunc_ext`) gives a regular realization. -/
theorem of_faithful_smul (G : Type) [Group G] [Finite G] [MulSemiringAction G (RatFunc ℚ)]
    [FaithfulSMul G (RatFunc ℚ)] : IsRegularInverseGalois G := by
  have hfix : ∀ (g : G) (c : ℚ), g • RatFunc.C c = RatFunc.C c := by
    intro g c
    rw [eq_ratCast (RatFunc.C : ℚ →+* RatFunc ℚ) c]
    exact map_ratCast (MulSemiringAction.toRingEquiv G (RatFunc ℚ) g) c
  obtain ⟨e⟩ := Rigidity.RET.exists_ringEquiv_fixedField hfix
  exact of_ratFunc_ext ↥(Rigidity.RET.fixedField hfix) e (Rigidity.RET.autMulEquiv hfix).symm

/-- **A finite group of ring automorphisms of `ℚ(T)` is a regular inverse Galois group.**  The
family acts on `ℚ(T)` by evaluation, and the action is faithful precisely because the family is
injective; the constants are fixed automatically, a ring automorphism preserving the rationals. -/
theorem of_injective_ringAut (G : Type) [Group G] [Finite G] (φ : G →* RingAut (RatFunc ℚ))
    (hφ : Function.Injective φ) : IsRegularInverseGalois G := by
  letI : MulSemiringAction G (RatFunc ℚ) := MulSemiringAction.compHom _ φ
  haveI : FaithfulSMul G (RatFunc ℚ) := ⟨fun {_ _} h => hφ (RingEquiv.ext fun x => h x)⟩
  exact of_faithful_smul G

end IsRegularInverseGalois
