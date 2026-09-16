/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.GlobalClasses
import InverseGalois.CFT.PoitouTate.TensorValuation
import InverseGalois.CFT.Units.IdeleClassFixed
import InverseGalois.CFT.Units.OrdFinsupp

/-!
# The units confined to a set of places

A prescription of radicands over a number field asks for units with three properties at once: they
are local powers at a prescribed set of places, their order is divisible by the exponent at every
place outside a prescribed set where ramification is allowed, and at the finitely many named places
their orders are the prescribed ones.  The first two properties are closed under multiplication, so
they cut out a **subgroup** of the units of the field; the third is the value of a homomorphism
from that subgroup onto the free abelian group on the named places.

That is exactly the shape the abstract descent consumes: a group carrying an equivariant valuation
onto the free abelian group on a permuted set, with the two standing conditions built into the
group rather than carried alongside.  This file constructs the group, the valuation and the kernel
of the valuation, and records that the Galois group carries each of them into itself.

## Main definitions

* `InverseGalois.CFT.ordAt`: the vector of orders at the places of a finite set.
* `InverseGalois.CFT.confinedUnits`: the units which are local powers at one set of places and have
  order divisible by the exponent outside another.
* `InverseGalois.CFT.confinedOrd`: the vector of orders of a confined unit at the named places.
* `InverseGalois.CFT.confinedSUnits`: the confined units whose orders at the named places vanish.

## Main results

* `InverseGalois.CFT.isStableSubgroup_confinedUnits`: **the confined units are carried into
  themselves by the Galois group.**
* `InverseGalois.CFT.confinedOrd_smul_apply`: **the vector of orders is equivariant.**
* `InverseGalois.CFT.mem_confinedSUnits_iff`: the kernel of the vector of orders is the subgroup of
  confined units without order at the named places.

## Tags

number field, place, order, local power, Galois action, valuation, descent
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### The places inside a stable set -/

section Inside

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
variable (Xs : Set (HeightOneSpectrum (𝓞 K))) [IsGaloisStablePlaces k K Xs]

/-- **The Galois group permutes the places of a stable set.** -/
instance mulActionInsidePlaces : MulAction Gal(K/k) ↥Xs where
  smul σ y := ⟨σ • (y : HeightOneSpectrum (𝓞 K)),
    (IsGaloisStablePlaces.smul_mem_iff σ (y : HeightOneSpectrum (𝓞 K))).2 y.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

@[simp]
theorem coe_smul_insidePlaces (σ : Gal(K/k)) (y : ↥Xs) :
    ((σ • y : ↥Xs) : HeightOneSpectrum (𝓞 K)) = σ • (y : HeightOneSpectrum (𝓞 K)) := rfl

end Inside

/-! ### The vector of orders at a finite set of places -/

section OrdAt

variable {K : Type} [Field K] [NumberField K]
variable (Xs : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs]

/-- **The vector of orders at the places of a finite set.** -/
noncomputable def ordAt : Additive Kˣ →+ (↥Xs →₀ ℤ) where
  toFun u := Finsupp.ofSupportFinite
    (fun y => ord K (y : HeightOneSpectrum (𝓞 K)) ((u.toMul : Kˣ) : K)) (Set.toFinite _)
  map_zero' := by
    refine Finsupp.ext fun y => ?_
    show ord K (y : HeightOneSpectrum (𝓞 K)) (((1 : Kˣ) : K)) = 0
    rw [Units.val_one, ord_one]
  map_add' u w := by
    refine Finsupp.ext fun y => ?_
    show ord K (y : HeightOneSpectrum (𝓞 K)) (((u.toMul * w.toMul : Kˣ) : K)) = _
    rw [Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _)]
    rfl

@[simp]
theorem ordAt_apply (u : Additive Kˣ) (y : ↥Xs) :
    ordAt Xs u y = ord K (y : HeightOneSpectrum (𝓞 K)) ((u.toMul : Kˣ) : K) := rfl

variable {k : Type} [Field k] [Algebra k K] [IsGaloisStablePlaces k K Xs]

/-- **The vector of orders is equivariant**: the order of a translated unit at a place is the order
of the unit at the place translated back. -/
theorem ordAt_smul_apply (σ : Gal(K/k)) (a : Kˣ) (y : ↥Xs) :
    ordAt Xs (Additive.ofMul (σ • a)) y = ordAt Xs (Additive.ofMul a) (σ⁻¹ • y) := by
  have h := ord_galSmul σ (σ⁻¹ • (y : HeightOneSpectrum (𝓞 K))) ((a : Kˣ) : K)
  rw [smul_inv_smul] at h
  exact h

end OrdAt

/-! ### The units confined to a set of places -/

section Confined

variable {K : Type} [Field K] [NumberField K]

/-- **The units which are local `n`-th powers at every place of one set and whose order is
divisible by `n` at every place outside another.**  The first set is where the radicand is asked to
be inert, the second is where its ramification is allowed to sit. -/
def confinedUnits (K : Type) [Field K] [NumberField K] (n : ℕ)
    (Tz Y : Set (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ where
  carrier := {x : Kˣ | (∀ v ∈ Tz, x ∈ (localClassHom v n).ker) ∧
    ∀ v ∉ Y, (n : ℤ) ∣ ord K v ((x : Kˣ) : K)}
  mul_mem' {x y} hx hy := by
    refine ⟨fun v hv => Subgroup.mul_mem _ (hx.1 v hv) (hy.1 v hv), fun v hv => ?_⟩
    rw [Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _)]
    exact dvd_add (hx.2 v hv) (hy.2 v hv)
  one_mem' := by
    refine ⟨fun v _ => Subgroup.one_mem _, fun v _ => ?_⟩
    rw [Units.val_one, ord_one]
    exact dvd_zero _
  inv_mem' {x} hx := by
    refine ⟨fun v hv => Subgroup.inv_mem _ (hx.1 v hv), fun v hv => ?_⟩
    rw [Units.val_inv_eq_inv_val, ord_inv]
    exact (hx.2 v hv).neg_right

theorem mem_confinedUnits {n : ℕ} {Tz Y : Set (HeightOneSpectrum (𝓞 K))} {x : Kˣ} :
    x ∈ confinedUnits K n Tz Y ↔ (∀ v ∈ Tz, localClassHom v n x = 1) ∧
      ∀ v ∉ Y, (n : ℤ) ∣ ord K v ((x : Kˣ) : K) := Iff.rfl

variable {k : Type} [Field k] [Algebra k K]

/-- **The confined units are carried into themselves by the Galois group.** -/
instance isStableSubgroup_confinedUnits (n : ℕ) (Tz Y : Set (HeightOneSpectrum (𝓞 K)))
    [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y] :
    IsStableSubgroup Gal(K/k) (confinedUnits K n Tz Y) where
  smul_mem σ {x} hx := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hv' : σ⁻¹ • v ∈ Tz := (IsGaloisStablePlaces.smul_mem_iff σ⁻¹ v).2 hv
      have h := localClassesGalEquiv_localClassHom σ (σ⁻¹ • v) n x
      rw [hx.1 (σ⁻¹ • v) hv', _root_.map_one, smul_inv_smul, galUnits_eq_smul] at h
      exact h.symm
    · have hv' : σ⁻¹ • v ∉ Y := fun hc => hv ((IsGaloisStablePlaces.smul_mem_iff σ⁻¹ v).1 hc)
      have h := ord_galSmul σ (σ⁻¹ • v) ((x : Kˣ) : K)
      rw [smul_inv_smul] at h
      exact h ▸ hx.2 (σ⁻¹ • v) hv'

end Confined

/-! ### The valuation of a confined unit at the named places -/

section Valuation

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] (n : ℕ)
variable (Tz Y : Set (HeightOneSpectrum (𝓞 K)))
variable (Xs : Set (HeightOneSpectrum (𝓞 K))) [Finite ↥Xs]

/-- **The vector of orders of a confined unit at the named places.** -/
noncomputable def confinedOrd :
    Additive ↥(confinedUnits K n Tz Y) →+ (↥Xs →₀ ℤ) :=
  (ordAt Xs).comp (MonoidHom.toAdditive (confinedUnits K n Tz Y).subtype)

@[simp]
theorem confinedOrd_apply (u : Additive ↥(confinedUnits K n Tz Y)) (y : ↥Xs) :
    confinedOrd n Tz Y Xs u y
      = ord K (y : HeightOneSpectrum (𝓞 K)) (((u.toMul : ↥(confinedUnits K n Tz Y)) : Kˣ) : K) :=
  rfl

/-- **The confined units whose orders at the named places all vanish.** -/
def confinedSUnits : Subgroup ↥(confinedUnits K n Tz Y) where
  carrier := {x | ∀ y : ↥Xs, ord K (y : HeightOneSpectrum (𝓞 K)) ((x : Kˣ) : K) = 0}
  mul_mem' {x y} hx hy z := by
    show ord K (z : HeightOneSpectrum (𝓞 K)) (((x : Kˣ) * (y : Kˣ) : Kˣ) : K) = 0
    rw [Units.val_mul, ord_mul _ (Units.ne_zero _) (Units.ne_zero _), hx z, hy z, add_zero]
  one_mem' z := by
    show ord K (z : HeightOneSpectrum (𝓞 K)) (((1 : Kˣ) : K)) = 0
    rw [Units.val_one, ord_one]
  inv_mem' {x} hx z := by
    show ord K (z : HeightOneSpectrum (𝓞 K)) ((((x : Kˣ)⁻¹ : Kˣ) : K)) = 0
    rw [Units.val_inv_eq_inv_val, ord_inv, hx z, neg_zero]

/-- **The kernel of the vector of orders is the subgroup of confined units without order at the
named places.** -/
theorem mem_confinedSUnits_iff (a : ↥(confinedUnits K n Tz Y)) :
    a ∈ confinedSUnits n Tz Y Xs ↔ confinedOrd n Tz Y Xs (Additive.ofMul a) = 0 := by
  refine ⟨fun h => Finsupp.ext fun y => ?_, fun h y => ?_⟩
  · rw [confinedOrd_apply]
    exact h y
  · have h2 := congrArg (fun z : ↥Xs →₀ ℤ => z y) h
    simpa using h2

variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K Xs]

/-- **The vector of orders of a confined unit is equivariant.** -/
theorem confinedOrd_smul_apply (σ : Gal(K/k)) (a : ↥(confinedUnits K n Tz Y)) (y : ↥Xs) :
    confinedOrd n Tz Y Xs (Additive.ofMul (σ • a)) y
      = confinedOrd n Tz Y Xs (Additive.ofMul a) (σ⁻¹ • y) :=
  ordAt_smul_apply Xs σ (a : Kˣ) y

/-- **The units without order at the named places are carried into themselves by the Galois
group.** -/
instance isStableSubgroup_confinedSUnits :
    IsStableSubgroup Gal(K/k) (confinedSUnits n Tz Y Xs) where
  smul_mem σ {a} ha := fun y =>
    (confinedOrd_smul_apply n Tz Y Xs σ a y).trans (ha (σ⁻¹ • y))

end Valuation

end InverseGalois.CFT
