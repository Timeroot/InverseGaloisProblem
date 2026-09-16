/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ClassSet
import InverseGalois.CFT.Units.SUnitFinite

/-!
# The units of order divisible by an exponent, modulo the powers

A unit of a number field whose order is divisible by a fixed exponent away from a prescribed finite
set of places is, outside that set, the
exponent-th power of a fractional ideal, and a fractional ideal differs from a representative of
its class by a principal one.  Choosing the representatives away from a fixed finite set of places
— which is possible because there are finitely many classes — the correction is an element of the
field whose exponent-th power absorbs the whole divisor outside the two sets together, so the unit
becomes, up to an exponent-th power of the field, a unit for a finite set of places.

Those units are finitely generated, by Dirichlet's theorem enlarged by the finitely many orders at
the chosen places.  So a **single finitely generated subgroup** carries every unit of order
divisible by the exponent outside the prescribed set, modulo exponent-th powers: adjoining the
exponent-th roots of finitely many elements produces a field containing an exponent-th root of
every one of them at once.

## Main results

* `InverseGalois.CFT.fg_sUnits`: the units for a finite set of places of a number field form a
  finitely generated subgroup.
* `InverseGalois.CFT.exists_fg_forall_mul_pow`: **a single finitely generated subgroup carries,
  modulo exponent-th powers, every unit whose order is divisible by the exponent away from a
  prescribed finite set of places.**

## Tags

number field, S-unit, finitely generated, Dirichlet unit theorem, Kummer theory, class group
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### The units for a finite set of places form a finitely generated subgroup -/

/-- **The units for a finite set of places of a number field form a finitely generated
subgroup**, the group-theoretic reading of their being a finitely generated abelian group. -/
theorem fg_sUnits {K : Type*} [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K)))
    (hT : T.Finite) : (sUnits K T).FG :=
  (Group.fg_iff_subgroup_fg _).1
    (GroupFG.iff_add_fg.2 (Module.Finite.iff_addGroup_fg.1 (module_finite_sUnits T hT)))

/-! ### Carrying the everywhere divisible units in one finitely generated subgroup -/

/-- **A single finitely generated subgroup carries, modulo exponent-th powers, every unit whose
order is divisible by the exponent away from a prescribed finite set of places.**

The subgroup is the one of units for that set together with the finite set of places away from
which every finitely supported system of orders is realised: dividing the divisor of such a unit by
the exponent outside the prescribed set and realising the negative of the quotient by an element of
the field, the unit corrected by the exponent-th power of that element has no order at all outside
the two sets together. -/
theorem exists_fg_forall_mul_pow (K : Type*) [Field K] [NumberField K] (ℓ : ℕ)
    {Tz : Set (HeightOneSpectrum (𝓞 K))} (hTz : Tz.Finite) :
    ∃ H : Subgroup Kˣ, H.FG ∧ ∀ u : Kˣ,
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tz → (ℓ : ℤ) ∣ ord K v (u : K)) →
      ∃ g ∈ H, ∃ z : Kˣ, u = g * z ^ ℓ := by
  classical
  obtain ⟨T, hTfin, hTrepr⟩ := exists_finite_ord_repr K
  refine ⟨sUnits K (T ∪ Tz), fg_sUnits _ (hTfin.union hTz), fun u hu => ?_⟩
  obtain ⟨a, ha⟩ := hTrepr (fun v => if v ∈ Tz then 0 else -(ord K v (u : K)) / (ℓ : ℤ))
    ((ord_finite (K := K) (u : K)).mono fun v hv => by
      simp only [hv, neg_zero, Int.zero_ediv, ite_self])
  refine ⟨u * a ^ ℓ, fun v hv => ?_, a⁻¹, ?_⟩
  · have hvT : v ∉ T := fun h => hv (Set.mem_union_left _ h)
    have hvTz : v ∉ Tz := fun h => hv (Set.mem_union_right _ h)
    have hmul : ord K v ((u * a ^ ℓ : Kˣ) : K)
        = ord K v (u : K) + (ℓ : ℤ) * ord K v (a : K) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val,
        ord_mul v u.ne_zero (pow_ne_zero _ a.ne_zero), ord_pow v a.ne_zero]
    rw [hmul, ha v hvT, if_neg hvTz, Int.mul_ediv_cancel' ((dvd_neg).2 (hu v hvTz)),
      add_neg_cancel]
  · rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]

end InverseGalois.CFT
