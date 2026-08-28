/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The power residue symbol attached to a character of the units

A homomorphism from the units modulo `q` to a cyclic group of order `ℓ`, written additively, turns
every natural number prime to `q` into an element of `ZMod ℓ`, and every natural number not prime to
`q` into zero.  The resulting symbol is additive on products of units, so a product of prime powers
is sent to the corresponding combination of the symbols of the primes; this is what makes the
correction of the residue degrees in the Scholz–Reichardt construction a piece of linear algebra
over the field with `ℓ` elements.

The symbol is also compatible with the two operations used to build the character of a composite
modulus out of characters of its prime factors: pulling a character back along the reduction map of
a divisor, and multiplying characters together.

## Main definitions

* `InverseGalois.CFT.powerResidueSymbol`: the symbol of a natural number.

## Main results

* `InverseGalois.CFT.powerResidueSymbol_prod_pow`: **the symbol of a product of prime powers is the
  corresponding combination of the symbols of the primes.**
* `InverseGalois.CFT.powerResidueSymbol_comp_unitsMap`: the symbol is unchanged by pulling the
  character back along the reduction map of a divisor.
* `InverseGalois.CFT.powerResidueSymbol_prod_hom`: the symbol of a product of characters is the sum
  of the symbols.

## Tags

power residue symbol, character, units, cyclic group
-/

namespace InverseGalois.CFT

open Finset

variable {ℓ q : ℕ}

/-- The symbol of a natural number attached to a character of the units modulo `q` with values in a
cyclic group of order `ℓ`: the value of the character on the class of the number when that class is
a unit, and zero otherwise. -/
noncomputable def powerResidueSymbol (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)) (n : ℕ) :
    ZMod ℓ :=
  open scoped Classical in
  if h : IsUnit ((n : ZMod q)) then Multiplicative.toAdd (κ h.unit) else 0

/-! ### Behaviour in the argument -/

variable (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ))

/-- The symbol of one is zero. -/
@[simp]
theorem powerResidueSymbol_one : powerResidueSymbol κ 1 = 0 := by
  have h : IsUnit ((1 : ℕ) : ZMod q) := by simp
  rw [powerResidueSymbol, dif_pos h, show h.unit = 1 from Units.ext (by simp),
    map_one]
  rfl

/-- The symbol is additive on products of units. -/
theorem powerResidueSymbol_mul {m n : ℕ} (hm : IsUnit ((m : ZMod q)))
    (hn : IsUnit ((n : ZMod q))) :
    powerResidueSymbol κ (m * n) = powerResidueSymbol κ m + powerResidueSymbol κ n := by
  have hmn : IsUnit ((↑(m * n) : ZMod q)) := by push_cast; exact hm.mul hn
  rw [powerResidueSymbol, powerResidueSymbol, powerResidueSymbol, dif_pos hmn, dif_pos hm,
    dif_pos hn]
  have hunit : hmn.unit = hm.unit * hn.unit := by
    apply Units.ext
    rw [hmn.unit_spec, Units.val_mul, hm.unit_spec, hn.unit_spec]
    push_cast
    ring
  rw [hunit, map_mul]
  rfl

/-- The symbol of a power of a unit is the multiple of its symbol. -/
theorem powerResidueSymbol_pow {n : ℕ} (hn : IsUnit ((n : ZMod q))) (k : ℕ) :
    powerResidueSymbol κ (n ^ k) = k • powerResidueSymbol κ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : IsUnit ((↑(n ^ k) : ZMod q)) := by push_cast; exact hn.pow k
    rw [pow_succ, powerResidueSymbol_mul κ hk hn, ih, succ_nsmul]

/-- **The symbol of a product of prime powers is the corresponding combination of the symbols of
the primes.** -/
theorem powerResidueSymbol_prod_pow {S : Finset ℕ} {e : ℕ → ℕ}
    (h : ∀ p ∈ S, IsUnit ((p : ZMod q))) :
    powerResidueSymbol κ (∏ p ∈ S, p ^ e p) = ∑ p ∈ S, e p • powerResidueSymbol κ p := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
    have hmem : ∀ p ∈ S, IsUnit ((p : ZMod q)) := fun p hp => h p (mem_insert_of_mem hp)
    have hunits : IsUnit ((↑(∏ p ∈ S, p ^ e p) : ZMod q)) := by
      push_cast
      exact Finset.prod_induction (fun p : ℕ => ((p : ZMod q)) ^ e p) IsUnit
        (fun _ _ => IsUnit.mul) isUnit_one fun p hp => (hmem p hp).pow _
    have hA : IsUnit ((↑(a ^ e a) : ZMod q)) := by
      push_cast
      exact (h a (mem_insert_self a S)).pow _
    rw [prod_insert ha, sum_insert ha, powerResidueSymbol_mul κ hA hunits, ih hmem,
      powerResidueSymbol_pow κ (h a (mem_insert_self a S))]

/-- The symbol vanishes exactly on the power residues, for a character whose kernel is the set of
power residues. -/
theorem powerResidueSymbol_eq_zero_iff
    (hκ : ∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) {n : ℕ}
    (hn : IsUnit ((n : ZMod q))) :
    powerResidueSymbol κ n = 0 ↔ (n : ZMod q) ^ ((q - 1) / ℓ) = 1 := by
  rw [powerResidueSymbol, dif_pos hn, toAdd_eq_zero, hκ, hn.unit_spec]

/-! ### Behaviour in the character -/

/-- The symbol is unchanged by pulling the character back along the reduction map of a divisor. -/
theorem powerResidueSymbol_comp_unitsMap {Q : ℕ} (h : q ∣ Q)
    {n : ℕ} (hn : IsUnit ((n : ZMod Q))) :
    powerResidueSymbol (κ.comp (ZMod.unitsMap h)) n = powerResidueSymbol κ n := by
  have hcast : (ZMod.castHom h (ZMod q)) ((n : ℕ) : ZMod Q) = ((n : ℕ) : ZMod q) := by
    simp
  have hn' : IsUnit ((n : ZMod q)) := hcast ▸ hn.map (ZMod.castHom h (ZMod q))
  rw [powerResidueSymbol, powerResidueSymbol, dif_pos hn, dif_pos hn', MonoidHom.comp_apply]
  congr 2
  apply Units.ext
  rw [hn'.unit_spec, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, hn.unit_spec, hcast]

/-- The symbol of a product of characters is the sum of the symbols. -/
theorem powerResidueSymbol_prod_hom {ι : Type*} (T : Finset ι)
    (f : ι → ((ZMod q)ˣ →* Multiplicative (ZMod ℓ))) {n : ℕ} (hn : IsUnit ((n : ZMod q))) :
    powerResidueSymbol (∏ i ∈ T, f i) n = ∑ i ∈ T, powerResidueSymbol (f i) n := by
  classical
  induction T using Finset.induction with
  | empty =>
    rw [prod_empty, sum_empty, powerResidueSymbol, dif_pos hn]
    rfl
  | insert a T ha ih =>
    rw [prod_insert ha, sum_insert ha, ← ih]
    rw [powerResidueSymbol, powerResidueSymbol, powerResidueSymbol, dif_pos hn, dif_pos hn,
      dif_pos hn, MonoidHom.mul_apply]
    rfl

/-- The symbol of a power of a character is the multiple of its symbol. -/
theorem powerResidueSymbol_pow_hom (k : ℕ) {n : ℕ} (hn : IsUnit ((n : ZMod q))) :
    powerResidueSymbol (κ ^ k) n = k • powerResidueSymbol κ n := by
  rw [powerResidueSymbol, powerResidueSymbol, dif_pos hn, dif_pos hn, MonoidHom.pow_apply]
  rfl

end InverseGalois.CFT
