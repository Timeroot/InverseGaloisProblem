/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Ord

/-!
# Independence of radicals detected by valuations

Adjoining `n`-th roots of elements `a i` of a field enlarges the degree by the full factor `nᵏ`
precisely when the classes of the `a i` are independent in `Kˣ / (Kˣ)ⁿ`, that is, when a product
`∏ (a i) ^ (e i)` can only be an `n`-th power if every exponent `e i` is divisible by `n`.  The
practical way to certify this is to exhibit, for each index `i`, valuations that vanish on every
other `a j` and whose values on `a i` are collectively coprime to `n`: the valuation of an `n`-th
power is divisible by `n`, so each such valuation forces `n ∣ e i * v (a i)`, and coprimality then
forces `n ∣ e i`.

A single valuation is not enough — with `n = 6` a valuation taking the value `2` only gives
`6 ∣ 2 * e i`, which `e i = 3` satisfies — so the statements below take a whole finite family of
valuations per index and ask for coprimality with their greatest common divisor.

Nothing here is about fields: the statements are about an abstract commutative group `G` (in the
application, the unit group of a field) and additive `ℤ`-valued functions on it.  A valuation is
presented as a bare function together with its additivity, which is the form in which any of the
several valuation APIs can supply it.

## Main results

* `Rigidity.RET.Wreath.dvd_mul_val_of_prod_zpow_eq_pow` — one valuation gives `n ∣ e i * v (a i)`.
* `Rigidity.RET.Wreath.dvd_of_forall_dvd_mul` — the arithmetic combination step.
* `Rigidity.RET.Wreath.dvd_of_prod_zpow_eq_pow` — the two together: a family of valuations private
  to the index `i`, with values coprime to `n`, forces `n ∣ e i`.
* `Rigidity.RET.Wreath.dvd_of_pow_eq_prod_zpow` — the same for a family of nonzero elements of a
  field, in the shape of the independence hypothesis of a Kummer setup.
* `Rigidity.RET.Wreath.dvd_of_pow_eq_prod_zpow_ord` — the specialization to the orders at the
  height-one primes of a Dedekind domain, which is the form in which a function field supplies its
  valuations.
-/

namespace Rigidity.RET.Wreath

section Valuation

variable {G : Type*} [CommGroup G] (V : G → ℤ) (hV : ∀ x y, V (x * y) = V x + V y)

include hV

theorem val_one : V 1 = 0 := by
  have h := hV 1 1
  rw [mul_one] at h
  omega

theorem val_inv (x : G) : V x⁻¹ = -V x := by
  have h := hV x x⁻¹
  rw [mul_inv_cancel, val_one V hV] at h
  omega

theorem val_pow (x : G) (m : ℕ) : V (x ^ m) = m * V x := by
  induction m with
  | zero => simpa using val_one V hV
  | succ k ih =>
    rw [pow_succ, hV, ih]
    push_cast
    ring

theorem val_zpow (x : G) (e : ℤ) : V (x ^ e) = e * V x := by
  cases e with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast, val_pow V hV]
  | negSucc m =>
    rw [zpow_negSucc, val_inv V hV, val_pow V hV, Int.negSucc_eq]
    push_cast
    ring

theorem val_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → G) :
    V (∏ j ∈ s, f j) = ∑ j ∈ s, V (f j) := by
  induction s using Finset.induction with
  | empty => simpa using val_one V hV
  | @insert a s ha ih => rw [Finset.prod_insert ha, hV, ih, Finset.sum_insert ha]

/-- **A valuation private to one factor bounds that factor's exponent.**  If a product of powers is
an `n`-th power and the valuation `V` vanishes on every factor except the one at `i`, then the
whole valuation of the product is `e i * V (a i)`, and it is divisible by `n` because it is `n`
times the valuation of an `n`-th root. -/
theorem dvd_mul_val_of_prod_zpow_eq_pow {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {a : ι → G} {e : ι → ℤ} {b : G} (hb : ∏ j, a j ^ e j = b ^ n) {i : ι}
    (hkill : ∀ j, j ≠ i → V (a j) = 0) :
    (n : ℤ) ∣ e i * V (a i) := by
  have h1 : V (∏ j, a j ^ e j) = e i * V (a i) := by
    rw [val_prod V hV, Finset.sum_eq_single i]
    · exact val_zpow V hV _ _
    · intro j _ hj
      rw [val_zpow V hV, hkill j hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hb, val_pow V hV] at h1
  exact ⟨V b, h1.symm⟩

end Valuation

/-- **Combining several divisibility constraints on the same integer.**  Knowing `n ∣ e * m i` for
every `i` gives `n ∣ e * gcd m`, and if `n` is coprime to that greatest common divisor then `n`
divides `e` itself. -/
theorem dvd_of_forall_dvd_mul {ι : Type*} {n : ℕ} {e : ℤ} (s : Finset ι) (m : ι → ℤ)
    (hdvd : ∀ i ∈ s, (n : ℤ) ∣ e * m i) (hcop : IsCoprime (n : ℤ) (s.gcd m)) :
    (n : ℤ) ∣ e := by
  have h1 : (n : ℤ) ∣ s.gcd fun i ↦ e * m i := Finset.dvd_gcd hdvd
  rw [Finset.gcd_mul_left] at h1
  exact (hcop.dvd_of_dvd_mul_right h1).trans (normalize_associated e).dvd

/-- **Independence of radicals from private valuations.**  If a product of powers of the `a j` is an
`n`-th power, and there is a finite family of valuations that all vanish on `a j` for `j ≠ i` while
their values on `a i` have greatest common divisor coprime to `n`, then `n` divides the exponent of
`a i`.  Applied to every index in turn, this is exactly the statement that the classes of the `a j`
are independent in `G / Gⁿ`. -/
theorem dvd_of_prod_zpow_eq_pow {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} {n : ℕ} {a : ι → G} {e : ι → ℤ} {b : G} (hb : ∏ j, a j ^ e j = b ^ n) (i : ι)
    (s : Finset κ) (V : κ → G → ℤ) (hV : ∀ k ∈ s, ∀ x y, V k (x * y) = V k x + V k y)
    (hkill : ∀ k ∈ s, ∀ j, j ≠ i → V k (a j) = 0)
    (hcop : IsCoprime (n : ℤ) (s.gcd fun k ↦ V k (a i))) :
    (n : ℤ) ∣ e i :=
  dvd_of_forall_dvd_mul s _
    (fun k hk ↦ dvd_mul_val_of_prod_zpow_eq_pow (V k) (hV k hk) hb (hkill k hk)) hcop

/-- **Independence of radicals in a field, from private valuations.**  This is the previous
statement transported to the unit group of a field, in the shape in which the independence
hypothesis of a Kummer setup is stated: the valuations are only required to be additive on nonzero
elements, which is how every valuation of a field presents itself. -/
theorem dvd_of_pow_eq_prod_zpow {E : Type*} [Field E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} {n : ℕ} {g : ι → E} (hg : ∀ j, g j ≠ 0) {m : ι → ℤ} {y : E} (hy : y ≠ 0)
    (hpow : y ^ n = ∏ j, g j ^ m j) (i : ι) (s : Finset κ) (V : κ → E → ℤ)
    (hV : ∀ k ∈ s, ∀ x z : E, x ≠ 0 → z ≠ 0 → V k (x * z) = V k x + V k z)
    (hkill : ∀ k ∈ s, ∀ j, j ≠ i → V k (g j) = 0)
    (hcop : IsCoprime (n : ℤ) (s.gcd fun k ↦ V k (g i))) :
    (n : ℤ) ∣ m i := by
  refine dvd_of_prod_zpow_eq_pow (a := fun j ↦ Units.mk0 (g j) (hg j)) (e := m)
    (b := Units.mk0 y hy) ?_ i s (fun k u ↦ V k (u : E)) ?_ hkill hcop
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val,
      show ((∏ j, Units.mk0 (g j) (hg j) ^ m j : Eˣ) : E)
        = ∏ j, ((Units.mk0 (g j) (hg j) : Eˣ) : E) ^ m j from by simp]
    simpa using hpow.symm
  · exact fun k hk x z ↦ hV k hk _ _ x.ne_zero z.ne_zero

/-- **Independence of radicals in a function field, certified by private places.**  For each index
`i` one exhibits a finite set of height-one primes at which every other `g j` is a unit and whose
orders on `g i` have greatest common divisor coprime to `n`; the classes of the `g j` are then
independent modulo `n`-th powers. -/
theorem dvd_of_pow_eq_prod_zpow_ord {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {g : ι → K} (hg : ∀ j, g j ≠ 0) {m : ι → ℤ} {y : K} (hy : y ≠ 0)
    (hpow : y ^ n = ∏ j, g j ^ m j) (i : ι) (s : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (hkill : ∀ v ∈ s, ∀ j, j ≠ i → ord K v (g j) = 0)
    (hcop : IsCoprime (n : ℤ) (s.gcd fun v ↦ ord K v (g i))) :
    (n : ℤ) ∣ m i :=
  dvd_of_pow_eq_prod_zpow hg hy hpow i s (fun v x ↦ ord K v x)
    (fun v _ _ _ hx hz ↦ ord_mul v hx hz) hkill hcop

end Rigidity.RET.Wreath
