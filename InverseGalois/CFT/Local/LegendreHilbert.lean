import Mathlib
import InverseGalois.CFT.Local.PadicHilbert
import InverseGalois.CFT.Local.RamifiedNormForm

/-!
# The Hilbert symbol of two integers over `ℚ_[p]`, as a Legendre symbol

Fix an odd prime `p`.  The computations of `PadicHilbert.lean` and `RamifiedNormForm.lean` give
the Hilbert symbol of any two nonzero `p`-adic numbers once each is written as a power of the
uniformiser times a unit of `ℤ_[p]`.  This file specialises that dictionary to arguments which are
*rational integers*, where the unit part is an integer prime to `p` and the quadratic character of
its residue is the Legendre symbol.

The bridge is elementary: an integer `m` is a unit of `ℤ_[p]` exactly when `p ∤ m`, because the
residue map `PadicInt.toZMod` sends `m` to `m` in `ZMod p` and detects units.  Feeding this into
`hilbertSymbol_ramified_eq` turns every symbol `⟨p ^ α * m, p ^ β * n⟩` with `m` and `n` prime to
`p` into a product of Legendre symbols; only the parities of `α` and `β` matter, since an even
power of `p` may be absorbed into a square.

## Main results

* `InverseGalois.CFT.Local.toZMod_intCast`,
  `InverseGalois.CFT.Local.isUnit_intCast_of_not_dvd`: an integer prime to `p` is a unit of
  `ℤ_[p]`, with the expected residue.
* `InverseGalois.CFT.Local.legendreSym_eq_quadraticChar_toZMod`: the Legendre symbol of an
  integer is the quadratic character of its `p`-adic residue.
* `InverseGalois.CFT.Local.legendreSym_sq`: the Legendre symbol of an integer prime to `p`
  squares to one.
* `InverseGalois.CFT.Local.hilbertSymbol_intCast_intCast`: two integers prime to an odd `p` have
  Hilbert symbol `1`.
* `InverseGalois.CFT.Local.hilbertSymbol_p_intCast`,
  `InverseGalois.CFT.Local.hilbertSymbol_intCast_p`: the uniformiser against an integer prime to
  `p` is the Legendre symbol of that integer.
* `InverseGalois.CFT.Local.hilbertSymbol_p_p`: the uniformiser against itself is the Legendre
  symbol of `-1`.
* `InverseGalois.CFT.Local.hilbertSymbol_p_mul_intCast`,
  `InverseGalois.CFT.Local.hilbertSymbol_p_mul_p_mul`: the two mixed cases with a factor `p`.
* `InverseGalois.CFT.Local.hilbertSymbol_pow_p_mod_left`,
  `InverseGalois.CFT.Local.hilbertSymbol_pow_p_mod_right`: only the parity of the power of the
  uniformiser matters.
* `InverseGalois.CFT.Local.hilbertSymbol_intCast_general`: the general formula
  `⟨p ^ α * m, p ^ β * n⟩ = (-1 / p) ^ (α * β) * (m / p) ^ β * (n / p) ^ α`.
-/

namespace InverseGalois.CFT.Local

variable {p : ℕ} [Fact p.Prime]

/-- The residue mod `p` of an integer viewed in `ℤ_[p]` is its residue mod `p` in `ZMod p`: the
residue map is a ring homomorphism, so it commutes with the integer casts. -/
theorem toZMod_intCast (m : ℤ) : PadicInt.toZMod ((m : ℤ_[p])) = (m : ZMod p) :=
  map_intCast _ m

/-- **An integer prime to `p` is a unit of `ℤ_[p]`.**  Its residue in `ZMod p` is nonzero, and
the residue map detects units. -/
theorem isUnit_intCast_of_not_dvd {m : ℤ} (h : ¬ (p : ℤ) ∣ m) : IsUnit ((m : ℤ_[p])) := by
  refine toZMod_ne_zero_iff_isUnit.mp ?_
  rw [toZMod_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact h

/-- The Legendre symbol of an integer is the quadratic character of its `p`-adic residue. -/
theorem legendreSym_eq_quadraticChar_toZMod (m : ℤ) :
    legendreSym p m = quadraticChar (ZMod p) (PadicInt.toZMod ((m : ℤ_[p]))) := by
  rw [toZMod_intCast, legendreSym]

/-- The Legendre symbol of an integer prime to `p` is a square root of one. -/
theorem legendreSym_sq {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) : legendreSym p m ^ 2 = 1 := by
  rw [legendreSym]
  exact quadraticChar_sq_one (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])

/-- An integer square root of one raised to an even power is one. -/
theorem pow_eq_one_of_sq_eq_one_of_even {s : ℤ} (hs : s ^ 2 = 1) {k : ℕ} (hk : k % 2 = 0) :
    s ^ k = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  rw [pow_mul, hs, one_pow]

/-- An integer square root of one raised to an odd power is itself. -/
theorem pow_eq_self_of_sq_eq_one_of_odd {s : ℤ} (hs : s ^ 2 = 1) {k : ℕ} (hk : k % 2 = 1) :
    s ^ k = s := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  rw [pow_add, pow_mul, hs, one_pow, one_mul, pow_one]

/-- **Two integers prime to an odd prime `p` have Hilbert symbol one** over `ℚ_[p]`: both are
units of `ℤ_[p]`. -/
theorem hilbertSymbol_intCast_intCast (hp : p ≠ 2) {m n : ℤ}
    (hm : ¬ (p : ℤ) ∣ m) (hn : ¬ (p : ℤ) ∣ n) :
    hilbertSymbol ((m : ℚ_[p])) ((n : ℚ_[p])) = 1 := by
  have h := hilbertSymbol_unit_unit hp (isUnit_intCast_of_not_dvd hm)
    (isUnit_intCast_of_not_dvd hn)
  rwa [PadicInt.coe_intCast, PadicInt.coe_intCast] at h

/-- **An integer prime to `p` against the uniformiser is its Legendre symbol**, for `p` odd:
read the symbol `⟨p ^ 0 * n, p * 1⟩` through the ramified computation, whose parity correction is
absent because the exponent is even. -/
theorem hilbertSymbol_intCast_p (hp : p ≠ 2) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    hilbertSymbol ((n : ℚ_[p])) ((p : ℚ_[p])) = legendreSym p n := by
  have h := hilbertSymbol_ramified_eq (p := p) hp (w := 1) isUnit_one (n := 0)
    (u := (n : ℤ_[p])) (isUnit_intCast_of_not_dvd hn)
  rw [zpow_zero, one_mul, PadicInt.coe_intCast, PadicInt.coe_one, mul_one,
    if_pos (Even.zero (α := ℤ)), mul_one] at h
  rw [h, legendreSym_eq_quadraticChar_toZMod]

/-- **The uniformiser against an integer prime to `p` is its Legendre symbol**, for `p` odd. -/
theorem hilbertSymbol_p_intCast (hp : p ≠ 2) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    hilbertSymbol ((p : ℚ_[p])) ((n : ℚ_[p])) = legendreSym p n := by
  rw [hilbertSymbol_comm]
  exact hilbertSymbol_intCast_p hp hn

/-- **The uniformiser against itself is the Legendre symbol of `-1`**, for `p` odd: the symbol
`⟨p ^ 1 * 1, p * 1⟩` has odd exponent, so the whole answer is the parity correction. -/
theorem hilbertSymbol_p_p (hp : p ≠ 2) :
    hilbertSymbol ((p : ℚ_[p])) ((p : ℚ_[p])) = legendreSym p (-1) := by
  have h := hilbertSymbol_ramified_eq (p := p) hp (w := 1) isUnit_one (n := 1)
    (u := 1) isUnit_one
  rw [zpow_one, PadicInt.coe_one, mul_one, map_one, MulChar.map_one, one_mul,
    if_neg (by decide : ¬ Even (1 : ℤ))] at h
  rw [h, legendreSym]
  norm_num

/-- **The uniformiser times an integer prime to `p`, against another such integer**, for `p` odd:
the answer is the Legendre symbol of the second integer.  Commute the arguments and read the
symbol `⟨p ^ 0 * n, p * m⟩`, whose exponent is even. -/
theorem hilbertSymbol_p_mul_intCast (hp : p ≠ 2) {m n : ℤ}
    (hm : ¬ (p : ℤ) ∣ m) (hn : ¬ (p : ℤ) ∣ n) :
    hilbertSymbol (((p : ℤ) * m : ℤ) : ℚ_[p]) ((n : ℚ_[p])) = legendreSym p n := by
  have h := hilbertSymbol_ramified_eq (p := p) hp (w := (m : ℤ_[p]))
    (isUnit_intCast_of_not_dvd hm) (n := 0) (u := (n : ℤ_[p]))
    (isUnit_intCast_of_not_dvd hn)
  rw [zpow_zero, one_mul, PadicInt.coe_intCast, PadicInt.coe_intCast,
    if_pos (Even.zero (α := ℤ)), mul_one] at h
  rw [hilbertSymbol_comm,
    show (((p : ℤ) * m : ℤ) : ℚ_[p]) = (p : ℚ_[p]) * (m : ℚ_[p]) by push_cast; ring, h,
    legendreSym_eq_quadraticChar_toZMod]

/-- **Two multiples of the uniformiser by integers prime to `p`**, for `p` odd: the symbol
`⟨p ^ 1 * m, p * n⟩` has odd exponent, so it is the Legendre symbol of `m` times that of `-n`, and
the latter splits off the Legendre symbol of `-1`. -/
theorem hilbertSymbol_p_mul_p_mul (hp : p ≠ 2) {m n : ℤ}
    (hm : ¬ (p : ℤ) ∣ m) (hn : ¬ (p : ℤ) ∣ n) :
    hilbertSymbol (((p : ℤ) * m : ℤ) : ℚ_[p]) (((p : ℤ) * n : ℤ) : ℚ_[p])
      = legendreSym p (-1) * legendreSym p m * legendreSym p n := by
  have h := hilbertSymbol_ramified_eq (p := p) hp (w := (n : ℤ_[p]))
    (isUnit_intCast_of_not_dvd hn) (n := 1) (u := (m : ℤ_[p]))
    (isUnit_intCast_of_not_dvd hm)
  rw [zpow_one, PadicInt.coe_intCast, PadicInt.coe_intCast,
    if_neg (by decide : ¬ Even (1 : ℤ))] at h
  rw [show (((p : ℤ) * m : ℤ) : ℚ_[p]) = (p : ℚ_[p]) * (m : ℚ_[p]) by push_cast; ring,
    show (((p : ℤ) * n : ℤ) : ℚ_[p]) = (p : ℚ_[p]) * (n : ℚ_[p]) by push_cast; ring, h]
  have h2 : quadraticChar (ZMod p) (PadicInt.toZMod (-(n : ℤ_[p])))
      = legendreSym p (-1) * legendreSym p n := by
    rw [← legendreSym.mul,
      show (-(n : ℤ_[p])) = (((-1 * n : ℤ)) : ℤ_[p]) by push_cast; ring,
      ← legendreSym_eq_quadraticChar_toZMod]
  rw [h2, ← legendreSym_eq_quadraticChar_toZMod]
  ring

/-- **Only the parity of a power of the uniformiser matters, on the right**: splitting
`p ^ γ = p ^ (γ % 2) * (p ^ (γ / 2)) ^ 2` removes a square factor, which the Hilbert symbol does
not see. -/
theorem hilbertSymbol_pow_p_mod_right (a b : ℚ_[p]) (γ : ℕ) :
    hilbertSymbol a ((p : ℚ_[p]) ^ γ * b) = hilbertSymbol a ((p : ℚ_[p]) ^ (γ % 2) * b) := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  have hsplit : (p : ℚ_[p]) ^ γ * b
      = ((p : ℚ_[p]) ^ (γ % 2) * b) * ((p : ℚ_[p]) ^ (γ / 2)) ^ 2 := by
    rw [← pow_mul, mul_right_comm, ← pow_add, Nat.mod_add_div']
  rw [hsplit, hilbertSymbol_mul_sq_right _ _ _ (pow_ne_zero _ hp0)]

/-- **Only the parity of a power of the uniformiser matters, on the left.** -/
theorem hilbertSymbol_pow_p_mod_left (a b : ℚ_[p]) (γ : ℕ) :
    hilbertSymbol ((p : ℚ_[p]) ^ γ * a) b = hilbertSymbol ((p : ℚ_[p]) ^ (γ % 2) * a) b := by
  rw [hilbertSymbol_comm, hilbertSymbol_pow_p_mod_right, hilbertSymbol_comm]

/-- **The Hilbert symbol of two integers in factored form**, for `p` odd: for `m` and `n` prime
to `p`,
`⟨p ^ α * m, p ^ β * n⟩ = (-1 / p) ^ (α * β) * (m / p) ^ β * (n / p) ^ α`,
where `(· / p)` denotes the Legendre symbol.  Discarding the even parts of the two powers of the
uniformiser leaves four cases, each one of the computations above; on the right-hand side the same
reduction is the statement that a square root of one only depends on the parity of its exponent. -/
theorem hilbertSymbol_intCast_general (hp : p ≠ 2) {α β : ℕ} {m n : ℤ}
    (hm : ¬ (p : ℤ) ∣ m) (hn : ¬ (p : ℤ) ∣ n) :
    hilbertSymbol ((((p : ℤ) ^ α * m : ℤ)) : ℚ_[p]) ((((p : ℤ) ^ β * n : ℤ)) : ℚ_[p])
      = legendreSym p (-1) ^ (α * β) * legendreSym p m ^ β * legendreSym p n ^ α := by
  have hm2 : legendreSym p m ^ 2 = 1 := legendreSym_sq hm
  have hn2 : legendreSym p n ^ 2 = 1 := legendreSym_sq hn
  have hneg2 : legendreSym p (-1 : ℤ) ^ 2 = 1 := legendreSym_sq (p := p) (by
    intro hd
    have := Int.le_of_dvd (by norm_num) ((dvd_neg).mp hd)
    have hp2 : 2 ≤ (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).two_le
    omega)
  have hcm : ((((p : ℤ) ^ α * m : ℤ)) : ℚ_[p]) = (p : ℚ_[p]) ^ α * (m : ℚ_[p]) := by
    push_cast; ring
  have hcn : ((((p : ℤ) ^ β * n : ℤ)) : ℚ_[p]) = (p : ℚ_[p]) ^ β * (n : ℚ_[p]) := by
    push_cast; ring
  rw [hcm, hcn, hilbertSymbol_pow_p_mod_left, hilbertSymbol_pow_p_mod_right]
  have e1 : (p : ℚ_[p]) ^ (1 : ℕ) * (m : ℚ_[p]) = (((p : ℤ) * m : ℤ) : ℚ_[p]) := by
    push_cast; ring
  have e2 : (p : ℚ_[p]) ^ (1 : ℕ) * (n : ℚ_[p]) = (((p : ℤ) * n : ℤ) : ℚ_[p]) := by
    push_cast; ring
  rcases Nat.mod_two_eq_zero_or_one α with hα | hα <;>
    rcases Nat.mod_two_eq_zero_or_one β with hβ | hβ
  · have hab : α * β % 2 = 0 := by rw [Nat.mul_mod, hα, Nat.zero_mul, Nat.zero_mod]
    rw [hα, hβ, pow_zero, one_mul, one_mul,
      hilbertSymbol_intCast_intCast hp hm hn,
      pow_eq_one_of_sq_eq_one_of_even hneg2 hab,
      pow_eq_one_of_sq_eq_one_of_even hm2 hβ,
      pow_eq_one_of_sq_eq_one_of_even hn2 hα]
    norm_num
  · have hab : α * β % 2 = 0 := by rw [Nat.mul_mod, hα, Nat.zero_mul, Nat.zero_mod]
    rw [hα, hβ, pow_zero, one_mul, e2, hilbertSymbol_comm,
      hilbertSymbol_p_mul_intCast hp hn hm,
      pow_eq_one_of_sq_eq_one_of_even hneg2 hab,
      pow_eq_self_of_sq_eq_one_of_odd hm2 hβ,
      pow_eq_one_of_sq_eq_one_of_even hn2 hα]
    norm_num
  · have hab : α * β % 2 = 0 := by rw [Nat.mul_mod, hβ, Nat.mul_zero, Nat.zero_mod]
    rw [hα, hβ, pow_zero, one_mul, e1, hilbertSymbol_p_mul_intCast hp hm hn,
      pow_eq_one_of_sq_eq_one_of_even hneg2 hab,
      pow_eq_one_of_sq_eq_one_of_even hm2 hβ,
      pow_eq_self_of_sq_eq_one_of_odd hn2 hα]
    norm_num
  · have hab : α * β % 2 = 1 := by rw [Nat.mul_mod, hα, hβ]
    rw [hα, hβ, e1, e2, hilbertSymbol_p_mul_p_mul hp hm hn,
      pow_eq_self_of_sq_eq_one_of_odd hneg2 hab,
      pow_eq_self_of_sq_eq_one_of_odd hm2 hβ,
      pow_eq_self_of_sq_eq_one_of_odd hn2 hα]

end InverseGalois.CFT.Local
