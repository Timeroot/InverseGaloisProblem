import Mathlib
import InverseGalois.CFT.Local.PadicHilbert
import InverseGalois.CFT.Global.HilbertPlaces

/-!
# Unit ternary forms at odd places, and the places where a rational is not a unit

Two facts are collected here, both about the behaviour of a rational quadratic form at the finite
places where nothing is ramified.

At an odd prime the Hilbert symbol of two `p`-adic units is one, so the conic they cut out has a
point.  A diagonal ternary form `u₁ X ^ 2 + u₂ Y ^ 2 + u₃ Z ^ 2` whose three coefficients are
units is a scalar multiple of such a conic: dividing by `u₃` turns it into the Hilbert conic of
`-u₁ / u₃` and `-u₂ / u₃`, whose two arguments are again units.  Hence a diagonal ternary form in
units is isotropic at every odd place, with no further hypothesis on the coefficients.

For a fixed nonzero rational `a`, the places at which `a` fails to be a unit are the primes
dividing its numerator or its denominator.  Both are nonzero integers, so only finitely many
primes are involved.

## Main results

* `InverseGalois.CFT.isotropic_ternary_of_norm_one`: at an odd prime, a diagonal ternary form
  over `ℚ_[p]` whose three coefficients have absolute value one represents zero nontrivially.
* `InverseGalois.CFT.finite_setOf_norm_ne_one`: a nonzero rational has absolute value one at all
  but finitely many finite places.
-/

namespace InverseGalois.CFT

open Local

/-- **A diagonal ternary form in `p`-adic units is isotropic at an odd place.**  Dividing the
equation by the last coefficient presents the form as the Hilbert conic of `-u₁ / u₃` and
`-u₂ / u₃`; those two quotients again have absolute value one, so their Hilbert symbol is one at
an odd finite place and the conic carries a point other than the origin. -/
theorem isotropic_ternary_of_norm_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {u₁ u₂ u₃ : ℚ_[p]} (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1) (h₃ : ‖u₃‖ = 1) :
    ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ u₁ * x ^ 2 + u₂ * y ^ 2 + u₃ * z ^ 2 = 0 := by
  have hu3 : u₃ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h₃
    exact zero_ne_one h₃
  have hA : ‖(-u₁ / u₃)‖ = 1 := by rw [norm_div, norm_neg, h₁, h₃, div_one]
  have hB : ‖(-u₂ / u₃)‖ = 1 := by rw [norm_div, norm_neg, h₂, h₃, div_one]
  obtain ⟨x, y, z, hne, hxyz⟩ :=
    hilbertSymbol_eq_one_iff.mp (hilbertSymbol_eq_one_of_norm_eq_one hp hA hB)
  refine ⟨x, y, z, hne, ?_⟩
  field_simp at hxyz
  linear_combination hxyz

/-- A rational prime to `p` in both numerator and denominator has `p`-adic absolute value one:
writing it as the quotient of its numerator by its denominator, the `p`-adic norm is
multiplicative and both integers are units. -/
private theorem norm_ratCast_eq_one {p : ℕ} [Fact p.Prime] {a : ℚ}
    (hn : ¬ (p : ℤ) ∣ a.num) (hd : ¬ (p : ℕ) ∣ a.den) : ‖((a : ℚ_[p]))‖ = 1 := by
  have h : padicNorm p a = 1 := by
    conv_lhs => rw [← Rat.num_div_den a]
    rw [padicNorm.div, padicNorm.int_eq_one_iff a.num |>.mpr hn,
      show ((a.den : ℚ)) = ((a.den : ℕ) : ℚ) from rfl,
      padicNorm.nat_eq_one_iff a.den |>.mpr hd]
    norm_num
  rw [Padic.eq_padicNorm, h]
  norm_num

/-- **A nonzero rational is a unit at all but finitely many finite places.**  A place at which the
absolute value is not one divides the numerator or the denominator, and each of those two nonzero
integers has only finitely many prime divisors. -/
theorem finite_setOf_norm_ne_one {a : ℚ} (ha : a ≠ 0) :
    {p : Nat.Primes | ‖((a : ℚ_[(p : ℕ)]))‖ ≠ 1}.Finite := by
  have hnum : a.num ≠ 0 := Rat.num_ne_zero.mpr ha
  have hden : ((a.den : ℤ)) ≠ 0 := by exact_mod_cast a.den_nz
  refine Set.Finite.subset (Set.Finite.union (finite_setOf_prime_dvd hnum)
    (finite_setOf_prime_dvd hden)) ?_
  intro p hp
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
  exact hp (norm_ratCast_eq_one hcon.1 (by exact_mod_cast hcon.2))

end InverseGalois.CFT
