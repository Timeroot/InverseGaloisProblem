import Mathlib
import InverseGalois.CFT.Global.HilbertBimul
import InverseGalois.CFT.Global.OddGenerators
import InverseGalois.CFT.Global.TwoGenerators

/-!
# Hilbert reciprocity over the rational field

The product over all places of the local Hilbert symbols of a pair of nonzero rationals is one.
This is the quadratic case of Artin reciprocity: a conic over the rationals fails to have a
rational point at an even number of places.

The proof is the classical one.  The product is bimultiplicative and blind to square factors, so
it is determined by its values on pairs drawn from `-1` and the rational primes, and every nonzero
rational is a product of such generators times a square.  On those pairs the identity is a finite
computation: for two odd primes it is quadratic reciprocity, for `-1` against an odd prime it is
the first supplementary law, for `2` against an odd prime it is the second, and the remaining
pairs involve only the real place and the dyadic one.

## Main results

* `InverseGalois.CFT.hilbertProduct_eq_one`: the product formula.
* `InverseGalois.CFT.hilbert_reciprocity`: the same statement with the product written out.
-/

namespace InverseGalois.CFT

open Local

/-- A generator of the group of square classes of the rationals: either `-1` or a rational
prime. -/
def IsHilbertGenerator (x : ℚ) : Prop := x = -1 ∨ ∃ p : ℕ, p.Prime ∧ x = (p : ℚ)

/-- A generator of the group of square classes is nonzero. -/
theorem IsHilbertGenerator.ne_zero {x : ℚ} (hx : IsHilbertGenerator x) : x ≠ 0 := by
  rcases hx with rfl | ⟨p, hp, rfl⟩
  · norm_num
  · exact Nat.cast_ne_zero.2 hp.pos.ne'

/-- **The product formula on a pair of generators.**  Every case is one of the supplementary laws
or quadratic reciprocity itself. -/
theorem hilbertProduct_generators {x y : ℚ} (hx : IsHilbertGenerator x)
    (hy : IsHilbertGenerator y) : hilbertProduct x y = 1 := by
  rcases hx with rfl | ⟨p, hp, rfl⟩
  · rcases hy with rfl | ⟨q, hq, rfl⟩
    · exact hilbertProduct_neg_one_neg_one
    · rcases eq_or_ne q 2 with rfl | hq2
      · exact_mod_cast hilbertProduct_neg_one_two
      · exact hilbertProduct_neg_one_prime hq hq2
  · rcases hy with rfl | ⟨q, hq, rfl⟩
    · rw [hilbertProduct_comm]
      rcases eq_or_ne p 2 with rfl | hp2
      · exact_mod_cast hilbertProduct_neg_one_two
      · exact hilbertProduct_neg_one_prime hp hp2
    · rcases eq_or_ne p 2 with rfl | hp2
      · rcases eq_or_ne q 2 with rfl | hq2
        · exact_mod_cast hilbertProduct_two_two
        · exact_mod_cast hilbertProduct_two_prime hq hq2
      · rcases eq_or_ne q 2 with rfl | hq2
        · rw [hilbertProduct_comm]
          exact_mod_cast hilbertProduct_two_prime hp hp2
        · rcases eq_or_ne p q with rfl | hpq
          · exact hilbertProduct_prime_self hp hp2
          · exact hilbertProduct_prime_prime hp hq hp2 hq2 hpq

/-- **The product formula against a fixed generator**, for an arbitrary nonzero rational in the
other argument. -/
theorem hilbertProduct_generator_right {y : ℚ} (hy : IsHilbertGenerator y) {a : ℚ} (ha : a ≠ 0) :
    hilbertProduct a y = 1 := by
  have hy0 : y ≠ 0 := hy.ne_zero
  refine Rat.induction_on_prime_mul_sq (motive := fun x => hilbertProduct x y = 1) ?_ ?_ ?_ ?_ ha
  · exact hilbertProduct_one_left y
  · exact hilbertProduct_generators (Or.inl rfl) hy
  · intro p x hp hx ih
    have hp0 : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
    rw [hilbertProduct_mul_left hp0 hx hy0, ih,
      hilbertProduct_generators (Or.inr ⟨p, hp, rfl⟩) hy, mul_one]
  · intro x c hx hc ih
    rw [hilbertProduct_mul_sq_left _ _ _ hc, ih]

/-- **Hilbert reciprocity over the rational field.**  For nonzero rationals the local Hilbert
symbols are trivial at all but finitely many places and their product over all places is one. -/
theorem hilbertProduct_eq_one {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : hilbertProduct a b = 1 := by
  refine Rat.induction_on_prime_mul_sq
    (motive := fun y => ∀ x : ℚ, x ≠ 0 → hilbertProduct x y = 1) ?_ ?_ ?_ ?_ hb a ha
  · intro x _
    exact hilbertProduct_one_right x
  · intro x hx
    exact hilbertProduct_generator_right (Or.inl rfl) hx
  · intro p y hp hy ih x hx
    have hp0 : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
    rw [hilbertProduct_mul_right hx hp0 hy, ih x hx,
      hilbertProduct_generator_right (Or.inr ⟨p, hp, rfl⟩) hx, mul_one]
  · intro y c hy hc ih x hx
    rw [hilbertProduct_mul_sq_right _ _ _ hc]
    exact ih x hx

/-- **Hilbert reciprocity, with the product over all places written out.** -/
theorem hilbert_reciprocity {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol ((a : ℝ)) ((b : ℝ)) * ∏ᶠ p : Nat.Primes, hilbertSymbolAt p a b = 1 :=
  hilbertProduct_eq_one ha hb

/-- **A conic over the rationals is anisotropic at an even number of places.**  The symbol at a
place is `-1` exactly at the places where the conic has no point, and the product of the signs is
one. -/
theorem hilbertProduct_finite_eq_real {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∏ᶠ p : Nat.Primes, hilbertSymbolAt p a b) = hilbertSymbol ((a : ℝ)) ((b : ℝ)) := by
  have hR : ((a : ℝ)) ≠ 0 := by simpa using ha
  have hRb : ((b : ℝ)) ≠ 0 := by simpa using hb
  have hsq : hilbertSymbol ((a : ℝ)) ((b : ℝ)) * hilbertSymbol ((a : ℝ)) ((b : ℝ)) = 1 := by
    have := hilbertSymbol_sq ((a : ℝ)) ((b : ℝ))
    rwa [sq] at this
  have h := hilbertProduct_eq_one ha hb
  unfold hilbertProduct at h
  calc (∏ᶠ p : Nat.Primes, hilbertSymbolAt p a b)
      = hilbertSymbol ((a : ℝ)) ((b : ℝ)) *
          (hilbertSymbol ((a : ℝ)) ((b : ℝ)) * ∏ᶠ p : Nat.Primes, hilbertSymbolAt p a b) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = hilbertSymbol ((a : ℝ)) ((b : ℝ)) := by rw [h, mul_one]

end InverseGalois.CFT
