/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.PCentralCoord

/-!
# Recognizing an elementary abelian group

An abelian group of exponent dividing a prime `p` is a vector space over the field with `p`
elements, and a finite-dimensional vector space is determined up to isomorphism by its dimension,
which the order of the group reads off.  So a finite abelian group of exponent dividing `p` and
order `p ^ d` is *the* elementary abelian group of rank `d`, and therefore also the free object of
rank `d` and `p`-class one.

The multiplicative form takes commutativity as a hypothesis rather than as an instance, because the
groups it is applied to — Galois groups of multiquadratic extensions — carry a `Group` instance
already.

## Main results

* `InverseGalois.exists_addEquiv_of_forall_nsmul_eq_zero`: a finite abelian group killed by a prime
  and of order a power of it is a coordinate space over the field with that many elements.
* `InverseGalois.exists_mulEquiv_multiplicative_of_pow_eq_one`: **a finite abelian group of
  exponent dividing `p` and order `p ^ d` is the elementary abelian group of rank `d`.**
* `InverseGalois.exists_mulEquiv_freePClass_one`: the same group is the free object of rank `d` and
  `p`-class one.

## Tags

elementary abelian group, `p`-group, free object
-/

namespace InverseGalois

open Multiplicative

/-- **A finite abelian group killed by a prime and of order a power of it is a coordinate space
over the field with that many elements.**  The exponent makes it a vector space, its order reads
off the dimension, and a basis is a coordinate system. -/
theorem exists_addEquiv_of_forall_nsmul_eq_zero {p d : ℕ} [Fact p.Prime] {A : Type*}
    [AddCommGroup A] [Finite A] (hexp : ∀ x : A, p • x = 0) (hcard : Nat.card A = p ^ d) :
    Nonempty (A ≃+ (Fin d → ZMod p)) := by
  haveI : Module (ZMod p) A := AddCommGroup.zmodModule hexp
  have hpow : Nat.card A = Nat.card (ZMod p) ^ Module.finrank (ZMod p) A :=
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := A)
  have hfr : Module.finrank (ZMod p) A = d := by
    rw [Nat.card_zmod] at hpow
    refine Nat.pow_right_injective (Fact.out : p.Prime).two_le ?_
    show p ^ Module.finrank (ZMod p) A = p ^ d
    rw [← hpow, ← hcard]
  exact ⟨(Module.finBasisOfFinrankEq (ZMod p) A hfr).equivFun.toAddEquiv⟩

variable {p d : ℕ} {G : Type*} [Group G]

/-- **A finite abelian group of exponent dividing a prime and of order a power of it is the
elementary abelian group of the corresponding rank.** -/
theorem exists_mulEquiv_multiplicative_of_pow_eq_one [Fact p.Prime] [Finite G]
    (hcomm : ∀ a b : G, a * b = b * a) (hexp : ∀ g : G, g ^ p = 1) (hcard : Nat.card G = p ^ d) :
    Nonempty (G ≃* Multiplicative (Fin d → ZMod p)) := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  haveI : Finite (Additive G) := inferInstanceAs (Finite G)
  have hsmul : ∀ x : Additive G, p • x = 0 := by
    intro x
    have hx : p • x = Additive.ofMul (Additive.toMul x ^ p) := (ofMul_pow p (Additive.toMul x)).symm
    rw [hx, hexp, ofMul_one]
  obtain ⟨e⟩ := exists_addEquiv_of_forall_nsmul_eq_zero (A := Additive G) hsmul hcard
  exact ⟨AddEquiv.toMultiplicativeRight e⟩

/-- **A finite abelian group of exponent dividing a prime and of order a power of it is the free
object of the corresponding rank and `p`-class one.** -/
theorem exists_mulEquiv_freePClass_one [Fact p.Prime] [Finite G]
    (hcomm : ∀ a b : G, a * b = b * a) (hexp : ∀ g : G, g ^ p = 1) (hcard : Nat.card G = p ^ d) :
    Nonempty (G ≃* FreePClass p d 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨e⟩ := exists_mulEquiv_multiplicative_of_pow_eq_one hcomm hexp hcard
  exact ⟨e.trans (FreePClass.coordEquiv p d).symm⟩

end InverseGalois
