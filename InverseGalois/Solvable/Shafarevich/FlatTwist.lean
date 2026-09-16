/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.TwistAction
import InverseGalois.Solvable.Shafarevich.KummerTensor

/-!
# The twist of an action by a character, and the invariance it buys

The equivariance the Kummer assembly asks of a tensor is not the invariance of the tensor for the
diagonal action of the group of the level: the coefficient has to be carried by the exponent to
which the automorphism raises the roots of unity as well.  That difference is a **twist**, and a
twist is undone by changing the action on the coefficient rather than the tensor.

If the target is killed by the exponent then the power of an element by a residue modulo the
exponent is well defined, so an action of the group on the target may be twisted by any character
of the group with values in the units modulo the exponent.  Twisting by the character inverse to
the one the automorphisms act on the roots of unity by turns the equivariance asked for into plain
invariance for the diagonal action — which is exactly the object the descent through the units for
a finite set of places produces.

## Main definitions

* `InverseGalois.Shafarevich.charTwistAction` — **the twist of an action by a character modulo the
  exponent.**

## Main results

* `InverseGalois.Shafarevich.charTwistAction_pow` — the twisted action raised to the exponent the
  character inverts gives back the original action.
* `InverseGalois.Shafarevich.map_unitsAut_eq_smul` — the diagonal action on the tensor product is
  the tensor of the action on the units with the action on the coefficient.
* `InverseGalois.Shafarevich.twistTensor_eq_coeffTensor_of_smul_eq` — **a tensor invariant for the
  diagonal action has the twist the assembly asks for**, as soon as the exponent-th power of the
  action is the map the coefficient is carried by.

## Tags

Shafarevich's theorem, Kummer theory, tensor product, cyclotomic character, twist
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT TensorProduct

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

/-! ### Powers by a residue modulo the exponent -/

section Pow

variable {ℓ : ℕ} [NeZero ℓ] {M : Type*} [Monoid M] {m : M}

/-- The power of an element killed by the exponent by the residue of a natural number is the power
by that number. -/
theorem pow_val_cast (hm : m ^ ℓ = 1) (i : ℕ) : m ^ ((i : ZMod ℓ)).val = m ^ i :=
  pow_eq_pow_of_pow_eq_one hm (ZMod.natCast_rightInverse (i : ZMod ℓ))

/-- The power of an element killed by the exponent by the residue one is the element. -/
theorem pow_val_one (hm : m ^ ℓ = 1) : m ^ ((1 : ZMod ℓ)).val = m := by
  rw [show (1 : ZMod ℓ) = ((1 : ℕ) : ZMod ℓ) by rw [Nat.cast_one], pow_val_cast hm, pow_one]

/-- The power of an element killed by the exponent by a product of residues is the iterated
power. -/
theorem pow_val_mul (hm : m ^ ℓ = 1) (a b : ZMod ℓ) :
    m ^ ((a * b)).val = (m ^ a.val) ^ b.val := by
  rw [← pow_mul]
  refine pow_eq_pow_of_pow_eq_one hm ?_
  rw [Nat.cast_mul, ZMod.natCast_rightInverse a, ZMod.natCast_rightInverse b,
    ZMod.natCast_rightInverse (a * b)]

/-- The power of an element killed by the exponent by a residue, raised to a number the residue
inverts, is the element. -/
theorem pow_val_pow_eq_of_mul_eq_one (hm : m ^ ℓ = 1) {c : ZMod ℓ} {e : ℕ}
    (hce : c * (e : ZMod ℓ) = 1) : (m ^ c.val) ^ e = m := by
  rw [← pow_mul]
  refine (pow_eq_pow_of_pow_eq_one hm (j := 1) ?_).trans (pow_one m)
  rw [Nat.cast_mul, ZMod.natCast_rightInverse c, hce, Nat.cast_one]

end Pow

/-! ### The twist of an action by a character -/

section Action

variable {ℓ : ℕ} [NeZero ℓ] {G M : Type*} [Group G] [CommGroup M]
variable (hexp : ∀ m : M, m ^ ℓ = 1) (act : G → M →* M) (hone : ∀ m : M, act 1 m = m)
  (hmul : ∀ (σ τ : G) (m : M), act (σ * τ) m = act σ (act τ m)) (χ : G →* (ZMod ℓ)ˣ)

/-- **The twist of an action of a group on a module by a character modulo the exponent**: the
group acts as it did and the result is raised to the power the character names.  The power is
well defined because the exponent kills the module, and the twist is again an action because the
character is multiplicative. -/
def charTwistAction : MulDistribMulAction G M where
  smul σ m := act σ m ^ ((χ σ : ZMod ℓ)).val
  one_smul m := by
    show act 1 m ^ ((χ 1 : ZMod ℓ)).val = m
    rw [hone, _root_.map_one]
    exact pow_val_one (hexp m)
  mul_smul σ τ m := by
    show act (σ * τ) m ^ ((χ (σ * τ) : ZMod ℓ)).val
      = act σ (act τ m ^ ((χ τ : ZMod ℓ)).val) ^ ((χ σ : ZMod ℓ)).val
    rw [hmul, _root_.map_pow, ← pow_val_mul (hexp (act σ (act τ m))), _root_.map_mul,
      Units.val_mul, mul_comm ((χ σ : (ZMod ℓ)ˣ) : ZMod ℓ)]
  smul_one σ := by
    show act σ 1 ^ ((χ σ : ZMod ℓ)).val = 1
    rw [_root_.map_one, one_pow]
  smul_mul σ m m' := by
    show act σ (m * m') ^ ((χ σ : ZMod ℓ)).val
      = act σ m ^ ((χ σ : ZMod ℓ)).val * act σ m' ^ ((χ σ : ZMod ℓ)).val
    rw [_root_.map_mul, mul_pow]

/-- The twisted action is the action followed by the power the character names. -/
theorem charTwistAction_smul (σ : G) (m : M) :
    letI := charTwistAction hexp act hone hmul χ
    σ • m = act σ m ^ ((χ σ : ZMod ℓ)).val := rfl

/-- **The twisted action raised to a number the character inverts gives back the original
action.** -/
theorem charTwistAction_pow {σ : G} {e : ℕ} (he : ((χ σ : ZMod ℓ)) * (e : ZMod ℓ) = 1) (m : M) :
    letI := charTwistAction hexp act hone hmul χ
    (σ • m : M) ^ e = act σ m :=
  pow_val_pow_eq_of_mul_eq_one (hexp (act σ m)) he

end Action

/-! ### The invariance the twist buys -/

section Bridge

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(↥K/k) M]

/-- **The diagonal action on the tensor product of the units of the level with the coefficient is
the tensor of the two actions.** -/
theorem map_unitsAut_eq_smul (σ : Gal(↥K/k)) (t : Additive (↥K)ˣ ⊗[ℤ] Additive M) :
    TensorProduct.map (unitsAut σ).toIntLinearMap
        (MonoidHom.toAdditive (MulDistribMulAction.toMonoidHom M σ)).toIntLinearMap t
      = σ • t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]
  | tmul u v => rfl
  | add t t' ht ht' => rw [map_add, smul_add, ht, ht']

/-- **A tensor invariant for the diagonal action has the twist the assembly asks for**, as soon as
the exponent-th power of the action on the coefficient is the map the coefficient is asked to be
carried by.  This is the whole of the equivariance clause: it is bought by choosing the action on
the coefficient to be the twist of the given one by the character inverse to the cyclotomic one. -/
theorem twistTensor_eq_coeffTensor_of_smul_eq {σ : Gal(↥K/k)} {e : ℕ} {f : M →* M}
    (hf : ∀ m : M, (σ • m : M) ^ e = f m) {t : Additive (↥K)ˣ ⊗[ℤ] Additive M}
    (ht : σ • t = t) : twistTensor M σ⁻¹ e t = coeffTensor M f t :=
  twistTensor_eq_coeffTensor_of_map_eq (ast := MulDistribMulAction.toMonoidHom M σ) hf
    ((map_unitsAut_eq_smul σ t).trans ht)

end Bridge

end InverseGalois.Shafarevich
