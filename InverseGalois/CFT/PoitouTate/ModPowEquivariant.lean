/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.OrbitProduct

/-!
# A splitting carried by the action only up to an exponent-th power

The obstruction to correcting a tensor with invariant valuation to an invariant tensor is killed by
a splitting of the valuation carried by the action, and such a splitting is assembled out of one
element per orbit of places, fixed by the automorphisms fixing its own place.  **Being fixed on the
nose is more than the obstruction ever uses.**  The splitting is read only after tensoring with the
module, and the module is killed by its exponent, so an element fixed by those automorphisms only
up to an exponent-th power serves just as well: the exponent-th power it is moved by contributes a
multiple of the exponent to the tensor, which is zero there.

Two things have to be arranged for that.  The element chosen over one place of each orbit no longer
translates around the orbit unambiguously, so the family it spreads into is permuted by the action
only up to exponent-th powers, and the homomorphism the family extends to is carried by the action
only up to exponent-th powers as well.  Both defects are of the same shape and both die against the
module, so the projection along the splitting still commutes with the action after tensoring, which
is all the obstruction asks of it.

In the intended reading the group is the confined units of a number field, the places are the ones
the prescribed divisor is supported on, and the demand is no longer for a unit of the subfield a
place decomposes in but only for a unit whose **class modulo exponent-th powers** that subfield's
automorphisms fix.  That is a strictly weaker demand, and the room between the two is the Kummer
room a decomposition group leaves.

## Main results

* `InverseGalois.CFT.zsmul_eq_zero_of_forall_pow_eq_one`: a module killed by its exponent is killed
  by the exponent as an integer multiple.
* `InverseGalois.CFT.rTensor_smul_of_smul_mul_pow`: **an endomorphism carried by the action up to
  exponent-th powers is carried by it on the nose after tensoring with a module the exponent
  kills.**
* `InverseGalois.CFT.exists_equivariant_of_forall_stabilizer_mul_pow`: one element per orbit, fixed
  up to an exponent-th power by the automorphisms fixing its own place, spreads over the orbit up
  to exponent-th powers.
* `InverseGalois.CFT.tensorInvariantClass_eq_zero_of_stabilizer_mod_pow`: **the obstruction vanishes
  as soon as each place carries an element whose orders agree with the diagonal up to the exponent
  and which the automorphisms fixing the place move only by exponent-th powers.**
* `InverseGalois.CFT.tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_pow`: the same for
  the confined units.
* `InverseGalois.CFT.tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_pow_order`: **the
  unit is only asked for at the places some automorphism of order the prime fixes.**

## Tags

group cohomology, permutation module, S-unit, tensor product, divisor, decomposition group
-/

set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField TensorProduct groupCohomology

/-! ### The exponent kills the module -/

section Exponent

variable (C : Type) [CommGroup C]

/-- **A module killed by its exponent is killed by the exponent as an integer multiple.** -/
theorem zsmul_eq_zero_of_forall_pow_eq_one (ℓ : ℕ) (hexp : ∀ c : C, c ^ ℓ = 1) (w : Additive C) :
    (ℓ : ℤ) • w = 0 := by
  have h1 : (ℓ : ℤ) • w = (ℓ : ℕ) • w := natCast_zsmul w ℓ
  have h2 : (ℓ : ℕ) • w = Additive.ofMul (w.toMul ^ ℓ) := (_root_.ofMul_pow ℓ w.toMul).symm
  rw [h1, h2, hexp]
  rfl

end Exponent

/-! ### An endomorphism carried by the action up to exponent-th powers -/

section Endo

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type) [CommGroup C] [MulDistribMulAction Q C]

/-- **An endomorphism carried by the action up to exponent-th powers is carried by it on the nose
after tensoring with a module the exponent kills.**

Read the identity on the pure tensors: the exponent-th power the endomorphism is moved by
contributes an exponent multiple in the first factor, which may be moved to the second, where the
exponent is zero. -/
theorem rTensor_smul_of_smul_mul_pow (ℓ : ℕ) (hexp : ∀ c : C, c ^ ℓ = 1)
    (P : Additive A →+ Additive A)
    (hP : ∀ (σ : Q) (a : A), ∃ c : Additive A,
      P (Additive.ofMul (σ • a))
        = Additive.ofMul (σ • (P (Additive.ofMul a)).toMul) + (ℓ : ℤ) • c)
    (σ : Q) (t : Additive A ⊗[ℤ] Additive C) :
    LinearMap.rTensor (Additive C) P.toIntLinearMap (σ • t)
      = σ • LinearMap.rTensor (Additive C) P.toIntLinearMap t := by
  have hw : ∀ w : Additive C, (ℓ : ℤ) • w = 0 := zsmul_eq_zero_of_forall_pow_eq_one C ℓ hexp
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, smul_add, ht, ht']
  | tmul z w =>
    obtain ⟨c, hc⟩ := hP σ z.toMul
    show LinearMap.rTensor (Additive C) P.toIntLinearMap
        (Additive.ofMul (σ • z.toMul) ⊗ₜ[ℤ] Additive.ofMul (σ • w.toMul))
      = σ • LinearMap.rTensor (Additive C) P.toIntLinearMap (z ⊗ₜ[ℤ] w)
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    show P (Additive.ofMul (σ • z.toMul)) ⊗ₜ[ℤ] Additive.ofMul (σ • w.toMul)
      = σ • (P z ⊗ₜ[ℤ] w)
    have h0 : ((ℓ : ℤ) • c) ⊗ₜ[ℤ] Additive.ofMul (σ • w.toMul)
        = (0 : Additive A ⊗[ℤ] Additive C) := by
      rw [← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, hw, TensorProduct.tmul_zero]
    rw [hc, TensorProduct.add_tmul, h0, add_zero]
    rfl

end Endo

/-! ### One element per orbit, spread over the orbit up to exponent-th powers -/

section Orbit

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {X : Type} [MulAction Q X]

/-- **One element per orbit, fixed up to an exponent-th power by the automorphisms fixing its own
place, spreads over the orbit up to exponent-th powers.**

Choose the element over one place of each orbit and translate it around the orbit.  Two
automorphisms carrying the place of the orbit to the same place differ by one fixing it, and those
move the element by an exponent-th power, so the translate is well defined up to an exponent-th
power.  Any property of a place and an element which the action carries along is carried along with
it. -/
theorem exists_equivariant_of_forall_stabilizer_mul_pow (ℓ : ℕ) (p : X → A → Prop)
    (hp : ∀ (σ : Q) (x : X) (a : A), p x a → p (σ • x) (σ • a))
    (hstab : ∀ x : X, ∃ a : A, p x a ∧ ∀ σ : Q, σ • x = x → ∃ v : A, σ • a = a * v ^ ℓ) :
    ∃ u : X → A, (∀ x : X, p x (u x)) ∧
      ∀ (σ : Q) (x : X), ∃ v : A, u (σ • x) = σ • u x * v ^ ℓ := by
  classical
  choose a ha hafix using hstab
  obtain ⟨R, hRorbit, hRsmul⟩ : ∃ R : X → X,
      (∀ x : X, ∃ σ : Q, σ • R x = x) ∧ ∀ (σ : Q) (x : X), R (σ • x) = R x := by
    refine ⟨fun x => (Quotient.mk'' x : Quotient (MulAction.orbitRel Q X)).out, fun x => ?_,
      fun σ x => ?_⟩
    · show ∃ σ : Q, σ • (Quotient.mk'' x : Quotient (MulAction.orbitRel Q X)).out = x
      have h := @Quotient.mk_out' X (MulAction.orbitRel Q X) x
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
      obtain ⟨σ, hσ⟩ := h
      exact ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩
    · show (Quotient.mk'' (σ • x) : Quotient (MulAction.orbitRel Q X)).out
        = (Quotient.mk'' x : Quotient (MulAction.orbitRel Q X)).out
      have h : (Quotient.mk'' (σ • x) : Quotient (MulAction.orbitRel Q X)) = Quotient.mk'' x :=
        Quotient.sound' (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨σ, rfl⟩))
      rw [h]
  choose τ hτ using hRorbit
  refine ⟨fun x => τ x • a (R x), fun x => ?_, fun σ x => ?_⟩
  · have h := hp (τ x) (R x) (a (R x)) (ha (R x))
    rwa [hτ x] at h
  · have h1 : τ (σ • x) • R x = σ • x := by
      rw [← hRsmul σ x]
      exact hτ (σ • x)
    have h2 : (σ * τ x) • R x = σ • x := by rw [mul_smul, hτ x]
    have h3 : ((σ * τ x)⁻¹ * τ (σ • x)) • R x = R x := by
      rw [mul_smul, h1, ← h2, inv_smul_smul]
    have h4 : τ (σ • x) = (σ * τ x) * ((σ * τ x)⁻¹ * τ (σ • x)) := by
      rw [mul_inv_cancel_left]
    obtain ⟨v, hv⟩ := hafix (R x) _ h3
    refine ⟨(σ * τ x) • v, ?_⟩
    show τ (σ • x) • a (R (σ • x)) = σ • (τ x • a (R x)) * ((σ * τ x) • v) ^ ℓ
    rw [hRsmul, h4, mul_smul, hv, smul_mul', smul_pow', ← mul_smul]

end Orbit

/-! ### The splitting and the obstruction -/

section Split

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C : Type} [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]
variable (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
variable (hgeq : ∀ (σ : Q) (a : A) (x : X),
  g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))

omit [DecidableEq X] in
include hgeq in
/-- **An element whose orders agree with the diagonal up to the exponent and which the
automorphisms fixing its place move only by exponent-th powers is enough at one place of each
orbit.**  The congruence on the orders is a condition place by place and travels around the orbit
with the element. -/
theorem exists_equivariant_diagonal_of_stabilizer_mod_pow (ℓ : ℕ)
    (hstab : ∀ x : X, ∃ a : A,
      (∀ y : X, (ℓ : ℤ) ∣ g (Additive.ofMul a) y - Finsupp.single x 1 y) ∧
        ∀ σ : Q, σ • x = x → ∃ v : A, σ • a = a * v ^ ℓ) :
    ∃ u : X → A,
      (∀ x y : X, (ℓ : ℤ) ∣ g (Additive.ofMul (u x)) y - Finsupp.single x 1 y) ∧
      ∀ (σ : Q) (x : X), ∃ v : A, u (σ • x) = σ • u x * v ^ ℓ := by
  classical
  refine exists_equivariant_of_forall_stabilizer_mul_pow ℓ
    (fun x a => ∀ y : X, (ℓ : ℤ) ∣ g (Additive.ofMul a) y - Finsupp.single x 1 y)
    (fun σ x a ha z => ?_) hstab
  have hiff : x = σ⁻¹ • z ↔ σ • x = z := eq_inv_smul_iff
  have hz : Finsupp.single (σ • x) (1 : ℤ) z = Finsupp.single x (1 : ℤ) (σ⁻¹ • z) := by
    simp only [Finsupp.single_apply, hiff]
  rw [hgeq σ a z, hz]
  exact ha (σ⁻¹ • z)

omit [DecidableEq X] in
include hgeq in
/-- **A family of elements permuted by the action up to exponent-th powers extends by linearity to
a homomorphism carried by the action up to exponent-th powers.**  The defect of the extension at a
generator is the defect of the family there, raised to the coefficient. -/
theorem exists_equivariant_addHom_mul_pow (ℓ : ℕ) (u : X → A)
    (husmul : ∀ (σ : Q) (x : X), ∃ v : A, u (σ • x) = σ • u x * v ^ ℓ) :
    ∃ s : (X →₀ ℤ) →+ Additive A,
      (∀ (y : X) (j : ℤ), s (Finsupp.single y j) = j • Additive.ofMul (u y)) ∧
      ∀ (σ : Q) (a : A), ∃ c : Additive A, s (g (Additive.ofMul (σ • a)))
        = Additive.ofMul (σ • (s (g (Additive.ofMul a))).toMul) + (ℓ : ℤ) • c := by
  classical
  set S : (X →₀ ℤ) →+ Additive A :=
    Finsupp.liftAddHom (fun x => zmultiplesHom (Additive A) (Additive.ofMul (u x))) with hS
  have hsingle : ∀ (y : X) (j : ℤ), S (Finsupp.single y j) = j • Additive.ofMul (u y) := by
    intro y j
    rw [hS]
    exact Finsupp.liftAddHom_apply_single _ y j
  have hinj : ∀ σ : Q, Function.Injective (fun x : X => σ • x) := by
    intro σ x y h
    simpa using congrArg (fun w : X => σ⁻¹ • w) h
  have hgmap : ∀ (σ : Q) (a : A), g (Additive.ofMul (σ • a))
      = Finsupp.mapDomain (fun x : X => σ • x) (g (Additive.ofMul a)) := by
    intro σ a
    ext z
    obtain ⟨y, rfl⟩ : ∃ y : X, z = σ • y := ⟨σ⁻¹ • z, (smul_inv_smul σ z).symm⟩
    rw [Finsupp.mapDomain_apply (hinj σ) (g (Additive.ofMul a)) y, hgeq, inv_smul_smul]
  have hsmap : ∀ (σ : Q) (n : X →₀ ℤ), ∃ c : Additive A,
      S (Finsupp.mapDomain (fun x : X => σ • x) n)
        = Additive.ofMul (σ • (S n).toMul) + (ℓ : ℤ) • c := by
    intro σ n
    induction n using Finsupp.induction_linear with
    | zero =>
      refine ⟨0, ?_⟩
      rw [Finsupp.mapDomain_zero, map_zero, smul_zero, add_zero]
      show (0 : Additive A) = Additive.ofMul (σ • (1 : A))
      rw [smul_one]
      rfl
    | add n n' hn hn' =>
      obtain ⟨c, hc⟩ := hn
      obtain ⟨c', hc'⟩ := hn'
      refine ⟨c + c', ?_⟩
      rw [Finsupp.mapDomain_add, map_add, map_add, hc, hc', _root_.toMul_add, smul_mul',
        _root_.ofMul_mul, smul_add]
      abel
    | single x m =>
      obtain ⟨v, hv⟩ := husmul σ x
      refine ⟨m • Additive.ofMul v, ?_⟩
      have hpow : Additive.ofMul (v ^ ℓ) = (ℓ : ℤ) • Additive.ofMul v := by
        rw [_root_.ofMul_pow, natCast_zsmul]
      rw [Finsupp.mapDomain_single, hsingle, hsingle, hv, _root_.ofMul_mul, hpow, smul_add,
        smul_comm m ((ℓ : ℤ)) (Additive.ofMul v), ← _root_.ofMul_zpow, ← smul_zpow',
        _root_.toMul_zsmul]
      rfl
  exact ⟨S, hsingle, fun σ a => by rw [hgmap σ a]; exact hsmap σ (g (Additive.ofMul a))⟩

omit [DecidableEq X] in
include hgeq in
/-- **A family whose orders agree with the diagonal up to the exponent and which the action permutes
up to exponent-th powers assembles into a splitting of the valuation of both kinds.** -/
theorem exists_equivariant_section_of_diagonal_mod_pow (ℓ : ℕ) (u : X → A)
    (hu : ∀ x y : X, (ℓ : ℤ) ∣ g (Additive.ofMul (u x)) y - Finsupp.single x 1 y)
    (husmul : ∀ (σ : Q) (x : X), ∃ v : A, u (σ • x) = σ • u x * v ^ ℓ) :
    ∃ s : (X →₀ ℤ) →+ Additive A, (∀ (n : X →₀ ℤ) (y : X), (ℓ : ℤ) ∣ g (s n) y - n y) ∧
      ∀ (σ : Q) (a : A), ∃ c : Additive A, s (g (Additive.ofMul (σ • a)))
        = Additive.ofMul (σ • (s (g (Additive.ofMul a))).toMul) + (ℓ : ℤ) • c := by
  classical
  obtain ⟨S, hsingle, hseq⟩ := exists_equivariant_addHom_mul_pow g hgeq ℓ u husmul
  have hgs : ∀ n : X →₀ ℤ, ∃ m : X →₀ ℤ, g (S n) = n + (ℓ : ℤ) • m := by
    intro n
    induction n using Finsupp.induction_linear with
    | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_zero, smul_zero, add_zero]
    | add n n' hn hn' =>
      obtain ⟨m, hm⟩ := hn
      obtain ⟨m', hm'⟩ := hn'
      refine ⟨m + m', ?_⟩
      rw [map_add, map_add, hm, hm', smul_add]
      abel
    | single x j =>
      obtain ⟨c, hc⟩ := exists_smul_of_forall_dvd ℓ (g (Additive.ofMul (u x)) - Finsupp.single x 1)
        (fun y => by rw [Finsupp.sub_apply]; exact hu x y)
      refine ⟨j • c, ?_⟩
      have hgu : g (Additive.ofMul (u x)) = Finsupp.single x 1 + (ℓ : ℤ) • c :=
        eq_add_of_sub_eq' hc
      rw [hsingle, map_zsmul, hgu, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one,
        smul_comm j ((ℓ : ℤ)) c]
  refine ⟨S, fun n y => ?_, hseq⟩
  obtain ⟨m, hm⟩ := hgs n
  rw [hm, Finsupp.add_apply, add_sub_cancel_left, Finsupp.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

variable (C) in
include hg hB hgeq in
/-- **The obstruction to invariance vanishes as soon as each place carries an element whose orders
agree with the diagonal up to the exponent of the module and which the automorphisms fixing the
place move only by an exponent-th power.**

Such elements spread over their orbits up to exponent-th powers, and the homomorphism they extend
to is carried by the action up to exponent-th powers.  Both defects are multiples of the exponent,
which the module kills, so after tensoring the projection along the splitting commutes with the
action on the nose, and that is what trivialises the obstruction.

This is the sharp arithmetic cost of correcting a prescribed divisor to an invariant radicand: one
element per orbit of places, asked for a congruence on its orders and for its class modulo
exponent-th powers to be fixed by the decomposition group of its place. -/
theorem tensorInvariantClass_eq_zero_of_stabilizer_mod_pow (ℓ : ℕ) (hexp : ∀ c : C, c ^ ℓ = 1)
    (hstab : ∀ x : X, ∃ a : A,
      (∀ y : X, (ℓ : ℤ) ∣ g (Additive.ofMul a) y - Finsupp.single x 1 y) ∧
        ∀ σ : Q, σ • x = x → ∃ v : A, σ • a = a * v ^ ℓ)
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t) :
    tensorInvariantClass C g B hg hB ht = 0 := by
  classical
  obtain ⟨u, hu, husmul⟩ := exists_equivariant_diagonal_of_stabilizer_mod_pow g hgeq ℓ hstab
  obtain ⟨s, hgs, hseq⟩ := exists_equivariant_section_of_diagonal_mod_pow g hgeq ℓ u hu husmul
  have hw : ∀ w : Additive C, (ℓ : ℤ) • w = 0 := zsmul_eq_zero_of_forall_pow_eq_one C ℓ hexp
  refine tensorInvariantClass_eq_zero_of_rTensor_comm C g B hg hB s (fun N => ?_)
    (fun σ N => rTensor_smul_of_smul_mul_pow C ℓ hexp (s.comp g) (fun σ a => hseq σ a) σ N) ht
  induction N using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add N N' hN hN' => rw [map_add, map_add, hN, hN']
  | tmul n w =>
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    obtain ⟨m, hm⟩ := exists_smul_of_forall_dvd ℓ (g (s n) - n)
      (fun y => by rw [Finsupp.sub_apply]; exact hgs n y)
    show g (s n) ⊗ₜ[ℤ] w = n ⊗ₜ[ℤ] w
    have h0 : ((ℓ : ℤ) • m) ⊗ₜ[ℤ] w = (0 : (X →₀ ℤ) ⊗[ℤ] Additive C) := by
      rw [← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, hw w, TensorProduct.tmul_zero]
    rw [eq_add_of_sub_eq hm, TensorProduct.add_tmul, h0, zero_add]

end Split

/-! ### The confined units -/

section Confined

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
variable {C : Type} [CommGroup C] [MulDistribMulAction Gal(K/k) C]
variable (n : ℕ) (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y] [IsGaloisStablePlaces k K Xs]

/-- **One confined unit per named place, of order one there and none at the other named places up
to the exponent and moved only by exponent-th powers by the automorphisms fixing it, kills the
obstruction** of every tensor whose valuation is invariant.

The vector of orders of a confined unit is equivariant, so the unit belonging to a place carries
with it the unit belonging to every place of the same orbit, up to exponent-th powers, and the
module the splitting is read against is killed by the exponent. -/
theorem tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_pow (hexp : ∀ c : C, c ^ n = 1)
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hstab : ∀ y : ↥Xs, ∃ u : ↥(confinedUnits K n Tz Y),
      (∀ z : ↥Xs, (n : ℤ) ∣ confinedOrd n Tz Y Xs (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
        ∀ σ : Gal(K/k), σ • y = y →
          ∃ v : ↥(confinedUnits K n Tz Y), σ • u = u * v ^ n)
    {t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C}
    (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
      = tensorVal C (confinedOrd n Tz Y Xs) t) :
    tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
      (mem_confinedSUnits_iff n Tz Y Xs) ht = 0 :=
  tensorInvariantClass_eq_zero_of_stabilizer_mod_pow C (confinedOrd n Tz Y Xs)
    (confinedSUnits n Tz Y Xs) hsurj (mem_confinedSUnits_iff n Tz Y Xs)
    (confinedOrd_smul_apply n Tz Y Xs) n hexp hstab ht

end Confined

section ConfinedOrder

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [FiniteDimensional k K]
variable {C : Type} [CommGroup C] [MulDistribMulAction Gal(K/k) C]
variable (n : ℕ) [Fact n.Prime] (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y] [IsGaloisStablePlaces k K Xs]

/-- **The unit the obstruction is bought with is only asked for at the places some automorphism of
order the prime fixes, and only up to exponent-th powers.**

Where no automorphism of order the prime fixes the place, the stabiliser has order prime to it by
Cauchy's theorem, and the product over that stabiliser of a preimage of the generator at the place,
raised to a power inverse to its size modulo the prime, supplies a unit fixed on the nose — so the
exponent-th power the demand allows may there be taken to be one. -/
theorem tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_pow_order
    (hexp : ∀ c : C, c ^ n = 1) (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hstab : ∀ y : ↥Xs, (∃ σ : Gal(K/k), σ ≠ 1 ∧ σ ^ n = 1 ∧ σ • y = y) →
      ∃ u : ↥(confinedUnits K n Tz Y),
        (∀ z : ↥Xs, (n : ℤ) ∣ confinedOrd n Tz Y Xs (Additive.ofMul u) z - Finsupp.single y 1 z) ∧
          ∀ σ : Gal(K/k), σ • y = y →
            ∃ v : ↥(confinedUnits K n Tz Y), σ • u = u * v ^ n)
    {t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C}
    (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
      = tensorVal C (confinedOrd n Tz Y Xs) t) :
    tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
      (mem_confinedSUnits_iff n Tz Y Xs) ht = 0 := by
  have hp : n.Prime := Fact.out
  haveI : NeZero n := ⟨hp.ne_zero⟩
  refine tensorInvariantClass_confinedOrd_eq_zero_of_stabilizer_mod_pow n Tz Y Xs hexp hsurj
    (fun y => ?_) ht
  by_cases hy : ∃ σ : Gal(K/k), σ ≠ 1 ∧ σ ^ n = 1 ∧ σ • y = y
  · exact hstab y hy
  · haveI : Finite Gal(K/k) := Finite.of_fintype _
    haveI : Finite ↥(stabilizer Gal(K/k) y) := Subtype.finite
    haveI : Fintype ↥(stabilizer Gal(K/k) y) := Fintype.ofFinite _
    have hcop : Nat.Coprime (Nat.card ↥(stabilizer Gal(K/k) y)) n := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => hy ?_)
      rw [Nat.card_eq_fintype_card] at hdvd
      obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card n hdvd
      have hσ1 : σ ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hσ
        exact hp.one_lt.ne hσ
      refine ⟨(σ : Gal(K/k)), fun h => hσ1 (OneMemClass.coe_eq_one.1 h), ?_,
        MulAction.mem_stabilizer_iff.1 σ.2⟩
      rw [← hσ, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
    obtain ⟨u, hord, hfix⟩ := exists_stabilizer_fixed_of_coprime (confinedOrd n Tz Y Xs)
      (confinedOrd_smul_apply n Tz Y Xs) hsurj n y hcop
    exact ⟨u, hord, fun σ hσ => ⟨1, by rw [hfix σ hσ, one_pow, mul_one]⟩⟩

end ConfinedOrder

end InverseGalois.CFT
