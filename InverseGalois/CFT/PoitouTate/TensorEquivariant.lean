/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TensorInvariant

/-!
# A splitting carried by the action kills the obstruction to invariance

A group acts on an abelian group carrying a valuation onto the free abelian group on a set of
places it permutes, and a tensor whose valuation is invariant carries an obstruction to being
invariant itself, a one cocycle with coefficients in the kernel of the valuation.  **The
obstruction vanishes as soon as the valuation splits equivariantly**: the projection of the tensor
along the splitting is an invariant tensor with the same valuation, and the difference between the
tensor and its projection trivialises the cocycle.

A splitting carried by the action is a family of elements of the group, one of order one at each
place and none anywhere else, permuted by the action exactly as the places are.  Such a family
costs no more than **one element per orbit**: choose the element over one place of each orbit and
translate it around the orbit, the translate being independent of the automorphism translating as
soon as the element is fixed by the automorphisms fixing its own place.  When the action on the
places is free that last condition is vacuous, so a tensor supported on places with trivial
decomposition group needs no arithmetic at all to be made invariant.

The splitting is only ever used after tensoring with the module, and the module has an exponent,
so **a splitting modulo the exponent is enough**: the elements are asked only for a congruence on
their orders, one at their own place and none anywhere else up to multiples of the exponent.

In the intended reading the abelian group is the multiplicative group of a number field modulo
exponent-th powers, the places are the primes outside a finite set, the kernel of the valuation is
the group of units for that set, and the module is a layer of a tower.  The obstruction is what a
Kummer assembly has to pay to turn a prescribed divisor into a family of radicands permuted by the
group, and the reading here is that the payment is nil at places no automorphism fixes.

## Main results

* `InverseGalois.CFT.rTensor_smul_of_smul`: an endomorphism carried by the action stays carried by
  it after tensoring with a module.
* `InverseGalois.CFT.tensorInvariantClass_eq_zero_of_section`: **a splitting of the valuation
  carried by the action kills the obstruction of every tensor with invariant valuation.**
* `InverseGalois.CFT.exists_equivariant_of_forall_stabilizer`: one element per orbit, fixed by the
  automorphisms fixing its own place, spreads over the orbit carrying any property the action
  carries along.
* `InverseGalois.CFT.exists_equivariant_diagonal_of_stabilizer`: hence a family of elements of
  order one at their own place and none elsewhere, permuted by the action.
* `InverseGalois.CFT.exists_equivariant_diagonal`: the same for a free action, where being fixed by
  the automorphisms fixing the place asks nothing.
* `InverseGalois.CFT.exists_equivariant_section_of_diagonal`: such a family assembles into a
  splitting carried by the action.
* `InverseGalois.CFT.tensorInvariantClass_eq_zero_of_stabilizer`: **the obstruction vanishes as
  soon as each place carries an element of order one there and none elsewhere, fixed by the
  automorphisms fixing the place.**
* `InverseGalois.CFT.tensorInvariantClass_eq_zero_of_smul_eq_one`: **the obstruction vanishes when
  no automorphism but the identity fixes a place.**
* `InverseGalois.CFT.tensorInvariantClass_eq_zero_of_stabilizer_mod`: **the orders of those
  elements are only asked for up to the exponent of the module.**

## Tags

group cohomology, permutation module, S-unit, tensor product, divisor, free action
-/

set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open MulAction TensorProduct groupCohomology

/-! ### An endomorphism carried by the action -/

section Endo

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type) [CommGroup C] [MulDistribMulAction Q C]

/-- **An endomorphism carried by the action stays carried by it after tensoring with a module.**
It is enough to read the identity on the pure tensors, where the two actions are the action on
each factor. -/
theorem rTensor_smul_of_smul (P : Additive A →+ Additive A)
    (hP : ∀ (σ : Q) (a : A),
      P (Additive.ofMul (σ • a)) = Additive.ofMul (σ • (P (Additive.ofMul a)).toMul))
    (σ : Q) (t : Additive A ⊗[ℤ] Additive C) :
    LinearMap.rTensor (Additive C) P.toIntLinearMap (σ • t)
      = σ • LinearMap.rTensor (Additive C) P.toIntLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, smul_add, ht, ht']
  | tmul z w =>
    show LinearMap.rTensor (Additive C) P.toIntLinearMap
        (Additive.ofMul (σ • z.toMul) ⊗ₜ[ℤ] Additive.ofMul (σ • w.toMul))
      = σ • LinearMap.rTensor (Additive C) P.toIntLinearMap (z ⊗ₜ[ℤ] w)
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    show P (Additive.ofMul (σ • z.toMul)) ⊗ₜ[ℤ] Additive.ofMul (σ • w.toMul)
      = σ • (P z ⊗ₜ[ℤ] w)
    rw [hP σ z.toMul]
    rfl

end Endo

/-! ### A splitting carried by the action -/

section Split

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C : Type} [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]
variable (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)

omit [MulAction Q X] in
variable (C) in
include hg hB in
/-- **A splitting of the valuation carried by the action kills the obstruction of a tensor whose
valuation is invariant.**

The projection of the tensor along the splitting has the same valuation as the tensor, and the
valuation of the tensor is literally unchanged by the action, so the projection is invariant.  The
difference between the tensor and its projection has vanishing valuation, hence comes from the
kernel, and its coboundary is the obstruction. -/
theorem tensorInvariantClass_eq_zero_of_rTensor_section
    (s : (X →₀ ℤ) →+ Additive A)
    (hgsT : ∀ n : (X →₀ ℤ) ⊗[ℤ] Additive C,
      LinearMap.rTensor (Additive C) g.toIntLinearMap
        (LinearMap.rTensor (Additive C) s.toIntLinearMap n) = n)
    (hseq : ∀ (σ : Q) (a : A), s (g (Additive.ofMul (σ • a)))
      = Additive.ofMul (σ • (s (g (Additive.ofMul a))).toMul))
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t) :
    tensorInvariantClass C g B hg hB ht = 0 := by
  classical
  have hgt : ∀ σ : Q, LinearMap.rTensor (Additive C) g.toIntLinearMap (σ • t)
      = LinearMap.rTensor (Additive C) g.toIntLinearMap t := by
    intro σ
    have h : tensorVal C g (σ • t - t) = 0 := by rw [map_sub, ht σ, sub_self]
    rw [tensorVal_eq_zero_iff, map_sub, sub_eq_zero] at h
    exact h
  have hcomp : ∀ u : Additive A ⊗[ℤ] Additive C,
      LinearMap.rTensor (Additive C) (s.comp g).toIntLinearMap u
        = LinearMap.rTensor (Additive C) s.toIntLinearMap
            (LinearMap.rTensor (Additive C) g.toIntLinearMap u) := by
    intro u
    rw [show ((s.comp g).toIntLinearMap : Additive A →ₗ[ℤ] Additive A)
      = s.toIntLinearMap ∘ₗ g.toIntLinearMap from rfl, LinearMap.rTensor_comp]
    rfl
  have hP : ∀ (σ : Q) (a : A), (s.comp g) (Additive.ofMul (σ • a))
      = Additive.ofMul (σ • ((s.comp g) (Additive.ofMul a)).toMul) := fun σ a => hseq σ a
  have hinv : ∀ σ : Q, σ • LinearMap.rTensor (Additive C) (s.comp g).toIntLinearMap t
      = LinearMap.rTensor (Additive C) (s.comp g).toIntLinearMap t := by
    intro σ
    rw [← rTensor_smul_of_smul C (s.comp g) hP σ t, hcomp, hgt σ, ← hcomp]
  obtain ⟨b, hbeq⟩ : t - LinearMap.rTensor (Additive C) (s.comp g).toIntLinearMap t
      ∈ LinearMap.range (tensorSubIncl C B) := by
    rw [range_tensorSubIncl g hg hB, LinearMap.mem_ker, map_sub, hcomp, hgsT, sub_self]
  refine (H1π_eq_zero_iff _).2 ⟨b, funext fun σ => ?_⟩
  show σ • b - b = tensorInvariantCocycle C g B hg hB ht σ
  refine tensorSubIncl_injective g hg hB ?_
  rw [map_sub, tensorSubIncl_smul, hbeq, tensorSubIncl_tensorInvariantCocycle, smul_sub, hinv σ]
  abel

omit [MulAction Q X] in
variable (C) in
include hg hB in
/-- **A splitting of the valuation carried by the action kills the obstruction of a tensor whose
valuation is invariant.**

The projection of the tensor along the splitting has the same valuation as the tensor, and the
valuation of the tensor is literally unchanged by the action, so the projection is invariant.  The
difference between the tensor and its projection has vanishing valuation, hence comes from the
kernel, and its coboundary is the obstruction. -/
theorem tensorInvariantClass_eq_zero_of_section
    (s : (X →₀ ℤ) →+ Additive A) (hgs : ∀ n : X →₀ ℤ, g (s n) = n)
    (hseq : ∀ (σ : Q) (a : A), s (g (Additive.ofMul (σ • a)))
      = Additive.ofMul (σ • (s (g (Additive.ofMul a))).toMul))
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t) :
    tensorInvariantClass C g B hg hB ht = 0 :=
  tensorInvariantClass_eq_zero_of_rTensor_section C g B hg hB s
    (fun n => by
      induction n using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | add n n' hn hn' => rw [map_add, map_add, hn, hn']
      | tmul x w =>
        rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
        exact congrArg (fun y => y ⊗ₜ[ℤ] w) (hgs x))
    hseq ht

end Split

/-! ### One element per orbit, spread over the orbit -/

section Orbit

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {X : Type} [MulAction Q X]

/-- **One element per orbit, fixed by the automorphisms fixing its own place, spreads over the
orbit.**

Choose the element over one place of each orbit and translate it around the orbit.  Two
automorphisms carrying the place of the orbit to the same place differ by one fixing it, and the
element is fixed by those, so the translate does not depend on the automorphism translating.  Any
property of a place and an element which the action carries along is carried along with it. -/
theorem exists_equivariant_of_forall_stabilizer (p : X → A → Prop)
    (hp : ∀ (σ : Q) (x : X) (a : A), p x a → p (σ • x) (σ • a))
    (hstab : ∀ x : X, ∃ a : A, p x a ∧ ∀ σ : Q, σ • x = x → σ • a = a) :
    ∃ u : X → A, (∀ x : X, p x (u x)) ∧ ∀ (σ : Q) (x : X), u (σ • x) = σ • u x := by
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
  · show τ (σ • x) • a (R (σ • x)) = σ • (τ x • a (R x))
    rw [hRsmul, ← mul_smul]
    have h1 : τ (σ • x) • R x = σ • x := by
      rw [← hRsmul σ x]
      exact hτ (σ • x)
    have h2 : (σ * τ x) • R x = σ • x := by rw [mul_smul, hτ x]
    have h3 : ((σ * τ x)⁻¹ * τ (σ • x)) • R x = R x := by
      rw [mul_smul, h1, ← h2, inv_smul_smul]
    have h4 : τ (σ • x) = (σ * τ x) * ((σ * τ x)⁻¹ * τ (σ • x)) := by
      rw [mul_inv_cancel_left]
    rw [h4, mul_smul, hafix (R x) _ h3]

end Orbit

/-! ### A free action carries a splitting -/

section Free

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C : Type} [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]
variable (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
variable (hgeq : ∀ (σ : Q) (a : A) (x : X),
  g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))

omit [DecidableEq X] in
include hgeq in
/-- **An element of order one at its own place and none anywhere else, fixed by the automorphisms
fixing that place, is enough at one place of each orbit to carry a family permuted by the action.**

Choose the element over one place of each orbit and translate it around the orbit.  Two
automorphisms carrying the place of the orbit to the same place differ by one fixing it, and the
element is fixed by those, so the translate does not depend on the automorphism translating. -/
theorem exists_equivariant_diagonal_of_stabilizer
    (hstab : ∀ x : X, ∃ a : A, g (Additive.ofMul a) = Finsupp.single x 1 ∧
      ∀ σ : Q, σ • x = x → σ • a = a) :
    ∃ u : X → A, (∀ x : X, g (Additive.ofMul (u x)) = Finsupp.single x 1) ∧
      ∀ (σ : Q) (x : X), u (σ • x) = σ • u x := by
  classical
  refine exists_equivariant_of_forall_stabilizer
    (fun x a => g (Additive.ofMul a) = Finsupp.single x 1) (fun σ x a ha => ?_) hstab
  ext z
  have hiff : x = σ⁻¹ • z ↔ σ • x = z := eq_inv_smul_iff
  rw [hgeq σ a z, ha]
  simp only [Finsupp.single_apply, hiff]

omit [DecidableEq X] in
include hg hgeq in
/-- **A free action on the places carries a family of elements of order one at its own place and
none anywhere else, permuted by the action.**  No automorphism but the identity fixes a place, so
the element chosen over one place of each orbit is asked for nothing beyond its orders. -/
theorem exists_equivariant_diagonal (hfree : ∀ (σ : Q) (x : X), σ • x = x → σ = 1) :
    ∃ u : X → A, (∀ x : X, g (Additive.ofMul (u x)) = Finsupp.single x 1) ∧
      ∀ (σ : Q) (x : X), u (σ • x) = σ • u x := by
  classical
  refine exists_equivariant_diagonal_of_stabilizer g hgeq fun x => ?_
  obtain ⟨a, ha⟩ := hg (Finsupp.single x (1 : ℤ))
  exact ⟨a.toMul, ha, fun σ hσ => by rw [hfree σ x hσ, one_smul]⟩

omit [DecidableEq X] in
include hgeq in
/-- **A family of elements permuted by the action extends by linearity to a homomorphism carried by
the action.**  The extension carries the action because the valuation does and the family does,
and it sends the generator at a place to the corresponding member of the family. -/
theorem exists_equivariant_addHom (u : X → A)
    (husmul : ∀ (σ : Q) (x : X), u (σ • x) = σ • u x) :
    ∃ s : (X →₀ ℤ) →+ Additive A,
      (∀ (y : X) (j : ℤ), s (Finsupp.single y j) = j • Additive.ofMul (u y)) ∧
      ∀ (σ : Q) (a : A), s (g (Additive.ofMul (σ • a)))
        = Additive.ofMul (σ • (s (g (Additive.ofMul a))).toMul) := by
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
  have hsmap : ∀ (σ : Q) (n : X →₀ ℤ),
      S (Finsupp.mapDomain (fun x : X => σ • x) n) = Additive.ofMul (σ • (S n).toMul) := by
    intro σ n
    induction n using Finsupp.induction_linear with
    | zero =>
      rw [Finsupp.mapDomain_zero, map_zero]
      show (0 : Additive A) = Additive.ofMul (σ • (1 : A))
      rw [smul_one]
      rfl
    | add n n' hn hn' =>
      rw [Finsupp.mapDomain_add, map_add, map_add, hn, hn', _root_.toMul_add, smul_mul',
        _root_.ofMul_mul]
    | single x m =>
      rw [Finsupp.mapDomain_single, hsingle, hsingle, husmul, ← _root_.ofMul_zpow, ← smul_zpow',
        _root_.toMul_zsmul]
      rfl
  exact ⟨S, hsingle, fun σ a => by rw [hgmap σ a, hsmap σ]⟩

omit [DecidableEq X] in
include hgeq in
/-- **A family of elements of order one at its own place and none anywhere else, permuted by the
action, assembles into a splitting of the valuation carried by the action.**  Extend the family by
linearity and read the orders one generator at a time. -/
theorem exists_equivariant_section_of_diagonal (u : X → A)
    (hu : ∀ x : X, g (Additive.ofMul (u x)) = Finsupp.single x 1)
    (husmul : ∀ (σ : Q) (x : X), u (σ • x) = σ • u x) :
    ∃ s : (X →₀ ℤ) →+ Additive A, (∀ n : X →₀ ℤ, g (s n) = n) ∧
      ∀ (σ : Q) (a : A), s (g (Additive.ofMul (σ • a)))
        = Additive.ofMul (σ • (s (g (Additive.ofMul a))).toMul) := by
  classical
  obtain ⟨S, hsingle, hseq⟩ := exists_equivariant_addHom g hgeq u husmul
  refine ⟨S, fun n => ?_, hseq⟩
  induction n using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add n n' hn hn' => rw [map_add, map_add, hn, hn']
  | single x m =>
    rw [hsingle, map_zsmul, hu, Finsupp.smul_single, smul_eq_mul, mul_one]

variable (C) in
include hg hB hgeq in
/-- **The obstruction to invariance vanishes as soon as each place carries an element of order one
there and none anywhere else, fixed by the automorphisms fixing the place.**

Such elements assemble into a splitting of the valuation carried by the action, and a splitting
carried by the action kills the obstruction.  This is the whole arithmetic cost of correcting a
prescribed divisor to an invariant radicand: one element per orbit of places, living in the field
the decomposition group of the place cuts out. -/
theorem tensorInvariantClass_eq_zero_of_stabilizer
    (hstab : ∀ x : X, ∃ a : A, g (Additive.ofMul a) = Finsupp.single x 1 ∧
      ∀ σ : Q, σ • x = x → σ • a = a)
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t) :
    tensorInvariantClass C g B hg hB ht = 0 := by
  obtain ⟨u, hu, husmul⟩ := exists_equivariant_diagonal_of_stabilizer g hgeq hstab
  obtain ⟨s, hgs, hseq⟩ := exists_equivariant_section_of_diagonal g hgeq u hu husmul
  exact tensorInvariantClass_eq_zero_of_section C g B hg hB s hgs hseq ht

variable (C) in
include hg hB hgeq in
/-- **The obstruction to invariance vanishes when no automorphism but the identity fixes a
place.**  A free action asks nothing of the elements beyond their orders.

Read arithmetically: a prescribed divisor supported on places with trivial decomposition group
lifts to an invariant tensor with no condition on the module whatever. -/
theorem tensorInvariantClass_eq_zero_of_smul_eq_one
    (hfree : ∀ (σ : Q) (x : X), σ • x = x → σ = 1)
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t) :
    tensorInvariantClass C g B hg hB ht = 0 := by
  obtain ⟨u, hu, husmul⟩ := exists_equivariant_diagonal g hg hgeq hfree
  obtain ⟨s, hgs, hseq⟩ := exists_equivariant_section_of_diagonal g hgeq u hu husmul
  exact tensorInvariantClass_eq_zero_of_section C g B hg hB s hgs hseq ht

end Free

/-! ### A splitting up to the exponent of the module -/

section Mod

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C : Type} [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]
variable (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
variable (hgeq : ∀ (σ : Q) (a : A) (x : X),
  g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))

omit [DecidableEq X] in
/-- **A vector of integers all of whose entries are divisible by a number is that number times a
vector of integers.**  Divide entry by entry; the quotient of a vanishing entry vanishes, so the
quotients again have finite support. -/
theorem exists_smul_of_forall_dvd (ℓ : ℕ) (n : X →₀ ℤ) (h : ∀ y : X, (ℓ : ℤ) ∣ n y) :
    ∃ m : X →₀ ℤ, n = (ℓ : ℤ) • m :=
  ⟨Finsupp.mapRange (fun a : ℤ => a / (ℓ : ℤ)) (Int.zero_ediv _) n,
    Finsupp.ext fun y => by
      rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (h y)).symm⟩

omit [DecidableEq X] in
include hgeq in
/-- **An element whose orders agree with the diagonal up to the exponent is enough at one place of
each orbit**, provided it is fixed by the automorphisms fixing that place.  The congruence is a
condition on the orders place by place, and the action permutes the places, so it travels around
the orbit with the element. -/
theorem exists_equivariant_diagonal_of_stabilizer_mod (ℓ : ℕ)
    (hstab : ∀ x : X, ∃ a : A,
      (∀ y : X, (ℓ : ℤ) ∣ g (Additive.ofMul a) y - Finsupp.single x 1 y) ∧
        ∀ σ : Q, σ • x = x → σ • a = a) :
    ∃ u : X → A,
      (∀ x y : X, (ℓ : ℤ) ∣ g (Additive.ofMul (u x)) y - Finsupp.single x 1 y) ∧
      ∀ (σ : Q) (x : X), u (σ • x) = σ • u x := by
  classical
  refine exists_equivariant_of_forall_stabilizer
    (fun x a => ∀ y : X, (ℓ : ℤ) ∣ g (Additive.ofMul a) y - Finsupp.single x 1 y)
    (fun σ x a ha z => ?_) hstab
  have hiff : x = σ⁻¹ • z ↔ σ • x = z := eq_inv_smul_iff
  have hz : Finsupp.single (σ • x) (1 : ℤ) z = Finsupp.single x (1 : ℤ) (σ⁻¹ • z) := by
    simp only [Finsupp.single_apply, hiff]
  rw [hgeq σ a z, hz]
  exact ha (σ⁻¹ • z)

omit [DecidableEq X] in
include hgeq in
/-- **A family whose orders agree with the diagonal up to the exponent, permuted by the action,
assembles into a splitting of the valuation up to the exponent, carried by the action.** -/
theorem exists_equivariant_section_of_diagonal_mod (ℓ : ℕ) (u : X → A)
    (hu : ∀ x y : X, (ℓ : ℤ) ∣ g (Additive.ofMul (u x)) y - Finsupp.single x 1 y)
    (husmul : ∀ (σ : Q) (x : X), u (σ • x) = σ • u x) :
    ∃ s : (X →₀ ℤ) →+ Additive A, (∀ (n : X →₀ ℤ) (y : X), (ℓ : ℤ) ∣ g (s n) y - n y) ∧
      ∀ (σ : Q) (a : A), s (g (Additive.ofMul (σ • a)))
        = Additive.ofMul (σ • (s (g (Additive.ofMul a))).toMul) := by
  classical
  obtain ⟨S, hsingle, hseq⟩ := exists_equivariant_addHom g hgeq u husmul
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
agree with the diagonal up to the exponent of the module, fixed by the automorphisms fixing the
place.**

The module is killed by its exponent, so the tensor product of the free module on the places with
it is killed by the exponent too, and a splitting of the valuation modulo the exponent is a genuine
splitting after tensoring.  This is the sharp arithmetic cost of correcting a prescribed divisor to
an invariant radicand: one element per orbit of places, living in the field the decomposition group
of the place cuts out, and asked only for a congruence on its orders. -/
theorem tensorInvariantClass_eq_zero_of_stabilizer_mod (ℓ : ℕ) (hexp : ∀ c : C, c ^ ℓ = 1)
    (hstab : ∀ x : X, ∃ a : A,
      (∀ y : X, (ℓ : ℤ) ∣ g (Additive.ofMul a) y - Finsupp.single x 1 y) ∧
        ∀ σ : Q, σ • x = x → σ • a = a)
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t) :
    tensorInvariantClass C g B hg hB ht = 0 := by
  classical
  obtain ⟨u, hu, husmul⟩ := exists_equivariant_diagonal_of_stabilizer_mod g hgeq ℓ hstab
  obtain ⟨s, hgs, hseq⟩ := exists_equivariant_section_of_diagonal_mod g hgeq ℓ u hu husmul
  have hw : ∀ w : Additive C, (ℓ : ℤ) • w = 0 := by
    intro w
    have h1 : (ℓ : ℤ) • w = (ℓ : ℕ) • w := natCast_zsmul w ℓ
    have h2 : (ℓ : ℕ) • w = Additive.ofMul (w.toMul ^ ℓ) := (_root_.ofMul_pow ℓ w.toMul).symm
    rw [h1, h2, hexp]
    rfl
  refine tensorInvariantClass_eq_zero_of_rTensor_section C g B hg hB s (fun N => ?_) hseq ht
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

end Mod

end InverseGalois.CFT
