/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.NamedRadicand

/-!
# The named radicand asked for only where the obstruction lives

The descent to an invariant radicand costs one class in the first cohomology of the Galois group
with coefficients in the kernel of the valuation, tensored with the module of coefficients.  Asking
that **whole** group to vanish is far more than the descent consumes: the classes that actually
arise are the obstructions of the tensors whose valuation is already invariant, that is the image
of the connecting homomorphism of the valuation, and that image is governed by the finitely many
named places alone while the group itself is governed by every place of the field.

This file records the descent with the hypothesis narrowed to exactly that image: every tensor
whose valuation is invariant has vanishing obstruction.  Equivalently, every invariant divisor with
coefficients in the module is already the divisor of an invariant radicand — which is the statement
the prescription needs and nothing more.

## Main results

* `InverseGalois.CFT.exists_invariant_tensorVal_eq_orbitRadicand_of_class`: **an invariant tensor
  realising the divisor carried by one orbit, once the obstructions of the invariantly valued
  tensors vanish.**
* `InverseGalois.CFT.exists_invariant_tensorVal_eq_of_named_of_class`: **an invariant tensor whose
  value is the prescribed one at each of finitely many places in distinct orbits**, under the same
  hypothesis.
* `InverseGalois.CFT.exists_invariant_confinedTensorVal_eq_of_named_of_class`: the same for the
  units of a number field which are local powers at one set of places and have order divisible by
  the exponent outside another.

## Tags

number field, S-unit, tensor product, divisor, orbit, descent, group cohomology, obstruction
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField TensorProduct groupCohomology

/-! ### One orbit -/

section Orbit

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C : Type} [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]

/-- **An invariant tensor realising the divisor carried by one orbit, once the obstructions of the
invariantly valued tensors vanish.**  The valuation is onto, so the divisor is realised; it is
equivariant and the divisor carried by an orbit is equivariant, so the valuation of the realising
tensor is invariant.  What is left is the obstruction of that tensor, and the hypothesis kills
it. -/
theorem exists_invariant_tensorVal_eq_orbitRadicand_of_class
    (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hδ : ∀ (t : Additive A ⊗[ℤ] Additive C)
      (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t),
      tensorInvariantClass C g B hg hB ht = 0)
    (x₀ : X) (V : C) (hV : ∀ s ∈ stabilizer Q x₀, s • V = V) :
    ∃ s : Additive A ⊗[ℤ] Additive C,
      (∀ σ : Q, σ • s = s) ∧
      ∀ x : X, tensorVal C g s x = orbitRadicand Q x₀ V x := by
  have hgeq' : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) (σ • x) = g (Additive.ofMul a) x := by
    intro σ a x
    rw [hgeq σ a (σ • x), inv_smul_smul]
  obtain ⟨t, ht⟩ := tensorVal_surjective C g hg (orbitRadicand Q x₀ V)
  have hinv : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t :=
    tensorVal_smul_eq_of_eq C g hgeq' ht (orbitRadicand_smul_apply Q x₀ V hV)
  obtain ⟨s, hs, hsval⟩ := exists_invariant_tensorCoeff_of_map_tensorInvariantClass_eq_zero
    g B hg hB (MonoidHom.id C) (fun _ _ => rfl) hinv (by rw [hδ t hinv, _root_.map_zero])
  exact ⟨s, hs, fun x => by rw [hsval x, ht]; rfl⟩

end Orbit

/-! ### The places named by a prescription -/

section Named

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C : Type} [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]

/-- **An invariant tensor whose value is the prescribed one at each of finitely many places lying
in distinct orbits, asked for only where the obstruction lives.**  Each demand is answered on its
own orbit, and the answers are added: invariance survives the addition, and the divisors carried by
distinct orbits have disjoint supports, so no demand disturbs another. -/
theorem exists_invariant_tensorVal_eq_of_named_of_class
    (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hδ : ∀ (t : Additive A ⊗[ℤ] Additive C)
      (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t),
      tensorInvariantClass C g B hg hB ht = 0)
    {ι : Type} [Fintype ι] (x : ι → X) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Q (x μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → x μ ∉ orbit Q (x ν)) :
    ∃ s : Additive A ⊗[ℤ] Additive C,
      (∀ σ : Q, σ • s = s) ∧
      (∀ μ : ι, tensorVal C g s (x μ) = Additive.ofMul (V μ)) ∧
      ∀ z : X, (∀ μ : ι, z ∉ orbit Q (x μ)) → tensorVal C g s z = 0 := by
  choose s hs hsval using fun μ : ι =>
    exists_invariant_tensorVal_eq_orbitRadicand_of_class g B hg hB hgeq hδ (x μ) (V μ) (hV μ)
  have hzero : ∀ (μ : ι) (z : X), z ∉ orbit Q (x μ) → tensorVal C g (s μ) z = 0 := by
    intro μ z hz
    rw [hsval μ z, orbitRadicand_apply_of_notMem Q (x μ) (V μ) hz]
  refine ⟨∑ μ : ι, s μ, fun σ => ?_, fun ν => ?_, fun z hz => ?_⟩
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun μ _ => hs μ σ
  · rw [_root_.map_sum, Finset.sum_apply']
    refine (Finset.sum_eq_single ν (fun μ _ hμ => hzero μ (x ν) (hdisj ν μ (Ne.symm hμ)))
      (fun hν => absurd (Finset.mem_univ ν) hν)).trans ?_
    rw [hsval ν (x ν), orbitRadicand_apply_self Q (x ν) (V ν) (hV ν)]
  · rw [_root_.map_sum, Finset.sum_apply']
    exact Finset.sum_eq_zero fun μ _ => hzero μ z (hz μ)

end Named

/-! ### The confined units of a number field -/

section Confined

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (n : ℕ) (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K Xs]
variable {C : Type} [CommGroup C] [MulDistribMulAction Gal(K/k) C]

/-- **An invariant radicand of confined units whose value is the prescribed one at each of finitely
many named places lying in distinct orbits, asked for only where the obstruction lives.**  Beyond
the surjectivity of the vector of orders, all that is asked is that a confined radicand whose
divisor is already invariant may be corrected to an invariant radicand with the same divisor. -/
theorem exists_invariant_confinedTensorVal_eq_of_named_of_class
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hδ : ∀ (t : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C)
      (ht : ∀ σ : Gal(K/k), tensorVal C (confinedOrd n Tz Y Xs) (σ • t)
        = tensorVal C (confinedOrd n Tz Y Xs) t),
      tensorInvariantClass C (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs) hsurj
        (mem_confinedSUnits_iff n Tz Y Xs) ht = 0)
    {ι : Type} [Fintype ι] (w : ι → ↥Xs) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Gal(K/k) (w μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → w μ ∉ orbit Gal(K/k) (w ν)) :
    ∃ s : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C,
      (∀ σ : Gal(K/k), σ • s = s) ∧
      (∀ μ : ι, tensorVal C (confinedOrd n Tz Y Xs) s (w μ) = Additive.ofMul (V μ)) ∧
      ∀ z : ↥Xs, (∀ μ : ι, z ∉ orbit Gal(K/k) (w μ)) →
        tensorVal C (confinedOrd n Tz Y Xs) s z = 0 :=
  exists_invariant_tensorVal_eq_of_named_of_class (confinedOrd n Tz Y Xs)
    (confinedSUnits n Tz Y Xs) hsurj (mem_confinedSUnits_iff n Tz Y Xs)
    (confinedOrd_smul_apply n Tz Y Xs) hδ w V hV hdisj

end Confined

end InverseGalois.CFT
