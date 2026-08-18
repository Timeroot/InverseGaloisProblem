/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Homomorphisms into an algebraically closed field extend along integral extensions

Let `B` be an integral extension of `A`, and let `φ : A → F` be a homomorphism into an
algebraically closed field which kills everything that dies in `B`.  Then `φ` extends to `B`.

Geometrically this is the surjectivity of `Spec B → Spec A` for an integral extension, together
with the fact that a point of the target with values in a field is dominated by a point of the
source with values in an algebraic extension of that field — and an algebraically closed field
admits no proper algebraic extension to escape to.  It is the mechanism which makes the image of
a finite morphism *closed*: a parameter value at which all the elimination equations hold really
does carry a solution.

## Main results

* `Rigidity.RET.Transfer.exists_ringHom_of_isIntegral` — the extension of `φ` to `B`.
-/

namespace Rigidity.RET.Transfer

section Domain

variable {R S F : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field F]
  [IsAlgClosed F] [Algebra R S] [Algebra R F] [Algebra.IsIntegral R S]

private theorem isTorsionFree_of_injective {M : Type*} [CommRing M] [IsDomain M] [Algebra R M]
    (h : Function.Injective (algebraMap R M)) : Module.IsTorsionFree R M :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x hrx => by
    rw [Algebra.smul_def, mul_eq_zero] at hrx
    rcases hrx with hz | hz
    · exact Or.inl (h (by simpa using hz))
    · exact Or.inr hz

/-- The extension of an embedding into an algebraically closed field along an integral extension
of domains. -/
private theorem exists_ringHom_of_isIntegral_of_isDomain
    (hinjS : Function.Injective (algebraMap R S))
    (hinjF : Function.Injective (algebraMap R F)) :
    ∃ ψ : S →+* F, ψ.comp (algebraMap R S) = algebraMap R F := by
  haveI : Module.IsTorsionFree R S := isTorsionFree_of_injective hinjS
  haveI : Module.IsTorsionFree R F := isTorsionFree_of_injective hinjF
  haveI : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  refine ⟨(IsAlgClosed.lift (R := R) (S := S) (M := F) : S →ₐ[R] F).toRingHom, ?_⟩
  ext r
  simp

end Domain

/-- **A homomorphism into an algebraically closed field extends along an integral extension.**

The hypothesis is the only one possible: a homomorphism that extends to `B` must kill the kernel
of `A → B`. -/
theorem exists_ringHom_of_isIntegral {A B F : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] [Field F] [IsAlgClosed F] (φ : A →+* F)
    (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker φ) :
    ∃ ψ : B →+* F, ψ.comp (algebraMap A B) = φ := by
  classical
  haveI hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B) (RingHom.ker φ) ⊥
      (by simpa using hker)
  haveI := hQprime
  haveI hlies : Q.LiesOver (RingHom.ker φ) := ⟨hQcomap.symm⟩
  haveI : IsDomain (A ⧸ RingHom.ker φ) := Ideal.Quotient.isDomain _
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker φ)
  letI : Algebra (A ⧸ RingHom.ker φ) F := (RingHom.kerLift φ).toAlgebra
  have hinjF : Function.Injective (algebraMap (A ⧸ RingHom.ker φ) F) :=
    RingHom.kerLift_injective φ
  have hmapB : (algebraMap (A ⧸ RingHom.ker φ) (B ⧸ Q)) =
      Ideal.quotientMap Q (algebraMap A B) (le_of_eq hQcomap.symm) := by
    ext a
    rfl
  have hinjB : Function.Injective (algebraMap (A ⧸ RingHom.ker φ) (B ⧸ Q)) := by
    rw [hmapB]
    exact Ideal.quotientMap_injective' (le_of_eq hQcomap)
  obtain ⟨ψ₀, hψ₀⟩ :=
    exists_ringHom_of_isIntegral_of_isDomain (R := A ⧸ RingHom.ker φ) (S := B ⧸ Q) (F := F)
      hinjB hinjF
  refine ⟨ψ₀.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h1 : (Ideal.Quotient.mk Q) (algebraMap A B a) =
      algebraMap (A ⧸ RingHom.ker φ) (B ⧸ Q) (Ideal.Quotient.mk (RingHom.ker φ) a) := rfl
  have h2 := congrArg (fun f => f (Ideal.Quotient.mk (RingHom.ker φ) a)) hψ₀
  simp only [RingHom.coe_comp, Function.comp_apply] at h2 ⊢
  rw [h1, h2]
  rfl

end Rigidity.RET.Transfer
