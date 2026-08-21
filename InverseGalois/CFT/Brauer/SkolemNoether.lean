import Mathlib
import InverseGalois.CFT.Brauer.TensorSimple

/-!
# The Skolem–Noether theorem

Let `K` be a field, `A` a finite-dimensional central simple `K`-algebra and `S` a
finite-dimensional simple `K`-algebra. This file proves that any two `K`-algebra homomorphisms
`f g : S →ₐ[K] A` differ by an inner automorphism of `A`.

The proof is the classical one. Put `B := S ⊗[K] Aᵐᵒᵖ`; it is a simple Artinian ring because
`Aᵐᵒᵖ` is central simple and `S` is simple. Each of `f` and `g` turns `A` into a `B`-module, with
`s ⊗ₜ op a` acting as `x ↦ f s * x * a` (respectively `x ↦ g s * x * a`). Over a simple Artinian
ring all simple modules are isomorphic, so every module is isotypic of one fixed type, and a
module of finite `K`-dimension is therefore determined up to isomorphism by that dimension. The
two `B`-modules built from `f` and `g` have the same `K`-dimension, namely `finrank K A`, so they
are isomorphic. A `B`-linear isomorphism between them is right multiplication by a unit `u` of
`A`, and `B`-linearity in the `S` factor says exactly that `g s * u = u * f s`.

## Main results

* `SkolemNoether.nonempty_linearEquiv_of_isSimpleModule`: over a simple Artinian ring, any two
  simple modules are isomorphic.
* `SkolemNoether.nonempty_linearEquiv_of_finrank_eq`: two modules over a finite-dimensional
  simple `K`-algebra which have the same finite `K`-dimension are isomorphic.
* `SkolemNoether.exists_conj`: the Skolem–Noether theorem.
* `SkolemNoether.exists_conj_of_algHom_self`: every `K`-algebra endomorphism of a
  finite-dimensional central simple `K`-algebra is inner.
-/

universe u v w

open scoped TensorProduct

open Module

namespace SkolemNoether

/-! ### Modules over a simple Artinian ring -/

section SimpleArtinian

variable (B : Type*) [Ring B] [IsSimpleRing B] [IsArtinianRing B]

/-- Over a simple Artinian ring any two simple modules are isomorphic. -/
theorem nonempty_linearEquiv_of_isSimpleModule (P : Type*) [AddCommGroup P] [Module B P]
    [IsSimpleModule B P] (Q : Type*) [AddCommGroup Q] [Module B Q] [IsSimpleModule B Q] :
    Nonempty (P ≃ₗ[B] Q) := by
  have hiso : IsIsotypic B (P × Q) := IsSimpleRing.isIsotypic B (P × Q)
  set m : Submodule B (P × Q) := LinearMap.range (LinearMap.inl B P Q) with hm
  have eP : P ≃ₗ[B] m := LinearEquiv.ofInjective _ (LinearMap.inl_injective (M := P) (M₂ := Q))
  haveI : IsSimpleModule B m := IsSimpleModule.congr eP.symm
  have h3 : IsIsotypicOfType B Q m :=
    (hiso m).of_injective (LinearMap.inr B P Q) (LinearMap.inr_injective (M := P) (M₂ := Q))
  haveI : IsSimpleModule B (⊤ : Submodule B Q) := IsSimpleModule.congr Submodule.topEquiv
  exact ⟨eP.trans ((h3 ⊤).some.symm.trans Submodule.topEquiv)⟩

/-- Over a simple Artinian ring every module is isotypic of type `P`, for any simple module
`P`. -/
theorem isIsotypicOfType_of_isSimpleModule (M : Type*) [AddCommGroup M] [Module B M]
    (P : Type*) [AddCommGroup P] [Module B P] [IsSimpleModule B P] :
    IsIsotypicOfType B M P :=
  fun m _ ↦ nonempty_linearEquiv_of_isSimpleModule B m P

end SimpleArtinian

section Counting

variable (K : Type u) [Field K] (B : Type*) [Ring B] [Algebra K B] [IsSimpleRing B]
  [FiniteDimensional K B]

/-- Two modules over a finite-dimensional simple algebra over a field which are
finite-dimensional of the same dimension over that field are isomorphic. -/
theorem nonempty_linearEquiv_of_finrank_eq
    (M : Type*) [AddCommGroup M] [Module K M] [Module B M] [IsScalarTower K B M]
    [FiniteDimensional K M]
    (N : Type*) [AddCommGroup N] [Module K N] [Module B N] [IsScalarTower K B N]
    [FiniteDimensional K N] (h : finrank K M = finrank K N) : Nonempty (M ≃ₗ[B] N) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨P, hP⟩ := IsAtomic.exists_atom (Submodule B B)
  haveI : IsSimpleModule B P := isSimpleModule_iff_isAtom.2 hP
  haveI : FiniteDimensional K P :=
    Module.Finite.of_injective (P.subtype.restrictScalars K) P.subtype_injective
  haveI : Module.Finite B M := Module.Finite.of_restrictScalars_finite K B M
  haveI : Module.Finite B N := Module.Finite.of_restrictScalars_finite K B N
  obtain ⟨n, ⟨eM⟩⟩ := (isIsotypicOfType_of_isSimpleModule B M P).linearEquiv_fun
  obtain ⟨n', ⟨eN⟩⟩ := (isIsotypicOfType_of_isSimpleModule B N P).linearEquiv_fun
  have hpi : ∀ k : ℕ, finrank K (Fin k → P) = k * finrank K P := by
    intro k
    rw [finrank_pi_fintype K (M := fun _ : Fin k ↦ P)]
    simp
  have hMn : finrank K M = n * finrank K P := by
    rw [(eM.restrictScalars K).finrank_eq, hpi]
  have hNn : finrank K N = n' * finrank K P := by
    rw [(eN.restrictScalars K).finrank_eq, hpi]
  have hpos : 0 < finrank K P := finrank_pos_iff.2 (IsSimpleModule.nontrivial B P)
  have hnn : n = n' := Nat.eq_of_mul_eq_mul_right hpos (by rw [← hMn, ← hNn, h])
  subst hnn
  exact ⟨eM.trans eN.symm⟩

end Counting

/-! ### The bimodule attached to an algebra homomorphism -/

section Bimod

variable {K : Type u} {A : Type v} {S : Type w}
variable [Field K] [Ring A] [Algebra K A] [Ring S] [Algebra K S]

/-- The action of `S ⊗[K] Aᵐᵒᵖ` on `A` determined by a `K`-algebra homomorphism
`f : S →ₐ[K] A`: the element `s ⊗ₜ op a` acts as `x ↦ f s * x * a`. -/
def toEnd (f : S →ₐ[K] A) : S ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  (AlgHom.mulLeftRight K A).comp (Algebra.TensorProduct.map f (AlgHom.id K Aᵐᵒᵖ))

@[simp]
theorem toEnd_tmul (f : S →ₐ[K] A) (s : S) (b : Aᵐᵒᵖ) (x : A) :
    toEnd f (s ⊗ₜ[K] b) x = f s * x * b.unop :=
  AlgHom.mulLeftRight_apply K A (f s) b x

/-- A copy of `A` carrying the `S ⊗[K] Aᵐᵒᵖ`-module structure attached to `f`. -/
def Bimod (_f : S →ₐ[K] A) : Type v := A

namespace Bimod

/-- The tautological bijection from `A` to `Bimod f`. -/
def mk (_f : S →ₐ[K] A) : A → Bimod _f := id

/-- The tautological bijection from `Bimod f` to `A`. -/
def val {f : S →ₐ[K] A} : Bimod f → A := id

@[simp] theorem val_mk (f : S →ₐ[K] A) (x : A) : val (mk f x) = x := rfl

@[simp] theorem mk_val {f : S →ₐ[K] A} (x : Bimod f) : mk f (val x) = x := rfl

instance (f : S →ₐ[K] A) : AddCommGroup (Bimod f) := inferInstanceAs (AddCommGroup A)

instance (f : S →ₐ[K] A) : Module K (Bimod f) := inferInstanceAs (Module K A)

instance (f : S →ₐ[K] A) [FiniteDimensional K A] : FiniteDimensional K (Bimod f) :=
  inferInstanceAs (FiniteDimensional K A)

noncomputable instance module (f : S →ₐ[K] A) : Module (S ⊗[K] Aᵐᵒᵖ) (Bimod f) :=
  letI : Module (Module.End K A) (Bimod f) := inferInstanceAs (Module (Module.End K A) A)
  Module.compHom (Bimod f) (toEnd f).toRingHom

theorem val_smul (f : S →ₐ[K] A) (b : S ⊗[K] Aᵐᵒᵖ) (x : Bimod f) :
    val (b • x) = toEnd f b (val x) := rfl

instance (f : S →ₐ[K] A) : IsScalarTower K (S ⊗[K] Aᵐᵒᵖ) (Bimod f) where
  smul_assoc k b x := by
    have : toEnd f (k • b) = k • toEnd f b := map_smul (toEnd f) k b
    have hv : val ((k • b) • x) = val (k • b • x) := by
      rw [val_smul, this]
      rfl
    exact hv

@[simp] theorem finrank_eq (f : S →ₐ[K] A) : finrank K (Bimod f) = finrank K A := rfl

end Bimod

end Bimod

/-! ### The theorem -/

section Main

variable {K : Type u} {A : Type v} {S : Type w}
variable [Field K] [Ring A] [Algebra K A] [Ring S] [Algebra K S]

open Bimod MulOpposite

variable {f g : S →ₐ[K] A}

/-- A `S ⊗[K] Aᵐᵒᵖ`-linear map out of `Bimod f` is right multiplication by the image of `1`. -/
theorem val_apply_eq (e : Bimod f →ₗ[S ⊗[K] Aᵐᵒᵖ] Bimod g) (x : A) :
    val (e (mk f x)) = val (e (mk f 1)) * x := by
  have hx : mk f x = ((1 : S) ⊗ₜ[K] op x) • mk f 1 := by
    have : val (((1 : S) ⊗ₜ[K] op x) • mk f 1) = x := by
      rw [val_smul, toEnd_tmul]
      simp
    exact congrArg (mk f) this.symm
  rw [hx, map_smul, val_smul, toEnd_tmul]
  simp

/-- The image of `f s` under a `S ⊗[K] Aᵐᵒᵖ`-linear map is `g s` times the image of `1`. -/
theorem val_apply_algHom (e : Bimod f →ₗ[S ⊗[K] Aᵐᵒᵖ] Bimod g) (s : S) :
    val (e (mk f (f s))) = g s * val (e (mk f 1)) := by
  have hs : mk f (f s) = (s ⊗ₜ[K] op (1 : A)) • mk f 1 := by
    have : val ((s ⊗ₜ[K] op (1 : A)) • mk f 1) = f s := by
      rw [val_smul, toEnd_tmul]
      simp
    exact congrArg (mk f) this.symm
  rw [hs, map_smul, val_smul, toEnd_tmul]
  simp

variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
variable [IsSimpleRing S] [FiniteDimensional K S]

omit [FiniteDimensional K A] [FiniteDimensional K S] in
/-- The enveloping algebra `S ⊗[K] Aᵐᵒᵖ` of the situation is a simple ring. -/
theorem isSimpleRing_tensor : IsSimpleRing (S ⊗[K] Aᵐᵒᵖ) :=
  IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm K Aᵐᵒᵖ S).toRingEquiv
    IsSimpleRing.tensorProduct_of_isCentral

/-- **Skolem–Noether**: two `K`-algebra homomorphisms from a finite-dimensional simple
`K`-algebra `S` to a finite-dimensional central simple `K`-algebra `A` are conjugate by a unit
of `A`. -/
theorem exists_conj (f g : S →ₐ[K] A) : ∃ u : Aˣ, ∀ s, g s = u * f s * (u⁻¹ : Aˣ) := by
  haveI : IsSimpleRing (S ⊗[K] Aᵐᵒᵖ) := isSimpleRing_tensor
  obtain ⟨e⟩ := nonempty_linearEquiv_of_finrank_eq K (S ⊗[K] Aᵐᵒᵖ) (Bimod f) (Bimod g) rfl
  set u : A := val (e (mk f 1)) with hu
  set w : A := val (e.symm (mk g 1)) with hw
  have he : ∀ x : A, val (e (mk f x)) = u * x := val_apply_eq e.toLinearMap
  have he' : ∀ y : A, val (e.symm (mk g y)) = w * y := val_apply_eq e.symm.toLinearMap
  have hg1 : mk g u = e (mk f 1) := mk_val _
  have hf1 : mk f w = e.symm (mk g 1) := mk_val _
  have hwu : w * u = 1 := by
    have h2 := he' u
    rw [hg1, e.symm_apply_apply] at h2
    simpa using h2.symm
  have huw : u * w = 1 := by
    have h2 := he w
    rw [hf1, e.apply_symm_apply] at h2
    simpa using h2.symm
  refine ⟨⟨u, w, huw, hwu⟩, fun s ↦ ?_⟩
  have hfs : u * f s = g s * u := by
    rw [← he (f s)]
    exact val_apply_algHom e.toLinearMap s
  show g s = u * f s * w
  rw [hfs, mul_assoc, huw, mul_one]

/-- Every `K`-algebra endomorphism of a finite-dimensional central simple `K`-algebra is
inner. -/
theorem exists_conj_of_algHom_self (f : A →ₐ[K] A) : ∃ u : Aˣ, ∀ a, f a = u * a * (u⁻¹ : Aˣ) := by
  obtain ⟨u, hu⟩ := exists_conj (AlgHom.id K A) f
  exact ⟨u, hu⟩

end Main

end SkolemNoether
