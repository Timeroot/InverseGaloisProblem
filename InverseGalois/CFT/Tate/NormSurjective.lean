/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.H0Norm
import InverseGalois.CFT.Tate.Pi
import InverseGalois.CFT.Tate.Prod

/-!
# Recognising a norm

The zeroth Tate group is the fixed points modulo the norms, so it vanishes exactly when every fixed
point is a norm.  That reading turns every vanishing statement about the group into a statement
about individual elements, and conversely.

Being a norm is transported by an equivariant isomorphism, and in a product, of two factors or of a
whole family, an element is a norm as soon as each of its components is.  These are the steps by
which a global statement about the ideles is assembled from local ones, where the vanishing of the
Tate group is too strong to hold: at the places in a finite exceptional set only some of the local
elements are norms, and the assembly has to keep track of which.

## Main results

* `InverseGalois.CFT.subsingleton_tateH0_iff`: **the zeroth Tate group vanishes exactly when every
  fixed point is a norm.**
* `InverseGalois.CFT.exists_normHom_of_addEquiv`: **being a norm is transported by an equivariant
  isomorphism.**
* `InverseGalois.CFT.exists_normHom_prodAut`: an element of a product of two modules is a norm as
  soon as both of its components are.
* `InverseGalois.CFT.exists_normHom_piAut`: **an element of a product of a family of modules is a
  norm as soon as all of its components are.**

## Tags

Tate cohomology, norm, fixed point, product, equivariant isomorphism
-/

namespace InverseGalois.CFT

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-! ### Vanishing of the zeroth Tate group -/

/-- **The zeroth Tate group vanishes exactly when every fixed point is a norm**, that group being
the fixed points modulo the norms. -/
theorem subsingleton_tateH0_iff {σ : A ≃+ A} {n : ℕ} :
    Subsingleton (tateH0 σ n) ↔ ∀ x : A, σ x = x → ∃ y, normHom σ n y = x := by
  refine ⟨fun h x hx => exists_normHom_of_subsingleton x hx, fun h => ⟨fun a b => ?_⟩⟩
  obtain ⟨x, hx, rfl⟩ := tateH0.mk_surjective a
  obtain ⟨z, hz, rfl⟩ := tateH0.mk_surjective b
  rw [(tateH0.mk_eq_zero_iff x hx).mpr (h x hx), (tateH0.mk_eq_zero_iff z hz).mpr (h z hz)]

/-! ### Transport along an equivariant isomorphism -/

section Equiv

variable {σA : A ≃+ A} {σB : B ≃+ B}

/-- The inverse of an equivariant isomorphism is equivariant. -/
theorem symm_apply_of_equivariant (e : A ≃+ B) (he : ∀ a, e (σA a) = σB (e a)) (b : B) :
    e.symm (σB b) = σA (e.symm b) :=
  e.injective (by rw [e.apply_symm_apply, he, e.apply_symm_apply])

/-- **Being a norm is transported by an equivariant isomorphism.** -/
theorem exists_normHom_of_addEquiv (e : A ≃+ B) (he : ∀ a, e (σA a) = σB (e a)) (n : ℕ) {x : A}
    (h : ∃ y, normHom σB n y = e x) : ∃ y, normHom σA n y = x := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.symm y, ?_⟩
  have hmap := map_normHom e.symm.toAddMonoidHom (symm_apply_of_equivariant e he) n y
  rw [hy] at hmap
  simpa using hmap.symm

end Equiv

/-! ### Products -/

/-- An element of a product of two modules is a norm as soon as both of its components are. -/
theorem exists_normHom_prodAut (σ : A ≃+ A) (τ : B ≃+ B) (n : ℕ) {z : A × B}
    (h1 : ∃ y, normHom σ n y = z.1) (h2 : ∃ y, normHom τ n y = z.2) :
    ∃ y, normHom (prodAut σ τ) n y = z := by
  obtain ⟨y1, hy1⟩ := h1
  obtain ⟨y2, hy2⟩ := h2
  exact ⟨(y1, y2), by rw [normHom_prodAut, hy1, hy2]⟩

/-- **An element of a product of a family of modules is a norm as soon as all of its components
are.** -/
theorem exists_normHom_piAut {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    (σ : ∀ i, M i ≃+ M i) (n : ℕ) {x : ∀ i, M i} (h : ∀ i, ∃ y, normHom (σ i) n y = x i) :
    ∃ y, normHom (piAut σ) n y = x := by
  choose y hy using h
  exact ⟨y, funext fun i => by rw [normHom_piAut]; exact hy i⟩

end InverseGalois.CFT
