/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Recognising a regular wreath product among group extensions

A surjection `f : E →* U` whose kernel `K` carries a homomorphism `ev : K →* C` presents each
element of `K` by its family of *coordinates* `u ↦ ev (u⁻¹ • k)`, where `U` acts on `K` by
conjugation.  If that family runs bijectively over all of `U → C` then `E` is the regular wreath
product `C ≀ᵣ U`.

The coordinate map is automatically equivariant, so all that is at stake is that the extension
splits, and it does: writing the factor set of an arbitrary set-theoretic section `s` as
`c x y = s x * s y * (s (x * y))⁻¹`, the family `β x u = ev (c u⁻¹ x)` satisfies
`c x y = ρ x (β y) * β x * (β (x * y))⁻¹` in coordinates — the cocycle identity evaluated at the
single coordinate `1` already says so — and correcting `s` by `β` turns it into a homomorphism.
This is the explicit form of Shapiro's lemma for a group of functions on `U`.

## Main results

* `RegularWreathProduct.quotientConj` — the conjugation action of the quotient on an abelian
  normal subgroup.
* `RegularWreathProduct.nonempty_mulEquiv_of_bijective_coord` — the recognition theorem.
* `RegularWreathProduct.nonempty_mulEquiv_of_equivariant` — its usable form, from an equivariant
  isomorphism of the kernel with the functions on the quotient.
-/

namespace RegularWreathProduct

section Recognition

variable {E U C : Type*} [Group E] [Group U] [CommGroup C]

/-- **Conjugation as an action of the quotient.**

Conjugation of the ambient group on a commutative normal subgroup is trivial on that subgroup
itself, so it descends to the quotient. -/
noncomputable def quotientConj (f : E →* U) (hf : Function.Surjective f)
    [IsMulCommutative ↥f.ker] : U →* MulAut ↥f.ker :=
  f.liftOfSurjective hf ⟨MulAut.conjNormal, by
    intro x hx
    refine MonoidHom.mem_ker.mpr (MulEquiv.ext fun k ↦ Subtype.ext ?_)
    rw [MulAut.conjNormal_apply]
    have hxk : x * (k : E) = (k : E) * x :=
      Subgroup.mul_comm_of_mem_isMulCommutative f.ker hx k.2
    rw [hxk, MulAut.one_apply]
    group⟩

@[simp]
theorem quotientConj_apply (f : E →* U) (hf : Function.Surjective f) [IsMulCommutative ↥f.ker]
    (x : E) (k : ↥f.ker) : ((quotientConj f hf (f x) k : ↥f.ker) : E) = x * k * x⁻¹ := by
  rw [quotientConj, MonoidHom.liftOfRightInverse_comp_apply]
  exact MulAut.conjNormal_apply x k

/-- **A group extension with coinduced kernel is a regular wreath product.**

The hypothesis is that the coordinates `u ↦ ev (ρ u⁻¹ k)` of an element `k` of the kernel exhaust
the functions `U → C` exactly once. -/
theorem nonempty_mulEquiv_of_bijective_coord (f : E →* U) (hf : Function.Surjective f)
    (ρ : U →* MulAut ↥f.ker)
    (hρ : ∀ (x : E) (k : ↥f.ker), ((ρ (f x) k : ↥f.ker) : E) = x * k * x⁻¹)
    (ev : ↥f.ker →* C)
    (hbij : Function.Bijective fun (k : ↥f.ker) (u : U) ↦ ev (ρ u⁻¹ k)) :
    Nonempty (E ≃* C ≀ᵣ U) := by
  classical
  -- The coordinate map, as a homomorphism.
  set coord : ↥f.ker →* (U → C) :=
    { toFun := fun k u ↦ ev (ρ u⁻¹ k)
      map_one' := by ext u; simp
      map_mul' := fun k l ↦ by ext u; simp } with hcoord
  set κ : ↥f.ker ≃* (U → C) := MulEquiv.ofBijective coord hbij with hκ
  have hκa : ∀ (k : ↥f.ker) (u : U), κ k u = ev (ρ u⁻¹ k) := fun _ _ ↦ rfl
  -- Coordinates turn the conjugation action into translation.
  have hκρ : ∀ (x : U) (k : ↥f.ker) (u : U), κ (ρ x k) u = κ k (x⁻¹ * u) := by
    intro x k u
    rw [hκa, hκa, ← MulAut.mul_apply, ← map_mul, mul_inv_rev, inv_inv]
  -- A set-theoretic section and its factor set.
  set s : U → E := Function.surjInv hf with hsdef
  have hs : ∀ u, f (s u) = u := fun u ↦ Function.surjInv_eq hf u
  have hρ' : ∀ (u : U) (k : ↥f.ker), ((ρ u k : ↥f.ker) : E) = s u * k * (s u)⁻¹ := by
    intro u k
    have := hρ (s u) k
    rwa [hs u] at this
  set c : U → U → ↥f.ker := fun x y ↦
    ⟨s x * s y * (s (x * y))⁻¹, by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]⟩ with hcdef
  have hc : ∀ x y, ((c x y : ↥f.ker) : E) = s x * s y * (s (x * y))⁻¹ := fun _ _ ↦ rfl
  -- The factor set is a two-cocycle.
  have hcocycle : ∀ x y z : U, ρ x (c y z) * c x (y * z) = c x y * c (x * y) z := by
    intro x y z
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, hρ', hc]
    rw [mul_assoc x y z]
    group
  -- The correcting family, and the cocycle identity read off at the coordinate `1`.
  set β : U → (U → C) := fun x u ↦ ev (c u⁻¹ x) with hβdef
  have hkey : ∀ x y u : U, κ (c x y) u = β y (x⁻¹ * u) * β x u * (β (x * y) u)⁻¹ := by
    intro x y u
    have h := congrArg ev (hcocycle u⁻¹ x y)
    rw [map_mul, map_mul] at h
    have h1 : ev (ρ u⁻¹ (c x y)) = κ (c x y) u := (hκa _ _).symm
    have h2 : ev (c u⁻¹ (x * y)) = β (x * y) u := rfl
    have h3 : ev (c u⁻¹ x) = β x u := rfl
    have h4 : ev (c (u⁻¹ * x) y) = β y (x⁻¹ * u) := by
      rw [hβdef]
      simp only [mul_inv_rev, inv_inv]
    rw [h1, h2, h3, h4] at h
    rw [eq_comm, mul_inv_eq_iff_eq_mul, h]
    exact mul_comm _ _
  set βh : U → ↥f.ker := fun x ↦ κ.symm (β x) with hβh
  have hβhκ : ∀ x, κ (βh x) = β x := fun x ↦ κ.apply_symm_apply (β x)
  have hcβ : ∀ x y : U, c x y = ρ x (βh y) * βh x * (βh (x * y))⁻¹ := by
    intro x y
    refine κ.injective ?_
    ext u
    rw [map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, hκρ, hβhκ, hβhκ,
      hβhκ, hkey]
  -- The corrected section is a homomorphism.
  set t : U →* E := MonoidHom.mk' (fun x ↦ ((βh x : E))⁻¹ * s x) (by
    intro x y
    have hmove : s x * ((βh y : E))⁻¹ = ((ρ x (βh y) : ↥f.ker) : E)⁻¹ * s x := by
      rw [hρ']
      group
    have hstep : (s x : E) * s y = ((c x y : ↥f.ker) : E) * s (x * y) := by
      rw [hc]; group
    show ((βh (x * y) : E))⁻¹ * s (x * y)
      = ((βh x : E))⁻¹ * s x * (((βh y : E))⁻¹ * s y)
    symm
    calc ((βh x : E))⁻¹ * s x * (((βh y : E))⁻¹ * s y)
        = ((βh x : E))⁻¹ * (s x * ((βh y : E))⁻¹) * s y := by group
      _ = ((βh x : E))⁻¹ * ((ρ x (βh y) : ↥f.ker) : E)⁻¹ * (s x * s y) := by
          rw [hmove]; group
      _ = ((βh x : E))⁻¹ * ((ρ x (βh y) : ↥f.ker) : E)⁻¹ *
            (((c x y : ↥f.ker) : E) * s (x * y)) := by rw [hstep]
      _ = ((βh (x * y) : E))⁻¹ * s (x * y) := by
          rw [hcβ x y]
          push_cast
          group) with ht
  have hta : ∀ x, t x = ((βh x : E))⁻¹ * s x := fun _ ↦ rfl
  have hft : ∀ x, f (t x) = x := by
    intro x
    rw [hta, map_mul, map_inv, MonoidHom.mem_ker.mp (βh x).2, hs, inv_one, one_mul]
  -- Conjugation by the section is the action.
  have hρt : ∀ (x : U) (k : ↥f.ker), ((ρ x k : ↥f.ker) : E) = t x * k * (t x)⁻¹ := by
    intro x k
    have := hρ (t x) k
    rwa [hft x] at this
  -- The kernel part of an element, relative to the corrected section.
  have hmemk : ∀ e : E, e * (t (f e))⁻¹ ∈ f.ker := by
    intro e
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hft, mul_inv_cancel]
  set kpart : E → ↥f.ker := fun e ↦ ⟨e * (t (f e))⁻¹, hmemk e⟩ with hkpart
  have hkp : ∀ e : E, ((kpart e : ↥f.ker) : E) = e * (t (f e))⁻¹ := fun _ ↦ rfl
  have hkmul : ∀ e₁ e₂ : E, kpart (e₁ * e₂) = kpart e₁ * ρ (f e₁) (kpart e₂) := by
    intro e₁ e₂
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, hρt, hkp, hkp, hkp]
    simp only [map_mul]
    group
  set Φ : E →* C ≀ᵣ U :=
    { toFun := fun e ↦ ⟨κ (kpart e), f e⟩
      map_one' := by
        refine RegularWreathProduct.ext ?_ ?_
        · show κ (kpart 1) = 1
          have : kpart 1 = 1 := by
            refine Subtype.ext ?_
            rw [hkp]
            simp
          rw [this, map_one]
        · exact map_one f
      map_mul' := fun e₁ e₂ ↦ by
        refine RegularWreathProduct.ext ?_ ?_
        · show κ (kpart (e₁ * e₂)) = κ (kpart e₁) * fun u ↦ κ (kpart e₂) ((f e₁)⁻¹ * u)
          rw [hkmul, map_mul]
          ext u
          rw [Pi.mul_apply, Pi.mul_apply, hκρ]
        · exact map_mul f e₁ e₂ } with hΦ
  have hΦa : ∀ e : E, Φ e = ⟨κ (kpart e), f e⟩ := fun _ ↦ rfl
  refine ⟨MulEquiv.ofBijective Φ ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro e he
    have h1 : f e = 1 := congrArg RegularWreathProduct.right he
    have h2 : κ (kpart e) = 1 := congrArg RegularWreathProduct.left he
    have h3 : kpart e = 1 := κ.injective (by rw [h2, map_one])
    have h4 : e * (t (f e))⁻¹ = 1 := congrArg Subtype.val h3
    rw [h1, map_one, inv_one, mul_one] at h4
    exact h4
  · rintro ⟨a, x⟩
    refine ⟨((κ.symm a : ↥f.ker) : E) * t x, ?_⟩
    have hfe : f (((κ.symm a : ↥f.ker) : E) * t x) = x := by
      rw [map_mul, MonoidHom.mem_ker.mp (κ.symm a).2, hft, one_mul]
    refine RegularWreathProduct.ext ?_ hfe
    show κ (kpart _) = a
    have : kpart (((κ.symm a : ↥f.ker) : E) * t x) = κ.symm a := by
      refine Subtype.ext ?_
      rw [hkp, hfe]
      group
    rw [this, κ.apply_symm_apply]

/-- **A group extension whose kernel is a group of functions on the quotient, with the quotient
acting by translation, is a regular wreath product.**

This is the form in which the recognition theorem is used: an isomorphism of the kernel with
`U → C` carrying conjugation to translation.  Evaluating at the coordinate `1` recovers the
hypothesis of `nonempty_mulEquiv_of_bijective_coord`, because equivariance says that the coordinate
family of `k` is exactly the function `e k`. -/
theorem nonempty_mulEquiv_of_equivariant (f : E →* U) (hf : Function.Surjective f)
    (ρ : U →* MulAut ↥f.ker)
    (hρ : ∀ (x : E) (k : ↥f.ker), ((ρ (f x) k : ↥f.ker) : E) = x * k * x⁻¹)
    (e : ↥f.ker ≃* (U → C)) (he : ∀ (x : U) (k : ↥f.ker) (u : U), e (ρ x k) u = e k (x⁻¹ * u)) :
    Nonempty (E ≃* C ≀ᵣ U) := by
  refine nonempty_mulEquiv_of_bijective_coord f hf ρ hρ
    ((Pi.evalMonoidHom (fun _ : U ↦ C) 1).comp e.toMonoidHom) ?_
  have hfun : (fun (k : ↥f.ker) (u : U) ↦
      ((Pi.evalMonoidHom (fun _ : U ↦ C) 1).comp e.toMonoidHom) (ρ u⁻¹ k)) = ⇑e := by
    funext k u
    show e (ρ u⁻¹ k) 1 = e k u
    rw [he, inv_inv, mul_one]
  rw [hfun]
  exact e.bijective

end Recognition

end RegularWreathProduct
