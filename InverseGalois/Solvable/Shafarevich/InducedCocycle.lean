/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The homomorphism to a semidirect product induced by a character of a normal subgroup

Let `φ : G →* U` be a homomorphism onto a group, let `V` be an abelian group and let `χ` be a
homomorphism from the kernel of `φ` to `V`.  Choosing a set-theoretic section `r` of `φ` produces
from these data a homomorphism from `G` to the semidirect product of `U` with the functions from `U`
to `V`, lying over `φ`: the coordinate at `u` of the value at `x` is the value of `χ` at the twisted
argument `r u⁻¹ * x * r ((φ x)⁻¹ * u)`, which lies in the kernel of `φ` because `φ` sends it to
`u⁻¹ * φ x * (φ x)⁻¹ * u`.

This is the concrete form of Shapiro's lemma in degree one, and it is what turns an arithmetic
problem over a subfield into a solution of an embedding problem over the base field.  A character of
the Galois group of the subfield — in the situation of Shafarevich's theorem, the Kummer character
of a radical — becomes a homomorphism of the Galois group of the base field onto a group of
functions on `U` extended by `U`, and the surjectivity is exactly the independence of the `|U|`
conjugates of the character.

When `U` is finite and `V` carries an action of `U`, the group of functions maps onto `V` by summing
the translates of the coordinates.  That map is equivariant and onto, so the homomorphism built here
maps onto any semidirect product of `U` with `V`, and it is through that map that the construction
reaches the groups an embedding problem actually names.

Nothing here is topological: what makes the result a *smooth* homomorphism is that an open normal
subgroup on which `φ` and `χ` are both trivial lies in the kernel, and that is recorded as a
statement about kernels alone.

## Main definitions

* `InverseGalois.Shafarevich.cocycleArg` — the twisted argument.
* `InverseGalois.Shafarevich.shiftAut` — the translation action of a group on its functions.
* `InverseGalois.Shafarevich.inducedCocycle` — the induced one cocycle.
* `InverseGalois.Shafarevich.inducedHom` — **the induced homomorphism to the semidirect product**.
* `InverseGalois.Shafarevich.inducedNorm` — the restriction of the cocycle to the kernel of `φ`,
  a homomorphism there whose coordinates are the conjugates of the character.
* `InverseGalois.Shafarevich.inducedCharKer` — the kernel of the character, read as a subgroup of
  the whole group.
* `InverseGalois.Shafarevich.shiftCounit` — the sum of the translates of the coordinates.

## Main results

* `InverseGalois.Shafarevich.inducedCocycle_mul` — **the induced cochain is a one cocycle.**
* `InverseGalois.Shafarevich.rightHom_inducedHom` — the induced homomorphism lies over `φ`.
* `InverseGalois.Shafarevich.inducedHom_surjective` — **it is onto as soon as the restriction of the
  cocycle to the kernel is.**
* `InverseGalois.Shafarevich.inducedHom_eq_one` — it kills an element of the kernel of `φ` all of
  whose translates the character kills.
* `InverseGalois.Shafarevich.shiftCounitMap_surjective` — **the group of functions maps onto any
  group carrying an action of `U`,** compatibly with the two semidirect products.

## Tags

Shapiro's lemma, induced module, semidirect product, embedding problem, Shafarevich's theorem
-/

namespace InverseGalois.Shafarevich

open scoped BigOperators

/-! ### The twisted argument -/

section Arg

variable {G U : Type*} [Group G] [Group U] (φ : G →* U) (r : U → G)

/-- The element whose value under the character the coordinate `u` of the induced cocycle reads. -/
def cocycleArg (x : G) (u : U) : G := (r u)⁻¹ * x * r ((φ x)⁻¹ * u)

/-- The twisted argument lies in the kernel of `φ`: the section contributes `u⁻¹` on the left and
`(φ x)⁻¹ * u` on the right, and what is between them is `φ x`. -/
theorem cocycleArg_mem (hr : ∀ u, φ (r u) = u) (x : G) (u : U) : cocycleArg φ r x u ∈ φ.ker := by
  simp only [MonoidHom.mem_ker, cocycleArg, _root_.map_mul, _root_.map_inv, hr]
  group

/-- Multiplying the twisted arguments of `x` at `u` and of `y` at `(φ x)⁻¹ * u` gives the twisted
argument of `x * y` at `u`, the two inner copies of the section cancelling. -/
theorem cocycleArg_mul (x y : G) (u : U) :
    cocycleArg φ r x u * cocycleArg φ r y ((φ x)⁻¹ * u) = cocycleArg φ r (x * y) u := by
  simp only [cocycleArg, _root_.map_mul, mul_inv_rev, mul_assoc]
  group

/-- At an element of the kernel the twisted argument is a plain conjugate. -/
theorem cocycleArg_of_mem_ker {x : G} (hx : φ x = 1) (u : U) :
    cocycleArg φ r x u = (r u)⁻¹ * x * r u := by
  rw [cocycleArg, hx, inv_one, one_mul]

end Arg

/-! ### Translating the functions on a group -/

section Shift

variable {U V : Type*} [Group U] [CommGroup V]

/-- Translation of the functions on a group by one of its elements. -/
def shiftEquiv (u : U) : (U → V) ≃* (U → V) where
  toFun f u' := f (u⁻¹ * u')
  invFun f u' := f (u * u')
  left_inv _ := funext fun u' => congrArg _ (inv_mul_cancel_left u u')
  right_inv _ := funext fun u' => congrArg _ (mul_inv_cancel_left u u')
  map_mul' _ _ := rfl

@[simp]
theorem shiftEquiv_apply (u : U) (f : U → V) (u' : U) : shiftEquiv u f u' = f (u⁻¹ * u') := rfl

variable (U V)

/-- **The translation action of a group on the group of functions on it**, which is the action
carried by a module induced from the trivial subgroup. -/
def shiftAut : U →* MulAut (U → V) where
  toFun := shiftEquiv
  map_one' := MulEquiv.ext fun f => funext fun u' => by
    rw [shiftEquiv_apply, inv_one, one_mul]
    rfl
  map_mul' u v := MulEquiv.ext fun f => funext fun u' => by
    rw [MulAut.mul_apply, shiftEquiv_apply, shiftEquiv_apply, shiftEquiv_apply]
    group

@[simp]
theorem shiftAut_apply (u : U) (f : U → V) (u' : U) : shiftAut U V u f u' = f (u⁻¹ * u') := rfl

end Shift

/-! ### The induced cocycle -/

section Induced

variable {G U V : Type*} [Group G] [Group U] [CommGroup V] (φ : G →* U) (r : U → G)
  (χ : ↥φ.ker →* V)

/-- **The one cocycle induced by a character of the kernel.**  Its coordinate at `u` is the value of
the character at the twisted argument there. -/
def inducedCocycle (hr : ∀ u, φ (r u) = u) (x : G) : U → V :=
  fun u => χ ⟨cocycleArg φ r x u, cocycleArg_mem φ r hr x u⟩

@[simp]
theorem inducedCocycle_apply (hr : ∀ u, φ (r u) = u) (x : G) (u : U) :
    inducedCocycle φ r χ hr x u = χ ⟨cocycleArg φ r x u, cocycleArg_mem φ r hr x u⟩ := rfl

/-- The coordinate of the induced cocycle at an element of the kernel is the value of the character
at a conjugate. -/
theorem inducedCocycle_apply_of_mem_ker (hr : ∀ u, φ (r u) = u) {x : G} (hx : φ x = 1) (u : U)
    (hmem : (r u)⁻¹ * x * r u ∈ φ.ker) :
    inducedCocycle φ r χ hr x u = χ ⟨(r u)⁻¹ * x * r u, hmem⟩ :=
  congrArg χ (Subtype.ext (cocycleArg_of_mem_ker φ r hx u))

/-- **The induced cochain is a one cocycle.**  Translating the value at `y` by `φ x` shifts its
coordinates, and at each coordinate the two factors are the values of the character at two elements
whose product is the twisted argument of `x * y`. -/
theorem inducedCocycle_mul (hr : ∀ u, φ (r u) = u) (x y : G) :
    inducedCocycle φ r χ hr (x * y)
      = inducedCocycle φ r χ hr x * shiftAut U V (φ x) (inducedCocycle φ r χ hr y) := by
  funext u
  rw [Pi.mul_apply, shiftAut_apply, inducedCocycle_apply, inducedCocycle_apply,
    inducedCocycle_apply, ← _root_.map_mul χ]
  refine congrArg χ (Subtype.ext ?_)
  rw [Subgroup.coe_mul]
  exact (cocycleArg_mul φ r x y u).symm

/-! ### The induced homomorphism -/

/-- **The homomorphism to the semidirect product induced by a character of the kernel.** -/
def inducedHom (hr : ∀ u, φ (r u) = u) : G →* (U → V) ⋊[shiftAut U V] U :=
  MonoidHom.mk' (fun x => ⟨inducedCocycle φ r χ hr x, φ x⟩) fun x y =>
    SemidirectProduct.ext (inducedCocycle_mul φ r χ hr x y) (_root_.map_mul φ x y)

@[simp]
theorem inducedHom_apply (hr : ∀ u, φ (r u) = u) (x : G) :
    inducedHom φ r χ hr x = ⟨inducedCocycle φ r χ hr x, φ x⟩ := rfl

/-- The induced homomorphism lies over `φ`. -/
theorem rightHom_inducedHom (hr : ∀ u, φ (r u) = u) (x : G) :
    SemidirectProduct.rightHom (inducedHom φ r χ hr x) = φ x := rfl

/-! ### The restriction to the kernel -/

/-- The restriction of the induced cocycle to the kernel of `φ`, where it is a homomorphism.  Its
coordinates are the conjugates of the character by the chosen representatives. -/
def inducedNorm (hr : ∀ u, φ (r u) = u) : ↥φ.ker →* (U → V) :=
  MonoidHom.mk' (fun h => inducedCocycle φ r χ hr (h : G)) fun h h' => by
    show inducedCocycle φ r χ hr ((h * h' : ↥φ.ker) : G) = _
    rw [Subgroup.coe_mul, inducedCocycle_mul, MonoidHom.mem_ker.1 h.2, _root_.map_one]
    rfl

theorem inducedNorm_apply (hr : ∀ u, φ (r u) = u) (h : ↥φ.ker) :
    inducedNorm φ r χ hr h = inducedCocycle φ r χ hr (h : G) := rfl

/-- **The induced homomorphism is onto as soon as its restriction to the kernel is.**  An element of
the semidirect product is the product of one coming from the kernel, which the restriction reaches,
and the value at the chosen representative of its second coordinate. -/
theorem inducedHom_surjective (hr : ∀ u, φ (r u) = u)
    (hnorm : Function.Surjective (inducedNorm φ r χ hr)) :
    Function.Surjective (inducedHom φ r χ hr) := by
  rintro ⟨a, g⟩
  obtain ⟨h, hh⟩ := hnorm (a * (inducedCocycle φ r χ hr (r g))⁻¹)
  refine ⟨(h : G) * r g, ?_⟩
  rw [_root_.map_mul]
  refine SemidirectProduct.ext ?_ ?_
  · show inducedCocycle φ r χ hr (h : G) * shiftAut U V (φ (h : G))
      (inducedCocycle φ r χ hr (r g)) = a
    rw [MonoidHom.mem_ker.1 h.2, _root_.map_one]
    show inducedCocycle φ r χ hr (h : G) * inducedCocycle φ r χ hr (r g) = a
    rw [← inducedNorm_apply, hh, inv_mul_cancel_right]
  · show φ (h : G) * φ (r g) = g
    rw [MonoidHom.mem_ker.1 h.2, one_mul, hr]

/-! ### Where the induced homomorphism is trivial -/

/-- The kernel of the character, read as a subgroup of the whole group. -/
def inducedCharKer : Subgroup G := χ.ker.map φ.ker.subtype

theorem mem_inducedCharKer {x : G} :
    x ∈ inducedCharKer φ χ ↔ ∃ h : x ∈ φ.ker, χ ⟨x, h⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

/-- **The induced homomorphism kills an element of the kernel of `φ` all of whose translates by the
section the character kills.** -/
theorem inducedHom_eq_one (hr : ∀ u, φ (r u) = u) {x : G} (hx : φ x = 1)
    (h : ∀ u : U, (r u)⁻¹ * x * r u ∈ inducedCharKer φ χ) : inducedHom φ r χ hr x = 1 := by
  refine SemidirectProduct.ext ?_ hx
  funext u
  obtain ⟨hmem, hker⟩ := (mem_inducedCharKer φ χ).1 (h u)
  show inducedCocycle φ r χ hr x u = (1 : U → V) u
  rw [inducedCocycle_apply_of_mem_ker φ r χ hr hx u hmem, hker]
  rfl

/-- **An open normal subgroup on which both `φ` and the character are trivial lies in the kernel of
the induced homomorphism**, which is what makes the latter smooth. -/
theorem le_ker_inducedHom (hr : ∀ u, φ (r u) = u) {W : Subgroup G} [W.Normal]
    (h1 : W ≤ φ.ker) (h2 : W ≤ inducedCharKer φ χ) : W ≤ (inducedHom φ r χ hr).ker := by
  intro x hx
  exact MonoidHom.mem_ker.2 (inducedHom_eq_one φ r χ hr (MonoidHom.mem_ker.1 (h1 hx))
    fun u => h2 (Subgroup.Normal.conj_mem' ‹W.Normal› x hx (r u)))

end Induced

/-! ### Summing the translates -/

section Counit

variable {U V : Type*} [Group U] [Fintype U] [CommGroup V] (ρ : U →* MulAut V)

/-- **The sum of the translates of the coordinates**, a homomorphism from the functions on a group
to any abelian group the group acts on. -/
def shiftCounit : (U → V) →* V where
  toFun f := ∏ u : U, ρ u (f u)
  map_one' := by simp
  map_mul' _ _ := by simp [Finset.prod_mul_distrib]

@[simp]
theorem shiftCounit_apply (f : U → V) : shiftCounit ρ f = ∏ u : U, ρ u (f u) := rfl

/-- Summing the translates is equivariant for the translation action on the functions. -/
theorem shiftCounit_shiftAut (u₀ : U) (f : U → V) :
    shiftCounit ρ (shiftAut U V u₀ f) = ρ u₀ (shiftCounit ρ f) := by
  rw [shiftCounit_apply, shiftCounit_apply, _root_.map_prod,
    ← Equiv.prod_comp (Equiv.mulLeft u₀) fun u : U => ρ u (shiftAut U V u₀ f u)]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [Equiv.coe_mulLeft, shiftAut_apply, inv_mul_cancel_left, _root_.map_mul, MulAut.mul_apply]

/-- Summing the translates is onto: a function supported at the identity has the sum it is given
there. -/
theorem shiftCounit_surjective : Function.Surjective (shiftCounit ρ) := by
  classical
  intro v
  refine ⟨Pi.mulSingle 1 v, ?_⟩
  rw [shiftCounit_apply, Finset.prod_eq_single (1 : U)]
  · rw [Pi.mulSingle_eq_same, _root_.map_one]
    rfl
  · intro u _ hu
    rw [Pi.mulSingle_eq_of_ne hu, _root_.map_one]
  · intro h
    exact absurd (Finset.mem_univ (1 : U)) h

/-- The map of semidirect products that summing the translates induces. -/
def shiftCounitMap : (U → V) ⋊[shiftAut U V] U →* V ⋊[ρ] U :=
  SemidirectProduct.map (shiftCounit ρ) (MonoidHom.id U) fun u =>
    MonoidHom.ext fun f => shiftCounit_shiftAut ρ u f

@[simp]
theorem shiftCounitMap_apply (x : (U → V) ⋊[shiftAut U V] U) :
    shiftCounitMap ρ x = ⟨shiftCounit ρ x.left, x.right⟩ := rfl

/-- The map of semidirect products lies over the identity. -/
theorem rightHom_shiftCounitMap (x : (U → V) ⋊[shiftAut U V] U) :
    SemidirectProduct.rightHom (shiftCounitMap ρ x) = SemidirectProduct.rightHom x := rfl

/-- **The group of functions maps onto any group carrying an action of `U`,** compatibly with the
two semidirect products. -/
theorem shiftCounitMap_surjective : Function.Surjective (shiftCounitMap ρ) := by
  rintro ⟨v, u⟩
  obtain ⟨f, hf⟩ := shiftCounit_surjective ρ v
  exact ⟨⟨f, u⟩, SemidirectProduct.ext hf rfl⟩

end Counit

end InverseGalois.Shafarevich
