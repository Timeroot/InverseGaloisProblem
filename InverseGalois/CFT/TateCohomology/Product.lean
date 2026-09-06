/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Junction
import InverseGalois.CFT.TateCohomology.Shifting

/-!
# The complete cohomology of a product of representations

A family of representations of one group, indexed by an arbitrary set, has a product on which the
group acts one factor at a time.  In degree zero the complete cohomology of the product is visibly
the product of the complete cohomologies: a family is invariant exactly when each of its members
is, and the norm of a family is the family of the norms, so an invariant family is a family of
norms exactly when each of its members is a norm.

Every other degree follows from that one by dimension shifting, and the shift can be carried out
without leaving the world of products.  A family of functions on the group is the same thing as a
function on the group with values in the product; under that identification a family of embeddings
into the functions on the group assembles into the single embedding of the product, and a family of
summation maps assembles into the single summation map of the product.  So the product sits in two
short exact sequences whose middle term is literally the functions on the group with values in the
product, whose complete cohomology vanishes in every degree, and whose remaining terms are again
products — of the shifts in one case, of the coshifts in the other.  The connecting maps of those
two sequences are therefore bijective, and running them in the two directions starting from degree
zero reaches every integer degree.

The point of the statement is arithmetic.  A module built place by place, such as the roots of
unity in every completion of a number field, is a product over the places of the base field of the
sections of a family over a single orbit, and the sections over an orbit are coinduced; so the
complete cohomology of such a module is a product of local contributions, one for each place of the
base field.

## Main definitions

* `InverseGalois.CFT.Tate.piRepresentation`, `InverseGalois.CFT.Tate.piRep`: **the product of a
  family of representations**, acting on each factor separately.
* `InverseGalois.CFT.Tate.piHom`: the map of products induced by a family of maps.
* `InverseGalois.CFT.Tate.piShiftSeq`, `InverseGalois.CFT.Tate.piCoshiftSeq`: the two short exact
  sequences that move the degree without leaving the world of products.

## Main results

* `InverseGalois.CFT.Tate.H0PiEquiv`: **the Tate group in degree zero of a product is the product
  of the Tate groups in degree zero.**
* `InverseGalois.CFT.Tate.tatePiShiftEquiv`, `InverseGalois.CFT.Tate.tatePiCoshiftEquiv`: the
  complete cohomology of the product of the shifts, and of the coshifts, moves the degree by one.
* `InverseGalois.CFT.Tate.tatePiEquiv`: **the complete cohomology of a product of representations
  is the product of their complete cohomologies, in every integer degree.**
* `InverseGalois.CFT.Tate.isZero_tateModule_piRep`: a family of representations without complete
  cohomology in a degree has a product without complete cohomology in that degree.

## Tags

Tate cohomology, product, dimension shifting, induced representation, local factor
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G ι : Type u} [CommRing k] [Group G]

/-! ### The product representation -/

section Construction

variable {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- **The product of a family of representations of a group**, acting on each factor
separately. -/
def piRepresentation (ρ : ∀ i, Representation k G (V i)) :
    Representation k G (∀ i, V i) where
  toFun g := LinearMap.pi fun i => (ρ i g).comp (LinearMap.proj i)
  map_one' := LinearMap.ext fun x => funext fun i => by
    show (ρ i) 1 (x i) = x i
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun x => funext fun i => by
    show (ρ i) (g * h) (x i) = (ρ i) g ((ρ i) h (x i))
    rw [map_mul]
    rfl

@[simp]
theorem piRepresentation_apply (ρ : ∀ i, Representation k G (V i)) (g : G) (x : ∀ i, V i)
    (i : ι) : piRepresentation ρ g x i = ρ i g (x i) := rfl

end Construction

/-- **The product of a family of representations.** -/
def piRep (A : ι → Rep k G) : Rep k G := Rep.of (piRepresentation fun i => (A i).ρ)

@[simp]
theorem piRep_ρ_apply (A : ι → Rep k G) (g : G) (x : ∀ i, ↥(A i).V) (i : ι) :
    (piRep A).ρ g x i = (A i).ρ g (x i) := rfl

/-- **The projection of the product onto a factor is equivariant.** -/
theorem proj_equivariant (A : ι → Rep k G) (i : ι) (g : G) :
    (LinearMap.proj i : (∀ j, ↥(A j).V) →ₗ[k] ↥(A i).V) ∘ₗ (piRep A).ρ g
      = (A i).ρ g ∘ₗ (LinearMap.proj i : (∀ j, ↥(A j).V) →ₗ[k] ↥(A i).V) :=
  LinearMap.ext fun _ => rfl

/-- **The projection of the product onto a factor.** -/
def piProj (A : ι → Rep k G) (i : ι) : piRep A ⟶ A i :=
  mkHom (LinearMap.proj i) (proj_equivariant A i)

/-- **A family is invariant exactly when each of its members is.** -/
theorem mem_invariants_piRep (A : ι → Rep k G) {x : ∀ i, ↥(A i).V} :
    x ∈ (piRep A).ρ.invariants ↔ ∀ i, x i ∈ (A i).ρ.invariants :=
  ⟨fun hx i g => congrFun (hx g) i, fun hx g => funext fun i => hx i g⟩

/-- **A family of maps of representations induces a map of the products.** -/
def piHom {A B : ι → Rep k G} (φ : ∀ i, A i ⟶ B i) : piRep A ⟶ piRep B :=
  mkHom (LinearMap.pi fun i => (φ i).hom.hom.comp (LinearMap.proj i))
    fun g => LinearMap.ext fun x => funext fun i =>
      LinearMap.congr_fun (hom_equivariant (φ i) g) (x i)

@[simp]
theorem piHom_apply {A B : ι → Rep k G} (φ : ∀ i, A i ⟶ B i) (x : ∀ i, ↥(A i).V) (i : ι) :
    (piHom φ).hom.hom x i = (φ i).hom.hom (x i) := rfl

/-! ### Swapping a family of functions on the group -/

section Swap

variable (A : ι → Rep k G)

/-- A function on the group with values in a product, read as a family of functions on the
group. -/
def indPiMap : (G → ∀ i, ↥(A i).V) →ₗ[k] ∀ i, G → ↥(A i).V where
  toFun f i x := f x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **A function on the group with values in a product is a family of functions on the group.** -/
def indPiHom : indObj (piRep A) ⟶ piRep fun i => indObj (A i) :=
  mkHom (indPiMap A) fun _ => LinearMap.ext fun _ => rfl

@[simp]
theorem indPiHom_apply (f : G → ∀ i, ↥(A i).V) (i : ι) (x : G) :
    (indPiHom A).hom.hom f i x = f x i := rfl

/-- A family of functions on the group, read as a function on the group with values in the
product. -/
def piIndMap : (∀ i, G → ↥(A i).V) →ₗ[k] G → ∀ i, ↥(A i).V where
  toFun u x i := u i x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **A family of functions on the group is a function on the group with values in the
product.** -/
def piIndHom : (piRep fun i => indObj (A i)) ⟶ indObj (piRep A) :=
  mkHom (piIndMap A) fun _ => LinearMap.ext fun _ => rfl

@[simp]
theorem piIndHom_apply (u : ∀ i, G → ↥(A i).V) (x : G) (i : ι) :
    (piIndHom A).hom.hom u x i = u i x := rfl

end Swap

/-! ### The sequence that raises the degree -/

section Raise

variable (A : ι → Rep k G)

/-- **The short exact sequence that raises the degree of a product**, in which a family is replaced
by the record of all of its translates. -/
def piShiftSeq : ShortComplex (Rep k G) where
  X₁ := piRep A
  X₂ := indObj (piRep A)
  X₃ := piRep fun i => shiftObj (A i)
  f := mkHom (coindEmb (piRep A).ρ) (coindEmb_equivariant _)
  g := indPiHom A ≫ piHom fun i => (shiftSeq (A i)).g
  zero := by
    ext v
    refine funext fun i => ?_
    show (LinearMap.range (coindEmb (A i).ρ)).mkQ (fun x => (A i).ρ x (v i)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨v i, rfl⟩

theorem piShiftSeq_shortExact : (piShiftSeq A).ShortExact := by
  refine shortExact_of_linearMap (coindEmb_injective (piRep A).ρ) ?_ ?_
  · intro y
    have h : ∀ i, ∃ z : G → ↥(A i).V,
        (LinearMap.range (coindEmb (A i).ρ)).mkQ z = y i := fun i =>
      Submodule.mkQ_surjective _ (y i)
    choose z hz using h
    refine ⟨fun x i => z i x, funext fun i => ?_⟩
    exact hz i
  · intro f hf
    have h : ∀ i, ∃ v : ↥(A i).V, coindEmb (A i).ρ v = fun x => f x i := by
      intro i
      have h0 : (LinearMap.range (coindEmb (A i).ρ)).mkQ (fun x => f x i) = 0 := congrFun hf i
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      exact h0
    choose v hv using h
    refine ⟨v, funext fun x => funext fun i => ?_⟩
    exact congrFun (hv i) x

end Raise

/-! ### Degree zero, and the sequence that lowers the degree -/

section Middle

variable [Finite G] (A : ι → Rep k G)

/-- **The norm of a family is the family of the norms.** -/
theorem normMap_piRep (x : ∀ i, ↥(A i).V) (i : ι) :
    normMap (piRep A).ρ x i = normMap (A i).ρ (x i) := by
  letI := Fintype.ofFinite G
  rw [normMap_apply, normMap_apply, Finset.sum_apply]
  rfl

/-- **The summation map of a family is the family of the summation maps.** -/
theorem augMap_piRep (f : G → ∀ i, ↥(A i).V) (i : ι) :
    augMap (piRep A).ρ f i = augMap (A i).ρ fun x => f x i := by
  letI := Fintype.ofFinite G
  rw [augMap_apply, augMap_apply, Finset.sum_apply]
  rfl

/-- The comparison of the Tate group in degree zero of a product with the Tate group in degree zero
of one of its factors. -/
def H0PiComp (i : ι) : H0 (piRep A).ρ →ₗ[k] H0 (A i).ρ :=
  H0map (LinearMap.proj i) (proj_equivariant A i)

theorem H0PiComp_H0mk (i : ι) (x : ↥(piRep A).ρ.invariants) :
    H0PiComp A i (H0mk (piRep A).ρ x) =
      H0mk (A i).ρ ⟨x.1 i, (mem_invariants_piRep A).1 x.2 i⟩ := rfl

/-- The comparison of the Tate group in degree zero of a product with the product of the Tate
groups in degree zero. -/
def H0PiMap : H0 (piRep A).ρ →ₗ[k] ∀ i, H0 (A i).ρ := LinearMap.pi (H0PiComp A)

theorem H0PiMap_apply (z : H0 (piRep A).ρ) (i : ι) : H0PiMap A z i = H0PiComp A i z := rfl

theorem H0PiMap_injective : Function.Injective (H0PiMap A) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := H0mk_surjective (piRep A).ρ z
  have h : ∀ i, ∃ v : ↥(A i).V, normMap (A i).ρ v = x.1 i := by
    intro i
    have h0 := congrFun hz i
    rw [H0PiMap_apply, H0PiComp_H0mk] at h0
    exact (H0mk_eq_zero_iff (A i).ρ _).1 h0
  choose v hv using h
  exact (H0mk_eq_zero_iff (piRep A).ρ x).2 ⟨v, funext fun i => (normMap_piRep A v i).trans (hv i)⟩

theorem H0PiMap_surjective : Function.Surjective (H0PiMap A) := by
  intro y
  have h : ∀ i, ∃ a : ↥(A i).ρ.invariants, H0mk (A i).ρ a = y i := fun i =>
    H0mk_surjective _ (y i)
  choose a ha using h
  have hinv : (fun i => (a i).1) ∈ (piRep A).ρ.invariants :=
    (mem_invariants_piRep A).2 fun i => (a i).2
  refine ⟨H0mk (piRep A).ρ ⟨fun i => (a i).1, hinv⟩, funext fun i => ?_⟩
  rw [H0PiMap_apply, H0PiComp_H0mk]
  exact ha i

/-- **The Tate group in degree zero of a product is the product of the Tate groups in degree
zero.** -/
def H0PiEquiv : H0 (piRep A).ρ ≃ₗ[k] ∀ i, H0 (A i).ρ :=
  LinearEquiv.ofBijective (H0PiMap A) ⟨H0PiMap_injective A, H0PiMap_surjective A⟩

/-- **The short exact sequence that lowers the degree of a product**, in which the values of a
family of functions are summed after undoing the translation. -/
def piCoshiftSeq : ShortComplex (Rep k G) where
  X₁ := piRep fun i => coshiftObj (A i)
  X₂ := indObj (piRep A)
  X₃ := piRep A
  f := (piHom fun i => (coshiftSeq (A i)).f) ≫ piIndHom A
  g := mkHom (augMap (piRep A).ρ) (augMap_comp_inducedRep _)
  zero := by
    ext u
    refine funext fun i => ?_
    show augMap (piRep A).ρ (fun x j => (u j).1 x) i = 0
    rw [augMap_piRep]
    exact (u i).2

theorem piCoshiftSeq_shortExact : (piCoshiftSeq A).ShortExact := by
  refine shortExact_of_linearMap ?_ (augMap_surjective (piRep A).ρ) ?_
  · intro u u' h
    refine funext fun i => Subtype.ext (funext fun x => ?_)
    exact congrFun (congrFun h x) i
  · intro f hf
    have h : ∀ i, augMap (A i).ρ (fun x => f x i) = 0 := by
      intro i
      have h0 : augMap (piRep A).ρ f i = 0 := congrFun hf i
      rwa [augMap_piRep] at h0
    refine ⟨fun i => ⟨fun x => f x i, h i⟩, ?_⟩
    exact funext fun x => funext fun i => rfl

end Middle

/-! ### The two degree shifts -/

section Shifts

variable [Finite G] (A : ι → Rep k G)

/-- **The complete cohomology of the product of the shifts in a degree is the complete cohomology
of the product in the following degree.** -/
def tatePiShiftEquiv (n : ℤ) :
    tateModule (piRep fun i => shiftObj (A i)) n ≃ₗ[k] tateModule (piRep A) (n + 1) :=
  LinearEquiv.ofBijective (tateδ (piShiftSeq_shortExact A) n).hom
    (bijective_tateδ (piShiftSeq_shortExact A) n
      (isZero_tateModule_indObj (piRep A) n) (isZero_tateModule_indObj (piRep A) (n + 1)))

/-- **The complete cohomology of a product in a degree is the complete cohomology of the product of
the coshifts in the following degree.** -/
def tatePiCoshiftEquiv (n : ℤ) :
    tateModule (piRep A) n ≃ₗ[k] tateModule (piRep fun i => coshiftObj (A i)) (n + 1) :=
  LinearEquiv.ofBijective (tateδ (piCoshiftSeq_shortExact A) n).hom
    (bijective_tateδ (piCoshiftSeq_shortExact A) n
      (isZero_tateModule_indObj (piRep A) n) (isZero_tateModule_indObj (piRep A) (n + 1)))

end Shifts

/-! ### Every degree -/

section Every

variable [Finite G]

/-- Moving the description of the complete cohomology of a product to an equal degree. -/
def piDegCongr (A : ι → Rep k G) {m n : ℤ} (h : m = n)
    (e : tateModule (piRep A) m ≃ₗ[k] ∀ i, tateModule (A i) m) :
    tateModule (piRep A) n ≃ₗ[k] ∀ i, tateModule (A i) n := by
  subst h; exact e

/-- The step that raises the degree by one. -/
def piStepUp (A : ι → Rep k G) (n : ℤ)
    (e : tateModule (piRep fun i => shiftObj (A i)) n ≃ₗ[k]
      ∀ i, tateModule (shiftObj (A i)) n) :
    tateModule (piRep A) (n + 1) ≃ₗ[k] ∀ i, tateModule (A i) (n + 1) :=
  ((tatePiShiftEquiv A n).symm.trans e).trans
    (LinearEquiv.piCongrRight fun i => tateShiftEquiv (A i) n)

/-- The step that lowers the degree by one. -/
def piStepDown (A : ι → Rep k G) (n : ℤ)
    (e : tateModule (piRep fun i => coshiftObj (A i)) (n + 1) ≃ₗ[k]
      ∀ i, tateModule (coshiftObj (A i)) (n + 1)) :
    tateModule (piRep A) n ≃ₗ[k] ∀ i, tateModule (A i) n :=
  ((tatePiCoshiftEquiv A n).trans e).trans
    (LinearEquiv.piCongrRight fun i => (tateCoshiftEquiv (A i) n).symm)

/-- The complete cohomology of a product in a nonnegative degree is the product of the complete
cohomologies. -/
def tatePiEquivNat : (m : ℕ) → (A : ι → Rep k G) →
    (tateModule (piRep A) (m : ℤ) ≃ₗ[k] ∀ i, tateModule (A i) (m : ℤ))
  | 0, A => piDegCongr A (m := (0 : ℤ)) (by norm_num) (H0PiEquiv A)
  | (m + 1), A =>
      piDegCongr A (m := (m : ℤ) + 1) (by push_cast; ring)
        (piStepUp A (m : ℤ) (tatePiEquivNat m fun i => shiftObj (A i)))

/-- The complete cohomology of a product in a negative degree is the product of the complete
cohomologies. -/
def tatePiEquivNeg : (m : ℕ) → (A : ι → Rep k G) →
    (tateModule (piRep A) (Int.negSucc m) ≃ₗ[k] ∀ i, tateModule (A i) (Int.negSucc m))
  | 0, A =>
      piStepDown A (Int.negSucc 0)
        (piDegCongr (fun i => coshiftObj (A i)) (m := ((0 : ℕ) : ℤ)) (by decide)
          (tatePiEquivNat 0 fun i => coshiftObj (A i)))
  | (m + 1), A =>
      piStepDown A (Int.negSucc (m + 1))
        (piDegCongr (fun i => coshiftObj (A i)) (m := Int.negSucc m)
          (by rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring)
          (tatePiEquivNeg m fun i => coshiftObj (A i)))

/-- **The complete cohomology of a product of representations is the product of their complete
cohomologies**, in every integer degree. -/
def tatePiEquiv (A : ι → Rep k G) :
    (n : ℤ) → (tateModule (piRep A) n ≃ₗ[k] ∀ i, tateModule (A i) n)
  | .ofNat m => tatePiEquivNat m A
  | .negSucc m => tatePiEquivNeg m A

/-- **A family of representations without complete cohomology in a degree has a product without
complete cohomology in that degree.** -/
theorem isZero_tateModule_piRep (A : ι → Rep k G) (n : ℤ)
    (h : ∀ i, Limits.IsZero (tateModule (A i) n)) :
    Limits.IsZero (tateModule (piRep A) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ i, Subsingleton ↥(tateModule (A i) n) := fun i =>
    ModuleCat.isZero_iff_subsingleton.1 (h i)
  exact (tatePiEquiv A n).injective.subsingleton

end Every

end

end InverseGalois.CFT.Tate
