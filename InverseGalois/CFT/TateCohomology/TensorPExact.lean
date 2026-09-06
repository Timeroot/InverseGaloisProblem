/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TensorPTorsion

/-!
# Tensoring a short exact sequence with coefficients killed by a prime

Tensoring preserves surjectivity and exactness in the middle whatever the coefficients are; what it
does not preserve is injectivity, and a short exact sequence tensored with coefficients that are
not flat need not stay short exact.  Over the integers, with coefficients killed by a prime, the
failure is confined to that one place and it can be removed by hand.

The observation is that a module killed by a prime is a vector space over the field with that many
elements, so a submodule of it is a direct summand: an injection into a module killed by a prime
has a retraction, additive but not equivariant, and a retraction is all that is needed to keep the
injection injective after tensoring.  For a general injection the same argument applies to its
reduction modulo the prime, because tensoring with coefficients killed by a prime does not see the
difference between a module and its reduction.

So a short exact sequence of representations over the integers stays short exact after tensoring
with coefficients killed by a prime as soon as its first map stays injective modulo that prime.
Two cases are recorded: the one where the middle term is itself killed by the prime, where nothing
has to be checked, and the general one.

## Main definitions

* `InverseGalois.CFT.Tate.modNsmulHom`: a map of representations, reduced modulo a natural number.

## Main results

* `InverseGalois.CFT.Tate.exists_addMonoidHom_leftInverse`: **an injection into a module killed by
  a prime has a retraction.**
* `InverseGalois.CFT.Tate.injective_tensorHomLeft_of_nsmul`: **a map into a representation killed
  by a prime stays injective after tensoring** with any representation.
* `InverseGalois.CFT.Tate.injective_tensorHomLeft_of_injective_modNsmul`: **a map whose reduction
  modulo a prime is injective stays injective after tensoring** with a representation killed by
  that prime.
* `InverseGalois.CFT.Tate.tensorSeq_shortExact_of_nsmul`,
  `InverseGalois.CFT.Tate.tensorSeq_shortExact_of_injective_modNsmul`: **a short exact sequence
  tensored with coefficients killed by a prime is short exact.**

## Tags

tensor product, torsion, short exact sequence, flatness, representation
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### A retraction over the prime field -/

section Retract

variable {p : ℕ} [Fact p.Prime] {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **An injection into a module killed by a prime has a retraction.**  Both modules are vector
spaces over the field with that many elements, and a subspace of a vector space is a direct
summand. -/
theorem exists_addMonoidHom_leftInverse (f : A →+ B) (hf : Function.Injective f)
    (hB : ∀ b : B, p • b = 0) : ∃ g : B →+ A, ∀ a : A, g (f a) = a := by
  have hA : ∀ a : A, p • a = 0 := fun a => hf (by rw [map_nsmul, hB, map_zero])
  letI : Module (ZMod p) A := AddCommGroup.zmodModule hA
  letI : Module (ZMod p) B := AddCommGroup.zmodModule hB
  obtain ⟨g, hg⟩ :=
    (f.toZModLinearMap p).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  exact ⟨g.toAddMonoidHom, fun a => LinearMap.congr_fun hg a⟩

end Retract

/-! ### Reducing a map modulo a natural number -/

section ModNsmulHom

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} (Φ : A ⟶ B) (m : ℕ)

/-- The multiples of a natural number are carried to the multiples of it. -/
theorem range_nsmulLinear_le_comap_hom :
    LinearMap.range (nsmulLinear k m ↥A.V)
      ≤ (LinearMap.range (nsmulLinear k m ↥B.V)).comap Φ.hom.hom := by
  rintro _ ⟨v, rfl⟩
  exact ⟨Φ.hom.hom v, by simp⟩

/-- **A map of representations, reduced modulo a natural number.** -/
def modNsmulHom : modNsmul A m ⟶ modNsmul B m :=
  mkHom (Submodule.mapQ _ _ Φ.hom.hom (range_nsmulLinear_le_comap_hom Φ m)) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (nsmulLinear k m ↥A.V)) x
    exact congrArg (Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥B.V)))
      (LinearMap.congr_fun (hom_equivariant Φ g) v)

@[simp]
theorem modNsmulHom_mkQ (v : ↥A.V) :
    (modNsmulHom Φ m).hom.hom (Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥A.V)) v)
      = Submodule.mkQ (LinearMap.range (nsmulLinear k m ↥B.V)) (Φ.hom.hom v) := rfl

/-- **Reducing a map modulo a natural number commutes with tensoring** with a representation
killed by that number. -/
theorem tensorHomLeft_comp_tensorModNsmulIso (M : Rep k G) (hM : ∀ v : ↥M.V, m • v = 0) :
    tensorHomLeft M Φ ≫ (tensorModNsmulIso B M m hM).hom
      = (tensorModNsmulIso A M m hM).hom ≫ tensorHomLeft M (modNsmulHom Φ m) :=
  tensorHomLeft_ext M fun _ _ => rfl

end ModNsmulHom

/-! ### Injectivity after tensoring -/

section Injective

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {A B : Rep ℤ G} (Φ : A ⟶ B) (M : Rep ℤ G)

/-- **A map into a representation killed by a prime stays injective after tensoring** with any
representation, because it has an additive retraction and the retraction survives the tensoring. -/
theorem injective_tensorHomLeft_of_nsmul (hΦ : Function.Injective Φ.hom.hom)
    (hB : ∀ b : ↥B.V, p • b = 0) : Function.Injective (tensorHomLeft M Φ).hom.hom := by
  obtain ⟨g, hg⟩ :=
    exists_addMonoidHom_leftInverse (p := p) Φ.hom.hom.toAddMonoidHom hΦ hB
  have hg' : ∀ a : ↥A.V, g (Φ.hom.hom a) = a := hg
  let gl : ↥B.V →ₗ[ℤ] ↥A.V :=
    { toFun := g
      map_add' := map_add g
      map_smul' := fun c x => by simpa using map_intCast_smul g ℤ ℤ c x }
  have hcomp : ∀ t : ↥(tensorObj A M).V,
      LinearMap.rTensor ↥M.V gl ((tensorHomLeft M Φ).hom.hom t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a w =>
        show g (Φ.hom.hom a) ⊗ₜ[ℤ] w = a ⊗ₜ[ℤ] w
        rw [hg' a]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact fun x y hxy => by rw [← hcomp x, ← hcomp y, hxy]

/-- **A map whose reduction modulo a prime is injective stays injective after tensoring** with a
representation killed by that prime, because tensoring with such a representation does not see the
difference between a representation and its reduction. -/
theorem injective_tensorHomLeft_of_injective_modNsmul (hM : ∀ w : ↥M.V, p • w = 0)
    (h : Function.Injective (modNsmulHom Φ p).hom.hom) :
    Function.Injective (tensorHomLeft M Φ).hom.hom := by
  have hcomm := congrArg (fun Ψ : tensorObj A M ⟶ tensorObj (modNsmul B p) M => Ψ.hom.hom)
    (tensorHomLeft_comp_tensorModNsmulIso Φ p M hM)
  have hright : Function.Injective
      ((tensorHomLeft M (modNsmulHom Φ p)).hom.hom.comp
        (tensorModNsmulIso A M p hM).hom.hom.hom) :=
    (injective_tensorHomLeft_of_nsmul (modNsmulHom Φ p) M h
      (nsmul_modNsmul_eq_zero B p)).comp
      (bijective_tensorHomLeft_nsmulSeq_g A M p hM).1
  have hleft : Function.Injective
      ((tensorModNsmulIso B M p hM).hom.hom.hom.comp (tensorHomLeft M Φ).hom.hom) := by
    rw [show (tensorModNsmulIso B M p hM).hom.hom.hom.comp (tensorHomLeft M Φ).hom.hom
        = (tensorHomLeft M (modNsmulHom Φ p)).hom.hom.comp
          (tensorModNsmulIso A M p hM).hom.hom.hom from hcomm]
    exact hright
  exact fun x y hxy => hleft (congrArg (tensorModNsmulIso B M p hM).hom.hom.hom hxy)

end Injective

/-! ### The tensored sequence -/

section Sequence

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {X : ShortComplex (Rep ℤ G)}
  (hX : X.ShortExact) (M : Rep ℤ G)

include hX in
/-- **A short exact sequence tensored with a representation is short exact** as soon as its first
map stays injective. -/
theorem tensorSeq_shortExact_of_injective
    (hinj : Function.Injective (tensorHomLeft M X.f).hom.hom) : (tensorSeq M X).ShortExact := by
  have hex : Function.Exact X.f.hom.hom X.g.hom.hom :=
    LinearMap.exact_iff.2 (shortExact_range_eq_ker hX).symm
  refine shortExact_of_linearMap hinj
    (LinearMap.rTensor_surjective _ (shortExact_surjective hX)) fun x hx => ?_
  exact (rTensor_exact ↥M.V hex (shortExact_surjective hX) x).1 hx

include hX in
/-- **A short exact sequence whose middle term is killed by a prime is short exact after tensoring
with any representation.** -/
theorem tensorSeq_shortExact_of_nsmul (hB : ∀ b : ↥X.X₂.V, p • b = 0) :
    (tensorSeq M X).ShortExact :=
  tensorSeq_shortExact_of_injective hX M
    (injective_tensorHomLeft_of_nsmul (p := p) X.f M (shortExact_injective hX) hB)

include hX in
/-- **A short exact sequence tensored with a representation killed by a prime is short exact** as
soon as its first map stays injective modulo that prime. -/
theorem tensorSeq_shortExact_of_injective_modNsmul (hM : ∀ w : ↥M.V, p • w = 0)
    (h : Function.Injective (modNsmulHom X.f p).hom.hom) : (tensorSeq M X).ShortExact :=
  tensorSeq_shortExact_of_injective hX M
    (injective_tensorHomLeft_of_injective_modNsmul X.f M hM h)

end Sequence

end

end InverseGalois.CFT.Tate
