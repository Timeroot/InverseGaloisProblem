import Mathlib
import InverseGalois.CFT.Brauer.CrossedProduct
import InverseGalois.CFT.Brauer.CrossedProductSimple
import InverseGalois.CFT.Brauer.SkolemNoether
import InverseGalois.CFT.Brauer.Centralizer

/-!
# Recognising a central simple algebra as a crossed product

Let `L / K` be a finite Galois extension of fields and let `A` be a finite-dimensional central
simple `K`-algebra containing a copy of `L`, that is, equipped with a `K`-algebra homomorphism
`emb : L →ₐ[K] A`.  If the image of `emb` is its own centralizer — equivalently, by the
centralizer theorem, if the dimension of `A` over `K` is the square of the dimension of `L` over
`K` — then `A` is a crossed product of `L / K`.

The construction is the classical one.  For every `σ : Gal(L/K)` the two `K`-algebra maps `emb`
and `emb ∘ σ` are conjugate by a unit `u σ` of `A`, by Skolem–Noether.  The element
`u σ * u τ * (u (σ * τ))⁻¹` then commutes with the whole image of `emb`, hence lies in that image
because the image is self-centralizing, and its (unique) preimage `c (σ, τ)` is a unit of `L`.
Associativity of `A` makes `c` a multiplicative `2`-cocycle, and sending the symbol `a * u g` of
the crossed product `(L, Gal(L/K), c)` to `emb a * u g` is a `K`-algebra homomorphism.  It is
injective because the crossed product is a simple ring, and then bijective for dimension reasons.

## Main results

* `InverseGalois.CFT.exists_eq_emb_of_centralizer_eq_range`: an element of `A` commuting with the
  image of a self-centralizing embedding lies in that image.
* `InverseGalois.CFT.exists_conjugating_units`: every element of `Gal(L/K)` is realised by
  conjugation by a unit of `A`.
* `InverseGalois.CFT.exists_units_and_cocycle`: the family of conjugating units multiplies up to
  a factor coming from `L`.
* `InverseGalois.CFT.isMulCocycle₂_of_units`: that factor is a multiplicative `2`-cocycle.
* `InverseGalois.CFT.crossedProductAlgHom`: the resulting `K`-algebra homomorphism from the
  crossed product to `A`.
* `InverseGalois.CFT.crossedProductAlgHom_bijective`: it is bijective.
* `InverseGalois.CFT.exists_algEquiv_crossedProduct`: a central simple algebra with a
  self-centralizing subfield `L` of degree the square root of its dimension is a crossed product
  of `L / K`.
* `InverseGalois.CFT.centralizer_eq_self_of_finrank_sq`: the self-centralizing hypothesis is
  automatic once the dimensions match.
* `InverseGalois.CFT.exists_algEquiv_crossedProduct_of_finrank_sq`: the combined statement, with
  the dimension hypothesis alone.
-/

universe u

open groupCohomology Module

namespace InverseGalois.CFT

variable {K L A : Type u} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

/-! ### The image of a self-centralizing embedding -/

/-- If the image of `emb : L →ₐ[K] A` is its own centralizer, then every element of `A` that
commutes with the whole image lies in the image. -/
theorem exists_eq_emb_of_centralizer_eq_range (emb : L →ₐ[K] A)
    (hcent : Subalgebra.centralizer K (emb.range : Set A) = emb.range)
    {w : A} (hw : ∀ x : L, w * emb x = emb x * w) : ∃ y : L, emb y = w := by
  have hmem : w ∈ Subalgebra.centralizer K (emb.range : Set A) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro a ha
    rw [SetLike.mem_coe, AlgHom.mem_range] at ha
    obtain ⟨x, rfl⟩ := ha
    exact (hw x).symm
  rw [hcent] at hmem
  exact (AlgHom.mem_range emb).mp hmem

/-- The image of a `K`-algebra homomorphism from a field is contained in its own centralizer. -/
theorem range_le_centralizer_range (emb : L →ₐ[K] A) :
    emb.range ≤ Subalgebra.centralizer K (emb.range : Set A) := by
  intro x hx
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe, AlgHom.mem_range] at hg
  obtain ⟨y, rfl⟩ := hg
  obtain ⟨z, rfl⟩ := (AlgHom.mem_range emb).mp hx
  rw [← map_mul, ← map_mul, mul_comm]

/-! ### The conjugating units and the cocycle -/

section Units

variable [FiniteDimensional K L] [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- **Skolem–Noether** provides, for every element of `Gal(L/K)`, a unit of `A` conjugating the
embedded copy of `L` by that element. -/
theorem exists_conjugating_units (emb : L →ₐ[K] A) :
    ∃ u : Gal(L/K) → Aˣ,
      ∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x := by
  have h : ∀ σ : Gal(L/K), ∃ v : Aˣ, ∀ x : L, emb (σ x) * (v : A) = (v : A) * emb x := by
    intro σ
    obtain ⟨v, hv⟩ := SkolemNoether.exists_conj emb (emb.comp σ.toAlgHom)
    refine ⟨v, fun x => ?_⟩
    have hvx := hv x
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom] at hvx
    rw [hvx, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  choose u hu using h
  exact ⟨u, hu⟩

/-- For a self-centralizing embedding of `L` into `A` there are units `u σ` of `A` inducing the
elements `σ` of `Gal(L/K)` by conjugation, whose products differ from the units attached to the
products of the `σ` by factors coming from `L`. -/
theorem exists_units_and_cocycle (emb : L →ₐ[K] A)
    (hcent : Subalgebra.centralizer K (emb.range : Set A) = emb.range) :
    ∃ (u : Gal(L/K) → Aˣ) (c : Gal(L/K) × Gal(L/K) → Lˣ),
      (∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x) ∧
        ∀ σ τ : Gal(L/K),
          (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A) := by
  obtain ⟨u, hu⟩ := exists_conjugating_units emb
  have huinv : ∀ (σ : Gal(L/K)) (y : L),
      ((u σ)⁻¹ : Aˣ) * emb y = emb (σ⁻¹ y) * ((u σ)⁻¹ : Aˣ) := by
    intro σ y
    have h1 := hu σ (σ⁻¹ y)
    rw [CrossedProduct.apply_inv_apply] at h1
    calc ((u σ)⁻¹ : Aˣ) * emb y
        = ((u σ)⁻¹ : Aˣ) * (emb y * (u σ : A)) * ((u σ)⁻¹ : Aˣ) := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
      _ = ((u σ)⁻¹ : Aˣ) * ((u σ : A) * emb (σ⁻¹ y)) * ((u σ)⁻¹ : Aˣ) := by rw [h1]
      _ = emb (σ⁻¹ y) * ((u σ)⁻¹ : Aˣ) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have key : ∀ σ τ : Gal(L/K),
      ∃ y : L, emb y = (u σ : A) * (u τ : A) * ((u (σ * τ))⁻¹ : Aˣ) := by
    intro σ τ
    refine exists_eq_emb_of_centralizer_eq_range emb hcent (fun x => ?_)
    have h2 : ((u (σ * τ))⁻¹ : Aˣ) * emb x = emb ((σ * τ)⁻¹ x) * ((u (σ * τ))⁻¹ : Aˣ) :=
      huinv (σ * τ) x
    have h3 : (u σ : A) * ((u τ : A) * emb ((σ * τ)⁻¹ x))
        = emb x * ((u σ : A) * (u τ : A)) := by
      rw [← hu τ ((σ * τ)⁻¹ x), ← mul_assoc, ← hu σ (τ ((σ * τ)⁻¹ x)), mul_assoc]
      congr 2
      rw [← AlgEquiv.mul_apply, CrossedProduct.apply_inv_apply]
    calc (u σ : A) * (u τ : A) * ((u (σ * τ))⁻¹ : Aˣ) * emb x
        = (u σ : A) * ((u τ : A) * (((u (σ * τ))⁻¹ : Aˣ) * emb x)) := by
          simp only [mul_assoc]
      _ = (u σ : A) * ((u τ : A) * (emb ((σ * τ)⁻¹ x) * ((u (σ * τ))⁻¹ : Aˣ))) := by rw [h2]
      _ = (u σ : A) * ((u τ : A) * emb ((σ * τ)⁻¹ x)) * ((u (σ * τ))⁻¹ : Aˣ) := by
          simp only [mul_assoc]
      _ = emb x * ((u σ : A) * (u τ : A)) * ((u (σ * τ))⁻¹ : Aˣ) := by rw [h3]
      _ = emb x * ((u σ : A) * (u τ : A) * ((u (σ * τ))⁻¹ : Aˣ)) := by simp only [mul_assoc]
  choose y hy using key
  have hy0 : ∀ σ τ : Gal(L/K), y σ τ ≠ 0 := by
    intro σ τ h
    have hunit : IsUnit ((u σ : A) * (u τ : A) * ((u (σ * τ))⁻¹ : Aˣ)) :=
      ((u σ * u τ * (u (σ * τ))⁻¹ : Aˣ)).isUnit
    rw [← hy σ τ, h, map_zero] at hunit
    exact (not_isUnit_zero (M₀ := A)) hunit
  refine ⟨u, fun p => Units.mk0 (y p.1 p.2) (hy0 p.1 p.2), hu, fun σ τ => ?_⟩
  simp only [Units.val_mk0]
  rw [hy σ τ, mul_assoc, Units.inv_mul, mul_one]

end Units

/-- Cancelling a unit appearing as a common right factor. -/
private theorem cancel_unit {a b : A} {v : Aˣ} (h : a * (v : A) = b * (v : A)) : a = b := by
  have h2 := congrArg (fun z => z * ((v⁻¹ : Aˣ) : A)) h
  simpa [mul_assoc] using h2

/-- A family of units of `A` inducing `Gal(L/K)` by conjugation on an embedded copy of `L`
multiplies according to a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_of_units [Nontrivial A] (emb : L →ₐ[K] A) (u : Gal(L/K) → Aˣ)
    (c : Gal(L/K) × Gal(L/K) → Lˣ)
    (hu : ∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x)
    (hmul : ∀ σ τ : Gal(L/K),
      (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A)) :
    IsMulCocycle₂ c := by
  have hinj : Function.Injective emb := emb.toRingHom.injective
  intro g h j
  refine Units.ext (hinj ?_)
  simp only [Units.val_mul, map_mul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe]
  refine cancel_unit (v := u (g * h * j)) ?_
  have e1 : (u g : A) * (u h : A) * (u j : A)
      = emb ((c (g, h) : Lˣ) : L) * emb ((c (g * h, j) : Lˣ) : L) * (u (g * h * j) : A) := by
    rw [hmul g h, mul_assoc, hmul (g * h) j, ← mul_assoc]
  have e2 : (u g : A) * (u h : A) * (u j : A)
      = emb (g ((c (h, j) : Lˣ) : L)) * emb ((c (g, h * j) : Lˣ) : L)
        * (u (g * h * j) : A) := by
    rw [mul_assoc, hmul h j, ← mul_assoc, ← hu g ((c (h, j) : Lˣ) : L), mul_assoc,
      hmul g (h * j), ← mul_assoc, ← mul_assoc, mul_assoc g h j]
  have hcomm : emb ((c (g * h, j) : Lˣ) : L) * emb ((c (g, h) : Lˣ) : L)
      = emb ((c (g, h) : Lˣ) : L) * emb ((c (g * h, j) : Lˣ) : L) := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [hcomm, ← e1, e2]

/-! ### The comparison map -/

section Map

variable {c : Gal(L/K) × Gal(L/K) → Lˣ}

/-- The underlying function of the comparison map from the crossed product `(L, Gal(L/K), c)` to
`A`: it sends the symbol `a * u g` to `emb a * u g`. -/
noncomputable def cpMap (emb : L →ₐ[K] A) (u : Gal(L/K) → Aˣ) (hc : IsMulCocycle₂ c)
    (x : CrossedProduct hc) : A :=
  (CrossedProduct.toFinsupp x).sum fun g a => emb a * (u g : A)

variable (emb : L →ₐ[K] A) (u : Gal(L/K) → Aˣ) (hc : IsMulCocycle₂ c)

/-- The comparison map sends zero to zero. -/
theorem cpMap_zero : cpMap emb u hc 0 = 0 := by
  simp only [cpMap, CrossedProduct.toFinsupp_zero]
  exact Finsupp.sum_zero_index

/-- The comparison map is additive. -/
theorem cpMap_add (x y : CrossedProduct hc) :
    cpMap emb u hc (x + y) = cpMap emb u hc x + cpMap emb u hc y := by
  simp only [cpMap, CrossedProduct.toFinsupp_add]
  exact Finsupp.sum_add_index' (fun _ => by rw [map_zero, zero_mul])
    (fun _ _ _ => by rw [map_add, add_mul])

/-- The comparison map sends the symbol `a * u g` to `emb a * u g`. -/
theorem cpMap_single (g : Gal(L/K)) (a : L) :
    cpMap emb u hc (CrossedProduct.single hc g a) = emb a * (u g : A) := by
  simp only [cpMap, CrossedProduct.toFinsupp_single]
  exact Finsupp.sum_single_index (by rw [map_zero, zero_mul])

variable {emb u}

/-- The unit attached to the identity of `Gal(L/K)` is the image of the value of the cocycle
at `(1, 1)`. -/
theorem val_units_one (hmul : ∀ σ τ : Gal(L/K),
    (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A)) :
    ((u 1 : Aˣ) : A) = emb ((c (1, 1) : Lˣ) : L) := by
  have h := hmul 1 1
  rw [one_mul] at h
  exact cancel_unit h

/-- The comparison map sends the unit of the crossed product to the unit of `A`. -/
theorem cpMap_one (hmul : ∀ σ τ : Gal(L/K),
    (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A)) :
    cpMap emb u hc 1 = 1 := by
  rw [CrossedProduct.one_def, cpMap_single, val_units_one hmul, ← map_mul, Units.inv_mul,
    map_one]

/-- The comparison map is multiplicative. -/
theorem cpMap_mul
    (hu : ∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x)
    (hmul : ∀ σ τ : Gal(L/K),
      (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A))
    (x y : CrossedProduct hc) :
    cpMap emb u hc (x * y) = cpMap emb u hc x * cpMap emb u hc y := by
  induction x using CrossedProduct.induction_linear with
  | zero => rw [zero_mul, cpMap_zero, zero_mul]
  | add p q hp hq => rw [add_mul, cpMap_add, hp, hq, cpMap_add, add_mul]
  | single g a =>
    induction y using CrossedProduct.induction_linear with
    | zero => rw [mul_zero, cpMap_zero, mul_zero]
    | add p q hp hq => rw [mul_add, cpMap_add, hp, hq, cpMap_add, mul_add]
    | single h b =>
      rw [CrossedProduct.single_mul_single, cpMap_single, cpMap_single, cpMap_single, map_mul,
        map_mul]
      calc emb a * emb (g b) * emb ((c (g, h) : Lˣ) : L) * (u (g * h) : A)
          = emb a * emb (g b) * (emb ((c (g, h) : Lˣ) : L) * (u (g * h) : A)) := by
            rw [mul_assoc]
        _ = emb a * emb (g b) * ((u g : A) * (u h : A)) := by rw [hmul g h]
        _ = emb a * (emb (g b) * (u g : A)) * (u h : A) := by simp only [mul_assoc]
        _ = emb a * ((u g : A) * emb b) * (u h : A) := by rw [hu g b]
        _ = emb a * (u g : A) * (emb b * (u h : A)) := by simp only [mul_assoc]

/-- The comparison map is compatible with the structure maps from the base field. -/
theorem cpMap_algebraMap (hmul : ∀ σ τ : Gal(L/K),
    (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A)) (k : K) :
    cpMap emb u hc (algebraMap K (CrossedProduct hc) k) = algebraMap K A k := by
  rw [CrossedProduct.algebraMap_eq, CrossedProduct.incl_eq_single, cpMap_single, map_mul,
    mul_assoc, val_units_one hmul, ← map_mul, Units.inv_mul, map_one, mul_one, AlgHom.commutes]

/-- The comparison `K`-algebra homomorphism from the crossed product `(L, Gal(L/K), c)` to `A`,
sending the symbol `a * u g` to `emb a * u g`. -/
noncomputable def crossedProductAlgHom (emb : L →ₐ[K] A) (u : Gal(L/K) → Aˣ)
    (hc : IsMulCocycle₂ c)
    (hu : ∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x)
    (hmul : ∀ σ τ : Gal(L/K),
      (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A)) :
    CrossedProduct hc →ₐ[K] A where
  toFun := cpMap emb u hc
  map_one' := cpMap_one hc hmul
  map_mul' := cpMap_mul hc hu hmul
  map_zero' := cpMap_zero emb u hc
  map_add' := cpMap_add emb u hc
  commutes' := cpMap_algebraMap hc hmul

/-- The comparison map sends the symbol `a * u g` to `emb a * u g`. -/
theorem crossedProductAlgHom_single (emb : L →ₐ[K] A) (u : Gal(L/K) → Aˣ)
    (hc : IsMulCocycle₂ c)
    (hu : ∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x)
    (hmul : ∀ σ τ : Gal(L/K),
      (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A))
    (g : Gal(L/K)) (a : L) :
    crossedProductAlgHom emb u hc hu hmul (CrossedProduct.single hc g a) = emb a * (u g : A) :=
  cpMap_single emb u hc g a

variable [FiniteDimensional K L] [IsGalois K L] [IsSimpleRing A] [FiniteDimensional K A]

/-- When the dimension of `A` is the square of the dimension of `L`, the comparison map is a
bijection. -/
theorem crossedProductAlgHom_bijective (emb : L →ₐ[K] A) (u : Gal(L/K) → Aˣ)
    (hc : IsMulCocycle₂ c)
    (hu : ∀ (σ : Gal(L/K)) (x : L), emb (σ x) * (u σ : A) = (u σ : A) * emb x)
    (hmul : ∀ σ τ : Gal(L/K),
      (u σ : A) * (u τ : A) = emb ((c (σ, τ) : Lˣ) : L) * (u (σ * τ) : A))
    (hdim : finrank K A = finrank K L * finrank K L) :
    Function.Bijective (crossedProductAlgHom emb u hc hu hmul) := by
  have hfr : finrank K (CrossedProduct hc) = finrank K A := by
    rw [CrossedProduct.finrank_eq, IsGalois.card_aut_eq_finrank K L, sq, hdim]
  have hinj : Function.Injective (crossedProductAlgHom emb u hc hu hmul) :=
    (crossedProductAlgHom emb u hc hu hmul).toRingHom.injective
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
    (f := (crossedProductAlgHom emb u hc hu hmul).toLinearMap)).mp hinj

end Map

/-! ### The recognition theorem -/

section Recognition

variable [FiniteDimensional K L] [IsGalois K L] [Algebra.IsCentral K A] [IsSimpleRing A]
  [FiniteDimensional K A]

/-- **Recognition of crossed products**: a finite-dimensional central simple `K`-algebra `A`
containing a self-centralizing copy of a finite Galois extension `L / K` of dimension the square
root of the dimension of `A` is a crossed product of `L / K`. -/
theorem exists_algEquiv_crossedProduct (emb : L →ₐ[K] A)
    (hcent : Subalgebra.centralizer K (emb.range : Set A) = emb.range)
    (hdim : finrank K A = finrank K L * finrank K L) :
    ∃ (c : Gal(L/K) × Gal(L/K) → Lˣ) (hc : IsMulCocycle₂ c),
      Nonempty (CrossedProduct hc ≃ₐ[K] A) := by
  obtain ⟨u, c, hu, hmul⟩ := exists_units_and_cocycle emb hcent
  have hc : IsMulCocycle₂ c := isMulCocycle₂_of_units emb u c hu hmul
  exact ⟨c, hc, ⟨AlgEquiv.ofBijective (crossedProductAlgHom emb u hc hu hmul)
    (crossedProductAlgHom_bijective emb u hc hu hmul hdim)⟩⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- An embedded copy of `L` in a finite-dimensional central simple `K`-algebra `A` whose
dimension is the square of the dimension of `L` is automatically its own centralizer. -/
theorem centralizer_eq_self_of_finrank_sq (emb : L →ₐ[K] A)
    (hdim : finrank K A = finrank K L * finrank K L) :
    Subalgebra.centralizer K (emb.range : Set A) = emb.range := by
  have hinj : Function.Injective emb := emb.toRingHom.injective
  have hrange : finrank K (emb.range : Subalgebra K A) = finrank K L :=
    ((AlgEquiv.ofInjective emb hinj).toLinearEquiv.finrank_eq).symm
  haveI : IsSimpleRing (emb.range : Subalgebra K A) :=
    IsSimpleRing.of_ringEquiv (AlgEquiv.ofInjective emb hinj).toRingEquiv inferInstance
  refine (Centralizer.centralizer_eq_self_iff_finrank_sq emb.range
    (range_le_centralizer_range emb)).mpr ?_
  rw [hrange, hdim]

/-- **Recognition of crossed products**: a finite-dimensional central simple `K`-algebra `A`
containing a copy of a finite Galois extension `L / K` of dimension the square root of the
dimension of `A` is a crossed product of `L / K`. -/
theorem exists_algEquiv_crossedProduct_of_finrank_sq (emb : L →ₐ[K] A)
    (hdim : finrank K A = finrank K L * finrank K L) :
    ∃ (c : Gal(L/K) × Gal(L/K) → Lˣ) (hc : IsMulCocycle₂ c),
      Nonempty (CrossedProduct hc ≃ₐ[K] A) :=
  exists_algEquiv_crossedProduct emb (centralizer_eq_self_of_finrank_sq emb hdim) hdim

end Recognition

end InverseGalois.CFT
