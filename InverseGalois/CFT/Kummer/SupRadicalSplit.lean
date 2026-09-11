/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.RadicalCharacter

/-!
# A radicand of a compositum splits when one factor is elementary abelian

Let `K` contain a primitive `p`-th root of unity and let `L` be a finite Galois extension of `K`
which is the compositum of two normal subextensions `E₁` and `E₂`, the Galois group of the second
being abelian and killed by `p`.  **An element of `K` which becomes a `p`-th power in `L` is then a
product of an element which is already a `p`-th power in `E₁` and one which is already a `p`-th
power in `E₂`.**

A `p`-th root of the element in `L` has all its conjugates differing from it by `p`-th roots of
unity, so it carries a character of the Galois group of `L` with values in `ZMod p`.  The two
subextensions present that Galois group as a subgroup of the product of the two smaller ones, and
the character splits along the two projections: the kernel of the first projection injects into the
second quotient, which is a vector space over the field with `p` elements, so the restriction of the
character to that kernel extends to the whole of the second quotient by linear algebra, and the
remaining factor is trivial on the kernel of the first projection and therefore descends.  Hilbert's
theorem 90 turns each of the two characters back into a radical, living in the corresponding
subextension, and the original root differs from their product by an element of the base.

Nothing weaker than the exponent hypothesis on the second group will do.  The two projections of a
subgroup of a product of two cyclic groups of order `p ^ 2` onto the factors can both be surjective
with the kernels meeting trivially while a character of the subgroup fails to split, so the linear
algebra really is what makes the argument work.

## Main results

* `InverseGalois.CFT.exists_linearMap_extend_of_injective`: **a linear form on a subspace of a
  vector space over the field with `p` elements extends to the whole space.**
* `InverseGalois.CFT.exists_addMonoidHom_extend_of_injective`: **a homomorphism to `ZMod p` on a
  group embedded in an abelian group killed by `p` extends along the embedding.**
* `InverseGalois.CFT.exists_character_add_eq_of_disjoint_ker`: **a character with values in
  `ZMod p` of a group with two quotients whose kernels meet trivially, the second quotient being
  abelian and killed by `p`, is the sum of a character of each quotient.**
* `InverseGalois.CFT.exists_mul_eq_pow_of_pow_mem_sup`: **an element of the base which is a `p`-th
  power in a compositum of two normal subextensions, one of them with elementary abelian group, is
  a product of a `p`-th power of each of the two.**

## Tags

Kummer theory, compositum, character, elementary abelian, radical, Hilbert 90
-/

namespace InverseGalois.CFT

/-! ### Extending a character of a group killed by a prime -/

section Extend

/-- **A linear form on a subspace of a vector space over the field with `p` elements, presented as
an injective linear map, extends to the whole space.**  The injection identifies the source with its
range, and a linear form on a subspace of a vector space extends. -/
theorem exists_linearMap_extend_of_injective {V W : Type*} {p : ℕ} [Fact p.Prime] [AddCommGroup V]
    [AddCommGroup W] [Module (ZMod p) V] [Module (ZMod p) W] (ι : W →ₗ[ZMod p] V)
    (hι : Function.Injective ι) (f : W →ₗ[ZMod p] ZMod p) :
    ∃ g : V →ₗ[ZMod p] ZMod p, ∀ w : W, g (ι w) = f w := by
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_extend (f.comp (LinearEquiv.ofInjective ι hι).symm.toLinearMap)
  refine ⟨g, fun w => ?_⟩
  have h := congrArg (fun t => t (LinearEquiv.ofInjective ι hι w)) hg
  simpa using h

/-- **A homomorphism to `ZMod p` on a group embedded in an abelian group killed by `p` extends
along the embedding.**  Both groups are vector spaces over the field with `p` elements and the
embedding is an injective linear map, so a linear form on the source extends to the target. -/
theorem exists_addMonoidHom_extend_of_injective {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    {p : ℕ} (hp : p.Prime) (hV : ∀ v : V, p • v = 0) (ι : W →+ V) (hι : Function.Injective ι)
    (f : W →+ ZMod p) : ∃ g : V →+ ZMod p, ∀ w : W, g (ι w) = f w := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hW : ∀ w : W, p • w = 0 := fun w => hι (by rw [map_nsmul, hV, map_zero])
  letI : Module (ZMod p) V := AddCommGroup.zmodModule hV
  letI : Module (ZMod p) W := AddCommGroup.zmodModule hW
  obtain ⟨g, hg⟩ :=
    exists_linearMap_extend_of_injective (ι.toZModLinearMap p) hι (f.toZModLinearMap p)
  exact ⟨g.toAddMonoidHom, hg⟩

end Extend

/-! ### Splitting a character along two quotients -/

section Character

variable {H A B : Type*} [Group H] [Group A] [Group B]

/-- **A character with values in `ZMod p` of a group with two quotients whose kernels meet
trivially, the second quotient being abelian and killed by `p`, is the sum of a character of each
quotient.**  The kernel of the first projection is carried injectively into the second quotient, so
the character restricted to it becomes a linear form on a subspace of a vector space over the field
with `p` elements; extending that form and subtracting it leaves a character trivial on the kernel
of the first projection, which therefore comes from the first quotient. -/
theorem exists_character_add_eq_of_disjoint_ker {p : ℕ} (hp : p.Prime)
    (hcomm : ∀ x y : B, x * y = y * x) (hexp : ∀ x : B, x ^ p = 1) (πa : H →* A) (πb : H →* B)
    (ha : Function.Surjective πa) (hdisj : ∀ σ : H, πa σ = 1 → πb σ = 1 → σ = 1)
    (χ : H → ZMod p) (hχ : ∀ x y : H, χ (x * y) = χ x + χ y) :
    ∃ (χa : A → ZMod p) (χb : B → ZMod p),
      (∀ x y : A, χa (x * y) = χa x + χa y) ∧ (∀ x y : B, χb (x * y) = χb x + χb y) ∧
        ∀ σ : H, χ σ = χa (πa σ) + χb (πb σ) := by
  classical
  letI : CommGroup B := { (inferInstance : Group B) with mul_comm := hcomm }
  have hχ1 : χ 1 = 0 := by
    have h := hχ 1 1
    rw [one_mul] at h
    linear_combination -h
  set X : H →* Multiplicative (ZMod p) :=
    { toFun := fun σ => Multiplicative.ofAdd (χ σ)
      map_one' := by simp [hχ1]
      map_mul' := fun x y => by simp [hχ x y, ofAdd_add] } with hXdef
  set N : Subgroup H := πa.ker with hNdef
  set N₀ : Subgroup B := N.map πb with hN₀def
  have hmemN₀ : ∀ x : ↥N, πb (x : H) ∈ N₀ := fun x => Subgroup.mem_map_of_mem _ x.2
  set φ : ↥N →* ↥N₀ := (πb.comp N.subtype).codRestrict N₀ hmemN₀ with hφdef
  have hφval : ∀ x : ↥N, (φ x : B) = πb (x : H) := fun _ => rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hb : πb ((x : H) * (y : H)⁻¹) = 1 := by
      have h : πb (x : H) = πb (y : H) := by
        rw [← hφval x, ← hφval y, hxy]
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have hax : πa ((x : H) * (y : H)⁻¹) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 x.2, MonoidHom.mem_ker.1 y.2, one_mul, inv_one]
    exact Subtype.ext (mul_inv_eq_one.1 (hdisj _ hax hb))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨-, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  set e : ↥N ≃* ↥N₀ := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩ with hedef
  set g₀ : ↥N₀ →* Multiplicative (ZMod p) := X.comp (N.subtype.comp e.symm.toMonoidHom) with hg₀def
  have hVexp : ∀ v : Additive B, p • v = 0 := fun v => by
    have h := hexp (Additive.toMul v)
    simpa [← ofMul_pow] using congrArg Additive.ofMul h
  obtain ⟨G, hG⟩ := exists_addMonoidHom_extend_of_injective (V := Additive B)
    (W := Additive ↥N₀) hp hVexp (MonoidHom.toAdditive N₀.subtype)
    (fun x y h => Subtype.ext h) (MonoidHom.toAdditiveLeft g₀)
  set χb : B → ZMod p := fun x => G (Additive.ofMul x) with hχbdef
  have hχbadd : ∀ x y : B, χb (x * y) = χb x + χb y := fun x y => G.map_add _ _
  have hχbN : ∀ σ : H, πa σ = 1 → χb (πb σ) = χ σ := by
    intro σ hσ
    have hmem : σ ∈ N := MonoidHom.mem_ker.2 hσ
    have h := hG (Additive.ofMul (φ ⟨σ, hmem⟩))
    have hsym : e.symm (φ ⟨σ, hmem⟩) = ⟨σ, hmem⟩ := by
      rw [show φ ⟨σ, hmem⟩ = e ⟨σ, hmem⟩ from rfl, MulEquiv.symm_apply_apply]
    simpa [hχbdef, hφval, hg₀def, hXdef, hsym] using h
  set ψ : H → ZMod p := fun σ => χ σ - χb (πb σ) with hψdef
  have hψadd : ∀ x y : H, ψ (x * y) = ψ x + ψ y := by
    intro x y
    simp only [hψdef, map_mul, hχ x y, hχbadd]
    ring
  have hχb1 : χb 1 = 0 := by simp [hχbdef]
  have hψ1 : ψ 1 = 0 := by simp [hψdef, hχ1, hχb1]
  have hψker : ∀ σ : H, πa σ = 1 → ψ σ = 0 := fun σ hσ => by simp [hψdef, hχbN σ hσ]
  have hψinv : ∀ x : H, ψ x + ψ x⁻¹ = 0 := by
    intro x
    have h := hψadd x x⁻¹
    rw [mul_inv_cancel, hψ1] at h
    linear_combination -h
  have hψwd : ∀ x y : H, πa x = πa y → ψ x = ψ y := by
    intro x y hxy
    have h1 : πa (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 := hψker _ h1
    rw [hψadd] at h2
    linear_combination h2 - hψinv y
  refine ⟨fun a => ψ (Classical.choose (ha a)), χb, ?_, hχbadd, ?_⟩
  · intro x y
    dsimp only
    have hx := Classical.choose_spec (ha x)
    have hy := Classical.choose_spec (ha y)
    have hxy := Classical.choose_spec (ha (x * y))
    have h : πa (Classical.choose (ha (x * y)))
        = πa (Classical.choose (ha x) * Classical.choose (ha y)) := by
      rw [hxy, map_mul, hx, hy]
    rw [hψwd _ _ h, hψadd]
  · intro σ
    dsimp only
    have h : πa (Classical.choose (ha (πa σ))) = πa σ := Classical.choose_spec (ha (πa σ))
    rw [hψwd _ _ h, hψdef]
    ring

end Character

/-! ### The radicand splits along the compositum -/

section Sup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **An element of the base which is a `p`-th power in a compositum of two normal subextensions,
the second having abelian Galois group killed by `p`, is a product of an element which is a `p`-th
power in the first and one which is a `p`-th power in the second.**  The character carried by a
`p`-th root of the element splits along the two restriction maps, and Hilbert's theorem 90 realises
each summand by a radical of the corresponding subextension. -/
theorem exists_mul_eq_pow_of_pow_mem_sup {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {E₁ E₂ : IntermediateField K L} [Normal K ↥E₁] [Normal K ↥E₂]
    (hsup : E₁ ⊔ E₂ = ⊤) (hcomm : ∀ σ τ : ↥E₂ ≃ₐ[K] ↥E₂, σ * τ = τ * σ)
    (hexp : ∀ σ : ↥E₂ ≃ₐ[K] ↥E₂, σ ^ p = 1) {b : K} (hb : b ≠ 0) {β : L}
    (hβ : β ^ p = algebraMap K L b) :
    ∃ b₁ b₂ : K, b = b₁ * b₂ ∧ (∃ x ∈ E₁, x ^ p = algebraMap K L b₁) ∧
      (∃ x ∈ E₂, x ^ p = algebraMap K L b₂) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Algebra.IsSeparable K ↥E₁ := Algebra.isSeparable_tower_bot_of_isSeparable K ↥E₁ L
  haveI : Algebra.IsSeparable K ↥E₂ := Algebra.isSeparable_tower_bot_of_isSeparable K ↥E₂ L
  haveI : IsGalois K ↥E₁ := ⟨⟩
  haveI : IsGalois K ↥E₂ := ⟨⟩
  have hbne : algebraMap K L b ≠ 0 := (map_ne_zero _).2 hb
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hβ
    exact hbne hβ.symm
  set ζL : L := algebraMap K L ζ with hζLdef
  have hζL : IsPrimitiveRoot ζL p := hζ.map_of_injective (algebraMap K L).injective
  have hfin : IsOfFinOrder ζL := isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hζL.pow_eq_one⟩
  have hmodEq : ∀ a b : ℕ, ζL ^ a = ζL ^ b ↔ a ≡ b [MOD p] := fun a b => by
    rw [hfin.pow_eq_pow_iff_modEq, ← hζL.eq_orderOf]
  have hζfix : ∀ (σ : L ≃ₐ[K] L) (m : ℕ), σ (ζL ^ m) = ζL ^ m := by
    intro σ m
    rw [map_pow, hζLdef, AlgEquiv.commutes]
  -- the character carried by the radical
  have hroot : ∀ σ : L ≃ₐ[K] L, ∃ i < p, ζL ^ i = σ β / β := by
    intro σ
    refine hζL.eq_pow_of_pow_eq_one ?_
    simp only [div_pow, ← map_pow, hβ, AlgEquiv.commutes]
    exact div_self hbne
  set n : (L ≃ₐ[K] L) → ℕ := fun σ => Classical.choose (hroot σ) with hndef
  have hnlt : ∀ σ, n σ < p := fun σ => (Classical.choose_spec (hroot σ)).1
  have hnspec : ∀ σ, ζL ^ n σ = σ β / β := fun σ => (Classical.choose_spec (hroot σ)).2
  have hnβ : ∀ σ, σ β = ζL ^ n σ * β := by
    intro σ
    rw [hnspec σ, div_mul_cancel₀ _ hβ0]
  set χ : (L ≃ₐ[K] L) → ZMod p := fun σ => (n σ : ZMod p) with hχdef
  have hχval : ∀ σ, (χ σ).val = n σ := fun σ => ZMod.val_natCast_of_lt (hnlt σ)
  have hχadd : ∀ σ τ : L ≃ₐ[K] L, χ (σ * τ) = χ σ + χ τ := by
    intro σ τ
    have h1 : (σ * τ) β = ζL ^ (n σ + n τ) * β := by
      show σ (τ β) = _
      rw [hnβ τ, map_mul, hζfix, hnβ σ, pow_add]
      ring
    rw [hnβ (σ * τ)] at h1
    have h2 : ζL ^ n (σ * τ) = ζL ^ (n σ + n τ) := mul_right_cancel₀ hβ0 h1
    have h3 : n (σ * τ) ≡ n σ + n τ [MOD p] := (hmodEq _ _).1 h2
    rw [hχdef]
    simp only
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h3, Nat.cast_add]
  -- the two restrictions
  have hsurja : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) ↥E₁) :=
    AlgEquiv.restrictNormalHom_surjective L
  have hfixE : ∀ (E : IntermediateField K L) (_ : Normal K ↥E) (σ : L ≃ₐ[K] L),
      AlgEquiv.restrictNormalHom ↥E σ = 1 → ∀ x ∈ E, σ x = x := by
    intro E hE σ hσ x hx
    have h := AlgEquiv.restrictNormalHom_apply (F := K) E σ ⟨x, hx⟩
    rw [hσ] at h
    simpa using h.symm
  have hdisj : ∀ σ : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom ↥E₁ σ = 1 →
      AlgEquiv.restrictNormalHom ↥E₂ σ = 1 → σ = 1 := by
    intro σ h1 h2
    have hE1 := hfixE E₁ inferInstance σ h1
    have hE2 := hfixE E₂ inferInstance σ h2
    have hgen : Algebra.adjoin K ((E₁ : Set L) ∪ (E₂ : Set L)) = ⊤ := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := K)
          (S := ((E₁ : Set L) ∪ (E₂ : Set L))) fun x _ => Algebra.IsAlgebraic.isAlgebraic x,
        IntermediateField.adjoin_union, IntermediateField.adjoin_self,
        IntermediateField.adjoin_self, hsup, IntermediateField.top_toSubalgebra]
    have hid : σ.toAlgHom = AlgHom.id K L :=
      AlgHom.ext_of_adjoin_eq_top hgen fun x hx => by
        rcases hx with hx | hx
        · exact hE1 x hx
        · exact hE2 x hx
    exact AlgEquiv.ext fun x => congrArg (fun f : L →ₐ[K] L => f x) hid
  obtain ⟨χa, χb, hχaadd, hχbadd, hsplit⟩ :=
    exists_character_add_eq_of_disjoint_ker hp hcomm hexp
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) ↥E₁)
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) ↥E₂) hsurja hdisj χ hχadd
  -- Hilbert 90 in each subextension
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  set u₁ : (↥E₁)ˣ := Units.mk0 (algebraMap K ↥E₁ ζ) ((map_ne_zero _).2 hζ0) with hu₁def
  set u₂ : (↥E₂)ˣ := Units.mk0 (algebraMap K ↥E₂ ζ) ((map_ne_zero _).2 hζ0) with hu₂def
  have hu₁ : u₁ ^ p = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hu₁def]
    simp [← map_pow, hζ.pow_eq_one]
  have hu₂ : u₂ ^ p = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hu₂def]
    simp [← map_pow, hζ.pow_eq_one]
  set f₁ : (↥E₁ ≃ₐ[K] ↥E₁) →* (↥E₁)ˣ := rootHom u₁ hu₁ χa hχaadd with hf₁def
  set f₂ : (↥E₂ ≃ₐ[K] ↥E₂) →* (↥E₂)ˣ := rootHom u₂ hu₂ χb hχbadd with hf₂def
  have hf₁val : ∀ σ, (f₁ σ : ↥E₁) = algebraMap K ↥E₁ (ζ ^ (χa σ).val) := by
    intro σ
    rw [hf₁def, rootHom_apply, Units.val_pow_eq_pow_val, hu₁def, map_pow]
    rfl
  have hf₂val : ∀ σ, (f₂ σ : ↥E₂) = algebraMap K ↥E₂ (ζ ^ (χb σ).val) := by
    intro σ
    rw [hf₂def, rootHom_apply, Units.val_pow_eq_pow_val, hu₂def, map_pow]
    rfl
  obtain ⟨α₁, hα₁0, hα₁, w₁, hw₁⟩ := exists_radical (ℓ := p) f₁
    (fun σ τ => by rw [hf₁val, AlgEquiv.commutes])
    (fun σ => by rw [hf₁val, ← map_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow,
      map_one])
  obtain ⟨α₂, hα₂0, hα₂, w₂, hw₂⟩ := exists_radical (ℓ := p) f₂
    (fun σ τ => by rw [hf₂val, AlgEquiv.commutes])
    (fun σ => by rw [hf₂val, ← map_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow,
      map_one])
  -- transport the two radicals into the compositum
  set x₁ : L := algebraMap ↥E₁ L α₁ with hx₁def
  set x₂ : L := algebraMap ↥E₂ L α₂ with hx₂def
  have hx₁mem : x₁ ∈ E₁ := α₁.2
  have hx₂mem : x₂ ∈ E₂ := α₂.2
  have hx₁0 : x₁ ≠ 0 := fun h => hα₁0 ((map_eq_zero _).1 h)
  have hx₂0 : x₂ ≠ 0 := fun h => hα₂0 ((map_eq_zero _).1 h)
  have hx₁pow : x₁ ^ p = algebraMap K L w₁ := by
    rw [hx₁def, ← map_pow, ← hw₁, ← IsScalarTower.algebraMap_apply]
  have hx₂pow : x₂ ^ p = algebraMap K L w₂ := by
    rw [hx₂def, ← map_pow, ← hw₂, ← IsScalarTower.algebraMap_apply]
  have hσx₁ : ∀ σ : L ≃ₐ[K] L,
      σ x₁ = ζL ^ (χa (AlgEquiv.restrictNormalHom ↥E₁ σ)).val * x₁ := by
    intro σ
    have h := AlgEquiv.restrictNormal_commutes σ ↥E₁ α₁
    rw [hx₁def, ← h, show σ.restrictNormal ↥E₁ α₁ = AlgEquiv.restrictNormalHom ↥E₁ σ α₁ from rfl,
      hα₁, map_mul, hf₁val, ← IsScalarTower.algebraMap_apply, map_pow, hζLdef]
  have hσx₂ : ∀ σ : L ≃ₐ[K] L,
      σ x₂ = ζL ^ (χb (AlgEquiv.restrictNormalHom ↥E₂ σ)).val * x₂ := by
    intro σ
    have h := AlgEquiv.restrictNormal_commutes σ ↥E₂ α₂
    rw [hx₂def, ← h, show σ.restrictNormal ↥E₂ α₂ = AlgEquiv.restrictNormalHom ↥E₂ σ α₂ from rfl,
      hα₂, map_mul, hf₂val, ← IsScalarTower.algebraMap_apply, map_pow, hζLdef]
  -- the quotient is fixed, hence lies in the base
  have hγfix : ∀ σ : L ≃ₐ[K] L, σ (β / (x₁ * x₂)) = β / (x₁ * x₂) := by
    intro σ
    have hcong : (n σ : ℕ) ≡ (χa (AlgEquiv.restrictNormalHom ↥E₁ σ)).val
        + (χb (AlgEquiv.restrictNormalHom ↥E₂ σ)).val [MOD p] := by
      refine (ZMod.natCast_eq_natCast_iff _ _ _).1 ?_
      rw [Nat.cast_add, ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id,
        ← hsplit σ, hχdef]
    have hpow : ζL ^ n σ = ζL ^ ((χa (AlgEquiv.restrictNormalHom ↥E₁ σ)).val
        + (χb (AlgEquiv.restrictNormalHom ↥E₂ σ)).val) := (hmodEq _ _).2 hcong
    have hζL0 : ζL ≠ 0 := by
      rw [hζLdef]
      exact (map_ne_zero _).2 hζ0
    rw [map_div₀, map_mul, hnβ σ, hσx₁ σ, hσx₂ σ, hpow, pow_add]
    field_simp
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (β / (x₁ * x₂))).mpr hγfix
  refine ⟨c ^ p * w₁, w₂, ?_, ⟨algebraMap K L c * x₁, mul_mem (E₁.algebraMap_mem c) hx₁mem, ?_⟩,
    ⟨x₂, hx₂mem, hx₂pow⟩⟩
  · refine (algebraMap K L).injective ?_
    have hβeq : β = algebraMap K L c * (x₁ * x₂) := by
      rw [hc, div_mul_cancel₀ _ (mul_ne_zero hx₁0 hx₂0)]
    rw [← hβ, hβeq, mul_pow, mul_pow, hx₁pow, hx₂pow, ← map_pow]
    push_cast
    ring
  · rw [mul_pow, ← map_pow, hx₁pow, ← map_mul]

end Sup

end InverseGalois.CFT
