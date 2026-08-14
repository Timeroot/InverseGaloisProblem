/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.MultiKummerInertia
import InverseGalois.Rigidity.RET.SubUnramified

/-!
# The free abelian cover of the line with prescribed branch cycles

For `s + 1` distinct points `t₀, …, t_s` of `ℚ̄` and an exponent `n`, adjoining to `ℚ̄(T)` the `s`
radicals

`w_l ⁿ = (T - t_l) · (T - t_s)^{n-1}`,  `l < s`,

produces a cover of the line whose deck group is the free `ℤ/n`-module of rank `s`, branched
exactly over the `s + 1` points, with the standard branch cycles: the `l`-th coordinate vector at
`t_l`, and the inverse of the diagonal vector at `t_s`.

Every finite abelian group of exponent dividing `n`, presented by `s + 1` generators multiplying
to `1`, is a quotient of this deck group by a map carrying the standard tuple to the prescribed
generators, so descending to the Galois subcover cut out by the kernel realizes any prescribed
abelian branch-cycle datum.

## Main definitions

* `Rigidity.RET.freeExp` — the exponent vector `Fin (s+1) → ℕ` attached to a monomial in the
  radicals.
* `Rigidity.RET.zmodPowHom` — the homomorphism `ℤ/n → H`, `1 ↦ x`, for an element `x` of exponent
  dividing `n`.

## Main results

* `Rigidity.RET.prod_multiA_pow` — a product of powers of multi-point data is a multi-point datum.
* `Rigidity.RET.eq_one_of_fixes` — an automorphism fixing a generating set is the identity.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

/-! ### Products of multi-point data -/

section Data

variable {r : ℕ}

/-- **A product of powers of multi-point data is again a multi-point datum**, with exponents the
matrix product. -/
theorem prod_multiA_pow {ι : Type} [Fintype ι] (t : Fin r → k) (U : ι → Fin r → ℕ) (c : ι → ℕ) :
    ∏ l, (multiA t (U l)) ^ c l = multiA t (fun i => ∑ l, U l i * c l) := by
  classical
  simp only [multiA, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun l _ => by rw [← pow_mul]

end Data

/-! ### The exponent vectors of the free cover -/

section FreeExp

variable {s : ℕ}

/-- The exponent vector of the monomial `∏ w_l^{c_l}` in the radicals of the free cover: the
exponent of `T - t_l` is `c_l`, and the exponent of `T - t_s` is `(n-1) ∑ c_l`. -/
def freeExp (n : ℕ) (c : Fin s → ℕ) : Fin (s + 1) → ℕ :=
  Fin.lastCases ((n - 1) * ∑ l, c l) c

@[simp] theorem freeExp_castSucc (n : ℕ) (c : Fin s → ℕ) (j : Fin s) :
    freeExp n c j.castSucc = c j := by
  rw [freeExp, Fin.lastCases_castSucc]

@[simp] theorem freeExp_last (n : ℕ) (c : Fin s → ℕ) :
    freeExp n c (Fin.last s) = (n - 1) * ∑ l, c l := by
  rw [freeExp, Fin.lastCases_last]

/-- The exponent vectors of the individual radicals combine to the exponent vector of a monomial:
this is the compatibility that makes the monomial in the radicals a Kummer root of a multi-point
datum. -/
theorem freeExp_sum (n : ℕ) (c : Fin s → ℕ) :
    (fun i => ∑ l, freeExp n (Pi.single l 1) i * c l) = freeExp n c := by
  classical
  funext i
  induction i using Fin.lastCases with
  | last =>
      simp only [freeExp_last, Finset.sum_pi_single', Finset.mem_univ, if_true, mul_one,
        Finset.mul_sum]
  | cast j =>
      simp only [freeExp_castSucc, Pi.single_apply]
      rw [Finset.sum_eq_single j (fun l _ hl => by simp [Ne.symm hl])
        (fun h => absurd (Finset.mem_univ j) h)]
      simp

end FreeExp

/-! ### Two small pieces of general algebra -/

section General

/-- **An automorphism fixing a generating set is the identity.** -/
theorem eq_one_of_fixes {K M : Type} [Field K] [Field M] [Algebra K M] {S : Set M}
    (hS : IntermediateField.adjoin K S = ⊤) {σ : M ≃ₐ[K] M} (h : ∀ x ∈ S, σ x = x) : σ = 1 := by
  have hfix : IntermediateField.adjoin K S ≤
      IntermediateField.fixedField (Subgroup.closure {σ}) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    refine Subgroup.closure_induction (p := fun f _ => f x = x) ?_ rfl ?_ ?_ hf
    · rintro g rfl
      exact h x hx
    · intro g g' _ _ hg hg'
      show g (g' x) = x
      rw [hg', hg]
    · intro g _ hg
      have h2 : g⁻¹ (g x) = g⁻¹ x := by rw [hg]
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h2
      exact h2.symm
  rw [hS] at hfix
  ext x
  have hx : x ∈ IntermediateField.fixedField (Subgroup.closure {σ}) := hfix IntermediateField.mem_top
  rw [IntermediateField.mem_fixedField_iff] at hx
  exact hx σ (Subgroup.subset_closure rfl)

/-- **The homomorphism `ℤ/n → H` sending `1` to a prescribed element** of exponent dividing `n`. -/
def zmodPowHom {H : Type*} [CommGroup H] {n : ℕ} [NeZero n] {x : H} (hx : x ^ n = 1) :
    Multiplicative (ZMod n) →* H where
  toFun c := x ^ (Multiplicative.toAdd c).val
  map_one' := by simp
  map_mul' a b := by
    show x ^ ((Multiplicative.toAdd a + Multiplicative.toAdd b).val)
      = x ^ (Multiplicative.toAdd a).val * x ^ (Multiplicative.toAdd b).val
    rw [← pow_add]
    refine pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hx) ?_)
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _

theorem zmodPowHom_apply {H : Type*} [CommGroup H] {n : ℕ} [NeZero n] {x : H} (hx : x ^ n = 1)
    (c : ZMod n) : zmodPowHom hx (Multiplicative.ofAdd c) = x ^ c.val := rfl

@[simp] theorem zmodPowHom_ofAdd_one {H : Type*} [CommGroup H] {n : ℕ} [NeZero n] {x : H}
    (hx : x ^ n = 1) : zmodPowHom hx (Multiplicative.ofAdd 1) = x := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)) with h1 | h1
  · have hx1 : x = 1 := by rw [← pow_one x, h1, hx]
    rw [zmodPowHom_apply, hx1, one_pow]
  · haveI : Fact (1 < n) := ⟨h1⟩
    rw [zmodPowHom_apply, ZMod.val_one, pow_one]

/-- **A finite cyclic group of order `n` is `ℤ/n`**, by an isomorphism pinned by a chosen
generator. -/
def zmodPowEquiv {G : Type*} [CommGroup G] [Finite G] {n : ℕ} [NeZero n] {g : G}
    (hg : IsPrimitiveRoot g n) (hcard : Nat.card G = n) :
    Multiplicative (ZMod n) ≃* G :=
  MulEquiv.ofBijective (zmodPowHom hg.pow_eq_one) (by
    rw [Nat.bijective_iff_injective_and_card]
    constructor
    · rw [injective_iff_map_eq_one]
      intro x hx
      have hval : g ^ (Multiplicative.toAdd x).val = 1 := hx
      have hdvd : n ∣ (Multiplicative.toAdd x).val := by
        have hd := orderOf_dvd_of_pow_eq_one hval
        rwa [← hg.eq_orderOf] at hd
      have h0 : (Multiplicative.toAdd x).val = 0 :=
        Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
      have hz : (Multiplicative.toAdd x) = 0 := by
        have hc := congrArg (fun m : ℕ => (m : ZMod n)) h0
        simpa [ZMod.natCast_val, ZMod.cast_id] using hc
      exact (Multiplicative.toAdd (α := ZMod n)).injective (by simpa using hz)
    · rw [hcard, Nat.card_congr (Multiplicative.toAdd (α := ZMod n)), Nat.card_zmod])

@[simp] theorem zmodPowEquiv_ofAdd_one {G : Type*} [CommGroup G] [Finite G] {n : ℕ} [NeZero n]
    {g : G} (hg : IsPrimitiveRoot g n) (hcard : Nat.card G = n) :
    zmodPowEquiv hg hcard (Multiplicative.ofAdd 1) = g :=
  zmodPowHom_ofAdd_one hg.pow_eq_one

end General

/-! ### Kummer roots inside the geometric integral model -/

section RootB

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] {n : ℕ} [NeZero n] {a : Polynomial k}

/-- A Kummer root of a polynomial datum is integral over `ℚ̄[T]`. -/
theorem isIntegral_of_pow_eq (u : Ω)
    (hu : u ^ n = algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k) a)) :
    IsIntegral (Polynomial k) u :=
  ⟨X ^ n - C a, monic_X_pow_sub_C _ (NeZero.ne n), by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hu,
      IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) Ω, sub_self]⟩

/-- A Kummer root of a polynomial datum, as an element of the geometric integral model. -/
def rootB (u : Ω)
    (hu : u ^ n = algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k) a)) : Bring Ω :=
  ⟨u, isIntegral_of_pow_eq u hu⟩

@[simp] theorem rootB_coe (u : Ω)
    (hu : u ^ n = algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k) a)) :
    ((rootB u hu : Bring Ω) : Ω) = u := rfl

theorem rootB_pow (u : Ω)
    (hu : u ^ n = algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k) a)) :
    (rootB u hu) ^ n = algebraMap (Polynomial k) (Bring Ω) a := by
  apply Subtype.ext
  rw [Subalgebra.coe_pow, Subalgebra.coe_algebraMap, rootB_coe, hu,
    IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) Ω]

omit [Algebra (Polynomial k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- **An automorphism scales a Kummer root by a power of a fixed primitive root of unity.** -/
theorem exists_pow_smul {ζ₀ : k} (hζ₀ : IsPrimitiveRoot ζ₀ n) {u : Ω} (hu : u ≠ 0)
    {b : RatFunc k} (hb : u ^ n = algebraMap (RatFunc k) Ω b) (σ : Ω ≃ₐ[RatFunc k] Ω) :
    ∃ m : ℕ, σ u = algebraMap (RatFunc k) Ω ((algebraMap k (RatFunc k) ζ₀) ^ m) * u := by
  have hinj : Function.Injective
      ((algebraMap (RatFunc k) Ω).comp (algebraMap k (RatFunc k))) :=
    (algebraMap (RatFunc k) Ω).injective.comp (algebraMap k (RatFunc k)).injective
  have hζ : IsPrimitiveRoot
      ((algebraMap (RatFunc k) Ω) (algebraMap k (RatFunc k) ζ₀)) n :=
    hζ₀.map_of_injective (f := (algebraMap (RatFunc k) Ω).comp (algebraMap k (RatFunc k))) hinj
  have hbne : algebraMap (RatFunc k) Ω b ≠ 0 := hb ▸ pow_ne_zero n hu
  have hξ : (σ u / u) ^ n = 1 := by
    rw [div_pow, ← map_pow, hb, σ.commutes, div_self hbne]
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one hξ
  exact ⟨m, by rw [map_pow, hm, div_mul_cancel₀ _ hu]⟩

end RootB

/-! ### The data of the free abelian cover -/

section FreeData

/-- The radicand of the `l`-th radical of the free abelian cover on `s + 1` branch points:
the polynomial `(T - t_l) · (T - t_last)^{n-1}`. -/
def freeB (n : ℕ) {s : ℕ} (t : Fin (s + 1) → k) (l : Fin s) : RatFunc k :=
  algebraMap (Polynomial k) (RatFunc k) (multiA t (freeExp n (Pi.single l 1)))

theorem freeB_ne_zero (n : ℕ) {s : ℕ} (t : Fin (s + 1) → k) (l : Fin s) : freeB n t l ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (multiA_ne_zero _ _)

/-- The defining polynomial of the free abelian cover: the product of the `s` Kummer equations. -/
def freePoly (n : ℕ) {s : ℕ} (t : Fin (s + 1) → k) : (RatFunc k)[X] :=
  ∏ l, (X ^ n - C (freeB n t l))

theorem freePoly_ne_zero (n : ℕ) [NeZero n] {s : ℕ} (t : Fin (s + 1) → k) :
    freePoly n t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l _ => (monic_X_pow_sub_C (freeB n t l) (NeZero.ne n)).ne_zero

/-- The exponents of a single radicand sum to `n`. -/
theorem freeExp_sum_single (n : ℕ) [NeZero n] {s : ℕ} (l : Fin s) :
    ∑ i, freeExp n (Pi.single l 1) i = n * 1 := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [freeExp_castSucc, freeExp_last, Finset.sum_pi_single', Finset.mem_univ, if_true]
  have := NeZero.pos n
  omega

end FreeData

/-! ### Products of powers indexed by `Pi.single` -/

section ProdPow

variable {G : Type*} [CommMonoid G] {s : ℕ}

theorem prod_pow_add (u : Fin s → G) (A B : Fin s → ℕ) :
    ∏ m, u m ^ (A m + B m) = (∏ m, u m ^ A m) * ∏ m, u m ^ B m := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => pow_add _ _ _

theorem prod_pow_single (u : Fin s → G) (l : Fin s) (p : ℕ) :
    ∏ m, u m ^ (Pi.single l p m) = u l ^ p := by
  classical
  rw [Finset.prod_eq_single l (fun m _ hm => by rw [Pi.single_eq_of_ne hm, pow_zero])
    (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same]

end ProdPow

/-! ### The inclusion of the roots of unity -/

section RootsOfUnityVal

/-- The inclusion of the group of `n`-th roots of unity of a field into the field. -/
def rootsOfUnityVal (n : ℕ) (Ω : Type) [Field Ω] : rootsOfUnity n Ω →* Ω :=
  (Units.coeHom Ω).comp (rootsOfUnity n Ω).subtype

@[simp] theorem rootsOfUnityVal_apply {n : ℕ} {Ω : Type} [Field Ω] (u : rootsOfUnity n Ω) :
    rootsOfUnityVal n Ω u = ((u : Ωˣ) : Ω) := rfl

theorem rootsOfUnityVal_injective (n : ℕ) (Ω : Type) [Field Ω] :
    Function.Injective (rootsOfUnityVal n Ω) := fun _ _ h => Subtype.ext (Units.ext h)

theorem rootsOfUnity_pow_eq_one {n : ℕ} {Ω : Type} [Field Ω] (u : rootsOfUnity n Ω) : u ^ n = 1 := by
  have h := u.2
  rw [mem_rootsOfUnity] at h
  exact Subtype.ext (by simpa using h)

end RootsOfUnityVal

/-! ### The monodromy of the free abelian cover -/

section Monodromy

variable {s n : ℕ} [NeZero n] {t : Fin (s + 1) → k} {ζ₀ : k}
  {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] {y : Fin s → Ω}

/-- The chosen primitive `n`-th root of unity of the cover, as an element of `μₙ`. -/
def freeZeta (n : ℕ) [NeZero n] {ζ₀ : k} (hζ₀ : IsPrimitiveRoot ζ₀ n) (Ω : Type) [Field Ω]
    [Algebra (RatFunc k) Ω] : rootsOfUnity n Ω :=
  rootsOfUnity.mkOfPowEq (algebraMap (RatFunc k) Ω (algebraMap k (RatFunc k) ζ₀))
    (by rw [← map_pow, ← map_pow, hζ₀.pow_eq_one, map_one, map_one])

@[simp] theorem freeZeta_val (hζ₀ : IsPrimitiveRoot ζ₀ n) :
    rootsOfUnityVal n Ω (freeZeta n hζ₀ Ω)
      = algebraMap (RatFunc k) Ω (algebraMap k (RatFunc k) ζ₀) := by
  simp only [rootsOfUnityVal_apply, freeZeta]
  exact rootsOfUnity.coe_mkOfPowEq _

omit [NeZero n] in
/-- The chosen root of unity is primitive in the field of the cover. -/
theorem isPrimitiveRoot_algebraMap (hζ₀ : IsPrimitiveRoot ζ₀ n) :
    IsPrimitiveRoot (algebraMap (RatFunc k) Ω (algebraMap k (RatFunc k) ζ₀)) n :=
  (hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective).map_of_injective
    (algebraMap (RatFunc k) Ω).injective

/-- Every `n`-th root of unity is a power of the chosen primitive one. -/
theorem exists_pow_freeZeta (hζ₀ : IsPrimitiveRoot ζ₀ n) (u : rootsOfUnity n Ω) :
    ∃ a : ℕ, freeZeta n hζ₀ Ω ^ a = u := by
  have hu : rootsOfUnityVal n Ω u ^ n = 1 := by
    have h := u.2
    rw [mem_rootsOfUnity] at h
    simpa using congrArg Units.val h
  obtain ⟨a, -, ha⟩ := (isPrimitiveRoot_algebraMap (Ω := Ω) hζ₀).eq_pow_of_pow_eq_one hu
  exact ⟨a, rootsOfUnityVal_injective n Ω (by rw [map_pow, freeZeta_val, ha])⟩

/-- **The monodromy homomorphism of the free abelian cover**, recording how a deck
transformation scales each of the `s` radicals. -/
def freeTheta (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) :
    (Ω ≃ₐ[RatFunc k] Ω) →* (Fin s → rootsOfUnity n Ω) :=
  kummerHom (hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective) (freeB_ne_zero n t) hy

theorem freeTheta_val (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l))
    (σ : Ω ≃ₐ[RatFunc k] Ω) (l : Fin s) :
    rootsOfUnityVal n Ω (freeTheta hζ₀ hy σ l) = σ (y l) / y l := by
  simp only [rootsOfUnityVal_apply, freeTheta]
  exact kummerHom_apply _ _ _ σ l

theorem freeRoot_ne_zero (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) (l : Fin s) :
    y l ≠ 0 :=
  radical_ne_zero (freeB_ne_zero n t) hy l

theorem freeMonomial_ne_zero (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l))
    (c : Fin s → ℕ) : (∏ l, y l ^ c l) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l _ => pow_ne_zero _ (freeRoot_ne_zero hy l)

omit [NeZero n] in
/-- **The `n`-th power of a monomial in the radicals** is the datum with the exponent vector
`freeExp n c`. -/
theorem freeMonomial_pow (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l))
    (c : Fin s → ℕ) :
    (∏ l, y l ^ c l) ^ n
      = algebraMap (RatFunc k) Ω
          (algebraMap (Polynomial k) (RatFunc k) (multiA t (freeExp n c))) := by
  classical
  calc (∏ l, y l ^ c l) ^ n = ∏ l, (y l ^ n) ^ c l := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun l _ => by rw [← pow_mul, ← pow_mul, mul_comm]
    _ = ∏ l, (algebraMap (RatFunc k) Ω (freeB n t l)) ^ c l :=
        Finset.prod_congr rfl fun l _ => by rw [hy l]
    _ = algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k)
          (∏ l, multiA t (freeExp n (Pi.single l 1)) ^ c l)) := by
        rw [map_prod, map_prod]
        exact Finset.prod_congr rfl fun l _ => by rw [freeB, map_pow, map_pow]
    _ = _ := by rw [prod_multiA_pow, freeExp_sum]

/-- A monomial in the radicals fixed by a deck transformation gives a relation on its
monodromy exponents. -/
theorem freeTheta_prod_eq_one (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) (c : Fin s → ℕ)
    {σ : Ω ≃ₐ[RatFunc k] Ω} (hfix : σ (∏ l, y l ^ c l) = ∏ l, y l ^ c l) :
    ∏ l, freeTheta hζ₀ hy σ l ^ c l = 1 := by
  classical
  refine rootsOfUnityVal_injective n Ω ?_
  rw [map_prod, map_one]
  have h1 : ∀ l : Fin s, rootsOfUnityVal n Ω (freeTheta hζ₀ hy σ l ^ c l)
      = (σ (y l)) ^ c l / (y l) ^ c l := fun l => by
    rw [map_pow, freeTheta_val, div_pow]
  rw [Finset.prod_congr rfl fun l _ => h1 l, Finset.prod_div_distrib]
  have h2 : ∏ l, (σ (y l)) ^ c l = ∏ l, y l ^ c l := by
    rw [← hfix, map_prod]
    exact Finset.prod_congr rfl fun l _ => (map_pow σ _ _).symm
  rw [h2, div_self (freeMonomial_ne_zero hy c)]

/-- **The radicals generate the free abelian cover.** -/
theorem freeRoots_adjoin_eq_top [IsSplittingField (RatFunc k) Ω (freePoly n t)]
    (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) :
    IntermediateField.adjoin (RatFunc k) (Set.range y) = ⊤ := by
  classical
  have hζΩ : IsPrimitiveRoot (algebraMap (RatFunc k) Ω (algebraMap k (RatFunc k) ζ₀)) n :=
    (hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective).map_of_injective
      (algebraMap (RatFunc k) Ω).injective
  have h1 : Algebra.adjoin (RatFunc k) ((freePoly n t).rootSet Ω) = ⊤ :=
    IsSplittingField.adjoin_rootSet _ _
  have h2 : (freePoly n t).rootSet Ω ⊆
      ((IntermediateField.adjoin (RatFunc k) (Set.range y) : IntermediateField (RatFunc k) Ω) :
        Set Ω) := by
    intro x hx
    have hev : (Polynomial.aeval x) (freePoly n t) = 0 := (Polynomial.mem_rootSet.mp hx).2
    rw [freePoly, map_prod] at hev
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hev
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hl
    have hxn : x ^ n = y l ^ n := by rw [hl, hy l]
    have hyl : y l ≠ 0 := freeRoot_ne_zero hy l
    have hone : (x / y l) ^ n = 1 := by rw [div_pow, hxn, div_self (pow_ne_zero _ hyl)]
    obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one hone
    have hxeq : x = algebraMap (RatFunc k) Ω ((algebraMap k (RatFunc k) ζ₀) ^ i) * y l := by
      rw [map_pow, hi, div_mul_cancel₀ _ hyl]
    rw [SetLike.mem_coe, hxeq]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin _ _ ⟨l, rfl⟩)
  have h3 : (⊤ : Subalgebra (RatFunc k) Ω) ≤
      (IntermediateField.adjoin (RatFunc k) (Set.range y)).toSubalgebra := by
    rw [← h1]; exact Algebra.adjoin_le h2
  exact eq_top_iff.mpr fun x _ => h3 Algebra.mem_top

/-- **The monodromy of the free abelian cover is injective.** -/
theorem freeTheta_injective [IsSplittingField (RatFunc k) Ω (freePoly n t)]
    (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) :
    Function.Injective (freeTheta hζ₀ hy) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine eq_one_of_fixes (freeRoots_adjoin_eq_top hζ₀ hy) ?_
  rintro x ⟨l, rfl⟩
  have h1 : rootsOfUnityVal n Ω (freeTheta hζ₀ hy σ l) = 1 := by
    rw [show freeTheta hζ₀ hy σ l = 1 from congrFun hσ l, map_one]
  rw [freeTheta_val] at h1
  exact (div_eq_one_iff_eq (freeRoot_ne_zero hy l)).mp h1

/-- **The monodromy of the free abelian cover is surjective**: the radicands are independent
modulo `n`-th powers because their exponent vectors are. -/
theorem freeTheta_surjective [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω]
    (ht : Function.Injective t) (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) :
    Function.Surjective (freeTheta hζ₀ hy) := by
  classical
  refine kummerHom_surjective _ _ _ ?_
  rintro e he ⟨c, hc⟩ l
  have h1 : ∏ l, freeB n t l ^ e l
      = algebraMap (Polynomial k) (RatFunc k) (multiA t (freeExp n e)) := by
    rw [show (∏ l, freeB n t l ^ e l)
        = algebraMap (Polynomial k) (RatFunc k)
            (∏ l, multiA t (freeExp n (Pi.single l 1)) ^ e l) by
      rw [map_prod]; exact Finset.prod_congr rfl fun l _ => by rw [freeB, map_pow],
      prod_multiA_pow, freeExp_sum]
  rw [h1] at hc
  have h2 : ∏ i, (RatFunc.X - RatFunc.C (t i)) ^ (freeExp n e i) = c ^ n := by
    rw [← hc]; simpa using (multiA_map_pow t (freeExp n e) 1).symm
  have hdvd := dvd_of_prod_linear_isPow ht (freeExp n e) ⟨c, h2⟩ l.castSucc
  rw [freeExp_castSucc] at hdvd
  exact Nat.eq_zero_of_dvd_of_lt hdvd (he l)

theorem freeZeta_isPrimitiveRoot (hζ₀ : IsPrimitiveRoot ζ₀ n) :
    IsPrimitiveRoot (freeZeta n hζ₀ Ω) n := by
  refine IsPrimitiveRoot.of_map_of_injective (f := rootsOfUnityVal n Ω) ?_
    (rootsOfUnityVal_injective n Ω)
  rw [freeZeta_val]
  exact isPrimitiveRoot_algebraMap hζ₀

theorem card_rootsOfUnity_eq (hζ₀ : IsPrimitiveRoot ζ₀ n) : Nat.card (rootsOfUnity n Ω) = n := by
  haveI : HasEnoughRootsOfUnity Ω n :=
    ⟨⟨_, isPrimitiveRoot_algebraMap (Ω := Ω) hζ₀⟩, rootsOfUnity.isCyclic Ω n⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω n

/-- **`ℤ/n` is the group of `n`-th roots of unity**, by the isomorphism pinned by the chosen
primitive root. -/
def freeZetaEquiv (hζ₀ : IsPrimitiveRoot ζ₀ n) (Ω : Type) [Field Ω] [Algebra (RatFunc k) Ω] :
    Multiplicative (ZMod n) ≃* rootsOfUnity n Ω :=
  zmodPowEquiv (freeZeta_isPrimitiveRoot (Ω := Ω) hζ₀) (card_rootsOfUnity_eq hζ₀)

@[simp] theorem freeZetaEquiv_ofAdd_one (hζ₀ : IsPrimitiveRoot ζ₀ n) :
    freeZetaEquiv hζ₀ Ω (Multiplicative.ofAdd 1) = freeZeta n hζ₀ Ω :=
  zmodPowEquiv_ofAdd_one _ _

end Monodromy

/-! ### The inertia groups of the free abelian cover -/

section Inertia

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

variable {s n : ℕ} [NeZero n] {t : Fin (s + 1) → k} {ζ₀ : k}
  {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω]
  [IsGalois (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] {y : Fin s → Ω}

omit [FiniteDimensional (RatFunc k) Ω] in
/-- **The inertia bound at a branch point of the free abelian cover**: an inertia element fixes
every monomial in the radicals whose exponent at that point is divisible by `n`. -/
theorem inertia_fix_monomial (ht : Function.Injective t) (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l))
    (c : Fin s → ℕ) (i : Fin (s + 1)) (hdvd : n ∣ freeExp n c i)
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP (t i))]
    {σ : Ω ≃ₐ[RatFunc k] Ω} (hσ : σ ∈ geomInertia Ω Q) :
    σ (∏ l, y l ^ c l) = ∏ l, y l ^ c l := by
  have hv0 : (∏ l, y l ^ c l) ≠ 0 := freeMonomial_ne_zero hy c
  have hvpow : (∏ l, y l ^ c l) ^ n = algebraMap (RatFunc k) Ω
      (algebraMap (Polynomial k) (RatFunc k) (multiA t (freeExp n c))) := freeMonomial_pow hy c
  obtain ⟨m, hm⟩ := exists_pow_smul hζ₀ hv0 hvpow σ
  have hgcd : Nat.gcd n (freeExp n c i) ∣ m :=
    gcd_dvd_of_mem_inertia_multi ht i (rootB (∏ l, y l ^ c l) hvpow)
      (rootB_pow _ hvpow) Q hσ hζ₀ hm
  rw [Nat.gcd_eq_left hdvd] at hgcd
  obtain ⟨q, rfl⟩ := hgcd
  have hz : (algebraMap k (RatFunc k) ζ₀) ^ (n * q) = 1 := by
    rw [pow_mul, ← map_pow, hζ₀.pow_eq_one, map_one, one_pow]
  rw [hm, hz, map_one, one_mul]

omit [FiniteDimensional (RatFunc k) Ω] in
/-- An inertia element at `t_j` acts trivially on every radical other than the `j`-th. -/
theorem freeTheta_inertia_eq_one (ht : Function.Injective t) (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) (j : Fin s)
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP (t j.castSucc))]
    {σ : Ω ≃ₐ[RatFunc k] Ω} (hσ : σ ∈ geomInertia Ω Q) {l : Fin s} (hl : l ≠ j) :
    freeTheta hζ₀ hy σ l = 1 := by
  have hfix := inertia_fix_monomial ht hζ₀ hy (Pi.single l 1) j.castSucc
    (by rw [freeExp_castSucc, Pi.single_eq_of_ne (Ne.symm hl)]; exact dvd_zero n) Q hσ
  rw [prod_pow_single, pow_one] at hfix
  refine rootsOfUnityVal_injective n Ω ?_
  rw [freeTheta_val, map_one, hfix, div_self (freeRoot_ne_zero hy l)]

/-- The radicals ramify to the full order `n` at their own branch point. -/
theorem le_card_inertia_castSucc (ht : Function.Injective t)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) (j : Fin s)
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP (t j.castSucc))] :
    n ≤ Nat.card (geomInertia Ω Q) := by
  have hyj : y j ^ n = algebraMap (RatFunc k) Ω
      (algebraMap (Polynomial k) (RatFunc k) (multiA t (freeExp n (Pi.single j 1)))) := hy j
  have hdvd := multi_pow_dvd_map_placeP ht j.castSucc (rootB (y j) hyj) (rootB_pow (y j) hyj) Q
  rw [freeExp_castSucc, Pi.single_eq_same, Nat.gcd_one_right, Nat.div_one] at hdvd
  exact le_card_geomInertia_of_pow_dvd (t j.castSucc) Q hdvd

/-- The radicals ramify to the full order `n` at the last branch point. -/
theorem le_card_inertia_last (ht : Function.Injective t)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l)) (l₀ : Fin s)
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP (t (Fin.last s)))] :
    n ≤ Nat.card (geomInertia Ω Q) := by
  classical
  have hyl : y l₀ ^ n = algebraMap (RatFunc k) Ω
      (algebraMap (Polynomial k) (RatFunc k) (multiA t (freeExp n (Pi.single l₀ 1)))) := hy l₀
  have hcop : Nat.gcd n (n - 1) = 1 := by
    have h1 := Nat.gcd_dvd_left n (n - 1)
    have h2 := Nat.gcd_dvd_right n (n - 1)
    have h3 := Nat.dvd_sub h1 h2
    rw [Nat.sub_sub_self (NeZero.pos n)] at h3
    exact Nat.dvd_one.mp h3
  have hexp : freeExp n (Pi.single l₀ 1) (Fin.last s) = n - 1 := by
    rw [freeExp_last]
    simp
  have hdvd := multi_pow_dvd_map_placeP ht (Fin.last s) (rootB (y l₀) hyl)
    (rootB_pow (y l₀) hyl) Q
  rw [hexp, hcop, Nat.div_one] at hdvd
  exact le_card_geomInertia_of_pow_dvd (t (Fin.last s)) Q hdvd

/-- **The inertia group of the free abelian cover at the branch point `t_j`, `j < s`**: the cyclic
group generated by the `j`-th coordinate vector. -/
theorem geomInertia_free_castSucc [IsSplittingField (RatFunc k) Ω (freePoly n t)]
    (ht : Function.Injective t) (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l))
    (E : (Ω ≃ₐ[RatFunc k] Ω) ≃* (Fin s → rootsOfUnity n Ω))
    (hE : ∀ σ, E σ = freeTheta hζ₀ hy σ) (j : Fin s)
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP (t j.castSucc))] :
    geomInertia Ω Q = Subgroup.zpowers (E.symm (Pi.mulSingle j (freeZeta n hζ₀ Ω))) := by
  classical
  have hle : geomInertia Ω Q ≤ Subgroup.zpowers (E.symm (Pi.mulSingle j (freeZeta n hζ₀ Ω))) := by
    intro σ hσ
    obtain ⟨a, ha⟩ := exists_pow_freeZeta hζ₀ (freeTheta hζ₀ hy σ j)
    have h2 : E σ = (Pi.mulSingle j (freeZeta n hζ₀ Ω)) ^ a := by
      rw [hE]
      funext l
      rcases eq_or_ne l j with rfl | hl
      · rw [Pi.pow_apply, Pi.mulSingle_eq_same, ha]
      · rw [Pi.pow_apply, Pi.mulSingle_eq_of_ne hl, one_pow,
          freeTheta_inertia_eq_one ht hζ₀ hy j Q hσ hl]
    refine ⟨(a : ℤ), ?_⟩
    show (E.symm (Pi.mulSingle j (freeZeta n hζ₀ Ω))) ^ (a : ℤ) = σ
    rw [zpow_natCast, ← map_pow, ← h2, MulEquiv.symm_apply_apply]
  have hpi : (Pi.mulSingle j (freeZeta n hζ₀ Ω) : Fin s → rootsOfUnity n Ω) ^ n = 1 := by
    funext l
    rw [Pi.pow_apply, Pi.one_apply]
    rcases eq_or_ne l j with rfl | hl
    · rw [Pi.mulSingle_eq_same, rootsOfUnity_pow_eq_one]
    · rw [Pi.mulSingle_eq_of_ne hl, one_pow]
  have hgn : (E.symm (Pi.mulSingle j (freeZeta n hζ₀ Ω))) ^ n = 1 := by
    rw [← map_pow, hpi, map_one]
  refine Subgroup.eq_of_le_of_card_le' hle ?_
  rw [Nat.card_zpowers]
  exact le_trans (orderOf_le_of_pow_eq_one (NeZero.pos n) hgn)
    (le_card_inertia_castSucc ht hy j Q)

/-- **The inertia group of the free abelian cover at the last branch point**: the cyclic group
generated by the inverse of the diagonal vector. -/
theorem geomInertia_free_last [IsSplittingField (RatFunc k) Ω (freePoly n t)]
    (ht : Function.Injective t) (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l))
    (E : (Ω ≃ₐ[RatFunc k] Ω) ≃* (Fin s → rootsOfUnity n Ω))
    (hE : ∀ σ, E σ = freeTheta hζ₀ hy σ) (l₀ : Fin s)
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP (t (Fin.last s)))] :
    geomInertia Ω Q = Subgroup.zpowers (E.symm (fun _ => freeZeta n hζ₀ Ω)⁻¹) := by
  classical
  have hswap : Subgroup.zpowers (E.symm (fun _ => freeZeta n hζ₀ Ω)⁻¹)
      = Subgroup.zpowers (E.symm (fun _ => freeZeta n hζ₀ Ω)) := by
    rw [map_inv, Subgroup.zpowers_inv]
  rw [hswap]
  have hinv : ∀ u : rootsOfUnity n Ω, u ^ (n - 1) = u⁻¹ := fun u => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos n), rootsOfUnity_pow_eq_one]
  have hle : geomInertia Ω Q ≤ Subgroup.zpowers (E.symm (fun _ => freeZeta n hζ₀ Ω)) := by
    intro σ hσ
    -- every coordinate of the monodromy of `σ` agrees with the `l₀`-th
    have hconst : ∀ l : Fin s, freeTheta hζ₀ hy σ l = freeTheta hζ₀ hy σ l₀ := by
      intro l
      have hsum : ∑ m, (Pi.single l 1 + Pi.single l₀ (n - 1) : Fin s → ℕ) m = n := by
        simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
          if_true]
        have := NeZero.pos n
        omega
      have hdvd : n ∣ freeExp n (Pi.single l 1 + Pi.single l₀ (n - 1)) (Fin.last s) := by
        rw [freeExp_last, hsum]
        exact dvd_mul_left n (n - 1)
      have hfix := inertia_fix_monomial ht hζ₀ hy _ (Fin.last s) hdvd Q hσ
      have hrel := freeTheta_prod_eq_one hζ₀ hy _ hfix
      simp only [Pi.add_apply] at hrel
      rw [prod_pow_add, prod_pow_single, prod_pow_single, pow_one, hinv] at hrel
      exact eq_of_div_eq_one (by rwa [div_eq_mul_inv])
    obtain ⟨a, ha⟩ := exists_pow_freeZeta hζ₀ (freeTheta hζ₀ hy σ l₀)
    have h2 : E σ = (fun _ => freeZeta n hζ₀ Ω) ^ a := by
      rw [hE]
      funext l
      rw [Pi.pow_apply, hconst l, ha]
    refine ⟨(a : ℤ), ?_⟩
    show (E.symm (fun _ => freeZeta n hζ₀ Ω)) ^ (a : ℤ) = σ
    rw [zpow_natCast, ← map_pow, ← h2, MulEquiv.symm_apply_apply]
  have hpi : ((fun _ => freeZeta n hζ₀ Ω) : Fin s → rootsOfUnity n Ω) ^ n = 1 := by
    funext l
    rw [Pi.pow_apply, Pi.one_apply, rootsOfUnity_pow_eq_one]
  have hgn : (E.symm (fun _ => freeZeta n hζ₀ Ω)) ^ n = 1 := by
    rw [← map_pow, hpi, map_one]
  refine Subgroup.eq_of_le_of_card_le' hle ?_
  rw [Nat.card_zpowers]
  exact le_trans (orderOf_le_of_pow_eq_one (NeZero.pos n) hgn)
    (le_card_inertia_last ht hy l₀ Q)

omit [FiniteDimensional (RatFunc k) Ω] in
/-- **The free abelian cover is unramified away from the `s + 1` branch points.** -/
theorem free_inertia_eq_one_outside [IsSplittingField (RatFunc k) Ω (freePoly n t)]
    (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) Ω (freeB n t l))
    {p : k} (hp : p ∉ Set.range t) (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP p)]
    {σ : Ω ≃ₐ[RatFunc k] Ω} (hσ : σ ∈ geomInertia Ω Q) : σ = 1 := by
  refine eq_one_of_fixes (freeRoots_adjoin_eq_top hζ₀ hy) ?_
  rintro x ⟨l, rfl⟩
  have hyl : y l ^ n = algebraMap (RatFunc k) Ω
      (algebraMap (Polynomial k) (RatFunc k) (multiA t (freeExp n (Pi.single l 1)))) := hy l
  obtain ⟨m, hm⟩ := exists_pow_smul hζ₀ (freeRoot_ne_zero hy l) (hy l) σ
  have hnot : rootB (y l) hyl ∉ Q := by
    intro hmem
    refine notMem_of_eval_ne_zero (Ω := Ω) (t := p)
      (b := multiA t (freeExp n (Pi.single l 1)))
      (multiA_eval fun i h => hp ⟨i, h.symm⟩) Q ?_
    rw [← rootB_pow (y l) hyl]
    exact Ideal.pow_mem_of_mem Q hmem n (NeZero.pos n)
  have hsmul : σ • rootB (y l) hyl
      = algebraMap (Polynomial k) (Bring Ω) (C (ζ₀ ^ m)) * rootB (y l) hyl := by
    apply Subtype.ext
    rw [coe_smul_geom, Submonoid.coe_mul, Subalgebra.coe_algebraMap]
    show σ (y l) = algebraMap (Polynomial k) Ω (C (ζ₀ ^ m)) * y l
    rw [hm]
    congr 1
    rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) Ω, ← map_pow]
    congr 1
  have hone : ζ₀ ^ m = 1 := const_eq_one_of_mem_inertia (Ω := Ω) Q hσ hnot hsmul
  rw [hm, ← map_pow, hone, map_one, map_one, one_mul]

end Inertia

/-! ### The free abelian cover -/

section Cover

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

variable {s n : ℕ} [NeZero n] {t : Fin (s + 1) → k} {ζ₀ : k}

/-- **The free abelian cover is unramified at the point at infinity**: each radical has total
degree `n`, so it has no pole there. -/
theorem free_isUnramifiedAtInfinity (M : Type) [Field M] [Algebra (RatFunc k) M]
    [Algebra (Polynomial k) M] [IsScalarTower (Polynomial k) (RatFunc k) M]
    [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
    [IsSplittingField (RatFunc k) M (freePoly n t)] (hζ₀ : IsPrimitiveRoot ζ₀ n)
    {y : Fin s → M} (hy : ∀ l, y l ^ n = algebraMap (RatFunc k) M (freeB n t l)) :
    ({ M := M } : LineCover).IsUnramifiedAtInfinity := by
  have hy' : ∀ l, y l ^ n = algebraMap (RatFunc k) M
      (algebraMap (Polynomial k) (RatFunc k) (multiA t (freeExp n (Pi.single l 1)))) := hy
  have hupow : ∀ l, (twistRootS 1 (y l)) ^ n =
      algebraMap (RatFunc k) (Twist (↑invSubst) M)
        (algebraMap (Polynomial k) (RatFunc k) (revMultiA t (freeExp n (Pi.single l 1)))) :=
    fun l => twistRootS_pow t _ (freeExp_sum_single n l) (y l) (hy' l)
  have hpolyinj' : Function.Injective
      ((algebraMap (RatFunc k) (Twist (↑invSubst) M)).comp
        (algebraMap (Polynomial k) (RatFunc k))) :=
    (algebraMap (RatFunc k) (Twist (↑invSubst) M)).injective.comp
      (IsFractionRing.injective (Polynomial k) (RatFunc k))
  have hu0 : ∀ l, (twistRootS 1 (y l) : Twist (↑invSubst) M) ≠ 0 := by
    intro l h
    have hp := hupow l
    rw [h, zero_pow (NeZero.ne n)] at hp
    have hz : ((algebraMap (RatFunc k) (Twist (↑invSubst) M)).comp
        (algebraMap (Polynomial k) (RatFunc k))) (revMultiA t (freeExp n (Pi.single l 1)))
        = ((algebraMap (RatFunc k) (Twist (↑invSubst) M)).comp
          (algebraMap (Polynomial k) (RatFunc k))) 0 := by
      rw [map_zero]; exact hp.symm
    exact revMultiA_ne_zero t _ (hpolyinj' hz)
  rintro τ ⟨Q, hQmax, hQover, hτ⟩
  haveI := hQmax
  haveI := hQover
  set σ : M ≃ₐ[RatFunc k] M := Twist.unaut τ with hσdef
  have hXinv : algebraMap (RatFunc k) M ((RatFunc.X)⁻¹ ^ 1) ≠ 0 := by
    refine (map_ne_zero_iff _ (algebraMap (RatFunc k) M).injective).mpr ?_
    exact pow_ne_zero _ (inv_ne_zero (RatFunc.X_ne_zero (K := k)))
  have hσy : ∀ l, σ (y l) = y l := by
    intro l
    have hfix : τ (twistRootS (N := M) 1 (y l)) = twistRootS (N := M) 1 (y l) :=
      kummer_fix_of_mem_inertia_zero_unit n
        (by rw [revMultiA_eval_zero]; exact one_ne_zero) (hu0 l) (hupow l) Q hτ
    have hσu : σ (y l * algebraMap (RatFunc k) M ((RatFunc.X)⁻¹ ^ 1))
        = y l * algebraMap (RatFunc k) M ((RatFunc.X)⁻¹ ^ 1) := hfix
    rw [map_mul, σ.commutes] at hσu
    exact mul_right_cancel₀ hXinv hσu
  have hσ1 : σ = 1 :=
    eq_one_of_fixes (freeRoots_adjoin_eq_top hζ₀ hy) (by rintro x ⟨l, rfl⟩; exact hσy l)
  have hτaut : τ = Twist.aut σ := AlgEquiv.ext fun _ => rfl
  rw [hτaut, hσ1]
  exact AlgEquiv.ext fun _ => rfl

/-- **The free abelian cover of the line**: for `s + 1` points of the line there is a cover with
deck group `(ℤ/n)^s`, unramified outside those points, whose inertia at the first `s` points is
generated by the coordinate vectors and whose inertia at the last point is generated by the
inverse of their product.  It is cut out by the `s` Kummer equations. -/
theorem exists_cover_free (n : ℕ) [NeZero n] {s : ℕ} (t : Fin (s + 1) → k)
    (ht : Function.Injective t) :
    ∃ (L : LineCover) (e : L.deck ≃* (Fin s → Multiplicative (ZMod n))),
      IsSplittingField (RatFunc k) L.M (freePoly n t) ∧
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      (∀ j : Fin s, L.IsInertiaGenAt (t j.castSucc)
          (e.symm (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod n))))) ∧
      (0 < s → L.IsInertiaGenAt (t (Fin.last s))
          (e.symm (fun _ => Multiplicative.ofAdd (1 : ZMod n))⁻¹)) := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot_k n
  have hζ : IsPrimitiveRoot (algebraMap k (RatFunc k) ζ₀) n :=
    hζ₀.map_of_injective (algebraMap k (RatFunc k)).injective
  let M := (freePoly n t).SplittingField
  haveI : FiniteDimensional (RatFunc k) M := IsSplittingField.finiteDimensional M (freePoly n t)
  haveI : Normal (RatFunc k) M := Normal.of_isSplittingField (freePoly n t)
  haveI : PerfectField (RatFunc k) := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic (RatFunc k) M := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (RatFunc k) M := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois (RatFunc k) M := ⟨⟩
  have hroot : ∀ l, ∃ x : M, x ^ n = algebraMap (RatFunc k) M (freeB n t l) := by
    intro l
    have hdvdP : ((X : (RatFunc k)[X]) ^ n - C (freeB n t l)) ∣ freePoly n t := by
      rw [freePoly]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ l)
    have hsplit : (((X : (RatFunc k)[X]) ^ n - C (freeB n t l)).map
        (algebraMap (RatFunc k) M)).Splits :=
      Polynomial.Splits.of_dvd (IsSplittingField.splits M (freePoly n t))
        ((Polynomial.map_ne_zero_iff (algebraMap (RatFunc k) M).injective).mpr
          (freePoly_ne_zero n t))
        (Polynomial.map_dvd _ hdvdP)
    obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero (by
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
        degree_X_pow_sub_C (NeZero.pos n)]
      exact_mod_cast (NeZero.pos n).ne')
    refine ⟨x, ?_⟩
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] at hx
    exact hx
  choose y hy using hroot
  -- the cover, with the integral model that `M` already carries
  let L : LineCover := { M := M }
  haveI : IsSplittingField (RatFunc k) L.M (freePoly n t) :=
    inferInstanceAs (IsSplittingField (RatFunc k) M (freePoly n t))
  let E : L.deck ≃* (Fin s → rootsOfUnity n M) :=
    MulEquiv.ofBijective (freeTheta hζ₀ hy)
      ⟨freeTheta_injective hζ₀ hy, freeTheta_surjective ht hζ₀ hy⟩
  have hE : ∀ σ, E σ = freeTheta hζ₀ hy σ := fun _ => rfl
  let ν : Multiplicative (ZMod n) ≃* rootsOfUnity n M := freeZetaEquiv hζ₀ M
  refine ⟨L, E.trans (MulEquiv.piCongrRight fun _ => ν.symm), inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro p hp σ ⟨Q, hQmax, hQover, hσ⟩
    haveI := hQmax
    haveI := hQover
    exact free_inertia_eq_one_outside hζ₀ hy hp Q hσ
  · show ({ M := M } : LineCover).IsUnramifiedAtInfinity
    exact free_isUnramifiedAtInfinity M hζ₀ hy
  · intro j
    have hcoord : (fun l => ν ((Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod n)) :
          Fin s → Multiplicative (ZMod n)) l))
        = Pi.mulSingle j (freeZeta n hζ₀ M) := by
      funext l
      rcases eq_or_ne l j with rfl | hl
      · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
        exact freeZetaEquiv_ofAdd_one hζ₀
      · rw [Pi.mulSingle_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl, map_one]
    have hsym : (E.trans (MulEquiv.piCongrRight fun _ => ν.symm)).symm
        (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod n)))
        = E.symm (Pi.mulSingle j (freeZeta n hζ₀ M)) := by
      rw [← hcoord]; rfl
    rw [hsym]
    obtain ⟨Q, hQmax, hQover⟩ := L.exists_place (t j.castSucc)
    haveI := hQmax
    haveI := hQover
    exact ⟨Q, hQmax, hQover, geomInertia_free_castSucc ht hζ₀ hy E hE j Q⟩
  · intro hs
    obtain ⟨l₀⟩ : Nonempty (Fin s) := Fin.pos_iff_nonempty.mp hs
    have hcoord : (fun l => ν ((((fun _ => Multiplicative.ofAdd (1 : ZMod n)) :
          Fin s → Multiplicative (ZMod n))⁻¹) l))
        = (fun _ => freeZeta n hζ₀ M)⁻¹ := by
      funext l
      rw [Pi.inv_apply, Pi.inv_apply, map_inv]
      exact congrArg Inv.inv (freeZetaEquiv_ofAdd_one hζ₀)
    have hsym : (E.trans (MulEquiv.piCongrRight fun _ => ν.symm)).symm
        ((fun _ => Multiplicative.ofAdd (1 : ZMod n))⁻¹)
        = E.symm (fun _ => freeZeta n hζ₀ M)⁻¹ := by
      rw [← hcoord]; rfl
    rw [hsym]
    obtain ⟨Q, hQmax, hQover⟩ := L.exists_place (t (Fin.last s))
    haveI := hQmax
    haveI := hQover
    exact ⟨Q, hQmax, hQover, geomInertia_free_last ht hζ₀ hy E hE l₀ Q⟩

end Cover

end Rigidity.RET
