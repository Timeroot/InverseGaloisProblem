/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.RadicalAut

/-!
# Descending a radicand along a radical extension

Let `K` be a field containing a primitive `p`-th root of unity and let `M` be generated over `K`
by radicals `βᵢ` with `βᵢ ^ p = bᵢ ∈ K`.  If an element `x` of `K` acquires a `p`-th root inside
`M`, then `x` differs from a monomial `∏ bᵢ ^ eᵢ` by a `p`-th power of `K`.

The proof is linear algebra over `ZMod p`.  An automorphism `σ` of `M / K` multiplies each radical
`βᵢ` by a `p`-th root of unity, and recording the corresponding exponents assembles an additive map
`Θ` from the Galois group to `ι → ZMod p`; the same recipe applied to the `p`-th root `y` of `x`
gives an additive map `ε` to `ZMod p`.  Because the `βᵢ` generate `M`, the map `Θ` is injective, so
`ε` factors through the image of `Θ` and extends to a linear functional on all of `ι → ZMod p`.
The coordinates `eᵢ` of that functional are the sought exponents: the quotient of `y` by
`∏ βᵢ ^ eᵢ` is then fixed by the whole Galois group and therefore lies in `K`.

## Main results

* `InverseGalois.CFT.rootOfUnityExp` — the exponent expressing a `p`-th root of unity as a power
  of a chosen primitive one.
* `InverseGalois.CFT.exists_pow_prod_of_pow_eq_of_adjoin_eq_top` — the descent of the radicand.
-/

namespace InverseGalois.CFT

/-! ### Exponents of roots of unity -/

section RootOfUnityExp

variable {G : Type*} [CommRing G] [IsDomain G]

/-- The exponent, taken in `ZMod p`, expressing a `p`-th root of unity as a power of a chosen
primitive one. -/
noncomputable def rootOfUnityExp (ζ : G) (p : ℕ) [NeZero p] (g : G) : ZMod p :=
  Function.invFun (fun c : ZMod p => ζ ^ c.val) g

variable {p : ℕ} [NeZero p] {ζ : G}

omit [IsDomain G] [NeZero p] in
/-- Powers of a primitive `p`-th root of unity depend only on the exponent modulo `p`. -/
theorem pow_eq_pow_of_natCast_eq (hζ : IsPrimitiveRoot ζ p) {m n : ℕ}
    (h : (m : ZMod p) = (n : ZMod p)) : ζ ^ m = ζ ^ n := by
  have key : ∀ a : ℕ, ζ ^ (a % p) = ζ ^ a := fun a => by
    conv_rhs => rw [← Nat.div_add_mod a p]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [← key m, ← key n, (ZMod.natCast_eq_natCast_iff' m n p).1 h]

omit [IsDomain G] in
/-- Distinct residues give distinct powers of a primitive `p`-th root of unity. -/
theorem pow_val_injective (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective fun c : ZMod p => ζ ^ c.val := fun a c hac =>
  calc a = ((a.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val a).symm
    _ = ((c.val : ℕ) : ZMod p) := by rw [hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt c) hac]
    _ = c := ZMod.natCast_zmod_val c

/-- The exponent recovers a `p`-th root of unity from a primitive one. -/
theorem pow_rootOfUnityExp_val (hζ : IsPrimitiveRoot ζ p) {g : G} (hg : g ^ p = 1) :
    ζ ^ (rootOfUnityExp ζ p g).val = g := by
  obtain ⟨i, -, hig⟩ := hζ.eq_pow_of_pow_eq_one hg
  have hex : ∃ c : ZMod p, (fun c : ZMod p => ζ ^ c.val) c = g := by
    refine ⟨(i : ZMod p), ?_⟩
    simp only
    rw [← hig]
    exact pow_eq_pow_of_natCast_eq hζ (ZMod.natCast_zmod_val ((i : ZMod p)))
  exact Function.invFun_eq hex

/-- The exponent is determined by the power that it produces. -/
theorem rootOfUnityExp_eq (hζ : IsPrimitiveRoot ζ p) {g : G} {c : ZMod p} (h : ζ ^ c.val = g) :
    rootOfUnityExp ζ p g = c := by
  have hg : g ^ p = 1 := by
    rw [← h, ← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  exact pow_val_injective hζ ((pow_rootOfUnityExp_val hζ hg).trans h.symm)

/-- The exponent turns products of `p`-th roots of unity into sums. -/
theorem rootOfUnityExp_mul (hζ : IsPrimitiveRoot ζ p) {g h : G} (hg : g ^ p = 1) (hh : h ^ p = 1) :
    rootOfUnityExp ζ p (g * h) = rootOfUnityExp ζ p g + rootOfUnityExp ζ p h := by
  refine rootOfUnityExp_eq hζ ?_
  have hcast : (((rootOfUnityExp ζ p g + rootOfUnityExp ζ p h).val : ℕ) : ZMod p)
      = (((rootOfUnityExp ζ p g).val + (rootOfUnityExp ζ p h).val : ℕ) : ZMod p) := by
    rw [ZMod.natCast_zmod_val, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [pow_eq_pow_of_natCast_eq hζ hcast, pow_add, pow_rootOfUnityExp_val hζ hg,
    pow_rootOfUnityExp_val hζ hh]

/-- A `p`-th root of unity has vanishing exponent exactly when it is one. -/
theorem rootOfUnityExp_eq_zero_iff (hζ : IsPrimitiveRoot ζ p) {g : G} (hg : g ^ p = 1) :
    rootOfUnityExp ζ p g = 0 ↔ g = 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hv := pow_rootOfUnityExp_val hζ hg
    rw [h, ZMod.val_zero, pow_zero] at hv
    exact hv.symm
  · exact rootOfUnityExp_eq hζ (by rw [ZMod.val_zero, pow_zero, h])

end RootOfUnityExp

/-! ### The ratio by which an automorphism scales an element -/

section Ratio

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- The ratio by which an automorphism scales a product is the product of the ratios. -/
theorem ratio_mul (σ : M ≃ₐ[K] M) (u v : M) :
    σ (u * v) / (u * v) = σ u / u * (σ v / v) := by
  rw [map_mul, div_mul_div_comm]

/-- The ratio by which an automorphism scales a power is the power of the ratio. -/
theorem ratio_pow (σ : M ≃ₐ[K] M) (u : M) (n : ℕ) : σ (u ^ n) / u ^ n = (σ u / u) ^ n := by
  rw [map_pow, div_pow]

/-- The ratio by which an automorphism scales a finite product is the product of the ratios. -/
theorem ratio_prod {ι : Type*} (σ : M ≃ₐ[K] M) (s : Finset ι) (u : ι → M) :
    σ (∏ i ∈ s, u i) / ∏ i ∈ s, u i = ∏ i ∈ s, σ (u i) / u i := by
  rw [map_prod, Finset.prod_div_distrib]

end Ratio

section RatioExp

variable {K M : Type*} [Field K] [Field M] [Algebra K M] {p : ℕ} [NeZero p] {ζ : K} {ξ : M}

/-- The ratios by which two automorphisms scale a radical of an element of the base field multiply
to the ratio for their product. -/
theorem ratio_aut_mul (hζ : IsPrimitiveRoot ζ p) (σ τ : M ≃ₐ[K] M) {u : M} (hu : u ≠ 0)
    (h : ∃ a : K, u ^ p = algebraMap K M a) :
    (σ * τ) u / u = σ u / u * (τ u / u) := by
  have hfix : σ (τ u / u) = τ u / u := map_radicalRatio_eq_self hζ τ σ hu h
  have hτ : τ u = τ u / u * u := (div_mul_cancel₀ _ hu).symm
  calc (σ * τ) u / u = σ (τ u) / u := by rw [AlgEquiv.mul_apply]
    _ = σ (τ u / u * u) / u := by rw [← hτ]
    _ = τ u / u * σ u / u := by rw [map_mul, hfix]
    _ = σ u / u * (τ u / u) := by ring

/-- The exponents attached to two automorphisms add up to the exponent attached to their
product. -/
theorem rootOfUnityExp_ratio_aut_mul (hξ : IsPrimitiveRoot ξ p) (hζ : IsPrimitiveRoot ζ p)
    (σ τ : M ≃ₐ[K] M) {u : M} (hu : u ≠ 0) (h : ∃ a : K, u ^ p = algebraMap K M a) :
    rootOfUnityExp ξ p ((σ * τ) u / u)
      = rootOfUnityExp ξ p (σ u / u) + rootOfUnityExp ξ p (τ u / u) := by
  rw [ratio_aut_mul hζ σ τ hu h,
    rootOfUnityExp_mul hξ (pow_radicalRatio_eq_one σ hu h) (pow_radicalRatio_eq_one τ hu h)]

end RatioExp

/-! ### Descending a radicand -/

section Descent

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  {p : ℕ} {ζ : K} {ι : Type*} [Fintype ι] {b : ι → Kˣ} {β : ι → M} {x : Kˣ} {y : M}

/-- **Descent of a radicand through a radical extension.**

If a Galois extension `M / K` is generated by `p`-th roots `βᵢ` of elements `bᵢ` of the base field,
and the base field contains a primitive `p`-th root of unity, then every element of the base field
which becomes a `p`-th power in `M` is, up to a `p`-th power of the base field, a monomial in the
`bᵢ`. -/
theorem exists_pow_prod_of_pow_eq_of_adjoin_eq_top (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hβ : ∀ i, β i ^ p = algebraMap K M ((b i : K)))
    (hgen : IntermediateField.adjoin K (Set.range β) = ⊤)
    (hy : y ^ p = algebraMap K M ((x : K))) :
    ∃ (e : ι → ℕ) (z : Kˣ), x = (∏ i, b i ^ e i) * z ^ p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Nonempty (Additive (M ≃ₐ[K] M)) := ⟨0⟩
  have hinj : Function.Injective (algebraMap K M) := (algebraMap K M).injective
  have hξ : IsPrimitiveRoot (algebraMap K M ζ) p := hζ.map_of_injective hinj
  have hβne : ∀ i, β i ≠ 0 := fun i hi => Units.ne_zero (b i)
    ((map_eq_zero_iff _ hinj).1 (by rw [← hβ i, hi, zero_pow hp.ne_zero]))
  have hyne : y ≠ 0 := fun hi => Units.ne_zero x
    ((map_eq_zero_iff _ hinj).1 (by rw [← hy, hi, zero_pow hp.ne_zero]))
  have hβrad : ∀ i, ∃ a : K, β i ^ p = algebraMap K M a := fun i => ⟨(b i : K), hβ i⟩
  have hyrad : ∃ a : K, y ^ p = algebraMap K M a := ⟨(x : K), hy⟩
  -- the exponents recorded by an automorphism, on the generators and on `y`
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Additive (M ≃ₐ[K] M) →+ (ι → ZMod p),
      ∀ (a : Additive (M ≃ₐ[K] M)) (i : ι),
        Θ a i = rootOfUnityExp (algebraMap K M ζ) p ((Additive.toMul a) (β i) / β i) :=
    ⟨AddMonoidHom.mk'
        (fun a i => rootOfUnityExp (algebraMap K M ζ) p ((Additive.toMul a) (β i) / β i))
        (fun a c => funext fun i => rootOfUnityExp_ratio_aut_mul hξ hζ (Additive.toMul a)
          (Additive.toMul c) (hβne i) (hβrad i)),
      fun _ _ => rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : Additive (M ≃ₐ[K] M) →+ ZMod p,
      ∀ a : Additive (M ≃ₐ[K] M),
        ε a = rootOfUnityExp (algebraMap K M ζ) p ((Additive.toMul a) y / y) :=
    ⟨AddMonoidHom.mk' (fun a => rootOfUnityExp (algebraMap K M ζ) p ((Additive.toMul a) y / y))
        (fun a c => rootOfUnityExp_ratio_aut_mul hξ hζ (Additive.toMul a) (Additive.toMul c) hyne
          hyrad),
      fun _ => rfl⟩
  -- the generators determine an automorphism, so `Θ` is injective
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hfix : ∀ r ∈ Set.range β, (Additive.toMul a) r = r := by
      rintro _ ⟨i, rfl⟩
      have h0 : rootOfUnityExp (algebraMap K M ζ) p ((Additive.toMul a) (β i) / β i) = 0 := by
        rw [← hΘ a i, ha]
        rfl
      have h1 : (Additive.toMul a) (β i) / β i = 1 :=
        (rootOfUnityExp_eq_zero_iff hξ
          (pow_radicalRatio_eq_one (Additive.toMul a) (hβne i) (hβrad i))).1 h0
      exact (div_eq_one_iff_eq (hβne i)).1 h1
    exact Additive.toMul.injective (aut_eq_of_eqOn hgen hfix)
  have hν : ∀ a : Additive (M ≃ₐ[K] M), Function.invFun Θ (Θ a) = a :=
    Function.leftInverse_invFun hΘinj
  -- `ε` factors through the image of `Θ` and extends to a linear functional
  set Sm : Submodule (ZMod p) (ι → ZMod p) := AddSubgroup.toZModSubmodule p Θ.range with hSmdef
  have hmemSm : ∀ s : Sm, ∃ a, Θ a = (s : ι → ZMod p) := fun s => AddMonoidHom.mem_range.1 s.2
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Sm →+ ZMod p,
      ∀ s : Sm, ψ s = ε (Function.invFun Θ (s : ι → ZMod p)) := by
    refine ⟨AddMonoidHom.mk' (fun s => ε (Function.invFun Θ (s : ι → ZMod p))) ?_, fun _ => rfl⟩
    intro s t
    obtain ⟨a, ha⟩ := hmemSm s
    obtain ⟨c, hc⟩ := hmemSm t
    have hst : (((s + t : Sm)) : ι → ZMod p) = Θ (a + c) := by
      rw [Submodule.coe_add, ← ha, ← hc, map_add]
    simp only [hst, ← ha, ← hc, hν]
    exact map_add ε a c
  obtain ⟨g, hg⟩ := (ψ.toZModLinearMap p).exists_extend
  have hgΘ : ∀ a : Additive (M ≃ₐ[K] M), g (Θ a) = ε a := by
    intro a
    have hmem : Θ a ∈ Sm := AddMonoidHom.mem_range.2 ⟨a, rfl⟩
    have h1 : g (Θ a) = ψ ⟨Θ a, hmem⟩ := LinearMap.congr_fun hg ⟨Θ a, hmem⟩
    rw [h1, hψ ⟨Θ a, hmem⟩]
    exact congrArg ε (hν a)
  -- the coordinates of that functional
  obtain ⟨e, he⟩ : ∃ e : ι → ZMod p, ∀ i, e i = g (Pi.single i 1) := ⟨_, fun _ => rfl⟩
  have hsingle : ∀ i : ι, (fun j => if i = j then (1 : ZMod p) else 0) = Pi.single i 1 := by
    intro i
    funext j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hsum : ∀ a : Additive (M ≃ₐ[K] M), ε a = ∑ i, Θ a i * e i := by
    intro a
    rw [← hgΘ a, LinearMap.pi_apply_eq_sum_univ g (Θ a)]
    exact Finset.sum_congr rfl fun i _ => by rw [hsingle i, smul_eq_mul, he i]
  -- the corresponding monomial in the radicals differs from `y` by an element of `K`
  obtain ⟨w, hw⟩ : ∃ w : M, w = ∏ i, β i ^ (e i).val := ⟨_, rfl⟩
  have hwne : w ≠ 0 := by
    rw [hw]
    exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hβne i)
  have hwpow : w ^ p = algebraMap K M (∏ i, ((b i : K)) ^ (e i).val) := by
    rw [map_prod, hw, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hβ i, ← map_pow]
  have hratio : ∀ σ : M ≃ₐ[K] M, σ y / y = σ w / w := by
    intro σ
    have hy1 : σ y / y = algebraMap K M ζ ^ (ε (Additive.ofMul σ)).val := by
      rw [hε (Additive.ofMul σ)]
      exact (pow_rootOfUnityExp_val hξ (pow_radicalRatio_eq_one σ hyne hyrad)).symm
    have hw2 : ∀ i, σ (β i) / β i
        = algebraMap K M ζ ^ (Θ (Additive.ofMul σ) i).val := by
      intro i
      rw [hΘ (Additive.ofMul σ) i]
      exact (pow_rootOfUnityExp_val hξ (pow_radicalRatio_eq_one σ (hβne i) (hβrad i))).symm
    have hw1 : σ w / w
        = ∏ i, algebraMap K M ζ ^ ((Θ (Additive.ofMul σ) i).val * (e i).val) := by
      rw [hw, ratio_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [ratio_pow, hw2 i, ← pow_mul]
    rw [hy1, hw1, Finset.prod_pow_eq_pow_sum]
    refine pow_eq_pow_of_natCast_eq hξ ?_
    rw [ZMod.natCast_zmod_val, Nat.cast_sum]
    refine (hsum (Additive.ofMul σ)).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hσw : ∀ σ : M ≃ₐ[K] M, σ w ≠ 0 := by
    intro σ h
    refine hwne ?_
    have hs := σ.symm_apply_apply w
    rw [h, map_zero] at hs
    exact hs.symm
  have hfixed : ∀ σ : M ≃ₐ[K] M, σ (y / w) = y / w := by
    intro σ
    rw [map_div₀, div_eq_div_iff (hσw σ) hwne]
    have hr := hratio σ
    rw [div_eq_div_iff hyne hwne] at hr
    linear_combination hr
  obtain ⟨z0, hz0⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (y / w)).2 hfixed
  have hz0ne : z0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hz0
    exact div_ne_zero hyne hwne hz0.symm
  -- assemble the identity in the base field
  have hcancel : w * (y / w) = y := by field_simp
  have hfinal : algebraMap K M ((x : K))
      = algebraMap K M ((∏ i, ((b i : K)) ^ (e i).val) * z0 ^ p) := by
    rw [map_mul, map_pow, hz0, ← hwpow, ← hy, ← mul_pow, hcancel]
  refine ⟨fun i => (e i).val, Units.mk0 z0 hz0ne, Units.ext ?_⟩
  have hcoeprod : ((∏ i, b i ^ (e i).val : Kˣ) : K) = ∏ i, ((b i : K)) ^ (e i).val := by
    rw [← Units.coeHom_apply, map_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Units.coeHom_apply, Units.val_pow_eq_pow_val]
  rw [Units.val_mul, hcoeprod, Units.val_pow_eq_pow_val, Units.val_mk0]
  exact hinj hfinal

end Descent

end InverseGalois.CFT
