/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Coeff
import InverseGalois.CFT.Profinite.Hilbert90
import InverseGalois.CFT.Profinite.Kummer

/-!
# The Kummer sequence in degree two

Let `Ω` be a Galois extension of `k` in which every unit has an `n`-th root, and let `M` be a
group of coefficients which the Galois group carries to the `n`-th roots of unity of `Ω`.  The
resulting map of second cohomology groups is injective with image the classes killed by `n`.

Injectivity is Hilbert's theorem ninety.  If the image of a cocycle is the coboundary of a cochain
`w`, then the `n`-th power of `w` has trivial coboundary, so it is a one cocycle, so it is the
coboundary of a single unit `β`; an `n`-th root `γ` of `β` corrects `w` into a cochain with values
in the roots of unity and with the same coboundary.  Surjectivity onto the `n`-torsion is the same
computation run backwards: if the `n`-th power of a cocycle `a` is the coboundary of a cochain `u`,
then choosing an `n`-th root of every value of `u` gives a cochain `v` whose coboundary differs
from `a` by a cocycle taking values in the roots of unity.

## Main results

* `InverseGalois.CFT.pow_coeffH2_eq_one`: every class in the image is killed by `n`.
* `InverseGalois.CFT.coeffH2_injective`: **the map to the second cohomology of the units of the
  extension is injective.**
* `InverseGalois.CFT.exists_coeffH2_eq_of_pow_eq_one`: **every class killed by `n` is in the
  image.**
* `InverseGalois.CFT.range_coeffH2`: the image is exactly the `n`-torsion.
* `InverseGalois.CFT.kummerH2Equiv`: **the second cohomology of the coefficients is the
  `n`-torsion of the second cohomology of the units of the extension.**

## Tags

Kummer theory, Galois cohomology, Hilbert ninety, roots of unity, Brauer group
-/

namespace InverseGalois.CFT

open groupCohomology

/-! ### Powers of a coboundary -/

section Pow

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- The coboundary of a power of a one cochain is the power of its coboundary. -/
theorem coboundary₂_pow (u : G → M) : ∀ j : ℕ, coboundary₂ (u ^ j) = coboundary₂ u ^ j
  | 0 => by rw [pow_zero, pow_zero, coboundary₂_one]
  | j + 1 => by rw [pow_succ, pow_succ, coboundary₂_mul, coboundary₂_pow u j]

/-- **A one cochain has trivial coboundary exactly when it is a one cocycle.** -/
theorem coboundary₂_eq_one_iff (u : G → M) : coboundary₂ u = 1 ↔ IsMulCocycle₁ u := by
  constructor
  · intro h g x
    have hgx : g • u x / u (g * x) * u g = 1 := congrFun h (g, x)
    rw [div_mul_eq_mul_div, div_eq_one] at hgx
    exact hgx.symm
  · intro h
    funext p
    obtain ⟨g, x⟩ := p
    show g • u x / u (g * x) * u g = 1
    rw [h g x]
    simp only [div_eq_mul_inv, mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

variable [TopologicalSpace G]

/-- The class of a power of a smooth two cocycle is the power of its class. -/
theorem smoothH2Mk_pow {a : G × G → M} (ha : IsMulCocycle₂ a) (has : IsSmooth₂ a) (j : ℕ) :
    smoothH2Mk (a ^ j) ((smoothCocycle₂ G M).pow_mem ⟨ha, has⟩ j).1
        ((smoothCocycle₂ G M).pow_mem ⟨ha, has⟩ j).2
      = smoothH2Mk a ha has ^ j := rfl

end Pow

/-! ### Reflecting the conditions along an injective homomorphism of the coefficients -/

section ReflectSmooth

variable {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N] {φ : M →* N}
  (hinj : Function.Injective φ)

include hinj

/-- An injective homomorphism of the coefficients reflects smoothness in degree one. -/
theorem isSmooth₁_of_coeffMap₁ {u : G → M} (h : IsSmooth₁ (coeffMap₁ φ u)) : IsSmooth₁ u := by
  obtain ⟨P, hP, hc⟩ := h
  exact ⟨P, hP, fun x m hm => hinj (hc x m hm)⟩

/-- An injective homomorphism of the coefficients reflects smoothness in degree two. -/
theorem isSmooth₂_of_coeffMap₂ {a : G × G → M} (h : IsSmooth₂ (coeffMap₂ φ a)) : IsSmooth₂ a := by
  obtain ⟨P, hP, hc⟩ := h
  exact ⟨P, hP, fun x y m hm l hl => hinj (hc x y m hm l hl)⟩

end ReflectSmooth

section ReflectCocycle

variable {G M N : Type*} [Group G] [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N] {φ : M →* N}

/-- An injective equivariant homomorphism of the coefficients reflects the cocycle condition in
degree two. -/
theorem isMulCocycle₂_of_coeffMap₂ (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    (hinj : Function.Injective φ) {a : G × G → M} (h : IsMulCocycle₂ (coeffMap₂ φ a)) :
    IsMulCocycle₂ a := by
  intro g x y
  refine hinj ?_
  have hgxy := h g x y
  simp only [coeffMap₂_apply] at hgxy
  simp only [map_mul, hφ]
  exact hgxy

end ReflectCocycle

/-! ### The coboundary of a cochain with values in the units of the extension -/

section Coboundary

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- **A smooth one cochain with values in the units of a Galois extension has all of its values
fixed by one open normal subgroup.**  The cochain is constant on the cosets of the fixing subgroup
of a finite level, so it takes only finitely many values, and the normal closure of the field they
generate is itself a finite level. -/
theorem exists_isOpenNormal_forall_smul_eq_of_isSmooth₁ {u : Gal(Ω/k) → Ωˣ} (hu : IsSmooth₁ u) :
    ∃ P : Subgroup Gal(Ω/k), IsOpenNormal P ∧ ∀ (g : Gal(Ω/k)) (m : Gal(Ω/k)), m ∈ P →
      m • u g = u g := by
  obtain ⟨N, hN, hcon⟩ := hu
  obtain ⟨E, hfin, hgal, hle⟩ := exists_fixingSubgroup_le hN
  haveI := hfin
  haveI := hgal
  -- the cochain only depends on the restriction to the level
  have hres : ∀ g h : Gal(Ω/k), AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) E g
      = AlgEquiv.restrictNormalHom E h → u g = u h := by
    intro g h hgh
    have hker : g⁻¹ * h ∈ E.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker E, MonoidHom.mem_ker, map_mul, map_inv, hgh,
        inv_mul_cancel]
    have hgh' := hcon g (g⁻¹ * h) (hle hker)
    rwa [mul_inv_cancel_left, eq_comm] at hgh'
  choose lift hlift using restrictNormalHom_surjective_level (k := k) (K := Ω) E
  -- the finitely many values generate a finite extension
  haveI : Finite ↥(Set.range fun τ : Gal(↥E/k) => (u (lift τ) : Ω)) :=
    (Set.finite_range _).to_subtype
  haveI : FiniteDimensional k
      ↥(IntermediateField.adjoin k (Set.range fun τ : Gal(↥E/k) => (u (lift τ) : Ω))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨(IntermediateField.normalClosure k
      ↥(IntermediateField.adjoin k (Set.range fun τ : Gal(↥E/k) => (u (lift τ) : Ω)))
      Ω).fixingSubgroup, isOpenNormal_fixingSubgroup _, fun g m hm => ?_⟩
  have hval : u g = u (lift (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) E g)) :=
    hres _ _ (hlift _).symm
  refine Units.ext ((IntermediateField.mem_fixingSubgroup_iff _ m).1 hm (u g : Ω) ?_)
  refine IntermediateField.le_normalClosure _ ?_
  exact IntermediateField.subset_adjoin k _ ⟨_, congrArg (Units.val (α := Ω)) hval.symm⟩

/-- **The coboundary of a smooth one cochain with values in the units of a Galois extension is a
smooth two cochain.** -/
theorem isSmooth₂_coboundary₂_of_isSmooth₁ {u : Gal(Ω/k) → Ωˣ} (hu : IsSmooth₁ u) :
    IsSmooth₂ (coboundary₂ u) := by
  obtain ⟨P, hP, hfix⟩ := exists_isOpenNormal_forall_smul_eq_of_isSmooth₁ hu
  obtain ⟨N, hN, hcon⟩ := hu
  haveI := hN.normal
  refine ⟨N ⊓ P, hN.inf hP, fun x y n hn m hm => ?_⟩
  have hconj : y⁻¹ * n * y ∈ N := by simpa using hN.normal.conj_mem n hn.1 y⁻¹
  have hxy : x * n * (y * m) = x * y * (y⁻¹ * n * y * m) := by group
  simp only [coboundary₂_apply, hxy, hcon x n hn.1, hcon (x * y) _ (N.mul_mem hconj hm.1),
    hcon y m hm.1, mul_smul, hfix y n hn.2]

end Coboundary

/-! ### The Kummer sequence in degree two -/

section Kummer

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
variable {M : Type*} [CommGroup M] [MulDistribMulAction Gal(Ω/k) M] {n : ℕ}

omit [IsGalois k Ω] in
/-- **A class coming from coefficients killed by `n` is killed by `n`.** -/
theorem pow_coeffH2_eq_one {ι : M →* Ωˣ} (hι : ∀ (g : Gal(Ω/k)) (m : M), ι (g • m) = g • ι m)
    (hpow : ∀ m : M, ι m ^ n = 1) (z : SmoothH2 Gal(Ω/k) M) : coeffH2 ι hι z ^ n = 1 := by
  obtain ⟨a, ha, hs, rfl⟩ := smoothH2Mk_surjective z
  rw [coeffH2_smoothH2Mk, ← smoothH2Mk_pow]
  refine (smoothH2Mk_eq_one_iff _ _).2 ⟨1, isSmooth₁_one, ?_⟩
  rw [coboundary₂_one]
  funext p
  exact (hpow (a p)).symm

/-- **The map from the second cohomology of the `n`-th roots of unity to the second cohomology of
the units of the extension is injective.**  A cochain whose coboundary is the image of a cocycle
has an `n`-th power with trivial coboundary, hence is a one cocycle, hence is the coboundary of a
single unit by Hilbert's theorem ninety; an `n`-th root of that unit corrects the cochain into one
with values in the roots of unity. -/
theorem coeffH2_injective {ι : M →* Ωˣ} (hι : ∀ (g : Gal(Ω/k)) (m : M), ι (g • m) = g • ι m)
    (hinj : Function.Injective ι) (hpow : ∀ m : M, ι m ^ n = 1)
    (hsurj : ∀ y : Ωˣ, y ^ n = 1 → ∃ m : M, ι m = y) (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ n = y) :
    Function.Injective (coeffH2 ι hι) := by
  refine (injective_iff_map_eq_one _).2 fun z hz => ?_
  obtain ⟨b, hb, hbs, rfl⟩ := smoothH2Mk_surjective z
  rw [coeffH2_smoothH2Mk] at hz
  obtain ⟨w, hws, hw⟩ := (smoothH2Mk_eq_one_iff _ _).1 hz
  have hwn : coboundary₂ (w ^ n) = 1 := by
    rw [coboundary₂_pow, hw]
    funext p
    exact hpow (b p)
  have hsm : IsSmooth₁ (w ^ n) := (smoothCochain₁ Gal(Ω/k) Ωˣ).pow_mem hws n
  obtain ⟨β, hβ⟩ :=
    isMulCoboundary₁_of_isMulCocycle₁_smooth ((coboundary₂_eq_one_iff _).1 hwn) hsm
  obtain ⟨γ, hγ⟩ := hroot β
  obtain ⟨t, htapp⟩ : ∃ t : Gal(Ω/k) → Ωˣ, ∀ g, t g = w g * (γ / (g • γ)) := ⟨_, fun _ => rfl⟩
  have htpow : ∀ g : Gal(Ω/k), t g ^ n = 1 := by
    intro g
    have h1 : w g ^ n = g • β / β := (hβ g).symm
    have h2 : (g • γ) ^ n = g • β := by rw [← smul_pow', hγ]
    rw [htapp, mul_pow, div_pow, h1, h2, hγ, div_mul_div_comm, div_eq_one, mul_comm]
  have hts : IsSmooth₁ t := by
    obtain ⟨N₁, hN₁, h₁⟩ := hws
    obtain ⟨N₂, hN₂, h₂⟩ := exists_isOpenNormal_forall_smul_eq (k := k) γ
    refine ⟨N₁ ⊓ N₂, hN₁.inf hN₂, fun x m hm => ?_⟩
    have hx1 : w (x * m) = w x := h₁ x m (Subgroup.mem_inf.1 hm).1
    have hx2 : (x * m) • γ = x • γ := by rw [mul_smul, h₂ m (Subgroup.mem_inf.1 hm).2]
    rw [htapp, htapp, hx1, hx2]
  choose s hs using fun g : Gal(Ω/k) => hsurj (t g) (htpow g)
  have hcoeff : coeffMap₁ ι s = t := funext hs
  have hssm : IsSmooth₁ s := isSmooth₁_of_coeffMap₁ hinj (by rw [hcoeff]; exact hts)
  have hcb2 : coboundary₂ (fun g : Gal(Ω/k) => γ / (g • γ)) = 1 := by
    have hfun : (fun g : Gal(Ω/k) => γ / (g • γ)) = (fun g : Gal(Ω/k) => g • γ / γ)⁻¹ :=
      funext fun g => (inv_div _ _).symm
    rw [hfun, coboundary₂_inv, coboundary₂_smul_div, inv_one]
  have hcob : coboundary₂ t = coboundary₂ w := by
    have htmul : t = w * fun g : Gal(Ω/k) => γ / (g • γ) := funext fun g => htapp g
    rw [htmul, coboundary₂_mul, hcb2, mul_one]
  refine (smoothH2Mk_eq_one_iff hb hbs).2 ⟨s, hssm, funext fun p => hinj ?_⟩
  have hp := congrFun (coboundary₂_coeffMap₁ ι hι s) p
  rw [hcoeff, hcob, hw] at hp
  exact hp.symm

/-- **Every class of the second cohomology of the units of the extension killed by `n` comes from
the `n`-th roots of unity.**  An `n`-th root of every value of a cochain whose coboundary is the
`n`-th power of the cocycle corrects the cocycle into one with values in the roots of unity. -/
theorem exists_coeffH2_eq_of_pow_eq_one {ι : M →* Ωˣ}
    (hι : ∀ (g : Gal(Ω/k)) (m : M), ι (g • m) = g • ι m) (hinj : Function.Injective ι)
    (hsurj : ∀ y : Ωˣ, y ^ n = 1 → ∃ m : M, ι m = y) (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ n = y)
    (y : SmoothH2 Gal(Ω/k) Ωˣ) (hy : y ^ n = 1) :
    ∃ z : SmoothH2 Gal(Ω/k) M, coeffH2 ι hι z = y := by
  obtain ⟨a, ha, has, rfl⟩ := smoothH2Mk_surjective y
  rw [← smoothH2Mk_pow] at hy
  obtain ⟨u, hus, hu⟩ := (smoothH2Mk_eq_one_iff _ _).1 hy
  choose ρ hρ using hroot
  obtain ⟨v, hvapp⟩ : ∃ v : Gal(Ω/k) → Ωˣ, ∀ g, v g = ρ (u g) := ⟨_, fun _ => rfl⟩
  have hvn : v ^ n = u := by
    funext g
    show v g ^ n = u g
    rw [hvapp, hρ]
  have hvs : IsSmooth₁ v := by
    obtain ⟨P, hP, hc⟩ := hus
    exact ⟨P, hP, fun x m hm => by rw [hvapp, hvapp, hc x m hm]⟩
  have hvmem : (coboundary₂ v) ∈ smoothCocycle₂ Gal(Ω/k) Ωˣ :=
    ⟨isMulCocycle₂_coboundary₂ v, isSmooth₂_coboundary₂_of_isSmooth₁ hvs⟩
  have hcmem : (a / coboundary₂ v) ∈ smoothCocycle₂ Gal(Ω/k) Ωˣ :=
    (smoothCocycle₂ Gal(Ω/k) Ωˣ).div_mem ⟨ha, has⟩ hvmem
  have hcpow : ∀ p : Gal(Ω/k) × Gal(Ω/k), (a / coboundary₂ v) p ^ n = 1 := by
    intro p
    have h1 : coboundary₂ v p ^ n = a p ^ n := by
      have hpv := congrFun (coboundary₂_pow v n) p
      rw [hvn, hu] at hpv
      exact hpv.symm
    show (a p / coboundary₂ v p) ^ n = 1
    rw [div_pow, h1, div_self']
  choose b hbapp using fun p => hsurj ((a / coboundary₂ v) p) (hcpow p)
  have hbc : coeffMap₂ ι b = a / coboundary₂ v := funext hbapp
  have hbcoc : IsMulCocycle₂ b :=
    isMulCocycle₂_of_coeffMap₂ hι hinj (by rw [hbc]; exact hcmem.1)
  have hbs : IsSmooth₂ b := isSmooth₂_of_coeffMap₂ hinj (by rw [hbc]; exact hcmem.2)
  refine ⟨smoothH2Mk b hbcoc hbs, ?_⟩
  rw [coeffH2_smoothH2Mk]
  refine (smoothH2Mk_eq_iff _ _ ha has).2 ⟨v⁻¹, hvs.inv, funext fun p => ?_⟩
  rw [coboundary₂_inv]
  show (coboundary₂ v p)⁻¹ = coeffMap₂ ι b p / a p
  rw [hbc]
  show (coboundary₂ v p)⁻¹ = a p / coboundary₂ v p / a p
  simp only [div_eq_mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- **The image of the second cohomology of the `n`-th roots of unity is the `n`-torsion of the
second cohomology of the units of the extension.** -/
theorem range_coeffH2 {ι : M →* Ωˣ} (hι : ∀ (g : Gal(Ω/k)) (m : M), ι (g • m) = g • ι m)
    (hinj : Function.Injective ι) (hpow : ∀ m : M, ι m ^ n = 1)
    (hsurj : ∀ y : Ωˣ, y ^ n = 1 → ∃ m : M, ι m = y) (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ n = y) :
    (coeffH2 ι hι).range = (powMonoidHom n : SmoothH2 Gal(Ω/k) Ωˣ →* _).ker := by
  ext y
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · rintro ⟨z, rfl⟩
    exact pow_coeffH2_eq_one hι hpow z
  · exact exists_coeffH2_eq_of_pow_eq_one hι hinj hsurj hroot y

/-- **The second cohomology of the `n`-th roots of unity is the `n`-torsion of the second
cohomology of the units of the extension.** -/
noncomputable def kummerH2Equiv {ι : M →* Ωˣ}
    (hι : ∀ (g : Gal(Ω/k)) (m : M), ι (g • m) = g • ι m) (hinj : Function.Injective ι)
    (hpow : ∀ m : M, ι m ^ n = 1) (hsurj : ∀ y : Ωˣ, y ^ n = 1 → ∃ m : M, ι m = y)
    (hroot : ∀ y : Ωˣ, ∃ z : Ωˣ, z ^ n = y) :
    SmoothH2 Gal(Ω/k) M ≃* (powMonoidHom n : SmoothH2 Gal(Ω/k) Ωˣ →* _).ker :=
  (MulEquiv.ofBijective (coeffH2 ι hι).rangeRestrict
      ⟨fun _ _ h => coeffH2_injective hι hinj hpow hsurj hroot (congrArg Subtype.val h),
        (coeffH2 ι hι).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (range_coeffH2 hι hinj hpow hsurj hroot))

end Kummer

end InverseGalois.CFT
