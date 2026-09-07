/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.RecursionClose
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.CFT.Units.ABHNTorsion
import InverseGalois.CFT.Units.DecompositionGalois
import InverseGalois.CFT.Units.LocalNorm
import InverseGalois.CFT.Units.PlaceComap
import InverseGalois.CFT.Units.Places

/-!
# The norm of an element with prescribed local behaviour

An element of a Galois extension of number fields has a norm to the base, and the local behaviour
of that norm at a place of the base is decided by the local behaviour of the element at the places
above it.  The bridge is the factorization of the group of automorphisms: read inside one
completion of the extension, the product of all the conjugates of an element breaks into a product
over the cosets of the decomposition group, and each inner product is a norm from that completion
down to the completion of the prime below.  So the global norm, read in the completion of the base,
is a product of genuine local norms of transported copies of the element.

Two consequences follow at once.  If the element is a `p`-th power in the completion at every place
above a place of the base, then each local norm is a `p`-th power and hence so is the norm; in the
language of local classes this says that the norm carries a trivial class at all the places above a
place of the base to a trivial class there, and therefore that two elements with the same local
classes above a place have norms with the same local class there.  And if the prime of the base is
unramified in the extension, the order of the norm is exactly the sum of the orders of the
conjugates, so it inherits whatever divides all of them; a unit unramified at every place above an
unramified prime therefore has an unramified norm.

## Main results

* `InverseGalois.CFT.exists_pow_eq_algebraMap_norm`: **an element which is a `p`-th power in the
  completion at every place above a place of the base has a norm which is a `p`-th power** in the
  completion of the base there.
* `InverseGalois.CFT.localClassHom_norm_eq_of_forall_eq`: **two units whose local classes agree at
  every place above a place of the base have norms whose local classes agree there.**
* `InverseGalois.CFT.dvd_ord_norm_of_forall_dvd`: **at a prime of the base unramified in the
  extension, the order of a norm is divisible by whatever divides the orders of the element at all
  the primes above.**
* `InverseGalois.CFT.localClassHom_norm_mem_localUnramified`: the norm of a unit unramified at every
  place above an unramified prime of the base is unramified there.

## Tags

number field, norm, completion, decomposition group, local class, unramified
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### A finite group as its cosets times a subgroup -/

section Coset

variable {G : Type*} [Group G] (H : Subgroup G)

/-- **A group is the cosets of a subgroup times the subgroup**, an element being recovered from its
coset and from the subgroup element carrying the chosen representative of that coset to it. -/
noncomputable def cosetProdEquiv : (G ⧸ H) × ↥H ≃ G where
  toFun p := (p.2 : G) * (Quotient.out p.1)⁻¹
  invFun σ := (QuotientGroup.mk σ⁻¹,
    ⟨σ * Quotient.out (QuotientGroup.mk σ⁻¹ : G ⧸ H), by
      simpa using QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk σ⁻¹ : G ⧸ H)).symm⟩)
  left_inv := by
    rintro ⟨L, d⟩
    have h1 : (QuotientGroup.mk (((d : G) * (Quotient.out L)⁻¹)⁻¹) : G ⧸ H) = L := by
      rw [mul_inv_rev, inv_inv, QuotientGroup.mk_mul_of_mem _ (H.inv_mem d.2),
        QuotientGroup.out_eq']
    refine Prod.ext h1 (Subtype.ext ?_)
    show (d : G) * (Quotient.out L)⁻¹
        * Quotient.out (QuotientGroup.mk (((d : G) * (Quotient.out L)⁻¹)⁻¹) : G ⧸ H) = (d : G)
    rw [h1, inv_mul_cancel_right]
  right_inv σ := mul_inv_cancel_right _ _

variable [Fintype G] [Fintype (G ⧸ H)] [Fintype ↥H]

/-- **A product over a finite group is a product over the cosets of a subgroup of products over
the subgroup.** -/
theorem prod_eq_prod_quotient_prod_subgroup {M : Type*} [CommMonoid M] (F : G → M) :
    ∏ σ : G, F σ = ∏ L : G ⧸ H, ∏ d : ↥H, F ((d : G) * (Quotient.out L)⁻¹) := by
  rw [← Fintype.prod_bijective (cosetProdEquiv H) (cosetProdEquiv H).bijective
      (fun p : (G ⧸ H) × ↥H => F ((p.2 : G) * (Quotient.out p.1)⁻¹)) F fun _ => rfl,
    Fintype.prod_prod_type]

end Coset

/-! ### The norm of an everywhere local power -/

section Norm

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The product of the conjugates of an element of a completion under the decomposition group is
its norm** down to the completion of the prime below. -/
theorem prod_stabilizer_smul_eq_algebraMap_norm [Fintype ↥(stabilizer Gal(K/k) w)]
    (z : w.adicCompletion K) :
    ∏ d : ↥(stabilizer Gal(K/k) w), d • z
      = algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
          (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z) := by
  haveI := isGalois_adicCompletion k w
  haveI : SMulCommClass ↥(stabilizer Gal(K/k) w)
      ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) :=
    ⟨fun d c x => by
      rw [Algebra.smul_def, Algebra.smul_def, smul_mul', stabilizer_smul_algebraMap k w]⟩
  refine (algebraMap_norm_eq_prod_smul (fun τ => ?_) z).symm
  obtain ⟨σ, hσ⟩ := decompositionHom_surjective k w τ
  exact ⟨σ, fun x => by rw [← hσ]; rfl⟩

omit [NumberField k] [IsGalois k K] in
/-- **Reading the image of an element under the inverse of an automorphism in the completion at a
place** is reading the element at the image place and transporting back. -/
theorem adicCoe_inv_smul_eq_symm (σ : Gal(K/k)) (t : K) :
    adicCoe ((σ⁻¹ : Gal(K/k)) t) w
      = (adicCompletionGalEquiv w σ).symm (adicCoe t (σ • w)) := by
  have h := adicCompletionGalEquiv_adicCoe w σ ((σ⁻¹ : Gal(K/k)) t)
  rw [show σ ((σ⁻¹ : Gal(K/k)) t) = t by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]] at h
  rw [← h, RingEquiv.symm_apply_apply]

variable (k) in
/-- **An element of a Galois extension which is a `p`-th power in the completion at every place
above a place of the base has a norm which is a `p`-th power** in the completion of the base
there.  Its conjugates are grouped into the cosets of the decomposition group, each group being a
local norm of a transported copy of the element. -/
theorem exists_pow_eq_algebraMap_norm {p : ℕ} (t : K)
    (ht : ∀ σ : Gal(K/k), ∃ s : (σ • w).adicCompletion K, adicCoe t (σ • w) = s ^ p) :
    ∃ c : (primeUnder (𝓞 k) w).adicCompletion k,
      algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (Algebra.norm k t) = c ^ p := by
  classical
  haveI : Fintype ↥(stabilizer Gal(K/k) w) := Fintype.ofFinite _
  haveI : Fintype (Gal(K/k) ⧸ stabilizer Gal(K/k) w) := Fintype.ofFinite _
  choose s hs using ht
  set z : Gal(K/k) ⧸ stabilizer Gal(K/k) w → w.adicCompletion K := fun L =>
    (adicCompletionGalEquiv w (Quotient.out L)).symm (s (Quotient.out L)) with hzdef
  refine ⟨∏ L : Gal(K/k) ⧸ stabilizer Gal(K/k) w,
    Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (z L), ?_⟩
  refine (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)).injective ?_
  have key : ∀ L : Gal(K/k) ⧸ stabilizer Gal(K/k) w,
      ∏ d : ↥(stabilizer Gal(K/k) w),
          adicCoe (((d : Gal(K/k)) * (Quotient.out L)⁻¹) t) w
        = (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
            (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (z L))) ^ p := by
    intro L
    have hzL : adicCoe (((Quotient.out L)⁻¹ : Gal(K/k)) t) w = z L ^ p := by
      rw [adicCoe_inv_smul_eq_symm w (Quotient.out L) t, hs, hzdef, map_pow]
    calc ∏ d : ↥(stabilizer Gal(K/k) w),
            adicCoe (((d : Gal(K/k)) * (Quotient.out L)⁻¹) t) w
        = ∏ d : ↥(stabilizer Gal(K/k) w), d • (z L ^ p) := by
          refine Finset.prod_congr rfl fun d _ => ?_
          rw [AlgEquiv.mul_apply, ← smul_adicCoe, hzL]
      _ = (∏ d : ↥(stabilizer Gal(K/k) w), d • z L) ^ p := by
          rw [← Finset.prod_pow]
          exact Finset.prod_congr rfl fun d _ => smul_pow' d (z L) p
      _ = _ := by rw [prod_stabilizer_smul_eq_algebraMap_norm k w]
  calc algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
        (algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (Algebra.norm k t))
      = ∏ σ : Gal(K/k), adicCoe (σ t) w := by
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K,
          Algebra.norm_eq_prod_automorphisms, map_prod]
        rfl
    _ = ∏ L : Gal(K/k) ⧸ stabilizer Gal(K/k) w, ∏ d : ↥(stabilizer Gal(K/k) w),
          adicCoe (((d : Gal(K/k)) * (Quotient.out L)⁻¹) t) w :=
        prod_eq_prod_quotient_prod_subgroup _ _
    _ = ∏ L : Gal(K/k) ⧸ stabilizer Gal(K/k) w,
          (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
            (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) (z L))) ^ p :=
        Finset.prod_congr rfl fun L _ => key L
    _ = _ := by rw [map_pow, map_prod, ← Finset.prod_pow]

variable (k) in
/-- **The norm of a unit whose local class is trivial at every place above a place of the base has
trivial local class there.** -/
theorem localClassHom_norm_eq_one {p : ℕ} (hp : p ≠ 0) (t : Kˣ)
    (ht : ∀ σ : Gal(K/k), localClassHom (σ • w) p t = 1) :
    localClassHom (primeUnder (𝓞 k) w) p (Units.map (Algebra.norm k : K →* k) t) = 1 := by
  obtain ⟨c, hc⟩ := exists_pow_eq_algebraMap_norm k w (t : K) fun σ => by
    obtain ⟨s, hs⟩ := exists_pow_eq_of_localClassHom_eq_one (ht σ)
    exact ⟨(s : (σ • w).adicCompletion K), by rw [← Units.val_pow_eq_pow_val, hs]; rfl⟩
  have hc0 : c ≠ 0 := by
    intro h
    refine Units.ne_zero (Units.map (Algebra.norm k : K →* k) t)
      ((algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k)).injective ?_)
    rw [map_zero]
    show algebraMap k _ (Algebra.norm k (t : K)) = 0
    rw [hc, h, zero_pow hp]
  refine (QuotientGroup.eq_one_iff _).2 ⟨Units.mk0 c hc0, Units.ext ?_⟩
  show c ^ p = algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (Algebra.norm k (t : K))
  rw [hc]

variable (k) in
/-- **Two units whose local classes agree at every place above a place of the base have norms
whose local classes agree there.** -/
theorem localClassHom_norm_eq_of_forall_eq {p : ℕ} (hp : p ≠ 0) (t s : Kˣ)
    (hts : ∀ σ : Gal(K/k), localClassHom (σ • w) p t = localClassHom (σ • w) p s) :
    localClassHom (primeUnder (𝓞 k) w) p (Units.map (Algebra.norm k : K →* k) t)
      = localClassHom (primeUnder (𝓞 k) w) p (Units.map (Algebra.norm k : K →* k) s) := by
  have h := localClassHom_norm_eq_one k w hp (t * s⁻¹) fun σ => by
    rw [_root_.map_mul, _root_.map_inv, hts σ, mul_inv_cancel]
  rw [_root_.map_mul, _root_.map_inv, _root_.map_mul, _root_.map_inv] at h
  exact mul_inv_eq_one.1 h

end Norm

/-! ### The order of a norm -/

section OrdNorm

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The order at a prime of the extension of an element of the base field** is its order at the
prime below, multiplied by the ramification index. -/
theorem ord_algebraMap_eq_ramIdx_mul {x : k} (hx : x ≠ 0) :
    ord K w (algebraMap k K x) = ramIdx (𝓞 k) w * ord k (primeUnder (𝓞 k) w) x := by
  have hxK : algebraMap k K x ≠ 0 := (map_ne_zero_iff _ (algebraMap k K).injective).2 hx
  have h := valuation_algebraMap (A := 𝓞 k) (B := 𝓞 K) (k := k) (K := K) w x
  rw [valuation_eq_exp_neg_ord K w hxK, valuation_eq_exp_neg_ord k _ hx,
    ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h
  linarith

variable (k) in
/-- **At a prime of the base unramified in the extension, the order of a norm is divisible by
whatever divides the orders of the element at all the primes above.**  The conjugates of the
element realise exactly those orders, and the norm is their product. -/
theorem dvd_ord_norm_of_forall_dvd [IsGalois k K] {p : ℕ} (he : ramIdx (𝓞 k) w = 1) {t : K}
    (ht0 : t ≠ 0) (ht : ∀ σ : Gal(K/k), (p : ℤ) ∣ ord K (σ • w) t) :
    (p : ℤ) ∣ ord k (primeUnder (𝓞 k) w) (Algebra.norm k t) := by
  classical
  have hn0 : Algebra.norm k t ≠ 0 := Algebra.norm_ne_zero_iff.2 ht0
  have h1 : ord K w (algebraMap k K (Algebra.norm k t))
      = ord k (primeUnder (𝓞 k) w) (Algebra.norm k t) := by
    rw [ord_algebraMap_eq_ramIdx_mul k w hn0, he, Nat.cast_one, one_mul]
  have hσ0 : ∀ σ : Gal(K/k), σ t ≠ 0 := fun σ => (map_ne_zero_iff σ σ.injective).2 ht0
  have hne : ∀ s : Finset Gal(K/k), (∏ σ ∈ s, σ t) ≠ 0 := fun s =>
    Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  rw [← h1, Algebra.norm_eq_prod_automorphisms]
  suffices h : ∀ s : Finset Gal(K/k), (p : ℤ) ∣ ord K w (∏ σ ∈ s, σ t) from h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, ord_mul w (hσ0 a) (hne s)]
      refine dvd_add ?_ ih
      have hkey : ord K w (a t) = ord K (a⁻¹ • w) t := by
        rw [← ord_galSmul a (a⁻¹ • w) t, smul_inv_smul]
      rw [hkey]
      exact ht a⁻¹

variable (k) in
/-- **The norm of a unit unramified at every place above a prime of the base unramified in the
extension is unramified there.** -/
theorem localClassHom_norm_mem_localUnramified [IsGalois k K] {p : ℕ} [NeZero p]
    (he : ramIdx (𝓞 k) w = 1) (t : Kˣ)
    (ht : ∀ σ : Gal(K/k), localClassHom (σ • w) p t ∈ localUnramified (σ • w) p) :
    localClassHom (primeUnder (𝓞 k) w) p (Units.map (Algebra.norm k : K →* k) t)
      ∈ localUnramified (primeUnder (𝓞 k) w) p := by
  rw [localClassHom_mem_localUnramified_iff, placeValue_eq_neg_ord, dvd_neg]
  refine dvd_ord_norm_of_forall_dvd k w he (Units.ne_zero t) fun σ => ?_
  have h := (localClassHom_mem_localUnramified_iff (σ • w) t).1 (ht σ)
  rwa [placeValue_eq_neg_ord, dvd_neg] at h

end OrdNorm

end InverseGalois.CFT
