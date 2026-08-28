/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.PowBasis

/-!
# The Kummer pairing on a power basis, read through exponent vectors

Let `B` be a subgroup of the units of a field `K` containing a primitive `p`-th root of unity, and
let `g₁, …, g_s` be a power basis of `B`: every element of `B` is a product of powers of the `gᵢ`
times a `p`-th power, and the only relations between the `gᵢ` are the obvious ones.  Adjoining a
`p`-th root `wᵢ` of each `gᵢ` gives a Galois extension whose group is described by the family of
roots of unity `σ wᵢ / wᵢ`, and every such family is realised by an automorphism.

Under this dictionary the radical attached to an element `∏ gᵢ ^ mᵢ ⬝ z ^ p` of `B` is fixed by the
automorphism with exponents `c` exactly when `p` divides `∑ cᵢ mᵢ`.  Two elements of `B` therefore
generate the same extension of `K` by radicals exactly when their exponent vectors are proportional
modulo `p`, and the whole comparison collapses to a statement about vectors over the field with `p`
elements: a vector annihilated by every functional annihilating another one is a multiple of it.

## Main results

* `InverseGalois.CFT.exists_mul_of_forall_dot`: a vector annihilated by every functional
  annihilating a second vector is a scalar multiple of that second vector.
* `InverseGalois.CFT.PowBasis.exists_aut_radOf_iff`: **for every exponent vector there is an
  automorphism fixing exactly the radicals whose exponent vector is orthogonal to it modulo `p`.**
* `InverseGalois.CFT.PowBasis.exists_zpow_mul_pow_of_forall_fix`: **an element of the subgroup whose
  radical is fixed by every automorphism fixing the radical of a second element is, modulo `p`-th
  powers, a power of that second element.**

## Tags

Kummer theory, radical extension, power basis, pairing, exponent vector
-/

namespace InverseGalois.CFT

open Rigidity.RET

/-! ### Auxiliary arithmetic -/

section Aux

/-- A product of powers of a fixed nonzero element is the power at the sum of the exponents. -/
theorem prod_zpow_eq_zpow_sum {F : Type*} [Field F] {ι : Type*} (s : Finset ι) {x : F}
    (hx : x ≠ 0) (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

variable {F : Type*} [Field F] {s : ℕ}

/-- Pairing a vector against a one-point-supported family picks out a single term. -/
theorem sum_single_mul (i : Fin s) (a : F) (N : Fin s → F) :
    ∑ j, (Pi.single i a : Fin s → F) j * N j = a * N i := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Pairing a vector against a difference of two one-point-supported families. -/
theorem sum_sub_single_mul (j i₀ : Fin s) (a b : F) (N : Fin s → F) :
    ∑ i, (Pi.single j a - Pi.single i₀ b : Fin s → F) i * N i = a * N j - b * N i₀ := by
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sum_single_mul]

/-- **A vector annihilated by every functional annihilating a second vector is a scalar multiple of
that second vector.**  If the second vector is zero then so is the first, and otherwise the scalar
is read off at any coordinate where the second vector does not vanish. -/
theorem exists_mul_of_forall_dot (N M : Fin s → F)
    (h : ∀ c : Fin s → F, ∑ i, c i * N i = 0 → ∑ i, c i * M i = 0) :
    ∃ l : F, ∀ i, M i = l * N i := by
  by_cases hN : ∀ i, N i = 0
  · refine ⟨0, fun i => ?_⟩
    rw [zero_mul]
    have := h (Pi.single i (1 : F)) (by rw [sum_single_mul, hN i, mul_zero])
    rwa [sum_single_mul, one_mul] at this
  · push_neg at hN
    obtain ⟨i₀, hi₀⟩ := hN
    refine ⟨M i₀ / N i₀, fun j => ?_⟩
    have key := h (Pi.single j (1 : F) - Pi.single i₀ (N j / N i₀)) ?_
    · rw [sum_sub_single_mul, one_mul] at key
      field_simp at key ⊢
      linear_combination key
    · rw [sum_sub_single_mul, one_mul, div_mul_cancel₀ _ hi₀, sub_self]

end Aux

/-! ### Radicals and roots of unity -/

section Roots

variable {K M : Type*} [Field K] [Field M] [Algebra K M] {p : ℕ} [NeZero p] {ζ : K}

/-- A `p`-th root of unity in an extension whose base contains a primitive `p`-th root of unity is
fixed by every automorphism over the base. -/
theorem map_eq_self_of_pow_eq_one (hζ : IsPrimitiveRoot ζ p) (σ : M ≃ₐ[K] M) {c : M}
    (hc : c ^ p = 1) : σ c = c := by
  have hζM : IsPrimitiveRoot (algebraMap K M ζ) p :=
    hζ.map_of_injective (algebraMap K M).injective
  obtain ⟨j, -, rfl⟩ := hζM.eq_pow_of_pow_eq_one hc
  rw [map_pow, AlgEquiv.commutes]

/-- Two `p`-th roots of the same element differ by a root of unity, so an automorphism fixes one of
them exactly when it fixes the other. -/
theorem aut_fix_iff_of_pow_eq (hζ : IsPrimitiveRoot ζ p) (σ : M ≃ₐ[K] M) {w w' : M}
    (hw : w ≠ 0) (hw' : w' ≠ 0) (h : w ^ p = w' ^ p) : σ w = w ↔ σ w' = w' := by
  have hc : (w / w') ^ p = 1 := by rw [div_pow, h, div_self (pow_ne_zero p hw')]
  have hcne : w / w' ≠ 0 := div_ne_zero hw hw'
  have hσc : σ (w / w') = w / w' := map_eq_self_of_pow_eq_one hζ σ hc
  have hweq : w = (w / w') * w' := by rw [div_mul_cancel₀ _ hw']
  constructor
  · intro hfix
    rw [hweq, map_mul, hσc] at hfix
    exact mul_left_cancel₀ hcne hfix
  · intro hfix
    rw [hweq, map_mul, hσc, hfix]

end Roots

namespace PowBasis

/-! ### The radical attached to an exponent vector -/

section Exponents

variable {K : Type*} [Field K] {p s : ℕ} [NeZero p] {B : Subgroup Kˣ} (P : PowBasis B p s)

/-- The `p`-th root, in the extension generated by the `p`-th roots of the radicands, of the
element of the subgroup described by an exponent vector and a correction factor. -/
noncomputable def radOf (m : Fin s → ℤ) (z : Kˣ) : P.ext :=
  (∏ i, Kummer.radRoot p P.rad i ^ m i) * algebraMap K P.ext (z : K)

theorem radOf_eq (m : Fin s → ℤ) (z : Kˣ) :
    P.radOf m z = (∏ i, Kummer.radRoot p P.rad i ^ m i) * algebraMap K P.ext (z : K) := rfl

theorem radRoot_ne_zero' (i : Fin s) : Kummer.radRoot p P.rad i ≠ 0 :=
  Kummer.radRoot_ne_zero P.rad_ne_zero i

theorem prod_radRoot_ne_zero (m : Fin s → ℤ) :
    (∏ i, Kummer.radRoot p P.rad i ^ m i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (P.radRoot_ne_zero' i)

theorem radOf_ne_zero (m : Fin s → ℤ) (z : Kˣ) : P.radOf m z ≠ 0 := by
  refine mul_ne_zero (P.prod_radRoot_ne_zero m) ?_
  simp only [ne_eq, map_eq_zero]
  exact Units.ne_zero z

/-- The `p`-th power of the radical attached to an exponent vector is the corresponding product of
radicands, times the `p`-th power of the correction factor. -/
theorem radOf_pow (m : Fin s → ℤ) (z : Kˣ) :
    P.radOf m z ^ p = algebraMap K P.ext ((∏ i, P.rad i ^ m i) * (z : K) ^ p) := by
  have hstep : ∀ i : Fin s, (Kummer.radRoot p P.rad i ^ m i) ^ p
      = algebraMap K P.ext (P.rad i) ^ m i := by
    intro i
    rw [← Kummer.radRoot_pow (n := p) (g := P.rad) i,
      ← zpow_natCast (Kummer.radRoot p P.rad i ^ m i) p, ← zpow_mul,
      ← zpow_natCast (Kummer.radRoot p P.rad i) p, ← zpow_mul, mul_comm]
  rw [radOf_eq, mul_pow, ← Finset.prod_pow, map_mul, map_prod, map_pow]
  refine congrArg (fun x => x * (algebraMap K P.ext (z : K)) ^ p) ?_
  exact Finset.prod_congr rfl fun i _ => (hstep i).trans (map_zpow₀ _ _ _).symm

/-- The radical attached to a presentation of an element of the subgroup is a `p`-th root of that
element. -/
theorem radOf_pow_of_span {x : Kˣ} {m : Fin s → ℤ} {z : Kˣ}
    (hx : x = (∏ i, P.g i ^ m i) * z ^ p) :
    P.radOf m z ^ p = algebraMap K P.ext (x : K) := by
  rw [radOf_pow, hx]
  congr 1
  push_cast
  rfl

/-- An automorphism fixes the radical attached to an exponent vector exactly when the corresponding
product of the roots of unity it introduces is trivial. -/
theorem aut_radOf_eq_iff (σ : P.ext ≃ₐ[K] P.ext) (m : Fin s → ℤ) (z : Kˣ) :
    σ (P.radOf m z) = P.radOf m z ↔
      ∏ i, (σ (Kummer.radRoot p P.rad i) / Kummer.radRoot p P.rad i) ^ m i = 1 := by
  have hz : algebraMap K P.ext (z : K) ≠ 0 := by
    simp only [ne_eq, map_eq_zero]
    exact Units.ne_zero z
  have hdiv : ∏ i, (σ (Kummer.radRoot p P.rad i) / Kummer.radRoot p P.rad i) ^ m i
      = (∏ i, (σ (Kummer.radRoot p P.rad i)) ^ m i)
        / (∏ i, Kummer.radRoot p P.rad i ^ m i) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun i _ => div_zpow _ _ _
  have hσ : σ (P.radOf m z) = (∏ i, (σ (Kummer.radRoot p P.rad i)) ^ m i)
      * algebraMap K P.ext (z : K) := by
    rw [radOf_eq, map_mul, map_prod, AlgEquiv.commutes]
    exact congrArg (fun x => x * algebraMap K P.ext (z : K))
      (Finset.prod_congr rfl fun i _ => map_zpow₀ σ _ _)
  rw [hdiv, div_eq_one_iff_eq (P.prod_radRoot_ne_zero m), hσ, radOf_eq]
  exact mul_left_inj' hz

end Exponents

/-! ### The Kummer condition in terms of exponent vectors -/

section Kummer

variable {K : Type*} [Field K] [CharZero K] {p s : ℕ} [NeZero p] {ζ : K} {B : Subgroup Kˣ}
  (P : PowBasis B p s)

/-- **For every exponent vector there is an automorphism fixing exactly the radicals whose exponent
vector is orthogonal to it modulo `p`.**  The automorphism multiplying the `i`-th radical by the
`cᵢ`-th power of the root of unity multiplies the radical of an exponent vector `m` by the power of
the root of unity at `∑ cᵢ mᵢ`. -/
theorem exists_aut_radOf_iff (hζ : IsPrimitiveRoot ζ p) (c : Fin s → ℤ) :
    ∃ σ : P.ext ≃ₐ[K] P.ext, ∀ (m : Fin s → ℤ) (z : Kˣ),
      (σ (P.radOf m z) = P.radOf m z ↔ (p : ℤ) ∣ ∑ i, c i * m i) := by
  obtain ⟨σ, hσ⟩ := (P.setup hζ).exists_aut_zpow c
  refine ⟨σ, fun m z => ?_⟩
  rw [P.aut_radOf_eq_iff σ m z]
  have hstep : ∀ i, σ (Kummer.radRoot p P.rad i) / Kummer.radRoot p P.rad i
      = (P.setup hζ).zetaL ^ c i := by
    intro i
    have h : σ (Kummer.radRoot p P.rad i)
        = (P.setup hζ).zetaL ^ c i * Kummer.radRoot p P.rad i := hσ i
    rw [h, mul_div_assoc, div_self (P.radRoot_ne_zero' i), mul_one]
  have hmul : ∀ i, ((P.setup hζ).zetaL ^ c i) ^ m i = (P.setup hζ).zetaL ^ (c i * m i) :=
    fun i => (zpow_mul _ _ _).symm
  simp only [hstep, hmul]
  rw [prod_zpow_eq_zpow_sum Finset.univ (P.setup hζ).zetaL_ne_zero]
  exact (P.setup hζ).zetaL_isPrimitiveRoot.zpow_eq_one_iff_dvd _

/-- **An element of the subgroup whose radical is fixed by every automorphism fixing the radical of
a second element is, modulo `p`-th powers, a power of that second element.**  Expanding both
elements in the power basis, the hypothesis says that every exponent vector orthogonal to the one
of the second element is orthogonal to the one of the first, so the two exponent vectors are
proportional modulo `p`. -/
theorem exists_zpow_mul_pow_of_forall_fix (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    {a x : Kˣ} (ha : a ∈ B) (hx : x ∈ B) {wa wx : P.ext}
    (hwa : wa ^ p = algebraMap K P.ext (a : K)) (hwx : wx ^ p = algebraMap K P.ext (x : K))
    (hfix : ∀ σ : P.ext ≃ₐ[K] P.ext, σ wa = wa → σ wx = wx) :
    ∃ (l : ℤ) (y : Kˣ), x = a ^ l * y ^ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, za, hn⟩ := P.span a ha
  obtain ⟨m, zx, hm⟩ := P.span x hx
  have hwa' := P.radOf_pow_of_span hn
  have hwx' := P.radOf_pow_of_span hm
  have hane : wa ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hwa
    exact Units.ne_zero a ((map_eq_zero _).mp hwa.symm)
  have hxne : wx ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hwx
    exact Units.ne_zero x ((map_eq_zero _).mp hwx.symm)
  have hfix' : ∀ σ : P.ext ≃ₐ[K] P.ext,
      σ (P.radOf n za) = P.radOf n za → σ (P.radOf m zx) = P.radOf m zx := by
    intro σ h
    refine (aut_fix_iff_of_pow_eq hζ σ (P.radOf_ne_zero m zx) hxne
      (hwx'.trans hwx.symm)).mpr (hfix σ ?_)
    exact (aut_fix_iff_of_pow_eq hζ σ (P.radOf_ne_zero n za) hane (hwa'.trans hwa.symm)).mp h
  have hdvd : ∀ c : Fin s → ℤ, (p : ℤ) ∣ ∑ i, c i * n i → (p : ℤ) ∣ ∑ i, c i * m i := by
    intro c hc
    obtain ⟨σ, hσ⟩ := P.exists_aut_radOf_iff hζ c
    exact (hσ m zx).mp (hfix' σ ((hσ n za).mpr hc))
  have hzm : ∀ c : Fin s → ZMod p,
      ∑ i, c i * (n i : ZMod p) = 0 → ∑ i, c i * (m i : ZMod p) = 0 := by
    intro c hc
    have hlift : ∀ i : Fin s, (((c i).val : ℕ) : ZMod p) = c i :=
      fun i => ZMod.natCast_rightInverse (c i)
    have hcn : ((∑ i, ((c i).val : ℤ) * n i : ℤ) : ZMod p) = ∑ i, c i * (n i : ZMod p) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [hlift i]
    have hcm : ((∑ i, ((c i).val : ℤ) * m i : ℤ) : ZMod p) = ∑ i, c i * (m i : ZMod p) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [hlift i]
    rw [← hcm, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine hdvd _ ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hcn]
    exact hc
  obtain ⟨l₀, hl₀⟩ := exists_mul_of_forall_dot (F := ZMod p) (fun i => (n i : ZMod p))
    (fun i => (m i : ZMod p)) hzm
  set l : ℤ := (l₀.val : ℤ) with hldef
  have hlcast : ((l : ℤ) : ZMod p) = l₀ := by
    rw [hldef]
    push_cast
    exact ZMod.natCast_rightInverse l₀
  have hdvd' : ∀ i, (p : ℤ) ∣ m i - l * n i := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hlcast, ← hl₀ i, sub_self]
  choose k hk using hdvd'
  refine ⟨l, (∏ i, P.g i ^ k i) * zx * za ^ (-l), ?_⟩
  have hGm : (∏ i, P.g i ^ m i)
      = (∏ i, P.g i ^ n i) ^ l * (∏ i, P.g i ^ k i) ^ p := by
    rw [← Finset.prod_zpow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, ← zpow_natCast (P.g i ^ k i) p, ← zpow_mul, ← zpow_add]
    congr 1
    linear_combination hk i
  have h1 : ((∏ i, P.g i ^ n i) * za ^ p) ^ l
      = (∏ i, P.g i ^ n i) ^ l * za ^ ((p : ℤ) * l) := by
    rw [mul_zpow, ← zpow_natCast za p, ← zpow_mul]
  have h2 : ((∏ i, P.g i ^ k i) * zx * za ^ (-l)) ^ p
      = (∏ i, P.g i ^ k i) ^ p * zx ^ p * za ^ (-l * (p : ℤ)) := by
    rw [mul_pow, mul_pow, ← zpow_natCast (za ^ (-l)) p, ← zpow_mul]
  have h3 : za ^ ((p : ℤ) * l) * za ^ (-l * (p : ℤ)) = 1 := by
    rw [← zpow_add, show (p : ℤ) * l + -l * (p : ℤ) = 0 by ring, zpow_zero]
  rw [hm, hn, h1, h2, hGm]
  calc (∏ i, P.g i ^ n i) ^ l * (∏ i, P.g i ^ k i) ^ p * zx ^ p
      = (∏ i, P.g i ^ n i) ^ l * ((∏ i, P.g i ^ k i) ^ p * zx ^ p)
        * (za ^ ((p : ℤ) * l) * za ^ (-l * (p : ℤ))) := by rw [h3, mul_one, mul_assoc]
    _ = (∏ i, P.g i ^ n i) ^ l * za ^ ((p : ℤ) * l)
        * ((∏ i, P.g i ^ k i) ^ p * zx ^ p * za ^ (-l * (p : ℤ))) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]

end Kummer

end PowBasis

end InverseGalois.CFT
