/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Prime divisors of polynomial values, and primes that split completely

A non-constant polynomial with integer coefficients has, among the values it takes at integer
arguments, numbers divisible by infinitely many different rational primes.  This is a classical
observation of Schur, and the proof given here is his: it uses nothing beyond the division
algorithm and the fact that a non-zero polynomial has only finitely many roots.

The mechanism is the congruence `f (c * Q * x) ≡ f 0 = c  (mod c * Q)`, valid because `a - b`
divides `f a - f b`.  Writing `f (c * Q * x) = c * m`, the cofactor `m` is congruent to `1`
modulo `Q`, so no prime dividing `Q` can divide `m`.  If the primes occurring as divisors of
values of `f` were finite in number and `Q` were their product, then any prime factor of `m`
would have to divide `Q`, and `m` would be forced to be a unit; but a non-constant polynomial
attains each of the two values `c` and `-c` only finitely often, so `m` can be made a non-unit.

Applied to the minimal polynomial `f` of a generator of a number field `K` which is Galois over
`ℚ`, this yields the classical statement that infinitely many rational primes split completely in
`K`.  Indeed, for all but finitely many `p` the theorem of Kummer and Dedekind reads the
factorization of `p` in the ring of integers off the factorization of `f` modulo `p`; a root of
`f` modulo `p` therefore produces a prime of `K` above `p` of residue degree one, and in a Galois
extension all the primes above `p` are conjugate, hence share that residue degree.  The
ramification indices are one as well, because for almost all `p` the reduction of `f` modulo `p`
is squarefree.

## Main results

* `InverseGalois.NumberTheory.finite_setOf_eval_eq` — a non-constant integer polynomial takes any
  prescribed value at only finitely many integers.
* `InverseGalois.NumberTheory.infinite_setOf_prime_dvd_eval` — the set of rational primes dividing
  some value of a non-constant integer polynomial is infinite.
* `InverseGalois.NumberTheory.infinite_setOf_prime_isRoot_map` — the same statement read modulo
  `p`: infinitely many primes `p` are such that the reduction of `f` modulo `p` has a root in
  `ZMod p`.
* `InverseGalois.NumberTheory.finite_setOf_prime_not_squarefree_map` — an integer polynomial whose
  rational reduction is separable has squarefree reduction modulo all but finitely many primes.
* `InverseGalois.NumberTheory.exponent_ne_zero` — the Kummer–Dedekind exponent of a generator of a
  number field is non-zero, so that only finitely many primes are excluded by it.
* `InverseGalois.NumberTheory.SplitsCompletely` — the property of a rational prime that every
  prime of the ring of integers above it is unramified of residue degree one.
* `InverseGalois.NumberTheory.infinite_setOf_prime_splitsCompletely` — infinitely many rational
  primes split completely in a number field that is Galois over `ℚ`.
-/

open Polynomial

namespace InverseGalois.NumberTheory

/-! ### Schur's theorem on prime divisors of polynomial values -/

/-- **A non-constant integer polynomial attains a prescribed value only finitely often.**  Indeed
the integers `y` with `f y = v` are exactly the roots of `f - v`, a non-zero polynomial. -/
theorem finite_setOf_eval_eq {f : ℤ[X]} (hf : 0 < f.natDegree) (v : ℤ) :
    {y : ℤ | f.eval y = v}.Finite := by
  have hne : f - C v ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, natDegree_C] at hf
    exact lt_irrefl 0 hf
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  simp [Polynomial.IsRoot, hy]

/-- **Infinitely many rational primes divide a value of a non-constant integer polynomial.**  Let
`c = f 0`.  If `c = 0` every prime divides `f 0`.  Otherwise, were the set of such primes finite
with product `Q`, the integer `m = f (c * Q * x) / c` would be congruent to `1` modulo `Q` for
every `x`, so that each of its prime factors, dividing a value of `f` and hence dividing `Q`,
would also divide `1`; consequently `m = ±1`, that is `f (c * Q * x) = ±c`, for every `x`, which
a non-constant polynomial cannot do. -/
theorem infinite_setOf_prime_dvd_eval {f : ℤ[X]} (hf : 0 < f.natDegree) :
    {p : ℕ | p.Prime ∧ ∃ n : ℤ, (p : ℤ) ∣ f.eval n}.Infinite := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, f.eval 0 = c := ⟨_, rfl⟩
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- Every prime divides the value `f 0 = 0`.
    refine Nat.infinite_setOf_prime.mono ?_
    intro p hp
    exact ⟨hp, 0, by rw [hc, hc0]; exact dvd_zero _⟩
  by_contra hcon
  rw [Set.not_infinite] at hcon
  set F : Finset ℕ := hcon.toFinset with hFdef
  set Q : ℤ := ∏ p ∈ F, (p : ℤ) with hQdef
  have hQ0 : Q ≠ 0 := by
    rw [hQdef]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hpp : p.Prime := (hcon.mem_toFinset.mp hp).1
    exact_mod_cast hpp.ne_zero
  have hcQ : c * Q ≠ 0 := mul_ne_zero hc0 hQ0
  -- Only finitely many arguments `x` give `f (c * Q * x) = ±c`.
  have hA : ({y : ℤ | f.eval y = c} ∪ {y : ℤ | f.eval y = -c}).Finite :=
    (finite_setOf_eval_eq hf c).union (finite_setOf_eval_eq hf (-c))
  have hB : ((fun x : ℤ => c * Q * x) ⁻¹'
      ({y : ℤ | f.eval y = c} ∪ {y : ℤ | f.eval y = -c})).Finite :=
    hA.preimage (mul_right_injective₀ hcQ).injOn
  obtain ⟨x, hx⟩ := hB.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq,
    not_or] at hx
  obtain ⟨hx1, hx2⟩ := hx
  -- The value at `c * Q * x` is congruent to `c` modulo `c * Q`.
  have hdvd : c * Q ∣ f.eval (c * Q * x) - c := by
    have h1 : c * Q * x - 0 ∣ f.eval (c * Q * x) - f.eval 0 :=
      Polynomial.sub_dvd_eval_sub _ _ f
    rw [sub_zero, hc] at h1
    exact dvd_trans ⟨x, rfl⟩ h1
  obtain ⟨k, hk⟩ := hdvd
  have hval : f.eval (c * Q * x) = c * (1 + Q * k) := by linear_combination hk
  -- The cofactor is not a unit.
  have hm1 : (1 + Q * k).natAbs ≠ 1 := by
    intro h
    rcases Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr h) with h1 | h1
    · exact hx1 (by rw [hval, h1, mul_one])
    · exact hx2 (by rw [hval, h1, mul_neg_one])
  obtain ⟨q, hq, hqm⟩ := Int.exists_prime_and_dvd hm1
  have hqf : q ∣ f.eval (c * Q * x) := by rw [hval]; exact hqm.mul_left c
  have hmemF : q.natAbs ∈ F :=
    hcon.mem_toFinset.mpr ⟨Int.prime_iff_natAbs_prime.mp hq, c * Q * x,
      Int.natAbs_dvd.mpr hqf⟩
  have hqQ : q ∣ Q := by
    have h2 : ((q.natAbs : ℕ) : ℤ) ∣ Q := by
      rw [hQdef]; exact Finset.dvd_prod_of_mem (fun p : ℕ => (p : ℤ)) hmemF
    exact Int.natAbs_dvd.mp h2
  have hq1 : q ∣ (1 : ℤ) := by
    have h3 : (1 : ℤ) = (1 + Q * k) - Q * k := by ring
    rw [h3]
    exact dvd_sub hqm (hqQ.mul_right k)
  exact hq.not_unit (isUnit_of_dvd_one hq1)

/-- **For infinitely many primes `p` the reduction of a non-constant integer polynomial modulo `p`
has a root.**  Having a root in `ZMod p` is the same as having a value divisible by `p`, so this is
a restatement of the previous theorem. -/
theorem infinite_setOf_prime_isRoot_map {f : ℤ[X]} (hf : 0 < f.natDegree) :
    {p : ℕ | p.Prime ∧
      ∃ a : ZMod p, (f.map (Int.castRingHom (ZMod p))).IsRoot a}.Infinite := by
  refine (infinite_setOf_prime_dvd_eval hf).mono ?_
  rintro p ⟨hp, n, hn⟩
  refine ⟨hp, (n : ZMod p), ?_⟩
  have : ((f.eval n : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hn
  simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    Polynomial.hom_eval₂] using this

/-! ### Squarefreeness of the reduction -/

/-- **An integer polynomial with separable rational reduction has squarefree reduction modulo all
but finitely many primes.**  Clearing denominators in a Bézout relation between the polynomial and
its derivative over the rationals produces integer polynomials `U` and `V` and a non-zero integer
`N` with `U * f + V * f' = N`.  Modulo any prime not dividing `N` the constant `N` is invertible,
so the same relation exhibits the reduction of `f` as separable, hence squarefree. -/
theorem finite_setOf_prime_not_squarefree_map {f : ℤ[X]}
    (hf : (f.map (Int.castRingHom ℚ)).Separable) :
    {p : ℕ | p.Prime ∧ ¬ Squarefree (f.map (Int.castRingHom (ZMod p)))}.Finite := by
  classical
  have hsmulQ : ∀ (x : ℤ) (q : ℚ[X]), x • q = C ((x : ℚ)) * q := fun x q => by
    simp [zsmul_eq_mul]
  obtain ⟨u, v, huv⟩ := hf
  obtain ⟨bu, hbu⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) u
  obtain ⟨bv, hbv⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) v
  set U : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) u with hU
  set V : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) v with hV
  set N : ℤ := (bu : ℤ) * (bv : ℤ) with hN
  have hNne : N ≠ 0 :=
    mul_ne_zero (nonZeroDivisors.coe_ne_zero bu) (nonZeroDivisors.coe_ne_zero bv)
  set W : ℤ[X] := (C (bv : ℤ) * U) * f + (C (bu : ℤ) * V) * (derivative f) with hW
  -- The Bézout relation, cleared of denominators.
  have hWeq : W = C N := by
    refine Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective ?_
    have hbu' : U.map (Int.castRingHom ℚ) = C ((bu : ℤ) : ℚ) * u := by
      rw [show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, hbu, hsmulQ]
    have hbv' : V.map (Int.castRingHom ℚ) = C ((bv : ℤ) : ℚ) * v := by
      rw [show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, hbv, hsmulQ]
    simp only [hW, hN, Polynomial.map_add, Polynomial.map_mul, hbu', hbv',
      ← Polynomial.derivative_map, eq_intCast, map_intCast, Polynomial.map_intCast, Int.cast_mul]
    linear_combination (((bu : ℤ) : ℚ[X]) * ((bv : ℤ) : ℚ[X])) * huv
  -- Every bad prime divides `N`, and there are finitely many such primes.
  refine Set.Finite.subset (N.natAbs.divisors : Finset ℕ).finite_toSet ?_
  rintro p ⟨hp, hsq⟩
  simp only [Finset.mem_coe, Nat.mem_divisors]
  refine ⟨?_, Int.natAbs_ne_zero.mpr hNne⟩
  by_contra hpd
  apply hsq
  haveI := Fact.mk hp
  have hNp : ((N : ZMod p)) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    exact hpd (by simpa using Int.natAbs_dvd_natAbs.mpr h)
  have hmodW : (C (bv : ℤ) * U).map (Int.castRingHom (ZMod p)) * f.map (Int.castRingHom (ZMod p))
      + (C (bu : ℤ) * V).map (Int.castRingHom (ZMod p))
        * derivative (f.map (Int.castRingHom (ZMod p))) = C ((N : ZMod p)) := by
    have h0 : W.map (Int.castRingHom (ZMod p)) = C ((N : ZMod p)) := by
      rw [hWeq, Polynomial.map_C]; rfl
    rw [hW] at h0
    rw [Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_add]
    exact h0
  refine Polynomial.Separable.squarefree ?_
  rw [Polynomial.separable_def']
  refine ⟨C ((N : ZMod p))⁻¹ * ((C (bv : ℤ) * U).map (Int.castRingHom (ZMod p))),
    C ((N : ZMod p))⁻¹ * ((C (bu : ℤ) * V).map (Int.castRingHom (ZMod p))), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, hmodW, ← C_mul, inv_mul_cancel₀ hNp, C_1]

/-- **An irreducible divisor of a squarefree element occurs with multiplicity exactly one.**
Were it to occur twice, its square would divide the element, contradicting squarefreeness. -/
theorem multiplicity_eq_one_of_squarefree {M : Type*} [CommMonoidWithZero M]
    {g Q : M} (hg : Squarefree g) (hQ : Irreducible Q) (hdvd : Q ∣ g) :
    multiplicity Q g = 1 := by
  refine multiplicity_eq_of_dvd_of_not_dvd (by simpa using hdvd) ?_
  intro h
  rw [show (1 : ℕ) + 1 = 2 from rfl, sq] at h
  exact hQ.not_isUnit (hg Q h)

/-! ### Number fields -/

section NumberFieldSection

open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid
open scoped IntermediateField

attribute [local instance] Int.ideal_span_isMaximal_of_prime

variable (K : Type*) [Field K] [NumberField K]

/-- **A number field is generated over the rationals by a single algebraic integer.**  A primitive
element exists by the theorem of the primitive element, and multiplying it by a suitable non-zero
integer makes it integral without changing the field it generates. -/
theorem exists_integral_primitive_element : ∃ θ : 𝓞 K, ℚ⟮(θ : K)⟯ = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  haveI : Algebra.IsAlgebraic ℤ K := (IsFractionRing.isAlgebraic_iff' ℤ (𝓞 K) K).mp inferInstance
  obtain ⟨y, hy, hyi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) α).exists_integral_multiple
  have hmul : (y : K) * α = y • α := by simp [Algebra.smul_def, algebraMap_int_eq]
  have hmem : IsIntegral ℤ ((y : K) * α) := by rw [hmul]; exact hyi
  refine ⟨⟨(y : K) * α, hmem⟩, ?_⟩
  show ℚ⟮(y : K) * α⟯ = ⊤
  rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
  have hy' : ((y : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hy
  have hkey : α = algebraMap ℚ K ((y : ℚ)⁻¹) * ((y : K) * α) := by
    rw [← mul_assoc, ← map_intCast (algebraMap ℚ K) y, ← map_mul, inv_mul_cancel₀ hy', map_one,
      one_mul]
  have hmem2 : algebraMap ℚ K ((y : ℚ)⁻¹) * ((y : K) * α) ∈ ℚ⟮(y : K) * α⟯ :=
    mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self _ _)
  rwa [← hkey] at hmem2

variable {K}

/-- **Every algebraic integer of a number field lies, after multiplication by a suitable non-zero
integer, in the ring generated by a primitive element.**  Since the primitive element generates the
field, the given integer is a polynomial in it with rational coefficients; clearing the denominators
of those coefficients supplies the required integer multiplier. -/
theorem exists_intCast_smul_mem_adjoin (θ : 𝓞 K) (hθ : ℚ⟮(θ : K)⟯ = ⊤) (b : 𝓞 K) :
    ∃ d : ℤ, d ≠ 0 ∧ d • b ∈ Subalgebra.toSubmodule (Algebra.adjoin ℤ ({θ} : Set (𝓞 K))) := by
  have hint : IsAlgebraic ℚ (θ : K) := Algebra.IsAlgebraic.isAlgebraic _
  have h1 : (b : K) ∈ Algebra.adjoin ℚ ({(θ : K)} : Set K) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint, hθ]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h1
  obtain ⟨q, hq⟩ := h1
  have hq' : Polynomial.aeval ((θ : K)) q = (b : K) := hq
  obtain ⟨m, hm⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) q
  set Q : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q with hQ
  refine ⟨(m : ℤ), nonZeroDivisors.coe_ne_zero m, ?_⟩
  have hcoe : ((Polynomial.aeval θ Q : 𝓞 K) : K) = Polynomial.aeval ((θ : K)) Q := by
    simp [Polynomial.aeval_algebraMap_apply]
  have hsm : ((m : ℤ) • q) = Polynomial.C (((m : ℤ) : ℚ)) * q := by simp [zsmul_eq_mul]
  have h2 : Polynomial.aeval ((θ : K)) Q = (m : ℤ) • (b : K) := by
    rw [← Polynomial.aeval_map_algebraMap (A := ℚ) ((θ : K)) Q, hm, hsm, map_mul,
      Polynomial.aeval_C, hq', zsmul_eq_mul]
    norm_num
  have h3 : (Polynomial.aeval θ Q : 𝓞 K) = (m : ℤ) • b := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap, hcoe, h2]
    simp
  rw [← h3]
  show (Polynomial.aeval θ Q : 𝓞 K) ∈ Algebra.adjoin ℤ ({θ} : Set (𝓞 K))
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨Q, rfl⟩

/-- **A single non-zero integer clears the denominators of the whole ring of integers at once.**
The ring of integers is a finitely generated abelian group; the product of the multipliers attached
to a finite generating set works for every element, because the ring generated by the primitive
element is a subgroup. -/
theorem exists_intCast_smul_mem_adjoin_forall (θ : 𝓞 K) (hθ : ℚ⟮(θ : K)⟯ = ⊤) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ b : 𝓞 K,
      d • b ∈ Subalgebra.toSubmodule (Algebra.adjoin ℤ ({θ} : Set (𝓞 K))) := by
  classical
  set A : Submodule ℤ (𝓞 K) := Subalgebra.toSubmodule (Algebra.adjoin ℤ ({θ} : Set (𝓞 K))) with hA
  choose dd hdd0 hddmem using exists_intCast_smul_mem_adjoin θ hθ
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 K)).FG)
  refine ⟨∏ b ∈ s, dd b, Finset.prod_ne_zero_iff.mpr fun b _ => hdd0 b, fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (s : Set (𝓞 K)) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rw [← Finset.prod_erase_mul _ _ hy, mul_smul]
      exact A.smul_mem _ (hddmem y)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact A.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact A.smul_mem c hy

/-- **The Kummer–Dedekind exponent of a primitive algebraic integer is non-zero.**  The exponent is
the least positive integer lying in the conductor of the order generated by the element, and any
integer clearing the denominators of the whole ring of integers lies in that conductor. -/
theorem exponent_ne_zero (θ : 𝓞 K) (hθ : ℚ⟮(θ : K)⟯ = ⊤) : RingOfIntegers.exponent θ ≠ 0 := by
  obtain ⟨d, hd0, hd⟩ := exists_intCast_smul_mem_adjoin_forall θ hθ
  have hne : ((d.natAbs : ℕ) : 𝓞 K) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro b
    have hb : (d : 𝓞 K) * b ∈ Algebra.adjoin ℤ ({θ} : Set (𝓞 K)) := by
      have := hd b
      rwa [zsmul_eq_mul] at this
    have hcast : ((d.natAbs : ℕ) : 𝓞 K) = ((d.natAbs : ℤ) : 𝓞 K) :=
      (Int.cast_natCast d.natAbs).symm
    rw [hcast]
    rcases Int.natAbs_eq d with h | h
    · rw [← h]; exact hb
    · rw [show ((d.natAbs : ℤ)) = -d by omega, Int.cast_neg, neg_mul]
      exact Subalgebra.neg_mem _ hb
  have hS : {e : ℕ | 0 < e ∧ (e : 𝓞 K) ∈ conductor ℤ θ}.Nonempty :=
    ⟨d.natAbs, Int.natAbs_pos.mpr hd0, hne⟩
  have hmem := Nat.sInf_mem hS
  rw [RingOfIntegers.exponent_eq_sInf]
  have h4 := hmem.1
  omega

/-- **The rational reduction of the minimal polynomial of an algebraic integer is separable.**
Over an integrally closed ring the minimal polynomial is unchanged by passing to the fraction
field, and minimal polynomials over a field of characteristic zero are separable. -/
theorem separable_map_minpoly (θ : 𝓞 K) :
    ((minpoly ℤ θ).map (Int.castRingHom ℚ)).Separable := by
  have h1 : minpoly ℚ ((θ : K)) = (minpoly ℤ ((θ : K))).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ θ.isIntegral_coe
  rw [NumberField.RingOfIntegers.minpoly_coe] at h1
  rw [show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, ← h1]
  exact Algebra.IsSeparable.isSeparable ℚ ((θ : K))

/-- **A rational prime splits completely in a number field when every prime of the ring of integers
above it is unramified with residue field the prime field.** -/
def SplitsCompletely (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
    Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P = 1 ∧
    (Ideal.span {(p : ℤ)}).inertiaDeg P = 1

open Classical in
/-- **A prime for which the minimal polynomial of a generator has a root modulo `p` splits
completely in a Galois number field.**  Provided `p` does not divide the Kummer–Dedekind exponent,
the primes above `p` correspond to the monic irreducible factors of the minimal polynomial modulo
`p`, matching multiplicities with ramification indices and degrees with residue degrees.  A root
modulo `p` supplies a linear factor, hence a prime of residue degree one; in a Galois extension all
the primes above `p` are conjugate and so share this residue degree.  Squarefreeness of the
reduction makes every multiplicity, hence every ramification index, equal to one. -/
theorem splitsCompletely_of_isRoot [IsGalois ℚ K] {θ : 𝓞 K} {p : ℕ} [Fact p.Prime]
    (hexp : ¬ p ∣ RingOfIntegers.exponent θ)
    (hsq : Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))))
    {a : ZMod p} (ha : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).IsRoot a) :
    SplitsCompletely K p := by
  have hg0 : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  -- `X - C a` is a monic irreducible factor of `minpoly ℤ θ` mod `p`.
  have hmem : (X - C a) ∈ monicFactorsMod θ p := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg0]
    exact ⟨irreducible_X_sub_C a, monic_X_sub_C a, dvd_iff_isRoot.mpr ha⟩
  -- the corresponding prime above `p`, of inertia degree `1`
  set P₀ : Ideal (𝓞 K) :=
    (((primesOverSpanEquivMonicFactorsMod hexp).symm ⟨X - C a, hmem⟩ : _) :
      Ideal (𝓞 K)) with hP₀def
  have hP₀mem : P₀ ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) :=
    ((primesOverSpanEquivMonicFactorsMod hexp).symm ⟨X - C a, hmem⟩).2
  haveI : P₀.IsPrime := hP₀mem.1
  haveI : P₀.LiesOver (Ideal.span {(p : ℤ)}) := hP₀mem.2
  have hdeg₀ : (Ideal.span {(p : ℤ)}).inertiaDeg P₀ = 1 := by
    rw [hP₀def, inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hexp hmem,
      natDegree_X_sub_C]
  intro P hP
  obtain ⟨hP1, hP2⟩ := hP
  haveI : P.IsPrime := hP1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP2
  have h₂ := (primesOverSpanEquivMonicFactorsMod hexp ⟨P, ⟨hP1, hP2⟩⟩).2
  have hram := ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hexp h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at hram
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg0] at h₂
  refine ⟨?_, ?_⟩
  · rw [hram]
    exact multiplicity_eq_one_of_squarefree hsq h₂.1 h₂.2.2
  · rw [Ideal.inertiaDeg_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P P₀ (K ≃ₐ[ℚ] K), hdeg₀]

variable (K)

/-- **Infinitely many rational primes split completely in a number field that is Galois over the
rationals.**  Take a generator of the field which is an algebraic integer; its minimal polynomial
has a root modulo infinitely many primes, and only finitely many primes are excluded either by
dividing the Kummer–Dedekind exponent of the generator or by making the reduction of the minimal
polynomial non-squarefree.  Every remaining prime splits completely. -/
theorem infinite_setOf_prime_splitsCompletely [IsGalois ℚ K] :
    {p : ℕ | p.Prime ∧ SplitsCompletely K p}.Infinite := by
  obtain ⟨θ, hθ⟩ := exists_integral_primitive_element K
  have hdeg : 0 < (minpoly ℤ θ).natDegree := minpoly.natDegree_pos θ.isIntegral
  have hbad1 : {p : ℕ | p ∣ RingOfIntegers.exponent θ}.Finite := by
    refine Set.Finite.subset ((RingOfIntegers.exponent θ).divisors : Finset ℕ).finite_toSet ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simpa [Nat.mem_divisors] using ⟨hp, exponent_ne_zero θ hθ⟩
  have hbad2 : {p : ℕ | p.Prime ∧
      ¬ Squarefree ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))}.Finite :=
    finite_setOf_prime_not_squarefree_map (separable_map_minpoly θ)
  refine (((infinite_setOf_prime_isRoot_map hdeg).diff hbad1).diff hbad2).mono ?_
  intro p hp
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, not_not] at hp
  obtain ⟨⟨⟨hprime, a, ha⟩, hnb1⟩, hnb2⟩ := hp
  haveI := Fact.mk hprime
  exact ⟨hprime, splitsCompletely_of_isRoot hnb1 (hnb2 hprime) ha⟩

end NumberFieldSection

end InverseGalois.NumberTheory
