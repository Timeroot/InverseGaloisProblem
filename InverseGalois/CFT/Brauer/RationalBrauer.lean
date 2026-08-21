import Mathlib
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Brauer.Quaternion

/-!
# The Brauer group of the rationals is infinite

The field `ℚ(i)`, realised as the intermediate field `ℚ⟮Complex.I⟯` of `ℂ`, is a quadratic — hence
cyclic Galois — extension of `ℚ`, so the cyclic-algebra machinery of
`InverseGalois.CFT.Brauer.CyclicNorm` identifies the relative Brauer group `Br(ℚ(i) / ℚ)` with the
quotient of `ℚˣ` by the norms from `ℚ(i)ˣ`.  The norm of `u + v i` is `u ^ 2 + v ^ 2`, so a norm is
a sum of two rational squares, and clearing denominators turns this into a statement about a
natural number: by the classical two-squares theorem the exponent of every prime `q ≡ 3 mod 4` in
that natural number is even.  Consequently every prime `q ≡ 3 mod 4` has even `q`-adic valuation on
the norms.

Two distinct primes `q ≢ q'`, both `≡ 3 mod 4`, therefore give distinct classes in the quotient,
because `q / q'` has `q`-adic valuation `-1`.  Dirichlet's theorem supplies infinitely many such
primes, so `Br(ℚ(i) / ℚ)` is infinite and a fortiori so is `Br(ℚ)`.

## Main results

* `InverseGalois.CFT.forall_mem_zpowers_rat_I`: `Gal(ℚ(i)/ℚ)` is cyclic, with an explicit
  generator.
* `InverseGalois.CFT.exists_eq_add_mul_I`: every element of `ℚ(i)` is `u + v i` with `u v : ℚ`.
* `InverseGalois.CFT.exists_sq_add_sq_of_mem_normSubgroup`: a norm from `ℚ(i)` is a sum of two
  rational squares.
* `InverseGalois.CFT.even_padicValRat_of_mem_normSubgroup`: for a prime `q ≡ 3 mod 4` the `q`-adic
  valuation of a norm from `ℚ(i)` is even.
* `InverseGalois.CFT.mk_ne_mk_of_prime_ne`: distinct primes `≡ 3 mod 4` give distinct classes in
  `ℚˣ / N(ℚ(i)ˣ)`.
* `InverseGalois.CFT.infinite_relative_rat_I` and
  `InverseGalois.CFT.infinite_brauerGroup_rat`: **the main results**, `Br(ℚ(i) / ℚ)` and hence
  `Br(ℚ)` are infinite.

## Tags

Brauer group, rational numbers, sum of two squares, Dirichlet's theorem
-/

open Module Polynomial IntermediateField

namespace InverseGalois.CFT

/-! ### The Galois group of `ℚ(i) / ℚ` -/

/-- **`Gal(ℚ(i)/ℚ)` is cyclic.**  Being a quadratic extension, `ℚ(i) / ℚ` is Galois with cyclic
group, so its Galois group has a generator in the form the cyclic-algebra construction consumes. -/
theorem forall_mem_zpowers_rat_I :
    ∃ σ₀ : Gal(ℚ⟮Complex.I⟯/ℚ), ∀ x : Gal(ℚ⟮Complex.I⟯/ℚ), x ∈ Subgroup.zpowers σ₀ :=
  exists_generator_of_isCyclic

/-! ### Norms from `ℚ(i)` are sums of two squares -/

/-- **Every element of `ℚ(i)` has the shape `u + v i`.**  The powers `1, i` form a basis of
`ℚ(i)` over `ℚ`, so an element of `ℚ(i)` is a rational combination of them. -/
theorem exists_eq_add_mul_I (x : ℚ⟮Complex.I⟯) :
    ∃ u v : ℚ, (x : ℂ) = (u : ℂ) + (v : ℂ) * Complex.I := by
  set pb := IntermediateField.adjoin.powerBasis (K := ℚ) Complex.isIntegral_rat_I
  obtain ⟨f, hdeg, hf⟩ := pb.exists_eq_aeval x
  have hdim : pb.dim = 2 := natDegree_minpoly_rat_I
  have hle : f.natDegree ≤ 1 := by omega
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  have hx : (x : ℂ) = aeval Complex.I f := by
    rw [hf]
    exact (Polynomial.aeval_algHom_apply ℚ⟮Complex.I⟯.val pb.gen f).symm
  rw [hx]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hle]
  simp [Complex.ext_iff]

/-- **A norm from `ℚ(i)` is a sum of two rational squares.**  The norm of `u + v i` is
`u ^ 2 + v ^ 2`. -/
theorem exists_sq_add_sq_of_mem_normSubgroup (a : ℚˣ)
    (ha : a ∈ normSubgroup ℚ ℚ⟮Complex.I⟯) : ∃ u v : ℚ, (a : ℚ) = u ^ 2 + v ^ 2 := by
  rw [mem_normSubgroup_iff] at ha
  obtain ⟨b, hb⟩ := ha
  obtain ⟨u, v, huv⟩ := exists_eq_add_mul_I (b : ℚ⟮Complex.I⟯)
  refine ⟨u, v, ?_⟩
  have h := coe_norm_rat_I (b : ℚ⟮Complex.I⟯)
  rw [hb, huv] at h
  have h2 : Complex.normSq ((u : ℂ) + (v : ℂ) * Complex.I) = u ^ 2 + v ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  rw [h2] at h
  exact_mod_cast h

/-! ### The valuation obstruction at a prime `≡ 3 mod 4` -/

/-- **A norm from `ℚ(i)` has even valuation at every prime `q ≡ 3 mod 4`.**  Clearing the
denominators of a representation as a sum of two rational squares turns the norm into a natural
number which is a sum of two integer squares, and the classical two-squares theorem says that
every prime `≡ 3 mod 4` occurs in such a number to an even power. -/
theorem even_padicValRat_of_mem_normSubgroup {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) (a : ℚˣ)
    (ha : a ∈ normSubgroup ℚ ℚ⟮Complex.I⟯) : Even (padicValRat q (a : ℚ)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨u, v, huv⟩ := exists_sq_add_sq_of_mem_normSubgroup a ha
  have ha0 : (a : ℚ) ≠ 0 := a.ne_zero
  set d : ℕ := u.den * v.den with hd_def
  have hd0 : (d : ℚ) ≠ 0 := by
    simp [hd_def, u.den_nz, v.den_nz]
  set X : ℤ := u.num * v.den with hX
  set Y : ℤ := v.num * u.den with hY
  have hu : u * (d : ℚ) = (X : ℚ) := by
    rw [hd_def, hX]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  have hv : v * (d : ℚ) = (Y : ℚ) := by
    rw [hd_def, hY]
    push_cast
    rw [mul_comm (u.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]
  have hsq : ∀ Z : ℤ, ((Z.natAbs : ℚ)) ^ 2 = (Z : ℚ) ^ 2 := by
    intro Z
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  set n : ℕ := X.natAbs ^ 2 + Y.natAbs ^ 2 with hn_def
  have hn : (n : ℚ) = (a : ℚ) * (d : ℚ) ^ 2 := by
    rw [hn_def]
    push_cast
    rw [hsq X, hsq Y, ← hu, ← hv, huv]
    ring
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    simp only [Nat.cast_zero] at hn
    exact (mul_ne_zero ha0 (pow_ne_zero 2 hd0)) hn.symm
  have heven : Even (padicValNat q n) := by
    by_cases hdvd : q ∣ n
    · exact Nat.eq_sq_add_sq_iff.mp ⟨X.natAbs, Y.natAbs, rfl⟩ q
        (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hn0⟩) hq3
    · simp [padicValNat.eq_zero_of_not_dvd hdvd]
  have hval : padicValRat q (n : ℚ) = padicValRat q (a : ℚ) + 2 * padicValRat q (d : ℚ) := by
    rw [hn, padicValRat.mul ha0 (pow_ne_zero 2 hd0), padicValRat.pow hd0]
    norm_num
  rw [padicValRat.of_nat] at hval
  obtain ⟨k, hk⟩ := heven
  refine ⟨k - padicValRat q (d : ℚ), ?_⟩
  have hkk : ((padicValNat q n : ℤ)) = (k : ℤ) + k := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hk
  omega

/-! ### Distinct classes from distinct primes -/

/-- A prime number, read as a unit of `ℚ`. -/
def unitOfPrime {q : ℕ} (hq : q.Prime) : ℚˣ :=
  Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr hq.ne_zero)

/-- The unit attached to a prime has that prime as its underlying rational number. -/
theorem coe_unitOfPrime {q : ℕ} (hq : q.Prime) : (unitOfPrime hq : ℚ) = (q : ℚ) := rfl

/-- **Distinct primes `≡ 3 mod 4` give distinct classes modulo the norms.**  Their quotient has
`q`-adic valuation `-1`, which is odd, so it is not a norm from `ℚ(i)`. -/
theorem mk_ne_mk_of_prime_ne {q q' : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) (hq' : q'.Prime)
    (hne : q ≠ q') :
    (QuotientGroup.mk (unitOfPrime hq) : ℚˣ ⧸ normSubgroup ℚ ℚ⟮Complex.I⟯) ≠
      QuotientGroup.mk (unitOfPrime hq') := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro h
  have hmem : (unitOfPrime hq)⁻¹ * unitOfPrime hq' ∈ normSubgroup ℚ ℚ⟮Complex.I⟯ :=
    QuotientGroup.eq.mp h
  have heven := even_padicValRat_of_mem_normSubgroup hq hq3 _ hmem
  have hcoe : (((unitOfPrime hq)⁻¹ * unitOfPrime hq' : ℚˣ) : ℚ) = (q : ℚ)⁻¹ * (q' : ℚ) := by
    simp [unitOfPrime]
  rw [hcoe] at heven
  have hq0 : ((q : ℚ))⁻¹ ≠ 0 := by
    simpa using hq.ne_zero
  have hq'0 : ((q' : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero
  have hz : padicValRat q ((q' : ℚ)) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
    · simp
    · exact fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hq hq').mp hdvd)
  rw [padicValRat.mul hq0 hq'0, padicValRat.inv, padicValRat.self hq.one_lt, hz] at heven
  norm_num at heven

/-! ### Infinitude -/

/-- **There are infinitely many primes congruent to `3` modulo `4`.**  This is the case `q = 4`,
`a = 3` of Dirichlet's theorem on primes in arithmetic progressions. -/
theorem infinite_setOf_prime_mod_four_eq_three : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  have hu : IsUnit (3 : ZMod 4) := IsUnit.of_mul_eq_one 3 (by decide)
  refine Set.Infinite.mono ?_ (Nat.infinite_setOf_prime_and_eq_mod hu)
  rintro p ⟨hp, hp4⟩
  refine ⟨hp, ?_⟩
  have h3 : ((p : ℕ) : ZMod 4) = ((3 : ℕ) : ZMod 4) := by
    rw [hp4]
    norm_num
  rw [ZMod.natCast_eq_natCast_iff' p 3 4] at h3
  simpa using h3

/-- **The rational units modulo the norms from `ℚ(i)` form an infinite group.**  The primes
congruent to `3` modulo `4` give pairwise distinct classes, and there are infinitely many of
them. -/
theorem infinite_ratUnitsQuotient : Infinite (ℚˣ ⧸ normSubgroup ℚ ℚ⟮Complex.I⟯) := by
  haveI : Infinite ↥{p : ℕ | p.Prime ∧ p % 4 = 3} :=
    Set.infinite_coe_iff.mpr infinite_setOf_prime_mod_four_eq_three
  refine Infinite.of_injective
    (fun p : ↥{p : ℕ | p.Prime ∧ p % 4 = 3} =>
      (QuotientGroup.mk (unitOfPrime p.2.1) : ℚˣ ⧸ normSubgroup ℚ ℚ⟮Complex.I⟯)) ?_
  rintro ⟨p, hp, hp4⟩ ⟨p', hp', hp'4⟩ h
  by_contra hne
  exact mk_ne_mk_of_prime_ne hp hp4 hp' (fun hh => hne (Subtype.ext hh)) h

/-- **The relative Brauer group of `ℚ(i) / ℚ` is infinite.**  It is the quotient of `ℚˣ` by the
norms from `ℚ(i)ˣ`, which has infinitely many classes. -/
theorem infinite_relative_rat_I : Infinite ↥(BrauerGroup.relative ℚ ℚ⟮Complex.I⟯) := by
  obtain ⟨σ₀, hσ₀⟩ := forall_mem_zpowers_rat_I
  haveI := infinite_ratUnitsQuotient
  exact Infinite.of_injective (cyclicBrauerEquiv hσ₀) (cyclicBrauerEquiv hσ₀).injective

/-- **The Brauer group of the rationals is infinite.**  Already the classes split by `ℚ(i)` form
an infinite subgroup. -/
instance infinite_brauerGroup_rat : Infinite (BrauerGroup.{0, 0} ℚ) := by
  haveI := infinite_relative_rat_I
  exact Infinite.of_injective (Subtype.val : ↥(BrauerGroup.relative ℚ ℚ⟮Complex.I⟯) → _)
    Subtype.val_injective

end InverseGalois.CFT
