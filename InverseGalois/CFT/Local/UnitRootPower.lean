/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.PowClose
import InverseGalois.CFT.Local.UnitPowIndex

/-!
# Powers and roots of unity of order prime to the residue characteristic

In a complete valued field of residue characteristic `p` the units congruent to one form a pro-`p`
group: raising such a unit to the `p`-th power moves it one step up the filtration, because the
binomial coefficients strictly between the ends are divisible by `p` and the last term is a `p`-th
power.  Two consequences follow at once.  A unit congruent to one whose order is prime to `p` lies
in every step of the filtration and is therefore trivial, and a unit congruent to one is a power
with any exponent prime to `p`, since a high enough `p`-th power of it is such a power and the two
exponents are coprime.

The second consequence turns a congruence into an equation: a unit which is congruent modulo the
maximal ideal to an `n`-th power, with `n` prime to `p`, is an `n`-th power.  The first shows that
such roots are rigid when the residue field is the prime field: every element of the valuation ring
is then congruent to a rational integer, so an automorphism preserving the valuation moves a root
of unity of order prime to `p` by a unit congruent to one, which must be trivial.

## Main results

* `InverseGalois.CFT.pow_residueChar_mem_unitFiltration_succ`: raising to the residue characteristic
  moves a unit one step up the filtration.
* `InverseGalois.CFT.eq_one_of_pow_eq_one_of_mem_unitFiltration`: **a unit congruent to one whose
  order is prime to the residue characteristic is trivial.**
* `InverseGalois.CFT.exists_pow_eq_of_valued_sub_lt_one`: **a unit congruent to an `n`-th power is
  an `n`-th power**, for `n` prime to the residue characteristic.
* `InverseGalois.CFT.map_eq_self_of_pow_eq_one_of_primeResidue`: **over a prime residue field a
  root of unity of order prime to the residue characteristic is fixed by every valuation
  preserving automorphism.**
* `InverseGalois.CFT.exists_pow_eq_and_map_eq_self`: the two together, in the form the local
  condition of the Albert-Brauer-Hasse-Noether theorem asks for.

## Tags

valued field, unit filtration, root of unity, residue characteristic, prime residue field
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {p e : ℕ}

/-! ### The units congruent to one form a pro-`p` group -/

/-- **Raising to the residue characteristic moves a unit one step up the filtration.**  The
binomial coefficients away from the ends are divisible by the residue characteristic, and the last
term of the expansion is the power of an element of small valuation. -/
theorem pow_residueChar_mem_unitFiltration_succ (h : HasResidueChar A p e) {i : ℕ} {u : Aˣ}
    (hu : u ∈ unitFiltration A i) : u ^ p ∈ unitFiltration A (i + 1) := by
  have hp := h.prime
  have hp2 : 2 ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have he1 : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast h.pos
  set z : A := (u : A) - 1 with hzdef
  have hzv : Valued.v z ≤ WithZero.exp (-((i : ℤ) + 1)) := mem_unitFiltration.mp hu
  have hz1 : Valued.v z ≤ 1 :=
    hzv.trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega))
  have hu1 : (u : A) = z + 1 := by rw [hzdef]; ring
  -- expand the `p`-th power and remove the constant term
  have hexp : (u : A) ^ p - 1 = ∑ k ∈ Finset.range p, z ^ (k + 1) * (p.choose (k + 1) : A) := by
    have h1 : (u : A) ^ p = (∑ k ∈ Finset.range p, z ^ (k + 1) * (p.choose (k + 1) : A)) + 1 := by
      rw [hu1, add_pow,
        Finset.sum_range_succ' (fun k => z ^ k * (1 : A) ^ (p - k) * (p.choose k : A)) p]
      simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
    rw [h1]
    ring
  -- every term of the expansion is small
  have hbound : ∀ k ∈ Finset.range p, Valued.v (z ^ (k + 1) * (p.choose (k + 1) : A))
      ≤ WithZero.exp (-((i : ℤ) + 2)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [map_mul, map_pow]
    have hk' : k + 1 ≤ p := hk
    rcases eq_or_lt_of_le hk' with heq | hlt
    · -- the last term is a `p`-th power
      rw [heq, Nat.choose_self, Nat.cast_one, map_one, mul_one]
      calc Valued.v z ^ p ≤ WithZero.exp (-((i : ℤ) + 1)) ^ p := pow_le_pow_left' hzv p
        _ = WithZero.exp (-((i : ℤ) + 1) * p) := by
            rw [← WithZero.exp_nsmul, nsmul_eq_mul]
            congr 1
            ring
        _ ≤ WithZero.exp (-((i : ℤ) + 2)) := WithZero.exp_le_exp.mpr (by nlinarith)
    · -- the inner binomial coefficients are divisible by the residue characteristic
      obtain ⟨m, hm⟩ := hp.dvd_choose_self (Nat.succ_ne_zero k) hlt
      have hcast : ((p.choose (k + 1) : ℕ) : A) = (p : A) * (m : A) := by
        rw [hm]
        push_cast
        ring
      have hchoose : Valued.v ((p.choose (k + 1) : ℕ) : A) ≤ WithZero.exp (-(1 : ℤ)) := by
        rw [hcast, map_mul, h.val_p]
        calc WithZero.exp (-(e : ℤ)) * Valued.v (m : A)
            ≤ WithZero.exp (-(e : ℤ)) * 1 := mul_le_mul' le_rfl (valued_natCast_le_one m)
          _ = WithZero.exp (-(e : ℤ)) := mul_one _
          _ ≤ WithZero.exp (-(1 : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
      have hpowz : Valued.v z ^ (k + 1) ≤ WithZero.exp (-((i : ℤ) + 1)) := by
        calc Valued.v z ^ (k + 1) = Valued.v z * Valued.v z ^ k := pow_succ' _ _
          _ ≤ WithZero.exp (-((i : ℤ) + 1)) * 1 := mul_le_mul' hzv (pow_le_one' hz1 k)
          _ = WithZero.exp (-((i : ℤ) + 1)) := mul_one _
      calc Valued.v z ^ (k + 1) * Valued.v ((p.choose (k + 1) : ℕ) : A)
          ≤ WithZero.exp (-((i : ℤ) + 1)) * WithZero.exp (-(1 : ℤ)) :=
            mul_le_mul' hpowz hchoose
        _ = WithZero.exp (-((i : ℤ) + 2)) := by
            rw [← WithZero.exp_add,
              show -((i : ℤ) + 1) + -(1 : ℤ) = -((i : ℤ) + 2) by ring]
  rw [mem_unitFiltration, Units.val_pow_eq_pow_val, hexp]
  refine (Valuation.map_sum_le _ hbound).trans (WithZero.exp_le_exp.mpr ?_)
  push_cast
  omega

/-- A unit congruent to one lands in an arbitrarily deep step of the filtration after enough
raisings to the residue characteristic. -/
theorem pow_pow_residueChar_mem_unitFiltration (h : HasResidueChar A p e) {u : Aˣ}
    (hu : u ∈ unitFiltration A 0) (j : ℕ) : u ^ p ^ j ∈ unitFiltration A j := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    have hstep := pow_residueChar_mem_unitFiltration_succ h ih
    rwa [← pow_mul, ← pow_succ] at hstep

/-- **A unit congruent to one whose order is prime to the residue characteristic is trivial.**
Such a unit is a power of an arbitrarily deep step of the filtration, because its order and the
powers of the residue characteristic are coprime. -/
theorem eq_one_of_pow_eq_one_of_mem_unitFiltration (h : HasResidueChar A p e) {u : Aˣ}
    (hu : u ∈ unitFiltration A 0) {m : ℕ} (hpm : ¬ p ∣ m) (hum : u ^ m = 1) : u = 1 := by
  have hp := h.prime
  -- the unit lies in every step of the filtration
  have hall : ∀ j : ℕ, u ∈ unitFiltration A j := by
    intro j
    have hcop : Nat.Coprime m (p ^ j) :=
      (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm).pow_right j
    have hbez : (m : ℤ) * Nat.gcdA m (p ^ j) + ((p : ℤ) ^ j) * Nat.gcdB m (p ^ j) = 1 := by
      have hg := Nat.gcd_eq_gcd_ab m (p ^ j)
      rw [Nat.Coprime.gcd_eq_one hcop] at hg
      push_cast at hg ⊢
      omega
    have hupow : u ^ ((p : ℕ) ^ j) ∈ unitFiltration A j :=
      pow_pow_residueChar_mem_unitFiltration h hu j
    have hzpow : (u ^ ((p : ℕ) ^ j)) ^ Nat.gcdB m (p ^ j) ∈ unitFiltration A j :=
      Subgroup.zpow_mem _ hupow _
    have hrewrite : (u ^ ((p : ℕ) ^ j)) ^ Nat.gcdB m (p ^ j) = u := by
      have hone : (u ^ m) ^ Nat.gcdA m (p ^ j) = 1 := by rw [hum, one_zpow]
      calc (u ^ ((p : ℕ) ^ j)) ^ Nat.gcdB m (p ^ j)
          = (u ^ m) ^ Nat.gcdA m (p ^ j) * (u ^ ((p : ℕ) ^ j)) ^ Nat.gcdB m (p ^ j) := by
            rw [hone, one_mul]
        _ = u ^ ((m : ℤ) * Nat.gcdA m (p ^ j) + ((p : ℤ) ^ j) * Nat.gcdB m (p ^ j)) := by
            rw [zpow_add, ← zpow_natCast u m, ← zpow_natCast u (p ^ j), ← zpow_mul, ← zpow_mul]
            push_cast
            ring_nf
        _ = u := by rw [hbez, zpow_one]
    rwa [hrewrite] at hzpow
  -- an element of every step of the filtration is trivial
  refine Units.ext ?_
  have hzero : Valued.v ((u : A) - 1) = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v ((u : A) - 1) = WithZero.exp c :=
      ⟨WithZero.log _, (WithZero.exp_log hne).symm⟩
    have hle := mem_unitFiltration.mp (hall (-c).toNat)
    rw [hc] at hle
    have hc' := WithZero.exp_le_exp.mp hle
    omega
  have hsub : (u : A) - 1 = 0 := (Valuation.zero_iff Valued.v).mp hzero
  rw [Units.val_one, ← sub_eq_zero]
  exact hsub

/-! ### Powers with exponent prime to the residue characteristic -/

variable [CompleteSpace A]

/-- **A unit congruent to one is a power with any exponent prime to the residue
characteristic.**  A high enough power with exponent a power of the residue characteristic is such
a power, and the two exponents are coprime. -/
theorem exists_pow_eq_of_mem_unitFiltration_zero (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0)
    (hpn : ¬ p ∣ n) {c : Aˣ} (hc : c ∈ unitFiltration A 0) : ∃ y : Aˣ, y ^ n = c := by
  have hp := h.prime
  have hvn : Valued.v ((n : ℕ) : A) = WithZero.exp (-((0 : ℕ) : ℤ)) := by
    rw [h.valued_natCast hn, padicValNat.eq_zero_of_not_dvd hpn]
    norm_num
  have hmem : c ^ p ^ e ∈ unitFiltration A (e + 0) := by
    simpa using pow_pow_residueChar_mem_unitFiltration h hc e
  obtain ⟨z, hz⟩ := unitFiltration_le_range_powMonoidHom h hn hvn hmem
  have hzn : z ^ n = c ^ p ^ e := by simpa [powMonoidHom] using hz
  -- the exponents are coprime
  have hcop : Nat.Coprime n (p ^ e) :=
    (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm).pow_right e
  have hbez : (n : ℤ) * Nat.gcdA n (p ^ e) + ((p : ℤ) ^ e) * Nat.gcdB n (p ^ e) = 1 := by
    have hg := Nat.gcd_eq_gcd_ab n (p ^ e)
    rw [Nat.Coprime.gcd_eq_one hcop] at hg
    push_cast at hg ⊢
    omega
  refine ⟨c ^ Nat.gcdA n (p ^ e) * z ^ Nat.gcdB n (p ^ e), ?_⟩
  have hstep : (c ^ Nat.gcdA n (p ^ e) * z ^ Nat.gcdB n (p ^ e)) ^ n
      = c ^ ((n : ℤ) * Nat.gcdA n (p ^ e)) * (z ^ n) ^ Nat.gcdB n (p ^ e) := by
    rw [mul_pow, ← zpow_natCast (c ^ Nat.gcdA n (p ^ e)) n, ← zpow_mul,
      ← zpow_natCast (z ^ Nat.gcdB n (p ^ e)) n, ← zpow_mul, ← zpow_natCast z n, ← zpow_mul]
    ring_nf
  rw [hstep, hzn, ← zpow_natCast c (p ^ e), ← zpow_mul, ← zpow_add]
  push_cast
  rw [hbez, zpow_one]

/-- **A unit congruent to an `n`-th power is an `n`-th power**, for an exponent prime to the
residue characteristic. -/
theorem exists_pow_eq_of_valued_sub_lt_one (h : HasResidueChar A p e) {n : ℕ} (hn : n ≠ 0)
    (hpn : ¬ p ∣ n) {ζ b : Aˣ} (hζ : Valued.v (ζ : A) = 1)
    (hb : Valued.v ((ζ : A) - (b : A) ^ n) < 1) : ∃ y : Aˣ, y ^ n = ζ := by
  have hbn : Valued.v ((b : A) ^ n) = 1 := by
    have hsum : (b : A) ^ n = (ζ : A) + -((ζ : A) - (b : A) ^ n) := by ring
    rw [hsum, Valuation.map_add_eq_of_lt_left, hζ]
    rwa [Valuation.map_neg, hζ]
  set c : Aˣ := ζ * (b ^ n)⁻¹ with hcdef
  have hbne : ((b : A)) ^ n ≠ 0 := pow_ne_zero n b.ne_zero
  have hcval : (c : A) - 1 = ((ζ : A) - (b : A) ^ n) * ((b : A) ^ n)⁻¹ := by
    simp only [hcdef, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp
  have hcmem : c ∈ unitFiltration A 0 := by
    rw [mem_unitFiltration, hcval, map_mul, map_inv₀, hbn, inv_one, mul_one]
    simpa using le_exp_neg_one_of_lt_one hb
  obtain ⟨y, hy⟩ := exists_pow_eq_of_mem_unitFiltration_zero h hn hpn hcmem
  refine ⟨y * b, ?_⟩
  rw [mul_pow, hy, hcdef, inv_mul_cancel_right]

/-! ### Rigidity over a prime residue field -/

omit [CompleteSpace A] in
/-- **Over a prime residue field a root of unity of order prime to the residue characteristic is
fixed by every valuation preserving automorphism.**  Such a root of unity is congruent to a
rational integer, which the automorphism fixes, so the automorphism moves it by a unit congruent
to one whose order is prime to the residue characteristic. -/
theorem map_eq_self_of_pow_eq_one_of_primeResidue (h : HasResidueChar A p e)
    (hres : ∀ x : A, Valued.v x ≤ 1 → ∃ b : ℤ, Valued.v (x - (b : A)) < 1) {σ : A ≃+* A}
    (hσ : ∀ x : A, Valued.v (σ x) = Valued.v x) {w : Aˣ} {m : ℕ} (hpm : ¬ p ∣ m)
    (hw : w ^ m = 1) : σ (w : A) = (w : A) := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hpm (dvd_zero p)
  have hwval : Valued.v (w : A) = 1 := valued_eq_one_of_pow_eq_one hm hw
  obtain ⟨b, hbv⟩ := hres (w : A) (le_of_eq hwval)
  -- the automorphism moves the unit by little
  have hshift : Valued.v (σ (w : A) - (w : A)) < 1 := by
    have h2 : Valued.v (σ (w : A) - (b : A)) < 1 := by
      rw [show σ (w : A) - (b : A) = σ ((w : A) - (b : A)) by rw [map_sub, map_intCast], hσ]
      exact hbv
    have h3 : σ (w : A) - (w : A) = (σ (w : A) - (b : A)) + -((w : A) - (b : A)) := by ring
    rw [h3]
    refine lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h2 ?_)
    rwa [Valuation.map_neg]
  have hσne : σ (w : A) ≠ 0 := fun hz => w.ne_zero (σ.injective (by rw [hz, map_zero]))
  set W : Aˣ := Units.mk0 (σ (w : A)) hσne with hWdef
  set u : Aˣ := W * w⁻¹ with hudef
  have hwne : (w : A) ≠ 0 := w.ne_zero
  have humem : u ∈ unitFiltration A 0 := by
    have hval : (u : A) - 1 = (σ (w : A) - (w : A)) * ((w : A))⁻¹ := by
      simp only [hudef, hWdef, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
      field_simp
    rw [mem_unitFiltration, hval, map_mul, map_inv₀, hwval, inv_one, mul_one]
    simpa using le_exp_neg_one_of_lt_one hshift
  have hWm : W ^ m = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hWdef, Units.val_mk0, ← map_pow,
      ← Units.val_pow_eq_pow_val, hw, Units.val_one, map_one]
  have hupow : u ^ m = 1 := by
    rw [hudef, mul_pow, hWm, inv_pow, hw, inv_one, mul_one]
  have hu1 := eq_one_of_pow_eq_one_of_mem_unitFiltration h humem hpm hupow
  have hWw : W = w := by
    rw [hudef] at hu1
    exact mul_inv_eq_one.mp hu1
  have hval := congrArg (fun t : Aˣ => (t : A)) hWw
  simpa [hWdef] using hval

/-- **A root of unity is a power with exponent prime to the residue characteristic, by a root
which every valuation preserving automorphism fixes**, as soon as it is congruent to such a power
and the residue field is the prime field. -/
theorem exists_pow_eq_and_map_eq_self (h : HasResidueChar A p e)
    (hres : ∀ x : A, Valued.v x ≤ 1 → ∃ b : ℤ, Valued.v (x - (b : A)) < 1) {n M : ℕ} (hn : n ≠ 0)
    (hpn : ¬ p ∣ n) (hpM : ¬ p ∣ M) {ζ b : Aˣ} (hζ : ζ ^ M = 1)
    (hb : Valued.v ((ζ : A) - (b : A) ^ n) < 1) :
    ∃ y : Aˣ, y ^ n = ζ ∧ ∀ σ : A ≃+* A, (∀ x : A, Valued.v (σ x) = Valued.v x) →
      σ (y : A) = (y : A) := by
  have hp := h.prime
  have hM : M ≠ 0 := by
    rintro rfl
    exact hpM (dvd_zero p)
  have hζval : Valued.v (ζ : A) = 1 := valued_eq_one_of_pow_eq_one hM hζ
  obtain ⟨y, hy⟩ := exists_pow_eq_of_valued_sub_lt_one h hn hpn hζval hb
  refine ⟨y, hy, fun σ hσ => ?_⟩
  refine map_eq_self_of_pow_eq_one_of_primeResidue h hres hσ (m := n * M) ?_ ?_
  · exact fun hdvd => (hp.dvd_mul.mp hdvd).elim hpn hpM
  · rw [pow_mul, hy, hζ]

end InverseGalois.CFT
