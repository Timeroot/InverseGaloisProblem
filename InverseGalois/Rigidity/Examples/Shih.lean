/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.FixedField
import InverseGalois.Rigidity.RET.MobiusAut

/-!
# Shih's theorem: `PSL₂(𝔽ₚ)` as a regular Galois group over `ℚ(T)`

The rigidity method reaches a finite group only when that group carries a rationally rigid tuple
of conjugacy classes, and `PSL₂(𝔽ₚ)` never does.  Shih's construction reaches it by a different
road, through the arithmetic of modular curves.

## The construction

Fix a prime `p ≥ 5` and an auxiliary level `N ∈ {2, 3, 7}`.

* The modular curve `X(p)` of full level `p` is a Galois cover of the `j`-line `X(1)`, defined
  over `ℚ`, with Galois group `GL₂(𝔽ₚ)/{±1}`.  Its field of constants is the cyclotomic field
  `ℚ(ζₚ)`, and the restriction of an automorphism to the constants is read off from the
  determinant.  So the *geometric* Galois group — the kernel of the determinant — is already
  `PSL₂(𝔽ₚ)`, but the cover is very far from regular: it acquires all of `ℚ(ζₚ)`.
* Pulling back along `X₀(N) → X(1)` changes nothing about the group or the constants, but it
  supplies an extra symmetry: the Atkin–Lehner involution `w_N` of `X₀(N)`.  For
  `N ∈ {2, 3, 7}` the curve `X₀(N)` has genus zero with a rational point, so its function field
  is a rational function field `ℚ(t)`, and so is the quotient `ℚ(t)^{w_N}`.
* On moduli, `w_N` sends a pair `(E, C)` to `(E/C, E[N]/C)`, and this multiplies the Weil pairing
  on the `p`-torsion by `N`.  A lift `ω` of `w_N` to the level-`p` tower therefore acts on the
  `p`-th roots of unity by `ζ ↦ ζ^N`.
* When `N` is a quadratic non-residue modulo `p`, the multiplier `N` is not a determinant of an
  element of the geometric group, and the extension of `PSL₂(𝔽ₚ)` by `⟨ω⟩` splits off the
  constants: the quotient tower over the Atkin–Lehner line `ℚ(t)^{w_N} = ℚ(s)` is a **regular**
  `PSL₂(𝔽ₚ)`-extension.

Since `X₀(N)/w_N` is a rational curve, this is a regular realization over `ℚ(T)`.

## Which primes are covered

Shih's hypothesis is that one of `2`, `3`, `7` is a quadratic non-residue modulo `p`.  By
quadratic reciprocity this depends only on `p mod 168`, and it fails exactly on the six residue
classes `1, 25, 47, 121, 143, 167` — a set of density `1/8` among the primes
(`Rigidity.Shih.shihPrime_iff`).  The smallest prime it misses is `47`.

## Organisation of this file

* `Rigidity.Shih.ShihPrime` and the quadratic-residue calculus around it — the elementary number
  theory, worked out completely.
* `Rigidity.Shih.atkinLehner` and `Rigidity.Shih.exists_ringEquiv_atkinLehnerFixedField` — the
  Atkin–Lehner involution of a rational curve and the rationality of its quotient.
* `Rigidity.Shih.LevelTower` — the modular tower of level `p` over a base curve, packaged as the
  two facts the descent consumes: the Galois group has the determinant as its character on
  constants, and the kernel of the determinant is `PSL₂(𝔽ₚ)`.
* `Rigidity.Shih.AtkinLehner` — a lift of the Atkin–Lehner involution to that tower, together
  with its multiplier on `p`-th roots of unity.
* `Rigidity.Shih.levelTower_atkinLehner_exists` — the modular input: such a tower and such a lift
  exist over `ℚ(X₀(N))` for `N ∈ {2, 3, 7}`.
* `Rigidity.Shih.isRegularInverseGalois_of_atkinLehner` — the twist: a lift with non-residue
  multiplier turns the tower into a regular `PSL₂(𝔽ₚ)`-extension.
* `Rigidity.Shih.shih` — the theorem.

## References

* K.-y. Shih, *On the construction of Galois extensions of function fields and number fields*,
  Math. Ann. 207 (1974), 99–120.
* G. Malle and B. H. Matzat, *Inverse Galois Theory*, Ch. I §9.
* J.-P. Serre, *Topics in Galois Theory*, Ch. 5.
-/

open scoped MatrixGroups

namespace Rigidity.Shih

/-! ## Shih primes -/

/-- **Shih's hypothesis on a prime.**  One of `2`, `3`, `7` is a quadratic non-residue modulo
`p`.  This is exactly the condition under which the Atkin–Lehner twist of the level-`p` modular
tower is defined over `ℚ`. -/
def ShihPrime (p : ℕ) : Prop :=
  ¬ IsSquare (2 : ZMod p) ∨ ¬ IsSquare (3 : ZMod p) ∨ ¬ IsSquare (7 : ZMod p)

/-- Squareness of a natural number modulo `q` only depends on its residue. -/
lemma isSquare_natCast_mod (q n : ℕ) [NeZero q] :
    IsSquare ((n : ZMod q)) ↔ IsSquare (((n % q : ℕ) : ZMod q)) := by
  rw [ZMod.natCast_mod]

lemma not_isSquare_two_zmod_three : ¬ IsSquare (2 : ZMod 3) := by decide

lemma not_isSquare_three_zmod_seven : ¬ IsSquare (3 : ZMod 7) := by decide

variable {p : ℕ} [Fact p.Prime]

/-- A prime is divisible by no other prime. -/
lemma not_dvd_of_ne {q : ℕ} (hq : q.Prime) (h : p ≠ q) : ¬ q ∣ p :=
  fun hd => h (((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd).symm)

/-- An odd prime is congruent to `1` or `3` modulo `4`. -/
lemma mod_four (hp2 : p ≠ 2) : p % 4 = 1 ∨ p % 4 = 3 := by
  have h := not_dvd_of_ne (p := p) Nat.prime_two hp2
  rw [Nat.dvd_iff_mod_eq_zero] at h
  omega

/-- `p` is a square modulo `3` exactly when `p % 3 = 1`. -/
lemma isSquare_mod_three (hp3 : p ≠ 3) : IsSquare ((p : ℕ) : ZMod 3) ↔ p % 3 = 1 := by
  have h := not_dvd_of_ne (p := p) (by norm_num) hp3
  rw [Nat.dvd_iff_mod_eq_zero] at h
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rw [isSquare_natCast_mod]
  rcases h3 with h3 | h3 <;> rw [h3]
  · simp
  · decide

/-- `p` is a square modulo `7` exactly when `p % 7` is `1`, `2` or `4`. -/
lemma isSquare_mod_seven (hp7 : p ≠ 7) :
    IsSquare ((p : ℕ) : ZMod 7) ↔ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have h := not_dvd_of_ne (p := p) (by norm_num) hp7
  rw [Nat.dvd_iff_mod_eq_zero] at h
  have h7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨ p % 7 = 6 := by omega
  rw [isSquare_natCast_mod]
  rcases h7 with h7 | h7 | h7 | h7 | h7 | h7 <;> rw [h7] <;> simp <;> decide

/-- **Quadratic reciprocity for an auxiliary prime `q ≡ 3 (mod 4)`.**  Whether `q` is a square
modulo `p` is decided by `p mod 4` together with the residue of `p` modulo `q`. -/
lemma isSquare_of_mod_four_eq_three (q : ℕ) [Fact q.Prime] (hq3 : q % 4 = 3)
    (hp2 : p ≠ 2) (hpq : p ≠ q) :
    IsSquare ((q : ℕ) : ZMod p) ↔
      (p % 4 = 1 ∧ IsSquare ((p : ℕ) : ZMod q)) ∨ (p % 4 = 3 ∧ ¬ IsSquare ((p : ℕ) : ZMod q)) := by
  have hq2 : q ≠ 2 := by omega
  rcases mod_four (p := p) hp2 with h4 | h4
  · rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h4 hq2]
    simp [h4]
  · rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 hq3 hpq]
    simp [h4]

/-- `2` is a square modulo `p` exactly when `p % 8` is `1` or `7`. -/
theorem isSquare_two_iff (hp2 : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  ZMod.exists_sq_eq_two_iff hp2

/-- `3` is a square modulo `p` exactly when `p % 12` is `1` or `11`. -/
theorem isSquare_three_iff (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    IsSquare (3 : ZMod p) ↔ p % 12 = 1 ∨ p % 12 = 11 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcast : ((3 : ℕ) : ZMod p) = (3 : ZMod p) := by push_cast; ring
  rw [← hcast, isSquare_of_mod_four_eq_three 3 (by norm_num) hp2 hp3,
    isSquare_mod_three (p := p) hp3]
  have e4 : p % 12 % 4 = p % 4 := Nat.mod_mod_of_dvd p (by norm_num)
  have e3 : p % 12 % 3 = p % 3 := Nat.mod_mod_of_dvd p (by norm_num)
  have hne3 : p % 3 ≠ 0 := by
    have h := not_dvd_of_ne (p := p) (by norm_num : Nat.Prime 3) hp3
    rwa [Nat.dvd_iff_mod_eq_zero] at h
  have hne2 : p % 2 ≠ 0 := by
    have h := not_dvd_of_ne (p := p) Nat.prime_two hp2
    rwa [Nat.dvd_iff_mod_eq_zero] at h
  have hlt : p % 12 < 12 := Nat.mod_lt _ (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r, p % 12 = r := ⟨_, rfl⟩
  rw [hr] at e4 e3 hlt ⊢
  interval_cases r <;> omega

/-- `7` is a square modulo `p` exactly when `p % 28` is `1`, `3`, `9`, `19`, `25` or `27`. -/
theorem isSquare_seven_iff (hp2 : p ≠ 2) (hp7 : p ≠ 7) :
    IsSquare (7 : ZMod p) ↔
      p % 28 = 1 ∨ p % 28 = 3 ∨ p % 28 = 9 ∨ p % 28 = 19 ∨ p % 28 = 25 ∨ p % 28 = 27 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcast : ((7 : ℕ) : ZMod p) = (7 : ZMod p) := by push_cast; ring
  rw [← hcast, isSquare_of_mod_four_eq_three 7 (by norm_num) hp2 hp7,
    isSquare_mod_seven (p := p) hp7]
  have e4 : p % 28 % 4 = p % 4 := Nat.mod_mod_of_dvd p (by norm_num)
  have e7 : p % 28 % 7 = p % 7 := Nat.mod_mod_of_dvd p (by norm_num)
  have hne7 : p % 7 ≠ 0 := by
    have h := not_dvd_of_ne (p := p) (by norm_num : Nat.Prime 7) hp7
    rwa [Nat.dvd_iff_mod_eq_zero] at h
  have hne2 : p % 2 ≠ 0 := by
    have h := not_dvd_of_ne (p := p) Nat.prime_two hp2
    rwa [Nat.dvd_iff_mod_eq_zero] at h
  have hlt : p % 28 < 28 := Nat.mod_lt _ (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r, p % 28 = r := ⟨_, rfl⟩
  rw [hr] at e4 e7 hlt ⊢
  interval_cases r <;> omega

/-- **The primes Shih's construction applies to.**

For an odd prime `p`, one of `2`, `3`, `7` fails to be a quadratic residue modulo `p` unless `p`
is congruent modulo `168` to one of `1`, `25`, `47`, `121`, `143`, `167`.  Those six classes are
six of the forty-eight units modulo `168`, so the construction covers a set of primes of Dirichlet
density `7/8`. -/
theorem shihPrime_iff (hp2 : p ≠ 2) :
    ShihPrime p ↔ ¬ (p % 168 = 1 ∨ p % 168 = 25 ∨ p % 168 = 47 ∨ p % 168 = 121 ∨
      p % 168 = 143 ∨ p % 168 = 167) := by
  rcases eq_or_ne p 3 with rfl | hp3
  · exact iff_of_true (Or.inl not_isSquare_two_zmod_three) (by decide)
  rcases eq_or_ne p 7 with rfl | hp7
  · exact iff_of_true (Or.inr (Or.inl not_isSquare_three_zmod_seven)) (by decide)
  rw [ShihPrime, isSquare_two_iff hp2, isSquare_three_iff hp2 hp3, isSquare_seven_iff hp2 hp7]
  have e8 : p % 168 % 8 = p % 8 := Nat.mod_mod_of_dvd p (by norm_num)
  have e12 : p % 168 % 12 = p % 12 := Nat.mod_mod_of_dvd p (by norm_num)
  have e28 : p % 168 % 28 = p % 28 := Nat.mod_mod_of_dvd p (by norm_num)
  omega

/-- **The auxiliary level.**  A Shih prime admits a level `N ∈ {2, 3, 7}` that is a quadratic
non-residue modulo `p`; this `N` is the one whose Atkin–Lehner involution carries the twist. -/
theorem exists_level (h : ShihPrime p) :
    ∃ N : ℕ, (N = 2 ∨ N = 3 ∨ N = 7) ∧ ¬ IsSquare ((N : ℕ) : ZMod p) := by
  rcases h with h | h | h
  · exact ⟨2, Or.inl rfl, by push_cast; exact h⟩
  · exact ⟨3, Or.inr (Or.inl rfl), by push_cast; exact h⟩
  · exact ⟨7, Or.inr (Or.inr rfl), by push_cast; exact h⟩

/-! ## The Atkin–Lehner line

For `N ∈ {2, 3, 7}` the modular curve `X₀(N)` has genus zero and a rational cusp, so its function
field is `ℚ(t)`; in the standard hauptmodul the Atkin–Lehner involution is the fractional linear
substitution `t ↦ c/t` for an explicit constant `c` (for instance `c = 2¹²`, `3⁶`, `7⁴` for the
hauptmoduln with `j = (t+256)³/t²`, `(t+27)(t+243)³/t³`, `(t²+13t+49)(t²+245t+2401)³/t⁷`).  Its
quotient curve is again rational, which is what makes the twisted tower a realization over
`ℚ(T)`. -/

/-- The matrix of the Atkin–Lehner substitution is invertible. -/
theorem atkinLehner_det {c : ℚ} (hc : c ≠ 0) : (0 : ℚ) * 0 - c * 1 ≠ 0 := by simpa using hc

/-- **The Atkin–Lehner involution `t ↦ c/t`** of the rational function field, as a ring
automorphism. -/
noncomputable def atkinLehner {c : ℚ} (hc : c ≠ 0) : RingAut (RatFunc ℚ) :=
  Rigidity.RET.mobiusRingAut (atkinLehner_det hc)

/-- The Atkin–Lehner substitution is an involution: its matrix squares to a scalar. -/
theorem atkinLehner_mul_self {c : ℚ} (hc : c ≠ 0) : atkinLehner hc * atkinLehner hc = 1 := by
  have hdet : (1 : ℚ) * 1 - 0 * 0 ≠ 0 := by norm_num
  rw [atkinLehner, Rigidity.RET.mobiusRingAut_mul_eq (atkinLehner_det hc) (atkinLehner_det hc)
      hdet hc (by ring) (by ring) (by ring) (by ring),
    Rigidity.RET.mobiusRingAut_scalar one_ne_zero hdet]

/-- The Atkin–Lehner substitution has order two. -/
theorem atkinLehner_sq {c : ℚ} (hc : c ≠ 0) : atkinLehner hc ^ 2 = 1 := by
  rw [pow_two, atkinLehner_mul_self]

/-- The group generated by the Atkin–Lehner involution. -/
noncomputable abbrev atkinLehnerGroup {c : ℚ} (hc : c ≠ 0) : Subgroup (RingAut (RatFunc ℚ)) :=
  Subgroup.zpowers (atkinLehner hc)

instance atkinLehnerGroup_finite {c : ℚ} (hc : c ≠ 0) : Finite ↥(atkinLehnerGroup hc) := by
  have hfin : IsOfFinOrder (atkinLehner hc) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, atkinLehner_sq hc⟩
  exact Set.Finite.to_subtype hfin.finite_zpowers

/-- **The Atkin–Lehner quotient of a rational curve is rational.**

The fixed field of `t ↦ c/t` inside `ℚ(t)` consists of the rational functions the substitution
leaves alone, and is itself a field of rational functions in one variable — the function field of
the quotient curve `X₀(N)/w_N`. -/
theorem exists_ringEquiv_atkinLehnerFixedField {c : ℚ} (hc : c ≠ 0) :
    ∃ F : Subfield (RatFunc ℚ),
      (∀ x : RatFunc ℚ, x ∈ F ↔ atkinLehner hc x = x) ∧ Nonempty (RatFunc ℚ ≃+* ↥F) := by
  letI : MulSemiringAction ↥(atkinLehnerGroup hc) (RatFunc ℚ) :=
    MulSemiringAction.compHom _ (atkinLehnerGroup hc).subtype
  have hfix : ∀ (g : ↥(atkinLehnerGroup hc)) (q : ℚ), g • RatFunc.C q = RatFunc.C q := by
    intro g q
    rw [eq_ratCast (RatFunc.C : ℚ →+* RatFunc ℚ) q]
    exact map_ratCast (MulSemiringAction.toRingEquiv _ (RatFunc ℚ) g) q
  refine ⟨FixedPoints.subfield ↥(atkinLehnerGroup hc) (RatFunc ℚ), fun x => ?_,
    Rigidity.RET.exists_ringEquiv_fixedField hfix⟩
  constructor
  · intro hx
    exact hx ⟨atkinLehner hc, Subgroup.mem_zpowers _⟩
  · intro hx
    show ∀ g : ↥(atkinLehnerGroup hc), g • x = x
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hstab : atkinLehner hc ∈ MulAction.stabilizer (RingAut (RatFunc ℚ)) x := hx
    exact Subgroup.zpow_mem _ hstab n

/-! ## The modular tower of level `p`

The two facts about the level-`p` tower that the descent uses are recorded here.  The first is the
shape of its Galois group: the determinant character has `PSL₂(𝔽ₚ)` as its kernel.  The second is
that the determinant is exactly the character measuring the action on the constants — the field of
constants of the tower is `ℚ(ζₚ)`, and an automorphism fixes it if and only if its determinant is
`1`. -/

/-- **A level-`p` modular tower over a base curve `B`.**

The data is a Galois extension `M / B` whose group `G` carries a surjective determinant character
onto `(ℤ/p)ˣ` with kernel `PSL₂(𝔽ₚ)`, and whose constants are cut out by that character: an
automorphism of `M` over `B` fixes every element algebraic over `ℚ` exactly when its determinant
is trivial.  For `B` the function field of the `j`-line this is the function field of the modular
curve `X(p)`; for `B` the function field of `X₀(N)` it is the compositum with `ℚ(X₀(N))`. -/
structure LevelTower (p : ℕ) (B : Type) [Field B] [Algebra ℚ B] where
  /-- the arithmetic monodromy group, a copy of `GL₂(𝔽ₚ)/{±1}` -/
  G : Type
  [group : Group G]
  [finite : Finite G]
  /-- the determinant character, which is the cyclotomic character of the tower -/
  det : G →* (ZMod p)ˣ
  /-- the constants of the tower are the whole of `ℚ(ζₚ)` -/
  det_surjective : Function.Surjective det
  /-- the geometric monodromy group is the projective special linear group -/
  geom : ↥det.ker ≃* PSL(2, ZMod p)
  /-- the function field of the tower -/
  M : Type
  [field : Field M]
  [alg : Algebra B M]
  [findim : FiniteDimensional B M]
  [galois : IsGalois B M]
  [algQ : Algebra ℚ M]
  [tower : IsScalarTower ℚ B M]
  /-- the identification of the Galois group -/
  gal : (M ≃ₐ[B] M) ≃* G
  /-- the determinant is the character of the action on the constants -/
  constants : ∀ σ : M ≃ₐ[B] M, (∀ x ∈ algebraicClosure ℚ M, σ x = x) ↔ det (gal σ) = 1

attribute [instance] LevelTower.group LevelTower.finite LevelTower.field LevelTower.alg
  LevelTower.findim LevelTower.galois LevelTower.algQ LevelTower.tower

/-- **An Atkin–Lehner lift of multiplier `N`.**

An involution `ω` of the level-`p` tower, defined over `ℚ` but not over the base, lying above an
involution `w` of the base curve and acting on the `p`-th roots of unity by the `N`-th power.  The
last condition is the Weil-pairing computation: `w_N` sends `(E, C)` to `(E/C, E[N]/C)`, an
`N`-isogeny, and an `N`-isogeny multiplies the pairing on the `p`-torsion by `N`. -/
structure AtkinLehner (p N : ℕ) (tower : LevelTower p (RatFunc ℚ)) where
  /-- the Atkin–Lehner involution of the base curve -/
  w : RingAut (RatFunc ℚ)
  /-- the involution is not the identity, so the quotient really is a degree-two quotient -/
  w_ne_one : w ≠ 1
  /-- the base involution squares to the identity -/
  w_mul_self : w * w = 1
  /-- the lift to the tower -/
  ω : tower.M ≃ₐ[ℚ] tower.M
  /-- the lift squares to the identity -/
  ω_mul_self : ω.trans ω = AlgEquiv.refl
  /-- the lift sits above the base involution -/
  ω_base : ∀ x : RatFunc ℚ,
    ω (algebraMap (RatFunc ℚ) tower.M x) = algebraMap (RatFunc ℚ) tower.M (w x)
  /-- the multiplier: the lift raises `p`-th roots of unity to the `N`-th power -/
  ω_root : ∀ ζ : tower.M, ζ ^ p = 1 → ω ζ = ζ ^ N

/-- **The modular input.**

For `N ∈ {2, 3, 7}` the modular curve `X₀(N)` is a rational curve over `ℚ`, so the level-`p` tower
pulled back along `X₀(N) → X(1)` sits over a rational function field, and the Atkin–Lehner
involution of `X₀(N)` lifts to it with multiplier `N`. -/
theorem levelTower_atkinLehner_exists (p N : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hN : N = 2 ∨ N = 3 ∨ N = 7) :
    ∃ tower : LevelTower p (RatFunc ℚ), Nonempty (AtkinLehner p N tower) := by
  sorry

/-- **The Atkin–Lehner twist.**

When the multiplier `N` is a quadratic non-residue modulo `p`, the lift `ω` of the Atkin–Lehner
involution moves the constants by a generator of the quotient of `(ℤ/p)ˣ` by its squares, and the
subgroup of the enlarged Galois group generated by the geometric group and `ω` maps onto
`PSL₂(𝔽ₚ)` with the constants split off.  The fixed field of the kernel over the Atkin–Lehner
quotient line — a rational function field, by
`Rigidity.Shih.exists_ringEquiv_atkinLehnerFixedField` — is a regular `PSL₂(𝔽ₚ)`-extension. -/
theorem isRegularInverseGalois_of_atkinLehner {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hN : ¬ IsSquare ((N : ℕ) : ZMod p)) {tower : LevelTower p (RatFunc ℚ)}
    (al : AtkinLehner p N tower) : IsRegularInverseGalois PSL(2, ZMod p) := by
  sorry

/-- **Shih's theorem.**

If one of `2`, `3`, `7` is a quadratic non-residue modulo the prime `p ≥ 5`, then `PSL₂(𝔽ₚ)` is a
regular Galois group over `ℚ(T)`: there is a finite Galois extension of `ℚ(T)` with group
`PSL₂(𝔽ₚ)` in which `ℚ` is relatively algebraically closed. -/
theorem shih (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (h : ShihPrime p) :
    IsRegularInverseGalois PSL(2, ZMod p) := by
  obtain ⟨N, hN, hNsq⟩ := exists_level h
  obtain ⟨tower, ⟨al⟩⟩ := levelTower_atkinLehner_exists p N hp hN
  exact isRegularInverseGalois_of_atkinLehner hp hNsq al

end Rigidity.Shih
