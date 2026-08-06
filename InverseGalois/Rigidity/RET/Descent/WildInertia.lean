/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Tame inertia in residue characteristic zero: wild inertia vanishes, inertia is cyclic

Let a finite group `G` act faithfully by ring automorphisms on a Noetherian domain `S`, and let
`P` be a maximal ideal of `S` whose residue field `S ⧸ P` has characteristic zero.  The **higher
inertia** (or *wild inertia*) subgroup

  `(P ^ 2).inertia G = {σ | ∀ x, σ • x - x ∈ P ^ 2}`

is then trivial.  Classically this is the statement that the ramification filtration
`G ⊇ G₀ ⊇ G₁ ⊇ ⋯` of a Galois extension of Dedekind domains has `G₁ = 1` whenever the residue
characteristic is `0` — the inertia group `G₀` is *tame*, so it embeds into the multiplicative group
of the residue field and is cyclic.

## The argument

The usual proof identifies the graded pieces `Gᵢ / Gᵢ₊₁` with subgroups of `(𝔪ⁱ / 𝔪ⁱ⁺¹, +)`, an
elementary abelian `p`-group for `p` the residue characteristic, and concludes that `G₁` is a
`p`-group.  In residue characteristic zero the same computation is available in a much more direct
form, and needs neither the local ring nor the Dedekind hypothesis:

* `sub_smul_mem_pow_succ` — an element of `Gₙ` (`n ≥ 2`) moves `P ^ k` by `P ^ (k+1)`: this is a
  Leibniz-rule induction on `k`, the point being that `P` is moved into `P ^ n ⊆ P ^ 2`.
* `smul_sub_mem_pow_succ_of_mem_inertia_pow` — hence `Gₙ ⊆ Gₙ₊₁`.  Writing `a = σ • x - x`, the
  telescoping sum `∑_{j < m} σ ^ j • a` vanishes (`m` the order of `σ`), while each term differs
  from `a` by an element of `P ^ (n+1)` by the previous step.  So `m · a ∈ P ^ (n+1)`; as `P ^ (n+1)`
  is `P`-primary and `m` is invertible modulo `P` in residue characteristic zero, `a ∈ P ^ (n+1)`.
* `inertia_pow_sq_eq_bot` — therefore an element of `G₁` lies in every `Gₙ`, so it moves each `x`
  into `⋂ₙ P ^ n = 0` (Krull), i.e. acts trivially; faithfulness finishes.

## Main results

* `Rigidity.RET.sub_smul_mem_pow_succ` — the Leibniz step for the ramification filtration.
* `Rigidity.RET.smul_sub_mem_pow_succ_of_mem_inertia_pow` — `Gₙ ⊆ Gₙ₊₁` for `n ≥ 2`.
* `Rigidity.RET.eq_one_of_mem_inertia_pow_two` — an element of `G₁` is trivial.
* `Rigidity.RET.inertia_pow_sq_eq_bot` — `(P ^ 2).inertia G = ⊥`.

## The tame character

With wild inertia gone, the inertia group at `P` is read off the residue field.  For a Dedekind
domain `S` and a uniformizer `π` at `P` (an element of `P` outside `P ^ 2`), an inertia element `g`
scales `π`:  `g • π ≡ u_g · π (mod P ^ 2)`, and `g ↦ u_g mod P` is a homomorphism

  `θ : P.inertia G → S ⧸ P`

independent of the uniformizer.  Its kernel consists of the elements acting trivially modulo
`P ^ 2`, provided the residues at `P` are represented by elements the inertia group fixes
(`ResidueFixed`) — automatic for a cover of curves over an algebraically closed constant field, and
automatic whenever the order of the inertia group is invertible in `S` (average a representative
over its inertia orbit), in particular over any `ℚ`-algebra.
Then `θ` is injective, so the inertia group embeds in the units of the residue field and is cyclic;
and its equivariance `θ (σ g σ⁻¹) = σ (θ g)` under the decomposition group is Fried's branch-cycle
formula.

* `Rigidity.RET.exists_uniformizer`, `Rigidity.RET.span_sup_sq_eq` — uniformizers at `P`.
* `Rigidity.RET.tameChar` — the tame character, with `tameChar_congr` (uniformizer-independence).
* `Rigidity.RET.tameChar_injective`, `Rigidity.RET.isCyclic_inertia` — tame inertia is cyclic.
* `Rigidity.RET.tameChar_conj`, `Rigidity.RET.conj_eq_pow_of_cyclotomic` — the branch-cycle formula.
* `Rigidity.RET.residueHom`, `Rigidity.RET.exists_cyclotomic_unit_residue` — the action of a
  decomposition element on the residue field, and its cyclotomic exponent on roots of unity.
* `Rigidity.RET.conj_eq_pow_cyclotomicUnit` — the branch-cycle formula with the exponent a unit of
  `ZMod M`.
* `Rigidity.RET.residueFixed_of_isUnit_card`, `Rigidity.RET.residueFixed_of_algebraRat` —
  invariant residue representatives by averaging over an inertia orbit.
* `Rigidity.RET.isPrimitiveRoot_quotient_mk` — reduction modulo a maximal ideal with residue
  characteristic zero keeps a root of unity primitive.
* `Rigidity.RET.isCyclic_inertia_of_algebraRat`, `Rigidity.RET.conj_eq_pow_of_smul_root` —
  cyclicity of inertia and the branch-cycle formula over a `ℚ`-algebra, with the exponent read off
  the action on a root of unity of `S` itself.
-/

open scoped Pointwise

namespace Rigidity.RET

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]

section Filtration

variable {P : Ideal S} {g : G}

/-- An element of the inertia group preserves every power of `P`. -/
theorem smul_mem_pow_of_inertia (hg : ∀ x : S, g • x - x ∈ P) :
    ∀ (k : ℕ) {y : S}, y ∈ P ^ k → g • y ∈ P ^ k := by
  intro k
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hy
    have hb : ∀ b : S, b ∈ P → g • b ∈ P := fun b hb => by
      have := Ideal.add_mem P (hg b) hb
      simpa using this
    have hle : P ^ k * P ≤ Ideal.comap (MulSemiringAction.toRingHom G S g) (P ^ (k + 1)) := by
      refine Ideal.mul_le.mpr fun a ha b hbP => ?_
      have : g • (a * b) ∈ P ^ (k + 1) := by
        rw [smul_mul', pow_succ]
        exact Ideal.mul_mem_mul (ih ha) (hb b hbP)
      simpa [Ideal.mem_comap] using this
    have hy' : y ∈ P ^ k * P := by rwa [← pow_succ]
    simpa [Ideal.mem_comap] using hle hy'

/-- **The Leibniz step for the ramification filtration.**

If `g` moves every element of `S` by `P ^ n` with `n ≥ 2`, then it moves every element of `P ^ k`
by `P ^ (k + 1)`: each factor drawn from `P` contributes one extra power of `P`. -/
theorem sub_smul_mem_pow_succ {n : ℕ} (hn : 2 ≤ n) (hg : ∀ x : S, g • x - x ∈ P ^ n) :
    ∀ (k : ℕ) {y : S}, y ∈ P ^ k → g • y - y ∈ P ^ (k + 1) := by
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hgP : ∀ x : S, g • x - x ∈ P := fun x =>
    (Ideal.pow_le_self (by omega) : P ^ n ≤ P) (hg x)
  have hsmul : ∀ (k : ℕ) {y : S}, y ∈ P ^ k → g • y ∈ P ^ k := smul_mem_pow_of_inertia hgP
  intro k
  induction k with
  | zero =>
    intro y _
    exact (Ideal.pow_le_pow_right (by omega) : P ^ n ≤ P ^ (0 + 1)) (hg y)
  | succ k ih =>
    have key : ∀ (c y : S), y ∈ P ^ (k + 1) → g • y - y ∈ P ^ (k + 2) →
        g • (c * y) - c * y ∈ P ^ (k + 2) := by
      intro c y hyP hy
      have hrw : g • (c * y) - c * y = (g • c - c) * (g • y) + c * (g • y - y) := by
        rw [smul_mul']; ring
      rw [hrw]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hy)
      have h1 : (g • c - c) * (g • y) ∈ P ^ n * P ^ (k + 1) :=
        Ideal.mul_mem_mul (hg c) (hsmul (k + 1) hyP)
      refine (Ideal.pow_le_pow_right (by omega) : P ^ (n + (k + 1)) ≤ P ^ (k + 2)) ?_
      rwa [← pow_add] at h1
    -- the elements of `P ^ (k+1)` moved by `P ^ (k+2)` form an ideal
    let M : Ideal S :=
      { carrier := {y : S | y ∈ P ^ (k + 1) ∧ g • y - y ∈ P ^ (k + 2)}
        add_mem' := fun {a b} ha hb => by
          refine ⟨Ideal.add_mem _ ha.1 hb.1, ?_⟩
          have : g • (a + b) - (a + b) = (g • a - a) + (g • b - b) := by
            rw [smul_add]; ring
          rw [this]
          exact Ideal.add_mem _ ha.2 hb.2
        zero_mem' := ⟨Ideal.zero_mem _, by simp⟩
        smul_mem' := fun c {y} hy => by
          exact ⟨Ideal.mul_mem_left _ _ hy.1, key c y hy.1 hy.2⟩ }
    have hMle : P ^ (k + 1) ≤ M := by
      rw [pow_succ]
      refine Ideal.mul_le.mpr fun a ha b hbP => ?_
      refine ⟨Ideal.mul_mem_mul ha hbP, ?_⟩
      have hrw : g • (a * b) - a * b = (g • a - a) * (g • b) + a * (g • b - b) := by
        rw [smul_mul']; ring
      rw [hrw]
      refine Ideal.add_mem _ ?_ ?_
      · have h1 : (g • a - a) * (g • b) ∈ P ^ (k + 1) * P :=
          Ideal.mul_mem_mul (ih ha) (by
            have := Ideal.add_mem P (hgP b) hbP
            simpa using this)
        rwa [← pow_succ] at h1
      · have h2 : a * (g • b - b) ∈ P ^ k * P ^ n := Ideal.mul_mem_mul ha (hg b)
        refine (Ideal.pow_le_pow_right (by omega) : P ^ (k + n) ≤ P ^ (k + 2)) ?_
        rwa [← pow_add] at h2
    intro y hy
    exact (hMle hy).2

end Filtration

section Deepening

variable [Finite G] {P : Ideal S} [P.IsMaximal] {g : G}

/-- **The ramification filtration does not drop in residue characteristic zero.**

If `g` moves every element by `P ^ n` (`n ≥ 2`), it already moves every element by `P ^ (n+1)`.
The telescoping sum `∑_{j < m} g ^ j • (g • x - x)` vanishes, and by `sub_smul_mem_pow_succ` each of
its `m` terms is congruent to `g • x - x` modulo `P ^ (n+1)`; so `m · (g • x - x) ∈ P ^ (n+1)`, and
`m` — the order of `g` — is invertible modulo `P`. -/
theorem smul_sub_mem_pow_succ_of_mem_inertia_pow [CharZero (S ⧸ P)] {n : ℕ} (hn : 2 ≤ n)
    (hg : ∀ x : S, g • x - x ∈ P ^ n) : ∀ x : S, g • x - x ∈ P ^ (n + 1) := by
  set m := orderOf g with hmdef
  have hmpos : 0 < m := orderOf_pos g
  -- the order of `g` is invertible modulo `P`
  have hmP : (m : S) ∉ P := by
    intro h
    have h0 : ((m : ℕ) : S ⧸ P) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P) m]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact hmpos.ne' (Nat.cast_eq_zero.mp h0)
  -- every power of `g` moves elements by `P ^ n`
  have hpow : ∀ (j : ℕ) (x : S), (g ^ j) • x - x ∈ P ^ n := by
    intro j x
    have : g ∈ (P ^ n).inertia G := hg
    exact (pow_mem this j : g ^ j ∈ (P ^ n).inertia G) x
  intro x
  set a : S := g • x - x with hadef
  have haP : a ∈ P ^ n := hg x
  -- the telescoping sum vanishes
  have htel : ∑ j ∈ Finset.range m, ((g ^ j) • a) = 0 := by
    have hterm : ∀ j : ℕ, (g ^ j) • a = (g ^ (j + 1)) • x - (g ^ j) • x := by
      intro j
      rw [hadef, smul_sub, pow_succ, mul_smul]
    calc ∑ j ∈ Finset.range m, ((g ^ j) • a)
        = ∑ j ∈ Finset.range m, ((g ^ (j + 1)) • x - (g ^ j) • x) := by
          exact Finset.sum_congr rfl fun j _ => hterm j
      _ = (g ^ m) • x - (g ^ 0) • x := Finset.sum_range_sub (fun j => (g ^ j) • x) m
      _ = 0 := by rw [hmdef, pow_orderOf_eq_one]; simp
  -- each term differs from `a` by `P ^ (n+1)`
  have hdiff : ∀ j ∈ Finset.range m, (g ^ j) • a - a ∈ P ^ (n + 1) := by
    intro j _
    exact sub_smul_mem_pow_succ hn (hpow j) n haP
  have hsum : (m : S) * a ∈ P ^ (n + 1) := by
    have h1 : ∑ j ∈ Finset.range m, ((g ^ j) • a - a) ∈ P ^ (n + 1) :=
      Ideal.sum_mem _ hdiff
    rw [Finset.sum_sub_distrib, htel] at h1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, zero_sub] at h1
    have := neg_mem h1
    simpa using this
  -- `P ^ (n+1)` is `P`-primary, and `m ∉ P`
  have hrad : (P ^ (n + 1)).radical = P := by
    rw [Ideal.radical_pow (I := P) (n := n + 1) (by omega),
      Ideal.IsPrime.radical (Ideal.IsMaximal.isPrime ‹P.IsMaximal›)]
  have hprimary : (P ^ (n + 1)).IsPrimary :=
    Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; infer_instance)
  rcases (Ideal.isPrimary_iff.mp hprimary).2
      (show a * (m : S) ∈ P ^ (n + 1) by rw [mul_comm]; exact hsum) with h | h
  · exact h
  · exact absurd (by rwa [hrad] at h) hmP

end Deepening

section Main

variable [IsNoetherianRing S] [IsDomain S] [Finite G] [FaithfulSMul G S]

/-- **Wild inertia is trivial in residue characteristic zero.**

An element of the first higher ramification group `G₁ = (P ^ 2).inertia G` acts trivially on `S`.
Indeed by `smul_sub_mem_pow_succ_of_mem_inertia_pow` it lies in `Gₙ` for every `n`, so it moves each
element of `S` into `⋂ₙ P ^ n`, which vanishes by the Krull intersection theorem. -/
theorem eq_one_of_mem_inertia_pow_two (P : Ideal S) [P.IsMaximal] [CharZero (S ⧸ P)] {g : G}
    (hg : g ∈ (P ^ 2).inertia G) : g = 1 := by
  have hall : ∀ n : ℕ, 2 ≤ n → ∀ x : S, g • x - x ∈ P ^ n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn
      rcases Nat.lt_or_ge n 2 with h | h
      · have : n + 1 = 2 := by omega
        rw [this]
        exact hg
      · exact smul_sub_mem_pow_succ_of_mem_inertia_pow h (ih h)
  have hbot : ⨅ i : ℕ, P ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isDomain P (Ideal.IsPrime.ne_top (Ideal.IsMaximal.isPrime ‹_›))
  refine FaithfulSMul.eq_of_smul_eq_smul (α := S) fun x => ?_
  have hmem : g • x - x ∈ ⨅ i : ℕ, P ^ i := by
    refine Ideal.mem_iInf.mpr fun i => ?_
    rcases Nat.lt_or_ge i 2 with h | h
    · exact (Ideal.pow_le_pow_right (by omega) : P ^ 2 ≤ P ^ i) (hall 2 le_rfl x)
    · exact hall i h x
  rw [hbot] at hmem
  have : g • x - x = 0 := by simpa using hmem
  rw [one_smul]
  linear_combination (norm := ring_nf) this

/-- **`(P ^ 2).inertia G = ⊥`**: the wild inertia subgroup of a maximal ideal with residue
characteristic zero is trivial.

Consequently the inertia group `(P).inertia G` is *tame*: it injects into the multiplicative group
of the residue field through the action on `P ⧸ P ^ 2`, and is therefore cyclic. -/
theorem inertia_pow_sq_eq_bot (P : Ideal S) [P.IsMaximal] [CharZero (S ⧸ P)] :
    (P ^ 2).inertia G = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hg => eq_one_of_mem_inertia_pow_two P hg

end Main

section Tame

/-- **The residue field of `P` is generated by invariants.**

Every element of `S` agrees modulo `P` with an element fixed by `G`.  This holds whenever the
residue extension at `P` is trivial — in particular for a cover of curves over an algebraically
closed constant field, where all residue fields are the constant field itself. -/
def ResidueFixed (P : Ideal S) (G : Type*) [Group G] [MulSemiringAction G S] : Prop :=
  ∀ x : S, ∃ y : S, (∀ g ∈ P.inertia G, g • y = y) ∧ x - y ∈ P

/-- **Averaging over the inertia orbit produces invariant residue representatives.**

If the order of the inertia group is invertible in `S`, the average `|I| ⁻¹ ∑_{g ∈ I} g • x` is an
inertia-invariant element congruent to `x` modulo `P`: each `g • x` is already congruent to `x` by
the definition of inertia, so the average is too. -/
theorem residueFixed_of_isUnit_card [Finite G] (P : Ideal S)
    (hu : IsUnit ((Nat.card (P.inertia G) : ℕ) : S)) : ResidueFixed P G := by
  classical
  haveI : Fintype (P.inertia G) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hu
  intro x
  set s : S := ∑ g : P.inertia G, (g : G) • x with hs
  have hcard : ((Nat.card (P.inertia G) : ℕ) : S) = ∑ _g : P.inertia G, (1 : S) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card, Finset.card_univ]
  -- the inertia average is invariant: left translation permutes the inertia group
  have hfix : ∀ h ∈ P.inertia G, h • s = s := by
    intro h hh
    rw [hs, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : P.inertia G)) _ _ fun g => ?_
    rw [← mul_smul]
    rfl
  have hfixu : ∀ h ∈ P.inertia G, h • (u : S) = (u : S) := by
    intro h _
    rw [hu]
    exact map_natCast (MulSemiringAction.toRingHom G S h) (Nat.card (P.inertia G))
  have hfixinv : ∀ h ∈ P.inertia G, h • ((u⁻¹ : Sˣ) : S) = ((u⁻¹ : Sˣ) : S) := by
    intro h hh
    have hmap : Units.map (MulSemiringAction.toRingHom G S h).toMonoidHom u = u :=
      Units.ext (hfixu h hh)
    have := congrArg (fun v : Sˣ => ((v⁻¹ : Sˣ) : S)) hmap
    simpa [Units.coe_map, MulSemiringAction.toRingHom] using this
  refine ⟨((u⁻¹ : Sˣ) : S) * s, fun h hh => by rw [smul_mul', hfixinv h hh, hfix h hh], ?_⟩
  -- `u * (x - y) = ∑ (x - g • x) ∈ P`, and `u` is a unit
  have hmem : (u : S) * (x - ((u⁻¹ : Sˣ) : S) * s) ∈ P := by
    have hexp : (u : S) * (x - ((u⁻¹ : Sˣ) : S) * s) = ∑ g : P.inertia G, (x - (g : G) • x) := by
      have hux : (u : S) * x = ∑ _g : P.inertia G, x := by
        rw [hu, hcard, Finset.sum_mul]
        simp
      rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, Finset.sum_sub_distrib, ← hs, hux]
    rw [hexp]
    exact Ideal.sum_mem _ fun g _ => (Ideal.neg_mem_iff _).mp (by simpa using g.2 x)
  have := Ideal.mul_mem_left P ((u⁻¹ : Sˣ) : S) hmem
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

/-- Over a `ℚ`-algebra the inertia order is always invertible, so residues always have invariant
representatives. -/
theorem residueFixed_of_algebraRat [Finite G] [Algebra ℚ S] (P : Ideal S) : ResidueFixed P G := by
  refine residueFixed_of_isUnit_card P ?_
  have hne : ((Nat.card (P.inertia G) : ℕ) : ℚ) ≠ 0 := by
    have : 0 < Nat.card (P.inertia G) := Nat.card_pos
    positivity
  have : IsUnit ((Nat.card (P.inertia G) : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr hne
  simpa using this.map (algebraMap ℚ S)

variable [IsDedekindDomain S]

/-- In a Dedekind domain a nonzero maximal ideal strictly contains its square, so a **uniformizer**
— an element of `P` outside `P ^ 2` — exists. -/
theorem exists_uniformizer (P : Ideal S) [hPm : P.IsMaximal] (hP0 : P ≠ ⊥) :
    ∃ π : S, π ∈ P ∧ π ∉ P ^ 2 := by
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P hP0 hPm.ne_top 2 le_rfl)
  exact ⟨π, hπP, hπ2⟩

/-- **A uniformizer generates `P` modulo `P ^ 2`.**  The ideal `(π) + P ^ 2` divides `P ^ 2`, hence
is one of `⊤`, `P`, `P ^ 2` by unique factorisation; it is contained in `P` and contains `π`. -/
theorem span_sup_sq_eq (P : Ideal S) [hPm : P.IsMaximal] (hP0 : P ≠ ⊥) {π : S}
    (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) : Ideal.span {π} ⊔ P ^ 2 = P := by
  have hJle : Ideal.span {π} ⊔ P ^ 2 ≤ P :=
    sup_le (Ideal.span_le.mpr (by simpa using hπ)) (Ideal.pow_le_self two_ne_zero)
  have hdvd : (Ideal.span {π} ⊔ P ^ 2) ∣ P ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ :=
    (dvd_prime_pow (Ideal.prime_of_isPrime hP0 hPm.isPrime) 2).mp hdvd
  have hJeq : Ideal.span {π} ⊔ P ^ 2 = P ^ i := associated_iff_eq.mp hassoc
  interval_cases i
  · rw [pow_zero] at hJeq
    exact absurd (hJeq ▸ hJle) (by simpa using hPm.ne_top)
  · rw [hJeq, pow_one]
  · exact absurd (hJeq ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)) hπ2

omit [IsDedekindDomain S] in
/-- A uniformizer is not a zero divisor modulo `P ^ 2`: this is the well-definedness of the tame
character. -/
theorem sub_mem_of_mul_sub_mul_mem_sq {P : Ideal S} [P.IsMaximal] {π : S} (hπ2 : π ∉ P ^ 2)
    {u v : S} (h : u * π - v * π ∈ P ^ 2) : u - v ∈ P := by
  have hrad : (P ^ 2).radical = P := by
    rw [Ideal.radical_pow (I := P) (n := 2) two_ne_zero,
      Ideal.IsPrime.radical (Ideal.IsMaximal.isPrime ‹P.IsMaximal›)]
  have hprimary : (P ^ 2).IsPrimary :=
    Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; infer_instance)
  have hmul : π * (u - v) ∈ P ^ 2 := by
    have : π * (u - v) = u * π - v * π := by ring
    rw [this]; exact h
  rcases (Ideal.isPrimary_iff.mp hprimary).2 hmul with h' | h'
  · exact absurd h' hπ2
  · rwa [hrad] at h'

variable (P : Ideal S) [P.IsMaximal] (hP0 : P ≠ ⊥) {π : S} (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2)

include hP0 hπ hπ2

/-- An inertia element scales a uniformizer, modulo `P ^ 2`. -/
theorem exists_tameCoeff {g : G} (hg : g ∈ P.inertia G) :
    ∃ u : S, g • π - u * π ∈ P ^ 2 := by
  have hmem : g • π ∈ Ideal.span {π} ⊔ P ^ 2 := by
    rw [span_sup_sq_eq P hP0 hπ hπ2]
    have := Ideal.add_mem P (hg π) hπ
    simpa using this
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  exact ⟨u, by rw [← hyz]; simpa using hz⟩

/-- The scaling coefficient of `g` on the uniformizer `π`, well defined modulo `P`. -/
noncomputable def tameCoeff (g : P.inertia G) : S :=
  (exists_tameCoeff P hP0 hπ hπ2 g.2).choose

theorem tameCoeff_spec (g : P.inertia G) :
    (g : G) • π - tameCoeff P hP0 hπ hπ2 g * π ∈ P ^ 2 :=
  (exists_tameCoeff P hP0 hπ hπ2 g.2).choose_spec

theorem tameCoeff_eq {g : P.inertia G} {u : S} (hu : (g : G) • π - u * π ∈ P ^ 2) :
    Ideal.Quotient.mk P u = Ideal.Quotient.mk P (tameCoeff P hP0 hπ hπ2 g) := by
  refine Ideal.Quotient.eq.mpr ?_
  refine sub_mem_of_mul_sub_mul_mem_sq hπ2 ?_
  have : u * π - tameCoeff P hP0 hπ hπ2 g * π =
      ((g : G) • π - tameCoeff P hP0 hπ hπ2 g * π) - ((g : G) • π - u * π) := by ring
  rw [this]
  exact Ideal.sub_mem _ (tameCoeff_spec P hP0 hπ hπ2 g) hu

/-- **The tame character.**

An element `g` of the inertia group scales a uniformizer, `g • π ≡ u_g · π (mod P ^ 2)`, and the
residue of `u_g` depends neither on the representative nor — as `tameChar_injective` shows — loses
any information in residue characteristic zero.  This is the multiplicative character
`I → (S ⧸ P)ˣ` through which tame inertia is read. -/
noncomputable def tameChar : P.inertia G →* S ⧸ P where
  toFun g := Ideal.Quotient.mk P (tameCoeff P hP0 hπ hπ2 g)
  map_one' := by
    have h := (tameCoeff_eq P hP0 hπ hπ2 (g := (1 : P.inertia G)) (u := 1) (by simp)).symm
    simpa using h
  map_mul' := by
    intro g h
    set u := tameCoeff P hP0 hπ hπ2 g with hu
    set v := tameCoeff P hP0 hπ hπ2 h with hv
    have hgP : ∀ x : S, (g : G) • x - x ∈ P := g.2
    have hsq : ∀ {y : S}, y ∈ P ^ 2 → (g : G) • y ∈ P ^ 2 :=
      fun {y} hy => smul_mem_pow_of_inertia hgP 2 hy
    have hkey : ((g * h : P.inertia G) : G) • π - ((g : G) • v) * u * π ∈ P ^ 2 := by
      have hexp : ((g * h : P.inertia G) : G) • π - ((g : G) • v) * u * π =
          (g : G) • ((h : G) • π - v * π)
            + ((g : G) • v) * ((g : G) • π - u * π) := by
        push_cast [mul_smul, smul_sub, smul_mul']
        ring
      rw [hexp]
      exact Ideal.add_mem _ (hsq (tameCoeff_spec P hP0 hπ hπ2 h))
        (Ideal.mul_mem_left _ _ (tameCoeff_spec P hP0 hπ hπ2 g))
    have h1 := (tameCoeff_eq P hP0 hπ hπ2 hkey).symm
    have h2 : Ideal.Quotient.mk P ((g : G) • v) = Ideal.Quotient.mk P v :=
      Ideal.Quotient.eq.mpr (hgP v)
    rw [h1, map_mul, h2, mul_comm]

theorem tameChar_apply (g : P.inertia G) :
    tameChar P hP0 hπ hπ2 g = Ideal.Quotient.mk P (tameCoeff P hP0 hπ hπ2 g) := rfl

/-- Every element of `P` is a multiple of the uniformizer up to `P ^ 2`. -/
theorem exists_eq_mul_uniformizer_add {z : S} (hz : z ∈ P) :
    ∃ s w : S, w ∈ P ^ 2 ∧ z = s * π + w := by
  rw [← span_sup_sq_eq P hP0 hπ hπ2] at hz
  obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp hz
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  exact ⟨s, w, hw, hyw.symm⟩

/-- **An inertia element in the kernel of the tame character acts trivially modulo `P ^ 2`.**

Writing an element of `P` as `s · π` up to `P ^ 2` and an arbitrary element of `S` as an invariant
plus an element of `P`, the Leibniz rule reduces everything to the single relation
`g • π ≡ π (mod P ^ 2)` expressed by `tameChar g = 1`. -/
theorem smul_sub_mem_sq_of_tameChar_eq_one (hres : ResidueFixed P G) {g : P.inertia G}
    (hg : tameChar P hP0 hπ hπ2 g = 1) : ∀ x : S, (g : G) • x - x ∈ P ^ 2 := by
  have hgP : ∀ x : S, (g : G) • x - x ∈ P := g.2
  have hsq : ∀ {y : S}, y ∈ P ^ 2 → (g : G) • y ∈ P ^ 2 :=
    fun {y} hy => smul_mem_pow_of_inertia hgP 2 hy
  -- the uniformizer is moved only by `P ^ 2`
  have hu1 : tameCoeff P hP0 hπ hπ2 g - 1 ∈ P := by
    refine Ideal.Quotient.eq.mp ?_
    rw [map_one]
    exact (tameChar_apply P hP0 hπ hπ2 g).symm.trans hg
  have hπg : (g : G) • π - π ∈ P ^ 2 := by
    have hrw : (g : G) • π - π =
        ((g : G) • π - tameCoeff P hP0 hπ hπ2 g * π)
          + (tameCoeff P hP0 hπ hπ2 g - 1) * π := by ring
    rw [hrw, pow_two]
    exact Ideal.add_mem _ (by rw [← pow_two]; exact tameCoeff_spec P hP0 hπ hπ2 g)
      (Ideal.mul_mem_mul hu1 hπ)
  -- hence every element of `P` is moved only by `P ^ 2`
  have hP2 : ∀ z ∈ P, (g : G) • z - z ∈ P ^ 2 := by
    intro z hz
    obtain ⟨s, w, hw, rfl⟩ := exists_eq_mul_uniformizer_add P hP0 hπ hπ2 hz
    have hrw : (g : G) • (s * π + w) - (s * π + w) =
        ((g : G) • s - s) * ((g : G) • π) + s * ((g : G) • π - π)
          + ((g : G) • w - w) := by
      rw [smul_add, smul_mul']; ring
    rw [hrw]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hπg))
      (Ideal.sub_mem _ (hsq hw) hw)
    rw [pow_two]
    refine Ideal.mul_mem_mul (hgP s) ?_
    have := Ideal.add_mem P (hgP π) hπ
    simpa using this
  intro x
  obtain ⟨y, hy, hxy⟩ := hres x
  have hrw : (g : G) • x - x = (g : G) • (x - y) - (x - y) := by
    rw [smul_sub, hy (g : G) g.2]; ring
  rw [hrw]
  exact hP2 _ hxy

/-- **The tame character does not depend on the chosen uniformizer.**

Two uniformizers differ by a unit modulo `P ^ 2`, and an inertia element scales that unit trivially
modulo `P`, so the residue of the scaling coefficient is unchanged. -/
theorem tameChar_congr {ρ : S} (hρ : ρ ∈ P) (hρ2 : ρ ∉ P ^ 2) (g : P.inertia G) :
    tameChar P hP0 hρ hρ2 g = tameChar P hP0 hπ hπ2 g := by
  have hgP : ∀ x : S, (g : G) • x - x ∈ P := g.2
  have hsq : ∀ {y : S}, y ∈ P ^ 2 → (g : G) • y ∈ P ^ 2 :=
    fun {y} hy => smul_mem_pow_of_inertia hgP 2 hy
  set u := tameCoeff P hP0 hπ hπ2 g with hu
  obtain ⟨w, p, hp, hρeq⟩ := exists_eq_mul_uniformizer_add P hP0 hπ hπ2 hρ
  have key : (g : G) • ρ - u * ρ ∈ P ^ 2 := by
    have hrw : (g : G) • ρ - u * ρ =
        ((g : G) • w - w) * ((g : G) • π) + w * ((g : G) • π - u * π)
          + ((g : G) • p - u * p) := by
      rw [hρeq, smul_add, smul_mul']; ring
    rw [hrw]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_
      (Ideal.mul_mem_left _ _ (tameCoeff_spec P hP0 hπ hπ2 g)))
      (Ideal.sub_mem _ (hsq hp) (Ideal.mul_mem_left _ _ hp))
    rw [pow_two]
    refine Ideal.mul_mem_mul (hgP w) ?_
    have := Ideal.add_mem P (hgP π) hπ
    simpa using this
  exact (tameCoeff_eq P hP0 hρ hρ2 key).symm

variable {σ : G}

omit [IsDedekindDomain S] [P.IsMaximal] hP0 hπ hπ2 in
/-- An element of the decomposition group of `P` preserves every power of `P`. -/
theorem smul_mem_pow_of_smul_eq (hσ : σ • P = P) (n : ℕ) {x : S} (hx : x ∈ P ^ n) :
    σ • x ∈ P ^ n := by
  have h := Ideal.smul_mem_pointwise_smul σ x (P ^ n) hx
  rwa [smul_pow', hσ] at h

omit [IsDedekindDomain S] [P.IsMaximal] hP0 hπ hπ2 in
/-- An element of the decomposition group of `P` preserves `P`. -/
theorem smul_mem_of_smul_eq (hσ : σ • P = P) {x : S} (hx : x ∈ P) : σ • x ∈ P := by
  have h := Ideal.smul_mem_pointwise_smul σ x P hx
  rwa [hσ] at h

omit [IsDedekindDomain S] [P.IsMaximal] hP0 hπ hπ2 in
/-- The inertia group is normal in the decomposition group. -/
theorem conj_mem_inertia (hσ : σ • P = P) (g : P.inertia G) :
    σ * (g : G) * σ⁻¹ ∈ P.inertia G := by
  show ∀ x : S, (σ * (g : G) * σ⁻¹) • x - x ∈ P
  intro x
  have h : (σ * (g : G) * σ⁻¹) • x - x = σ • ((g : G) • (σ⁻¹ • x) - σ⁻¹ • x) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  rw [h]
  exact smul_mem_of_smul_eq P hσ (g.2 (σ⁻¹ • x))

/-- **Equivariance of the tame character.**

Conjugating an inertia element by an element `σ` of the decomposition group twists its tame
character by the action of `σ` on the residue field:

  `θ (σ g σ⁻¹) = σ (θ g)`.

Composed with the action of `σ` on the roots of unity of the residue field this is Fried's
branch-cycle formula. -/
theorem tameChar_conj (hσ : σ • P = P) (g : P.inertia G) :
    tameChar P hP0 hπ hπ2 ⟨σ * (g : G) * σ⁻¹, conj_mem_inertia P hσ g⟩
      = Ideal.Quotient.mk P (σ • tameCoeff P hP0 hπ hπ2 g) := by
  set u := tameCoeff P hP0 hπ hπ2 g with hu
  have hσ' : σ⁻¹ • P = P := by rw [inv_smul_eq_iff]; exact hσ.symm
  have hπ' : σ • π ∈ P := smul_mem_of_smul_eq P hσ hπ
  have hπ'2 : σ • π ∉ P ^ 2 := by
    intro hmem
    refine hπ2 ?_
    have := smul_mem_pow_of_smul_eq P hσ' 2 hmem
    rwa [inv_smul_smul] at this
  have key : (σ * (g : G) * σ⁻¹) • (σ • π) - (σ • u) * (σ • π) ∈ P ^ 2 := by
    have hrw : (σ * (g : G) * σ⁻¹) • (σ • π) - (σ • u) * (σ • π)
        = σ • ((g : G) • π - u * π) := by
      rw [smul_sub, smul_mul', mul_smul, mul_smul, inv_smul_smul]
    rw [hrw]
    exact smul_mem_pow_of_smul_eq P hσ 2 (tameCoeff_spec P hP0 hπ hπ2 g)
  rw [← tameChar_congr P hP0 hπ hπ2 hπ' hπ'2, tameChar_apply]
  exact (tameCoeff_eq P hP0 hπ' hπ'2 key).symm

omit [IsDedekindDomain S] [P.IsMaximal] hP0 hπ hπ2 in
/-- **The action of a decomposition element on the residue field.**

An automorphism `σ` stabilizing `P` descends to a ring endomorphism of `S ⧸ P`. -/
noncomputable def residueHom (hσ : σ • P = P) : S ⧸ P →+* S ⧸ P :=
  Ideal.quotientMap P (MulSemiringAction.toRingHom G S σ)
    fun _ hx => Ideal.mem_comap.mpr (smul_mem_of_smul_eq P hσ hx)

omit [IsDedekindDomain S] [P.IsMaximal] hP0 hπ hπ2 in
@[simp] theorem residueHom_mk (hσ : σ • P = P) (x : S) :
    residueHom P hσ (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ • x) :=
  Ideal.quotientMap_mk

omit [IsDedekindDomain S] [P.IsMaximal] hP0 hπ hπ2 in
/-- The residue action of a decomposition element is injective: it is the reduction of an
automorphism whose inverse also stabilizes `P`. -/
theorem residueHom_injective (hσ : σ • P = P) : Function.Injective (residueHom P hσ) := by
  have hσ' : σ⁻¹ • P = P := by rw [inv_smul_eq_iff]; exact hσ.symm
  refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [residueHom_mk] at ha
  have hx : σ⁻¹ • (σ • x) ∈ P :=
    smul_mem_of_smul_eq P hσ' (Ideal.Quotient.eq_zero_iff_mem.mp ha)
  rw [inv_smul_smul] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

omit [IsDedekindDomain S] hP0 hπ hπ2 in
/-- **The cyclotomic exponent of a decomposition element.**

If the residue field contains a primitive `M`-th root of unity, a decomposition element acts on the
`M`-th roots of unity of the residue field by raising to a fixed power `c`, a unit of `ZMod M`. -/
theorem exists_cyclotomic_unit_residue (hσ : σ • P = P) {M : ℕ} [NeZero M] {ζ : S ⧸ P}
    (hζ : IsPrimitiveRoot ζ M) :
    ∃ c : (ZMod M)ˣ, ∀ x : S ⧸ P, x ^ M = 1 → residueHom P hσ x = x ^ ((c : ZMod M).val) := by
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime ‹P.IsMaximal›
  haveI : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hinj : Function.Injective (residueHom P hσ) := residueHom_injective P hσ
  have hpow : (residueHom P hσ ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨c, _, hc⟩ := hζ.eq_pow_of_pow_eq_one hpow
  have hprim : IsPrimitiveRoot (residueHom P hσ ζ) M := by
    refine ⟨hpow, fun l hl => ?_⟩
    refine hζ.dvd_of_pow_eq_one l (hinj ?_)
    rw [map_pow, map_one]
    exact hl
  rw [← hc] at hprim
  have hcop : Nat.Coprime c M := (hζ.pow_iff_coprime hM c).mp hprim
  have hred : ∀ (y : S ⧸ P) (n : ℕ), y ^ M = 1 → y ^ ((n : ZMod M).val) = y ^ n := by
    intro y n hy
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.div_add_mod n M, pow_add, pow_mul, hy, one_pow, one_mul]
  refine ⟨ZMod.unitOfCoprime c hcop, fun x hx => ?_⟩
  rw [ZMod.coe_unitOfCoprime, hred x c hx]
  obtain ⟨j, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, ← hc, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The tame character sends an inertia element of exponent `M` to an `M`-th root of unity. -/
theorem tameChar_pow_eq_one {M : ℕ} {g : P.inertia G} (hg : g ^ M = 1) :
    (tameChar P hP0 hπ hπ2 g) ^ M = 1 := by
  rw [← map_pow, hg, map_one]

variable [Finite G] [FaithfulSMul G S] [CharZero (S ⧸ P)]

/-- **The tame character is injective.**

Its kernel consists of the elements acting trivially modulo `P ^ 2`, and wild inertia is trivial in
residue characteristic zero. -/
theorem tameChar_injective (hres : ResidueFixed P G) :
    Function.Injective (tameChar (G := G) P hP0 hπ hπ2) := by
  intro g₁ g₂ h
  have hker : ∀ g : P.inertia G, tameChar P hP0 hπ hπ2 g = 1 → g = 1 := by
    intro g hg
    have : (g : G) ∈ (P ^ 2).inertia G := smul_sub_mem_sq_of_tameChar_eq_one P hP0 hπ hπ2 hres hg
    exact Subtype.ext (eq_one_of_mem_inertia_pow_two P this)
  have hinv : tameChar P hP0 hπ hπ2 (g₁ * g₂⁻¹) = 1 := by
    rw [map_mul, h, ← map_mul, mul_inv_cancel, map_one]
  have := hker _ hinv
  rwa [mul_inv_eq_one] at this

/-- **Tame inertia is cyclic.**

In residue characteristic zero the inertia group at `P` embeds, via the tame character, into the
multiplicative group of the residue field; a finite subgroup of the units of an integral domain is
cyclic. -/
theorem isCyclic_inertia (hres : ResidueFixed P G) : IsCyclic (P.inertia G) := by
  haveI : Finite (P.inertia G) := Subtype.finite
  haveI : (P.IsPrime) := Ideal.IsMaximal.isPrime ‹P.IsMaximal›
  haveI : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
  set f : P.inertia G →* (S ⧸ P)ˣ := (tameChar (G := G) P hP0 hπ hπ2).toHomUnits with hf
  have hinj : Function.Injective f := by
    intro g₁ g₂ h
    refine tameChar_injective P hP0 hπ hπ2 hres ?_
    simpa [hf, MonoidHom.coe_toHomUnits] using congrArg Units.val h
  haveI : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  haveI : IsCyclic f.range := subgroup_units_cyclic _
  exact isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
    (MulEquiv.surjective _)

/-- **Fried's branch-cycle formula.**

If an element `σ` of the decomposition group acts on the tame character of an inertia element `g` by
raising it to the `c`-th power — for `σ` an arithmetic Frobenius or a field automorphism, `c` is its
cyclotomic exponent on the roots of unity of the residue field — then conjugation by `σ` raises `g`
itself to the `c`-th power:

  `σ (θ g) = (θ g) ^ c  ⟹  σ g σ⁻¹ = g ^ c`.

This is the arithmetic action on tame inertia read off the arithmetic action on roots of unity; it
is what makes rational conjugacy classes descend. -/
theorem conj_eq_pow_of_cyclotomic (hres : ResidueFixed P G) (hσ : σ • P = P) (g : P.inertia G)
    (c : ℕ) (hc : Ideal.Quotient.mk P (σ • tameCoeff P hP0 hπ hπ2 g)
        = (Ideal.Quotient.mk P (tameCoeff P hP0 hπ hπ2 g)) ^ c) :
    σ * (g : G) * σ⁻¹ = (g : G) ^ c := by
  have h : (⟨σ * (g : G) * σ⁻¹, conj_mem_inertia P hσ g⟩ : P.inertia G) = g ^ c := by
    refine tameChar_injective P hP0 hπ hπ2 hres ?_
    rw [tameChar_conj P hP0 hπ hπ2 hσ g, map_pow, tameChar_apply, hc]
  simpa using congrArg (Subtype.val) h

/-- **Fried's branch-cycle formula, with the exponent a unit of `ZMod M`.**

Let `σ` be a decomposition element at `P` and `g` an inertia element of exponent dividing `M`, and
suppose the residue field contains a primitive `M`-th root of unity.  Then

  `σ g σ⁻¹ = g ^ c`,

where `c` is the unit of `ZMod M` describing the action of `σ` on the `M`-th roots of unity of the
residue field.  This is the shape branch data consumes: the exponent is a unit, hence automatically
coprime to `M`, and for an arithmetic automorphism `c` is its cyclotomic character. -/
theorem conj_eq_pow_cyclotomicUnit (hres : ResidueFixed P G) (hσ : σ • P = P) {M : ℕ} [NeZero M]
    {ζ : S ⧸ P} (hζ : IsPrimitiveRoot ζ M) (g : P.inertia G) (hgM : g ^ M = 1) :
    ∃ c : (ZMod M)ˣ, σ * (g : G) * σ⁻¹ = (g : G) ^ ((c : ZMod M).val) := by
  obtain ⟨c, hc⟩ := exists_cyclotomic_unit_residue P hσ hζ
  refine ⟨c, conj_eq_pow_of_cyclotomic P hP0 hπ hπ2 hres hσ g ((c : ZMod M).val) ?_⟩
  have h := hc (tameChar P hP0 hπ hπ2 g) (tameChar_pow_eq_one P hP0 hπ hπ2 hgM)
  rwa [tameChar_apply, residueHom_mk] at h

end Tame

section Reduction

/-- **A primitive root of unity stays primitive modulo a prime of residue characteristic zero.**

If the reduction had smaller order `M / d > 1`, then `ζ ^ d` would be a primitive `(M / d)`-th root
of unity congruent to `1`, and summing its powers — a vanishing geometric sum — would force
`M / d = 0` in the residue field. -/
theorem isPrimitiveRoot_quotient_mk [IsDomain S] {M : ℕ} [NeZero M] {ζ : S}
    (hζ : IsPrimitiveRoot ζ M) (P : Ideal S) [P.IsMaximal] [CharZero (S ⧸ P)] :
    IsPrimitiveRoot (Ideal.Quotient.mk P ζ) M := by
  have hone : (Ideal.Quotient.mk P ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  refine ⟨hone, fun l hl => ?_⟩
  set d := Nat.gcd l M with hd
  have hdvdM : d ∣ M := Nat.gcd_dvd_right l M
  have hdne : d ≠ 0 := fun h0 => (NeZero.ne M) (Nat.eq_zero_of_gcd_eq_zero_right h0)
  have hpow : (Ideal.Quotient.mk P ζ) ^ d = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hl) (orderOf_dvd_of_pow_eq_one hone))
  have hη : IsPrimitiveRoot (ζ ^ d) (M / d) := hζ.pow_of_dvd hdne hdvdM
  have hη1 : Ideal.Quotient.mk P (ζ ^ d) = 1 := by rw [map_pow]; exact hpow
  have hm1 : M / d = 1 := by
    have hge : 1 ≤ M / d :=
      (Nat.one_le_div_iff (Nat.pos_of_ne_zero hdne)).mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero
        (NeZero.ne M)) hdvdM)
    by_contra hne
    have h1 : 1 < M / d := lt_of_le_of_ne hge (Ne.symm hne)
    have hsum := congrArg (Ideal.Quotient.mk P) (hη.geom_sum_eq_zero h1)
    rw [map_sum, map_zero] at hsum
    simp only [map_pow, hη1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hsum
    exact absurd (Nat.cast_eq_zero.mp hsum) (by omega)
  have : M = d := by simpa using Nat.eq_mul_of_div_eq_right hdvdM hm1
  exact this ▸ Nat.gcd_dvd_left l M

end Reduction

section RatBase

/-! ## The tame character over a `ℚ`-algebra

Over a `ℚ`-algebra the order of the inertia group is invertible, so `ResidueFixed` is automatic
(`residueFixed_of_algebraRat`) and the tame theory becomes unconditional. -/

variable [Algebra ℚ S] [IsDedekindDomain S] [Finite G] [FaithfulSMul G S]

omit [IsDedekindDomain S] in
/-- The residue field at a maximal ideal of a `ℚ`-algebra has characteristic zero. -/
theorem charZero_quotient (P : Ideal S) [P.IsMaximal] : CharZero (S ⧸ P) := by
  haveI : Nontrivial (S ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr ‹P.IsMaximal›.ne_top
  exact charZero_of_injective_algebraMap (algebraMap ℚ (S ⧸ P)).injective

/-- **Inertia at a nonzero maximal ideal of a `ℚ`-algebra is cyclic.**

In residue characteristic zero all inertia is tame, and the tame character embeds it into the
multiplicative group of the residue field. -/
theorem isCyclic_inertia_of_algebraRat (P : Ideal S) [P.IsMaximal] (hP0 : P ≠ ⊥) :
    IsCyclic (P.inertia G) := by
  haveI := charZero_quotient (S := S) P
  obtain ⟨π, hπ, hπ2⟩ := exists_uniformizer P hP0
  exact isCyclic_inertia P hP0 hπ hπ2 (residueFixed_of_algebraRat P)

/-- **Fried's branch-cycle formula, with the cyclotomic exponent read off a root of unity in `S`.**

Let `ζ ∈ S` be a primitive `M`-th root of unity, `σ` an automorphism stabilizing the nonzero maximal
ideal `P` and raising `ζ` to the `c`-th power, and `g` an inertia element at `P` with `g ^ M = 1`.
Then `σ g σ⁻¹ = g ^ c`.

The tame character sends `g` to an `M`-th root of unity of the residue field; the reduction of `ζ`
is still primitive there (residue characteristic zero), so that root of unity is a power of `ζ`,
on which `σ` acts by the `c`-th power. -/
theorem conj_eq_pow_of_smul_root (P : Ideal S) [P.IsMaximal] (hP0 : P ≠ ⊥) {σ : G}
    (hσ : σ • P = P) {M : ℕ} [NeZero M] {ζ : S} (hζ : IsPrimitiveRoot ζ M) {c : ℕ}
    (hc : σ • ζ = ζ ^ c) (g : P.inertia G) (hgM : g ^ M = 1) :
    σ * (g : G) * σ⁻¹ = (g : G) ^ c := by
  haveI := charZero_quotient (S := S) P
  obtain ⟨π, hπ, hπ2⟩ := exists_uniformizer P hP0
  refine conj_eq_pow_of_cyclotomic P hP0 hπ hπ2 (residueFixed_of_algebraRat P) hσ g c ?_
  -- the residue of the tame character is an `M`-th root of unity, hence a power of `ζ` mod `P`
  set u := tameCoeff P hP0 hπ hπ2 g with hu
  have hζbar : IsPrimitiveRoot (Ideal.Quotient.mk P ζ) M := isPrimitiveRoot_quotient_mk hζ P
  have hM : (Ideal.Quotient.mk P u) ^ M = 1 := by
    have := tameChar_pow_eq_one P hP0 hπ hπ2 hgM
    rwa [tameChar_apply] at this
  obtain ⟨j, _, hj⟩ := hζbar.eq_pow_of_pow_eq_one hM
  calc Ideal.Quotient.mk P (σ • u)
      = residueHom P hσ (Ideal.Quotient.mk P u) := (residueHom_mk P hσ u).symm
    _ = residueHom P hσ (Ideal.Quotient.mk P ζ ^ j) := by rw [hj]
    _ = (Ideal.Quotient.mk P (σ • ζ)) ^ j := by rw [map_pow, residueHom_mk]
    _ = (Ideal.Quotient.mk P (ζ ^ c)) ^ j := by rw [hc]
    _ = (Ideal.Quotient.mk P u) ^ c := by
        rw [map_pow, ← pow_mul, mul_comm c j, pow_mul, hj]

end RatBase

end Rigidity.RET
