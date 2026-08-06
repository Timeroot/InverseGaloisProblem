/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Rigidity certificates (group-theoretic data)

This file defines the **rigidity certificate** for a finite group `G`: the finite, checkable
group-theoretic data that — via the Riemann Existence Theorem (isolated as an axiom in
`InverseGalois.Rigidity.RET.Existence`) — witnesses that `G` is realizable as a Galois group
over `ℚ`.

A certificate packages a tuple of conjugacy classes `C₁,…,C_r` that are

* **rational** (`IsRationalClass`): closed under `g ↦ gᵏ` for `k` coprime to `orderOf g`;
* **generating with product one** (`rigidTuples` nonempty): there is a tuple `(g₁,…,g_r)` with
  `gᵢ ∈ Cᵢ`, `∏ gᵢ = 1`, and `⟨g₁,…,g_r⟩ = G`;
* **rigid** (structure constant `= 1`): there are exactly `|G|` such generating product-one
  tuples — equivalently they form a single simultaneous-conjugacy orbit (proved in
  `InverseGalois.Rigidity.StructureConstant`), the group being centerless.

## Main definitions

* `IsRationalClass c` — the conjugacy class `c` is rational.
* `rigidTuples C` — the set of generating product-one tuples in the prescribed classes.
* `RigidityCertificate G` — the bundled certificate.

## Main results (soundness, axiom-free)

* `isRationalClass_iff_bounded` — the rationality condition only needs to be checked for
  `k < orderOf g`, making it decidable and `decide`-friendly for concrete groups.
* `center_triv_iff_center_eq_bot` — the stored centerless condition is `Subgroup.center G = ⊥`.
-/

open scoped BigOperators

variable {G : Type*} [Group G]

/-- A conjugacy class `c` is **rational** if it is closed under `g ↦ g ^ k` for every natural
number `k` coprime to `orderOf g`.  Equivalently `c` is fixed by the Galois action of
`(ZMod (exponent G))ˣ` permuting conjugacy classes; that reformulation is what lets the branch
cycle argument descend the cover's field of definition to `ℚ`. -/
def IsRationalClass (c : ConjClasses G) : Prop :=
  ∀ g : G, ConjClasses.mk g = c → ∀ k : ℕ, Nat.Coprime k (orderOf g) →
    ConjClasses.mk (g ^ k) = c

/-- The **decidable** form of rationality: it suffices to check `k < orderOf g`.  For a concrete
finite group this is a genuine `Fintype`/`Nat.decidableBallLT` decision, so it closes by
`decide` / `native_decide`. -/
def IsRationalClassBounded (c : ConjClasses G) : Prop :=
  ∀ g : G, ConjClasses.mk g = c → ∀ k : ℕ, k < orderOf g → Nat.Coprime k (orderOf g) →
    ConjClasses.mk (g ^ k) = c

/-- Rationality only needs to be checked on the finite range `k < orderOf g`: the two forms
agree, because `g ^ k` depends only on `k % orderOf g` and coprimality is preserved mod
`orderOf g`. -/
theorem isRationalClass_iff_bounded {c : ConjClasses G} :
    IsRationalClass c ↔ IsRationalClassBounded c := by
  refine ⟨fun h g hg k _ hk => h g hg k hk, fun h g hg k hk => ?_⟩
  rcases eq_or_ne (orderOf g) 0 with h0 | h0
  · -- `orderOf g = 0` forces `k = 0` in a coprime pair, and `g ^ 0 = g` up to the class of `g`.
    simp only [h0, Nat.coprime_zero_right] at hk
    subst hk
    simpa using hg
  · have hpos : 0 < orderOf g := Nat.pos_of_ne_zero h0
    have hmod : k % orderOf g < orderOf g := Nat.mod_lt _ hpos
    have hcop : Nat.Coprime (k % orderOf g) (orderOf g) := by
      show Nat.gcd (k % orderOf g) (orderOf g) = 1
      rw [← Nat.gcd_rec, Nat.gcd_comm]
      exact hk
    have := h g hg (k % orderOf g) hmod hcop
    rwa [pow_mod_orderOf] at this

/-- The set of tuples `(g₁,…,g_r)` with `gᵢ` in the prescribed class `Cᵢ`, whose product is `1`,
and which generate `G`.  Rigidity is the statement that this set has exactly `|G|` elements. -/
def rigidTuples {r : ℕ} (C : Fin r → ConjClasses G) : Set (Fin r → G) :=
  { g | (∀ i, ConjClasses.mk (g i) = C i) ∧ (List.ofFn g).prod = 1 ∧
        Subgroup.closure (Set.range g) = ⊤ }

/-- A **rigidity certificate** for a finite group `G`: rational conjugacy classes admitting a
unique (up to simultaneous conjugation) generating product-one tuple, the group being centerless.

Together with the Riemann Existence Theorem (`InverseGalois.Rigidity.RET.Existence`) this data
proves `IsInverseGalois G` — see `Rigidity.rigidity_realizable`. -/
structure RigidityCertificate (G : Type*) [Group G] [Finite G] where
  /-- the number of prescribed classes (branch points). -/
  r : ℕ
  /-- the prescribed conjugacy classes `C₁,…,C_r`. -/
  C : Fin r → ConjClasses G
  /-- `G` is centerless (trivial center). -/
  center_triv : ∀ g : G, g ∈ Subgroup.center G → g = 1
  /-- each class is rational. -/
  rational : ∀ i, IsRationalClass (C i)
  /-- there is at least one generating product-one tuple in the prescribed classes. -/
  gen : (rigidTuples C).Nonempty
  /-- **rigidity**: exactly `|G|` such tuples (structure constant `= 1`). -/
  rigid : Nat.card (rigidTuples C) = Nat.card G

/-- The stored centerless condition is exactly `Subgroup.center G = ⊥`. -/
theorem center_triv_iff_center_eq_bot :
    (∀ g : G, g ∈ Subgroup.center G → g = 1) ↔ Subgroup.center G = ⊥ :=
  Subgroup.eq_bot_iff_forall _ |>.symm
