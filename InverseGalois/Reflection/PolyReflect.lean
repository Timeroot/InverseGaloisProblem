/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A computable reflection tactic for polynomial identities

The D₅ resolvent development needs a large number of *polynomial identities* in a handful
of variables over an arbitrary commutative ring, e.g.

```
(prod of pentagonal squares) = (explicit degree-20 polynomial).
```

This file provides a *computable* alternative.  We reflect a ring expression into a small
inductive type `RE`, give it a computable multivariate-polynomial normal form `toNF`
(a sorted association list of monomials), and prove the soundness lemma

```
eval_toNF : e.eval ρ = evalNF ρ (toNF e).
```

To prove an identity `P = Q` it then suffices to:

* exhibit reflections `e₁, e₂ : RE` with `e₁.eval ρ` (resp. `e₂.eval ρ`) *definitionally
  equal* to `P` (resp. `Q`) — this holds by construction when the reflections mirror the
  syntax of `P` and `Q`, so the bridge is closed by `simp only [RE.eval]`;
* check `toNF e₁ = toNF e₂` by `native_decide`, which runs as compiled code on the
  association-list normal forms and is essentially instantaneous.

The helper `eval_eq_of_toNF` packages this up.  See `PentagonalSumCertificates` for the consumers. -/

namespace PolyReflect

/-- A reflected commutative-ring expression in variables `atom 0, atom 1, …`. -/
inductive RE where
  | atom : ℕ → RE
  | lit : ℤ → RE
  | add : RE → RE → RE
  | sub : RE → RE → RE
  | mul : RE → RE → RE
  | neg : RE → RE
  | pow : RE → ℕ → RE
deriving Repr, DecidableEq

variable {R : Type*} [CommRing R]

/-- Evaluate a reflected expression at an assignment `ρ` of the atoms. -/
def RE.eval (ρ : ℕ → R) : RE → R
  | atom i => ρ i
  | lit n => (n : R)
  | add a b => a.eval ρ + b.eval ρ
  | sub a b => a.eval ρ - b.eval ρ
  | mul a b => a.eval ρ * b.eval ρ
  | neg a => - a.eval ρ
  | pow a n => (a.eval ρ) ^ n

/-- A monomial: a list of `(variable, exponent)` pairs (kept sorted, exponents `> 0`). -/
abbrev Mono := List (ℕ × ℕ)
/-- A normal form: a list of `(monomial, coefficient)` pairs (kept sorted, coeffs `≠ 0`). -/
abbrev NF := List (Mono × ℤ)

/-- Multiply two monomials by merging their (sorted) exponent lists. -/
def monoMul : Mono → Mono → Mono
  | [], m => m
  | m, [] => m
  | (i,a)::s, (j,b)::t =>
      if i < j then (i,a) :: monoMul s ((j,b)::t)
      else if j < i then (j,b) :: monoMul ((i,a)::s) t
      else (i, a+b) :: monoMul s t

/-- A strict total order on monomials (lexicographic on the sorted exponent lists). -/
def monoLt : Mono → Mono → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | (i,a)::s, (j,b)::t =>
      if i < j then true else if j < i then false
      else if a < b then true else if b < a then false else monoLt s t

/-- Insert the term `c · m` into a normal form, combining like monomials. -/
def nfInsert (m : Mono) (c : ℤ) : NF → NF
  | [] => if c = 0 then [] else [(m, c)]
  | (m', c') :: rest =>
      if m = m' then
        let c'' := c + c'
        if c'' = 0 then rest else (m', c'') :: rest
      else if monoLt m m' then
        if c = 0 then (m',c')::rest else (m, c) :: (m', c') :: rest
      else (m', c') :: nfInsert m c rest

/-- Add two normal forms by a linear merge of the two sorted association lists.

This is `O(|f| + |g|)`, whereas the earlier insertion-based `nfAdd` (folding `nfInsert`
over `f`) was `O(|f| · |g|)`.  Crucially for soundness, the evaluation lemma
`evalNF_nfAdd` holds *unconditionally* (no sortedness hypothesis): at each step the merge
emits exactly one head term and recurses on the rest, and the only place it combines two
terms is when the monomials are syntactically equal, where `c · m + c' · m = (c+c') · m`.
Sortedness is what makes the *runtime* result canonical (so the `native_decide` check
`toNF e = []` succeeds), but it is never needed in the proof. -/
def nfAdd : NF → NF → NF
  | [], g => g
  | f, [] => f
  | (m,c)::f, (m',c')::g =>
      if m = m' then
        let c'' := c + c'
        if c'' = 0 then nfAdd f g else (m, c'') :: nfAdd f g
      else if monoLt m m' then (m, c) :: nfAdd f ((m',c')::g)
      else (m', c') :: nfAdd ((m,c)::f) g
  termination_by f g => f.length + g.length

/-- Multiply a single term `c · m` into a normal form. -/
def nfMulMono (m : Mono) (c : ℤ) (g : NF) : NF :=
  g.foldr (fun p acc => nfInsert (monoMul m p.1) (c * p.2) acc) []

/-- Multiply each term of `f` into `g`, accumulating with `nfAdd`. -/
def nfMulL (f g : NF) : NF :=
  f.foldr (fun p acc => nfAdd (nfMulMono p.1 p.2 g) acc) []

/-- Multiply two normal forms.  We fold over the *longer* operand and multiply each of its
monomials into the *shorter* one, so the per-monomial `nfMulMono` work (which is quadratic
in the length of its `NF` argument) is always paid on the shorter list.  This is a
substantial speedup whenever one factor is much smaller than the other (e.g. multiplying a
dense degree-20 polynomial by a sparse ideal generator). -/
def nfMul (f g : NF) : NF :=
  if f.length ≤ g.length then nfMulL g f else nfMulL f g

/-- Negate a normal form. -/
def nfNeg (f : NF) : NF := f.map (fun p => (p.1, -p.2))

/-- Raise a normal form to a power. -/
def nfPow (base : NF) : ℕ → NF
  | 0 => [([],1)]
  | (k+1) => nfMul base (nfPow base k)

/-- The computable normal form of a reflected expression. -/
def toNF : RE → NF
  | RE.atom i => [([(i,1)], 1)]
  | RE.lit n => if n = 0 then [] else [([], n)]
  | RE.add a b => nfAdd (toNF a) (toNF b)
  | RE.sub a b => nfAdd (toNF a) (nfNeg (toNF b))
  | RE.mul a b => nfMul (toNF a) (toNF b)
  | RE.neg a => nfNeg (toNF a)
  | RE.pow a k => nfPow (toNF a) k

/-- Evaluate a monomial. -/
def evalMono (ρ : ℕ → R) (m : Mono) : R := (m.map (fun p => (ρ p.1) ^ p.2)).prod
/-- Evaluate a normal form. -/
def evalNF (ρ : ℕ → R) (f : NF) : R := (f.map (fun p => (p.2 : R) * evalMono ρ p.1)).sum

@[simp] theorem evalNF_nil (ρ : ℕ → R) : evalNF ρ [] = 0 := rfl

theorem evalMono_monoMul (ρ : ℕ → R) (m m' : Mono) :
    evalMono ρ (monoMul m m') = evalMono ρ m * evalMono ρ m' := by
      induction' m with i a m ih generalizing m'
      · induction m' <;> simp [*, monoMul]
        all_goals simp [evalMono]
      · induction' m' with j b m' ih'
        · simp [monoMul, evalMono]
        · unfold monoMul
          split_ifs <;> simp_all [evalMono]
          · ring
          · ring
          · grind

theorem evalNF_nfInsert (ρ : ℕ → R) (m : Mono) (c : ℤ) (f : NF) :
    evalNF ρ (nfInsert m c f) = (c : R) * evalMono ρ m + evalNF ρ f := by
      induction' f with f_head f_tail ih generalizing m c
      · by_cases hc : c = 0 <;> simp [hc, evalNF, evalMono, nfInsert]
      · by_cases hm : m = f_head.1 <;> simp_all [nfInsert]
        · split_ifs <;> simp_all [evalNF]
          · simp_all [← add_assoc, ← eq_sub_iff_add_eq']
          · ring
        · split_ifs <;> simp_all [evalNF]
          ring

theorem evalNF_nfAdd (ρ : ℕ → R) (f g : NF) :
    evalNF ρ (nfAdd f g) = evalNF ρ f + evalNF ρ g := by
  induction' n : f.length + g.length using Nat.strong_induction_on with n ih generalizing f g
  rcases f with (_ | ⟨m, c⟩) <;> rcases g with (_ | ⟨m', c'⟩) <;> simp_all
  · unfold nfAdd
    simp [evalNF]
  · unfold nfAdd
    subst n
    simp_all only [Order.lt_add_one_iff]
  · unfold nfAdd
    subst n
    simp_all only [Order.lt_add_one_iff]
  · unfold nfAdd
    split_ifs <;> simp_all [evalNF]
    · split_ifs <;> simp_all [add_assoc]
      · rw [ih _ (by linarith) _ _ rfl]
        rw [show m.2 = -m'.2 by linarith]
        simp
        ring
      · rw [ih _ (by linarith) _ _ rfl]
        ring
    · grind
    · grind

theorem evalNF_nfMulMono (ρ : ℕ → R) (m : Mono) (c : ℤ) (g : NF) :
    evalNF ρ (nfMulMono m c g) = (c : R) * evalMono ρ m * evalNF ρ g := by
      unfold nfMulMono
      induction' g with p g ih
      · simp [evalNF]
      · simp [evalNF_nfInsert, evalMono_monoMul, ih]
        simp [evalNF, List.map_cons, List.sum_cons]
        ring

theorem evalNF_nfMulL (ρ : ℕ → R) (f g : NF) :
    evalNF ρ (nfMulL f g) = evalNF ρ f * evalNF ρ g := by
      -- We'll use induction on `f`.
      induction' f with m c f ih generalizing g
      · simp [nfMulL]
      · have h_fold : evalNF ρ (nfMulL (m :: c) g) = ((m.2 : R) * evalMono ρ m.1 + evalNF ρ c) * evalNF ρ g := by
          convert congr_arg₂ (· + ·) (evalNF_nfMulMono ρ m.1 m.2 g) (f g) using 1
          · convert evalNF_nfAdd ρ (nfMulMono m.1 m.2 g) (nfMulL c g) using 1
          · ring
        convert h_fold using 1

theorem evalNF_nfMul (ρ : ℕ → R) (f g : NF) :
    evalNF ρ (nfMul f g) = evalNF ρ f * evalNF ρ g := by
      unfold nfMul
      split
      · rw [evalNF_nfMulL, mul_comm]
      · rw [evalNF_nfMulL]

theorem evalNF_nfNeg (ρ : ℕ → R) (f : NF) :
    evalNF ρ (nfNeg f) = - evalNF ρ f := by
      unfold evalNF
      unfold nfNeg
      simp [List.sum_neg]
      congr! 2
      ext
      simp

theorem evalNF_nfPow (ρ : ℕ → R) (base : NF) (k : ℕ) :
    evalNF ρ (nfPow base k) = (evalNF ρ base) ^ k := by
      induction' k with k ih <;> simp_all [pow_succ]
      · unfold nfPow
        simp [evalNF, evalMono]
      · convert evalNF_nfMul ρ base (nfPow base k) using 1
        rw [ih, mul_comm]

/-
**Soundness**: evaluating a reflected expression agrees with evaluating its normal form.
-/
theorem eval_toNF (ρ : ℕ → R) (e : RE) : e.eval ρ = evalNF ρ (toNF e) := by
  induction e with
  | atom i => simp [RE.eval, toNF, evalNF, evalMono]
  | lit n =>
      simp only [RE.eval, toNF]
      by_cases hn : n = 0 <;> simp [hn, evalNF, evalMono]
  | add a b ha hb => rw [RE.eval, toNF, evalNF_nfAdd, ha, hb]
  | sub a b ha hb => rw [RE.eval, toNF, evalNF_nfAdd, evalNF_nfNeg, ha, hb, sub_eq_add_neg]
  | mul a b ha hb => rw [RE.eval, toNF, evalNF_nfMul, ha, hb]
  | neg a ha => rw [RE.eval, toNF, evalNF_nfNeg, ha]
  | pow a k ha => rw [RE.eval, toNF, evalNF_nfPow, ha]

/-- If two reflected expressions have the same normal form, they evaluate equally in any
commutative ring. -/
theorem eval_eq_of_toNF (ρ : ℕ → R) (e1 e2 : RE) (h : toNF e1 = toNF e2) :
    e1.eval ρ = e2.eval ρ := by
  rw [eval_toNF ρ e1, eval_toNF ρ e2, h]

/-! ### Parsing a normal form from a compact string literal

Since the cofactors are only ever multiplied by an ideal generator that vanishes (their
`evalNF` is killed by `mul_zero`), their *value* is irrelevant to soundness — we never prove
anything about them.  We can therefore store them as a single compact **string literal**
(which the elaborator handles in one step) and decode them to an `NF` at `native_decide`
time with the computable parser below.  Correctness of the parse is checked *computationally*
by the `native_decide` certificate (if the string decodes to the wrong cofactor, the
certificate simply fails to reduce to `[]`); no lemma about `parseNF` is needed.

Format: terms are separated by `'|'`; within a term, whitespace-separated tokens are the
integer coefficient followed by alternating `variable exponent` pairs.  E.g.
`"-2 0 9 1 1|106 3 1"` denotes `-2·x₀⁹·x₁ + 106·x₃`. -/
def parseMono : List String → Mono
  | v :: e :: rest => (v.toNat?.getD 0, e.toNat?.getD 0) :: parseMono rest
  | _ => []

/-- Parse a single term `"coeff v e v e …"` into a `(monomial, coefficient)` pair. -/
def parseTerm (s : String) : Mono × ℤ :=
  match s.splitOn " " with
  | c :: rest => (parseMono rest, (c.toInt?).getD 0)
  | [] => ([], 0)

/-- Decode a compact string literal into a normal form (see the module note above). -/
def parseNF (s : String) : NF := (s.splitOn "|").map parseTerm

/-- Evaluate a checked two-generator ideal-membership certificate.

The pentagonal-sum identities all use the same argument: the normal form of
`lhs - rhs - (cof₂ * gen₂ + cof₃ * gen₃)` is empty, and both generators vanish.
Keeping that argument here avoids repeating the normal-form evaluation plumbing in every
coefficient identity. -/
theorem eval_eq_of_two_generator_certificate
    (ρ : ℕ → R) (lhs rhs gen₂ gen₃ : RE) (cof₂ cof₃ : NF)
    (hcert :
      nfAdd (toNF (.sub lhs rhs))
        (nfNeg (nfAdd (nfMul cof₂ (toNF gen₂)) (nfMul cof₃ (toNF gen₃)))) = [])
    (hgen₂ : gen₂.eval ρ = 0) (hgen₃ : gen₃.eval ρ = 0) :
    lhs.eval ρ = rhs.eval ρ := by
  have hev :
      evalNF ρ
        (nfAdd (toNF (.sub lhs rhs))
          (nfNeg (nfAdd (nfMul cof₂ (toNF gen₂)) (nfMul cof₃ (toNF gen₃))))) = 0 := by
    rw [hcert]
    rfl
  rw [evalNF_nfAdd, evalNF_nfNeg, evalNF_nfAdd, evalNF_nfMul, evalNF_nfMul,
      ← eval_toNF, ← eval_toNF, ← eval_toNF, hgen₂, hgen₃, mul_zero, mul_zero] at hev
  simpa only [RE.eval, add_zero, neg_zero, sub_eq_zero] using hev

end PolyReflect