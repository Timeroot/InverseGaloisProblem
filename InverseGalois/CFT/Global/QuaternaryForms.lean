import Mathlib
import InverseGalois.CFT.Global.ExistenceGeneral
import InverseGalois.CFT.Global.HasseMinkowski
import InverseGalois.CFT.Global.RationalSquareClasses
import InverseGalois.CFT.Global.TernaryForms
import InverseGalois.CFT.Global.ThreeSquares

/-!
# The Hasse principle for diagonal quaternary forms

A diagonal form in four variables splits as a difference of two binary forms, and it is isotropic
exactly when those two binary forms have a nonzero value in common.  Being a value of a binary form
is a condition on a Hilbert symbol, so a common value is a rational number whose symbols against
two fixed rational numbers are prescribed at every place.  That is precisely the datum Serre's
existence theorem realises, the product formula needed for it being Hilbert reciprocity and the
local witnesses being supplied by the assumed local isotropy.

Concretely, write the form as `⟨a₁, a₂⟩` against `⟨-a₃, -a₄⟩` and set `d₁ = -a₁a₂`,
`d₂ = -a₃a₄`.  A nonzero `t` is a value of `⟨a₁, a₂⟩` at a place `v` exactly when
`(a₁ t, d₁)_v = 1`, that is, by bimultiplicativity, exactly when `(d₁, t)_v = (d₁, a₁)_v`;
similarly for the second form.  So the prescription to realise is that the symbol against `d₁`
match its value at `a₁` and the symbol against `d₂` match its value at `-a₃`, and the product
formula for that prescription is reciprocity applied to the pairs `(d₁, a₁)` and `(d₂, -a₃)`.

Unlike the ternary case the real place is a genuine hypothesis: the form `X² + Y² + Z² + W²` is
anisotropic there while being isotropic at every odd place.

## Main results

* `InverseGalois.CFT.Local.IsQuaternaryIsotropic`: a diagonal form in four variables represents
  zero nontrivially.
* `InverseGalois.CFT.Local.exists_repr_of_binary_isotropic`: an isotropic diagonal binary form
  with nonzero coefficients represents every element.
* `InverseGalois.CFT.Local.isQuaternaryIsotropic_iff_exists_common`: a diagonal quaternary form is
  isotropic exactly when its two halves share a nonzero value.
* `InverseGalois.CFT.isQuaternaryIsotropic_rat_of_forall_local`: **the Hasse principle for
  diagonal quaternary forms over the rational field.**
* `InverseGalois.CFT.isQuaternaryIsotropic_rat_iff_forall_local`: the same, as an equivalence.
-/

namespace InverseGalois.CFT.Local

section Isotropy

variable {K : Type*} [Field K]

/-- The diagonal quaternary form `⟨a, b, c, d⟩` over `K` is **isotropic** when it represents zero
at a point other than the origin. -/
def IsQuaternaryIsotropic (a b c d : K) : Prop :=
  ∃ x y z w : K, ¬(x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
    a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * w ^ 2 = 0

/-- **An isotropic diagonal binary form with nonzero coefficients is universal.**  Writing
`b = -a s ^ 2` for the slope `s` of a nontrivial zero, the form factors as
`a (x - s y) (x + s y)`, and the two factors may be prescribed independently. -/
theorem exists_repr_of_binary_isotropic (h2 : (2 : K) ≠ 0) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    {x₀ y₀ : K} (hne : ¬(x₀ = 0 ∧ y₀ = 0)) (h : a * x₀ ^ 2 + b * y₀ ^ 2 = 0) (c : K) :
    ∃ x y : K, c = a * x ^ 2 + b * y ^ 2 := by
  have hx₀ : x₀ ≠ 0 := by
    rintro rfl
    refine hne ⟨rfl, ?_⟩
    have hz : b * y₀ ^ 2 = 0 := by linear_combination h
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd h' hb
    · exact sq_eq_zero_iff.1 h'
  have hy₀ : y₀ ≠ 0 := by
    rintro rfl
    refine hne ⟨?_, rfl⟩
    have hz : a * x₀ ^ 2 = 0 := by linear_combination h
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd h' ha
    · exact sq_eq_zero_iff.1 h'
  have hs0 : x₀ / y₀ ≠ 0 := div_ne_zero hx₀ hy₀
  have hb' : b = -(a * (x₀ / y₀) ^ 2) := by
    field_simp
    linear_combination h
  refine ⟨(1 + c / a) / 2, (c / a - 1) / (2 * (x₀ / y₀)), ?_⟩
  rw [hb']
  field_simp
  ring

/-- **A diagonal quaternary form is isotropic exactly when its two halves share a nonzero
value.** -/
theorem isQuaternaryIsotropic_iff_exists_common (h2 : (2 : K) ≠ 0) {a b c d : K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    IsQuaternaryIsotropic a b c d ↔ ∃ t : K, t ≠ 0 ∧ (∃ x y : K, t = a * x ^ 2 + b * y ^ 2) ∧
      ∃ z w : K, t = -c * z ^ 2 + -d * w ^ 2 := by
  constructor
  · rintro ⟨x, y, z, w, hne, hxyzw⟩
    rcases eq_or_ne (a * x ^ 2 + b * y ^ 2) 0 with hzero | hzero
    · by_cases hxy : x = 0 ∧ y = 0
      · obtain ⟨rfl, rfl⟩ := hxy
        have hzw : ¬(z = 0 ∧ w = 0) := fun hzw => hne ⟨rfl, rfl, hzw.1, hzw.2⟩
        have hiso : -c * z ^ 2 + -d * w ^ 2 = 0 := by linear_combination -hxyzw
        exact ⟨a, ha, ⟨1, 0, by ring⟩,
          exists_repr_of_binary_isotropic h2 (neg_ne_zero.2 hc) (neg_ne_zero.2 hd) hzw hiso a⟩
      · exact ⟨-c, neg_ne_zero.2 hc,
          exists_repr_of_binary_isotropic h2 ha hb hxy hzero (-c), ⟨1, 0, by ring⟩⟩
    · exact ⟨a * x ^ 2 + b * y ^ 2, hzero, ⟨x, y, rfl⟩, ⟨z, w, by linear_combination hxyzw⟩⟩
  · rintro ⟨t, ht, ⟨x, y, hxy⟩, ⟨z, w, hzw⟩⟩
    refine ⟨x, y, z, w, ?_, by linear_combination hzw - hxy⟩
    rintro ⟨rfl, rfl, -, -⟩
    exact ht (by rw [hxy]; ring)

end Isotropy

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- **The Hilbert symbol only depends on the square class of its first argument.** -/
theorem hilbertSymbol_congr_of_isSquare_div_left {K : Type*} [Field K] {a u v : K} (hu : u ≠ 0)
    (hv : v ≠ 0) (h : IsSquare (u / v)) : hilbertSymbol u a = hilbertSymbol v a := by
  rw [hilbertSymbol_comm, hilbertSymbol_congr_of_isSquare_div hu hv h, hilbertSymbol_comm]

/-- **Being a value of a diagonal binary form at a finite place, read as an identity between
Hilbert symbols.**  A nonzero rational `t` is a value of `⟨α, β⟩` over `ℚ_[p]` exactly when the
symbol of `-αβ` against `t` agrees with its symbol against `α`. -/
theorem hilbertSymbolAt_eq_of_repr {p : Nat.Primes} {α β t : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (ht : t ≠ 0) (h : ∃ x y : ℚ_[(p : ℕ)], ((t : ℚ_[(p : ℕ)]))
      = ((α : ℚ_[(p : ℕ)])) * x ^ 2 + ((β : ℚ_[(p : ℕ)])) * y ^ 2) :
    hilbertSymbolAt p (-(α * β)) t = hilbertSymbolAt p (-(α * β)) α := by
  have hαp : ((α : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hα
  have hβp : ((β : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hβ
  have hd : (-(α * β) : ℚ) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hα hβ)
  have hsym : hilbertSymbolAt p (α * t) (-(α * β)) = 1 := by
    unfold hilbertSymbolAt
    rw [show (((α * t : ℚ)) : ℚ_[(p : ℕ)]) = ((α : ℚ_[(p : ℕ)])) * ((t : ℚ_[(p : ℕ)])) by
        push_cast; ring,
      show (((-(α * β) : ℚ)) : ℚ_[(p : ℕ)]) = -(((α : ℚ_[(p : ℕ)])) * ((β : ℚ_[(p : ℕ)]))) by
        push_cast; ring]
    exact (exists_repr_iff_hilbertSymbol hαp hβp).1 h
  rw [hilbertSymbolAt_mul_left' hα ht hd] at hsym
  rw [hilbertSymbolAt_comm p _ t, hilbertSymbolAt_comm p _ α]
  rcases hilbertSymbolAt_eq_one_or p α (-(α * β)) with hA | hA
  · rw [hA] at hsym ⊢
    linarith
  · rw [hA] at hsym ⊢
    linarith

/-- **The same identity at the real place.** -/
theorem hilbertSymbol_real_eq_of_repr {α β t : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (ht : t ≠ 0)
    (h : ∃ x y : ℝ, t = α * x ^ 2 + β * y ^ 2) :
    hilbertSymbol (-(α * β)) t = hilbertSymbol (-(α * β)) α := by
  have hd : (-(α * β) : ℝ) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hα hβ)
  have hsym : hilbertSymbol (α * t) (-(α * β)) = 1 := (exists_repr_iff_hilbertSymbol hα hβ).1 h
  rw [hilbertSymbol_real_mul_left _ _ _ hα ht hd] at hsym
  rw [hilbertSymbol_comm (-(α * β)) t, hilbertSymbol_comm (-(α * β)) α]
  rcases hilbertSymbol_eq_one_or α (-(α * β)) with hA | hA
  · rw [hA] at hsym ⊢
    linarith
  · rw [hA] at hsym ⊢
    linarith

/-- **The converse reading over the rational field.**  If the symbol of `-αβ` against a nonzero
rational `t` agrees with its symbol against `α` at every finite place, then `t` is a value of
`⟨α, β⟩` over the rational field. -/
theorem exists_repr_of_hilbertSymbol_eq {α β t : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0) (ht : t ≠ 0)
    (h : ∀ p : Nat.Primes,
      hilbertSymbolAt p (-(α * β)) t = hilbertSymbolAt p (-(α * β)) α) :
    ∃ x y : ℚ, t = α * x ^ 2 + β * y ^ 2 := by
  have hd : (-(α * β) : ℚ) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hα hβ)
  rw [exists_repr_iff_hilbertSymbol hα hβ]
  refine hilbertSymbol_rat_of_forall_finite (mul_ne_zero hα ht) hd fun p => ?_
  rw [hilbertSymbolAt_mul_left' hα ht hd, hilbertSymbolAt_comm p α, hilbertSymbolAt_comm p t, h p]
  rcases hilbertSymbolAt_eq_one_or p (-(α * β)) α with hA | hA
  · rw [hA]
    norm_num
  · rw [hA]
    norm_num

/-- **The Hasse principle for diagonal quaternary forms over the rational field.**  A diagonal
form in four variables with a nontrivial zero at every place, the real place included, has a
nontrivial rational zero. -/
theorem isQuaternaryIsotropic_rat_of_forall_local {a₁ a₂ a₃ a₄ : ℚ} (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0)
    (h3 : a₃ ≠ 0) (h4 : a₄ ≠ 0)
    (hloc : ∀ p : Nat.Primes, IsQuaternaryIsotropic ((a₁ : ℚ_[(p : ℕ)])) ((a₂ : ℚ_[(p : ℕ)]))
      ((a₃ : ℚ_[(p : ℕ)])) ((a₄ : ℚ_[(p : ℕ)])))
    (hreal : IsQuaternaryIsotropic ((a₁ : ℝ)) ((a₂ : ℝ)) ((a₃ : ℝ)) ((a₄ : ℝ))) :
    IsQuaternaryIsotropic a₁ a₂ a₃ a₄ := by
  classical
  have hn3 : (-a₃ : ℚ) ≠ 0 := neg_ne_zero.2 h3
  have hn4 : (-a₄ : ℚ) ≠ 0 := neg_ne_zero.2 h4
  set d₁ : ℚ := -(a₁ * a₂) with hd₁def
  set d₂ : ℚ := -(-a₃ * -a₄) with hd₂def
  have hd₁ : d₁ ≠ 0 := neg_ne_zero.2 (mul_ne_zero h1 h2)
  have hd₂ : d₂ ≠ 0 := neg_ne_zero.2 (mul_ne_zero hn3 hn4)
  set T : Finset Nat.Primes := (finite_mulSupport_hilbertSymbolAt hd₁ h1).toFinset ∪
    (finite_mulSupport_hilbertSymbolAt hd₂ hn3).toFinset with hTdef
  have hTa : ∀ p ∉ T, hilbertSymbolAt p d₁ a₁ = 1 := by
    intro p hp
    by_contra hne
    exact hp (by
      rw [hTdef]
      exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 hne))
  have hTb : ∀ p ∉ T, hilbertSymbolAt p d₂ (-a₃) = 1 := by
    intro p hp
    by_contra hne
    exact hp (by
      rw [hTdef]
      exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hne))
  have hproda : hilbertSymbol ((d₁ : ℝ)) ((a₁ : ℝ)) * ∏ p ∈ T, hilbertSymbolAt p d₁ a₁ = 1 := by
    have hrec := hilbertProduct_eq_one hd₁ h1
    rwa [hilbertProduct_eq_prod_of_subset _ _ T hTa] at hrec
  have hprodb :
      hilbertSymbol ((d₂ : ℝ)) (((-a₃ : ℚ) : ℝ)) * ∏ p ∈ T, hilbertSymbolAt p d₂ (-a₃) = 1 := by
    have hrec := hilbertProduct_eq_one hd₂ hn3
    rwa [hilbertProduct_eq_prod_of_subset _ _ T hTb] at hrec
  have hlocp : ∀ p : Nat.Primes, ∃ w : ℚ, w ≠ 0 ∧
      hilbertSymbolAt p d₁ w = hilbertSymbolAt p d₁ a₁ ∧
      hilbertSymbolAt p d₂ w = hilbertSymbolAt p d₂ (-a₃) := by
    intro p
    have hp1 : ((a₁ : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using h1
    have hp2 : ((a₂ : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using h2
    have hp3 : ((a₃ : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using h3
    have hp4 : ((a₄ : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using h4
    obtain ⟨t, ht, hta, htb⟩ :=
      (isQuaternaryIsotropic_iff_exists_common (by norm_num) hp1 hp2 hp3 hp4).1 (hloc p)
    obtain ⟨w, hw0, hwsq⟩ := exists_rat_isSquare_div ht
    have hwp : ((w : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hw0
    obtain ⟨c, hc⟩ := hwsq
    rw [div_eq_iff hwp] at hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_mul] at hc
      exact ht hc
    have hwt : ((w : ℚ_[(p : ℕ)])) = t * c⁻¹ ^ 2 := by
      field_simp
      linear_combination -hc
    refine ⟨w, hw0, ?_, ?_⟩
    · refine hilbertSymbolAt_eq_of_repr h1 h2 hw0 ?_
      obtain ⟨x, y, hxy⟩ := hta
      exact ⟨x * c⁻¹, y * c⁻¹, by rw [hwt, hxy]; ring⟩
    · refine hilbertSymbolAt_eq_of_repr hn3 hn4 hw0 ?_
      obtain ⟨z, y, hzy⟩ := htb
      refine ⟨z * c⁻¹, y * c⁻¹, ?_⟩
      push_cast
      rw [hwt, hzy]
      ring
  have hlocr : ∃ w : ℚ, w ≠ 0 ∧
      hilbertSymbol ((d₁ : ℝ)) ((w : ℝ)) = hilbertSymbol ((d₁ : ℝ)) ((a₁ : ℝ)) ∧
      hilbertSymbol ((d₂ : ℝ)) ((w : ℝ)) = hilbertSymbol ((d₂ : ℝ)) (((-a₃ : ℚ) : ℝ)) := by
    have hr1 : ((a₁ : ℝ)) ≠ 0 := by exact_mod_cast h1
    have hr2 : ((a₂ : ℝ)) ≠ 0 := by exact_mod_cast h2
    have hr3 : ((a₃ : ℝ)) ≠ 0 := by exact_mod_cast h3
    have hr4 : ((a₄ : ℝ)) ≠ 0 := by exact_mod_cast h4
    obtain ⟨t, ht, hta, htb⟩ :=
      (isQuaternaryIsotropic_iff_exists_common (by norm_num) hr1 hr2 hr3 hr4).1 hreal
    have hcd₁ : ((d₁ : ℝ)) = -(((a₁ : ℝ)) * ((a₂ : ℝ))) := by
      rw [hd₁def]
      push_cast
      ring
    have hcd₂ : ((d₂ : ℝ)) = -((-((a₃ : ℝ))) * (-((a₄ : ℝ)))) := by
      rw [hd₂def]
      push_cast
      ring
    have hn3r : ((((-a₃ : ℚ)) : ℝ)) = -((a₃ : ℝ)) := by push_cast; ring
    by_cases hpos : 0 < t
    · have hw0 : ((1 : ℚ)) ≠ 0 := one_ne_zero
      have hwsq : IsSquare (t / ((((1 : ℚ)) : ℝ))) := by
        rw [show ((((1 : ℚ)) : ℝ)) = 1 by norm_num, div_one]
        exact (isSquare_real_iff t).2 hpos.le
      have hwr : ((((1 : ℚ)) : ℝ)) ≠ 0 := by norm_num
      refine ⟨1, hw0, ?_, ?_⟩
      · rw [hcd₁, ← hilbertSymbol_congr_of_isSquare_div ht hwr hwsq]
        exact hilbertSymbol_real_eq_of_repr hr1 hr2 ht hta
      · rw [hcd₂, hn3r, ← hilbertSymbol_congr_of_isSquare_div ht hwr hwsq]
        exact hilbertSymbol_real_eq_of_repr (neg_ne_zero.2 hr3) (neg_ne_zero.2 hr4) ht htb
    · have hw0 : ((-1 : ℚ)) ≠ 0 := by norm_num
      have hwsq : IsSquare (t / ((((-1 : ℚ)) : ℝ))) := by
        rw [show ((((-1 : ℚ)) : ℝ)) = -1 by norm_num, div_neg, div_one]
        exact (isSquare_real_iff (-t)).2 (by linarith [not_lt.1 hpos])
      have hwr : ((((-1 : ℚ)) : ℝ)) ≠ 0 := by norm_num
      refine ⟨-1, hw0, ?_, ?_⟩
      · rw [hcd₁, ← hilbertSymbol_congr_of_isSquare_div ht hwr hwsq]
        exact hilbertSymbol_real_eq_of_repr hr1 hr2 ht hta
      · rw [hcd₂, hn3r, ← hilbertSymbol_congr_of_isSquare_div ht hwr hwsq]
        exact hilbertSymbol_real_eq_of_repr (neg_ne_zero.2 hr3) (neg_ne_zero.2 hr4) ht htb
  obtain ⟨x, hx0, hxa, hxb, -, -⟩ :=
    exists_rat_hilbert_prescribed_two' hd₁ hd₂
      (fun p => hilbertSymbolAt p d₁ a₁) (fun p => hilbertSymbolAt p d₂ (-a₃))
      (hilbertSymbol ((d₁ : ℝ)) ((a₁ : ℝ))) (hilbertSymbol ((d₂ : ℝ)) (((-a₃ : ℚ) : ℝ)))
      T hTa hTb hproda hprodb hlocp hlocr
  refine (isQuaternaryIsotropic_iff_exists_common (by norm_num) h1 h2 h3 h4).2 ⟨x, hx0, ?_, ?_⟩
  · exact exists_repr_of_hilbertSymbol_eq h1 h2 hx0 fun p => hxa p
  · exact exists_repr_of_hilbertSymbol_eq hn3 hn4 hx0 fun p => hxb p

/-- **The Hasse principle for diagonal quaternary forms, as an equivalence.** -/
theorem isQuaternaryIsotropic_rat_iff_forall_local {a₁ a₂ a₃ a₄ : ℚ} (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0)
    (h3 : a₃ ≠ 0) (h4 : a₄ ≠ 0) :
    IsQuaternaryIsotropic a₁ a₂ a₃ a₄ ↔
      (∀ p : Nat.Primes, IsQuaternaryIsotropic ((a₁ : ℚ_[(p : ℕ)])) ((a₂ : ℚ_[(p : ℕ)]))
        ((a₃ : ℚ_[(p : ℕ)])) ((a₄ : ℚ_[(p : ℕ)]))) ∧
      IsQuaternaryIsotropic ((a₁ : ℝ)) ((a₂ : ℝ)) ((a₃ : ℝ)) ((a₄ : ℝ)) := by
  constructor
  · rintro ⟨x, y, z, w, hne, hxyzw⟩
    constructor
    · intro p
      refine ⟨((x : ℚ_[(p : ℕ)])), ((y : ℚ_[(p : ℕ)])), ((z : ℚ_[(p : ℕ)])),
        ((w : ℚ_[(p : ℕ)])), ?_, ?_⟩
      · rintro ⟨hx, hy, hz, hw⟩
        exact hne ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz,
          by exact_mod_cast hw⟩
      · have hcast := congrArg (fun q : ℚ => ((q : ℚ_[(p : ℕ)]))) hxyzw
        push_cast at hcast
        linear_combination hcast
    · refine ⟨((x : ℝ)), ((y : ℝ)), ((z : ℝ)), ((w : ℝ)), ?_, ?_⟩
      · rintro ⟨hx, hy, hz, hw⟩
        exact hne ⟨by exact_mod_cast hx, by exact_mod_cast hy, by exact_mod_cast hz,
          by exact_mod_cast hw⟩
      · have hcast := congrArg (fun q : ℚ => ((q : ℝ))) hxyzw
        push_cast at hcast
        linear_combination hcast
  · rintro ⟨hloc, hreal⟩
    exact isQuaternaryIsotropic_rat_of_forall_local h1 h2 h3 h4 hloc hreal

end InverseGalois.CFT
