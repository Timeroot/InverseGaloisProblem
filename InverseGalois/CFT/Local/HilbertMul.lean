import Mathlib
import InverseGalois.CFT.Local.HilbertSymbol
import InverseGalois.CFT.Brauer.QuadraticExt

/-!
# The Hilbert symbol and the norm subgroup of a quadratic extension

For a non-square `b` in a field `K`, the Hilbert symbol `⟨a, b⟩` is `1` exactly when the unit `a`
belongs to the group `N` of norms from `K(√b)`, so the symbol is the indicator of a subgroup of
`Kˣ`.  This file records that dictionary and draws its consequences: the symbol only depends on
the coset of `a` modulo `N`, it is unchanged by inversion, the elements of symbol `1` are closed
under multiplication, and the relative Brauer group `Br(K(√b) / K)` vanishes exactly when the
symbol `⟨a, b⟩` is `1` for every nonzero `a`.

Over a general field the symbol is *not* multiplicative in its arguments: multiplicativity is
equivalent to the norm group having index at most two in `Kˣ`, which is a genuinely arithmetic
input.  Accordingly the bimultiplicativity statements below carry the hypothesis that
`N` has index two, under which the symbol becomes a group homomorphism `Kˣ →* ℤˣ`.

## Main results

* `InverseGalois.CFT.Local.hilbertSymbol_mul_of_eq_one`: the elements of symbol `1` are closed
  under multiplication, by the composition law of the binary norm form.
* `InverseGalois.CFT.Local.hilbertSymbol_inv_left`,
  `InverseGalois.CFT.Local.hilbertSymbol_inv_right`: the symbol is invariant under inversion.
* `InverseGalois.CFT.Local.hilbertSymbol_mul_left_of_eq_one`,
  `InverseGalois.CFT.Local.hilbertSymbol_mul_right_of_eq_one`: multiplying an argument by an
  element of symbol `1` leaves the symbol unchanged.
* `InverseGalois.CFT.Local.mem_normSubgroup_sqrtExt_iff_hilbertSymbol`: **the dictionary**, a unit
  is a norm from `K(√b)` exactly when its Hilbert symbol against `b` is `1`.
* `InverseGalois.CFT.Local.sq_mem_normSubgroup_sqrtExt`: squares are norms.
* `InverseGalois.CFT.Local.hilbertSymbol_mul_left_of_index_two`,
  `InverseGalois.CFT.Local.hilbertSymbol_mul_right_of_index_two`: **bimultiplicativity** for a
  norm group of index two.
* `InverseGalois.CFT.Local.hilbertHom`, `InverseGalois.CFT.Local.coe_hilbertHom` and
  `InverseGalois.CFT.Local.ker_hilbertHom`: the symbol as a homomorphism `Kˣ →* ℤˣ` with kernel
  the norm group.
* `InverseGalois.CFT.Local.relative_sqrtExt_eq_bot_iff_forall_hilbertSymbol`: **the bridge to the
  Brauer group**, `Br(K(√b) / K) = ⊥` exactly when every nonzero element of `K` has symbol `1`
  against `b`.

## Tags

Hilbert symbol, norm group, quadratic extension, Brauer group
-/

open Polynomial

namespace InverseGalois.CFT.Local

/-! ### Elementary properties of the set of symbols equal to one -/

section Elementary

variable {K : Type*} [Field K]

/-- **The composition law of the binary norm form.**  If `a` and `a'` both have Hilbert symbol
`1` against `b`, then so does their product: writing `a = u ^ 2 - b * v ^ 2` and
`a' = u' ^ 2 - b * v' ^ 2`, the product is `w ^ 2 - b * t ^ 2` for
`w = u * u' + b * (v * v')` and `t = u * v' + u' * v`. -/
theorem hilbertSymbol_mul_of_eq_one {a a' b : K} (h : hilbertSymbol a b = 1)
    (h' : hilbertSymbol a' b = 1) : hilbertSymbol (a * a') b = 1 := by
  by_cases hb : IsSquare b
  · exact hilbertSymbol_of_isSquare_right _ _ hb
  · rw [hilbertSymbol_eq_one_iff_exists_sub_sq hb] at h h' ⊢
    obtain ⟨u, v, rfl⟩ := h
    obtain ⟨u', v', rfl⟩ := h'
    exact ⟨u * u' + b * (v * v'), u * v' + u' * v, by ring⟩

/-- **The Hilbert symbol is invariant under inverting its first argument**, since `a⁻¹` differs
from `a` by the square `(a⁻¹) ^ 2`. -/
theorem hilbertSymbol_inv_left (a b : K) (ha : a ≠ 0) :
    hilbertSymbol a⁻¹ b = hilbertSymbol a b := by
  have h : a * a⁻¹ ^ 2 = a⁻¹ := by
    field_simp
  rw [← h, hilbertSymbol_mul_sq_left a b a⁻¹ (inv_ne_zero ha)]

/-- **The Hilbert symbol is invariant under inverting its second argument.** -/
theorem hilbertSymbol_inv_right (a b : K) (hb : b ≠ 0) :
    hilbertSymbol a b⁻¹ = hilbertSymbol a b := by
  rw [hilbertSymbol_comm a b⁻¹, hilbertSymbol_inv_left b a hb, hilbertSymbol_comm]

/-- **The Hilbert symbol is unchanged by multiplying its first argument by an element of symbol
`1`.**  The symbol against a fixed `b` is therefore a function of the class of `a` modulo the
norms from `K(√b)`. -/
theorem hilbertSymbol_mul_left_of_eq_one {a b : K} (ha : a ≠ 0) (h : hilbertSymbol a b = 1)
    (a' : K) : hilbertSymbol (a * a') b = hilbertSymbol a' b := by
  rcases hilbertSymbol_eq_one_or a' b with h' | h'
  · rw [h', hilbertSymbol_mul_of_eq_one h h']
  · rw [h']
    rcases hilbertSymbol_eq_one_or (a * a') b with h'' | h''
    · have hinv : hilbertSymbol a⁻¹ b = 1 := by rw [hilbertSymbol_inv_left a b ha, h]
      have hkey := hilbertSymbol_mul_of_eq_one hinv h''
      rw [show a⁻¹ * (a * a') = a' by field_simp] at hkey
      omega
    · exact h''

/-- **The Hilbert symbol is unchanged by multiplying its second argument by an element of symbol
`1`.** -/
theorem hilbertSymbol_mul_right_of_eq_one {a b : K} (hb : b ≠ 0) (h : hilbertSymbol a b = 1)
    (b' : K) : hilbertSymbol a (b * b') = hilbertSymbol a b' := by
  rw [hilbertSymbol_comm a (b * b'), hilbertSymbol_comm a b']
  exact hilbertSymbol_mul_left_of_eq_one hb ((hilbertSymbol_comm a b).symm.trans h) b'

/-- The Hilbert symbol, as a unit of `ℤ`. -/
noncomputable def hilbertUnit (a b : K) : ℤˣ :=
  if hilbertSymbol a b = 1 then 1 else -1

/-- The unit-valued Hilbert symbol has the Hilbert symbol as its underlying integer. -/
@[simp] theorem coe_hilbertUnit (a b : K) : ((hilbertUnit a b : ℤˣ) : ℤ) = hilbertSymbol a b := by
  unfold hilbertUnit
  split_ifs with h
  · rw [h, Units.val_one]
  · rcases hilbertSymbol_eq_one_or a b with h' | h'
    · exact absurd h' h
    · rw [h', Units.val_neg, Units.val_one]

/-- The unit-valued Hilbert symbol is `1` exactly when the Hilbert symbol is. -/
theorem hilbertUnit_eq_one_iff (a b : K) : hilbertUnit a b = 1 ↔ hilbertSymbol a b = 1 := by
  rw [← Units.val_inj, coe_hilbertUnit, Units.val_one]

end Elementary

/-! ### The norm subgroup of a quadratic extension -/

section NormSubgroup

variable {K : Type} [Field K] {b : K} [Fact (Irreducible (X ^ 2 - C (b : K)))]

/-- **The Hilbert symbol is the indicator of the norm group of `K(√b)`.**  A unit `a` of `K` is a
norm from `K(√b)` exactly when the Hilbert symbol `⟨a, b⟩` is `1`. -/
theorem mem_normSubgroup_sqrtExt_iff_hilbertSymbol (hb : ¬ IsSquare b) (a : Kˣ) :
    a ∈ normSubgroup K (sqrtExt K b) ↔ hilbertSymbol (a : K) b = 1 :=
  (mem_normSubgroup_iff_exists a).trans (hilbertSymbol_eq_one_iff_exists_sub_sq hb).symm

/-- **Every square is a norm from `K(√b)`**, being the norm of the corresponding element of the
base field. -/
theorem sq_mem_normSubgroup_sqrtExt (a : Kˣ) : a ^ 2 ∈ normSubgroup K (sqrtExt K b) := by
  rw [mem_normSubgroup_iff_exists]
  exact ⟨(a : K), 0, by push_cast; ring⟩

/-- **The product of two non-norms is a norm when the norm group has index two.**  Choosing a
representative `g` of the nontrivial coset, both `a * g` and `a' * g` are norms, and so therefore
is `a * a' * g ^ 2`; as `g ^ 2` is a norm, so is `a * a'`. -/
theorem mul_mem_normSubgroup_sqrtExt_of_index_two
    (h2 : (normSubgroup K (sqrtExt K b)).index = 2) {a a' : Kˣ}
    (ha : a ∉ normSubgroup K (sqrtExt K b)) (ha' : a' ∉ normSubgroup K (sqrtExt K b)) :
    a * a' ∈ normSubgroup K (sqrtExt K b) := by
  obtain ⟨g, hg⟩ := Subgroup.index_eq_two_iff.1 h2
  have h1 : a * g ∈ normSubgroup K (sqrtExt K b) :=
    ((hg a).resolve_right fun h => ha h.1).1
  have h1' : a' * g ∈ normSubgroup K (sqrtExt K b) :=
    ((hg a').resolve_right fun h => ha' h.1).1
  have heq : a * a' * g ^ 2 = a * g * (a' * g) := by
    rw [sq, mul_mul_mul_comm]
  refine (Subgroup.mul_mem_cancel_right _ (sq_mem_normSubgroup_sqrtExt g)).1 ?_
  rw [heq]
  exact Subgroup.mul_mem _ h1 h1'

/-- **Bimultiplicativity of the Hilbert symbol in the first argument** for a norm group of index
two: the symbol against `b` is the indicator of a subgroup of index two of `Kˣ`, hence a
character. -/
theorem hilbertSymbol_mul_left_of_index_two (hb : ¬ IsSquare b)
    (h2 : (normSubgroup K (sqrtExt K b)).index = 2) {a a' : K} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    hilbertSymbol (a * a') b = hilbertSymbol a b * hilbertSymbol a' b := by
  rcases hilbertSymbol_eq_one_or a b with h | h
  · rw [h, one_mul, hilbertSymbol_mul_left_of_eq_one ha h]
  · rcases hilbertSymbol_eq_one_or a' b with h' | h'
    · rw [h', mul_one, mul_comm a a', hilbertSymbol_mul_left_of_eq_one ha' h']
    · have hmem := mul_mem_normSubgroup_sqrtExt_of_index_two h2
        (a := Units.mk0 a ha) (a' := Units.mk0 a' ha')
        (fun hx => by
          rw [mem_normSubgroup_sqrtExt_iff_hilbertSymbol hb, Units.val_mk0] at hx
          omega)
        (fun hx => by
          rw [mem_normSubgroup_sqrtExt_iff_hilbertSymbol hb, Units.val_mk0] at hx
          omega)
      rw [mem_normSubgroup_sqrtExt_iff_hilbertSymbol hb] at hmem
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0] at hmem
      rw [h, h', hmem]
      norm_num

/-- **Bimultiplicativity of the Hilbert symbol in the second argument** for a norm group of index
two. -/
theorem hilbertSymbol_mul_right_of_index_two (hb : ¬ IsSquare b)
    (h2 : (normSubgroup K (sqrtExt K b)).index = 2) {a a' : K} (ha : a ≠ 0) (ha' : a' ≠ 0) :
    hilbertSymbol b (a * a') = hilbertSymbol b a * hilbertSymbol b a' := by
  rw [hilbertSymbol_comm b (a * a'), hilbertSymbol_comm b a, hilbertSymbol_comm b a']
  exact hilbertSymbol_mul_left_of_index_two hb h2 ha ha'

/-- **The Hilbert symbol against a fixed non-square `b` as a character of `Kˣ`**, for a norm group
of index two. -/
noncomputable def hilbertHom (hb : ¬ IsSquare b)
    (h2 : (normSubgroup K (sqrtExt K b)).index = 2) : Kˣ →* ℤˣ where
  toFun a := hilbertUnit (a : K) b
  map_one' := by
    rw [← Units.val_inj]
    simp only [Units.val_one, coe_hilbertUnit]
    exact hilbertSymbol_one_left b
  map_mul' a a' := by
    rw [← Units.val_inj]
    simp only [Units.val_mul, coe_hilbertUnit]
    exact hilbertSymbol_mul_left_of_index_two hb h2 a.ne_zero a'.ne_zero

/-- The character of `Kˣ` attached to `b` is computed by the Hilbert symbol. -/
@[simp] theorem coe_hilbertHom (hb : ¬ IsSquare b)
    (h2 : (normSubgroup K (sqrtExt K b)).index = 2) (a : Kˣ) :
    ((hilbertHom hb h2 a : ℤˣ) : ℤ) = hilbertSymbol (a : K) b :=
  coe_hilbertUnit _ _

/-- **The kernel of the Hilbert character is the norm group of `K(√b)`.** -/
theorem ker_hilbertHom (hb : ¬ IsSquare b)
    (h2 : (normSubgroup K (sqrtExt K b)).index = 2) :
    (hilbertHom hb h2).ker = normSubgroup K (sqrtExt K b) := by
  ext a
  rw [MonoidHom.mem_ker, mem_normSubgroup_sqrtExt_iff_hilbertSymbol hb]
  exact hilbertUnit_eq_one_iff _ _

end NormSubgroup

/-! ### The bridge to the Brauer group -/

section Brauer

variable {K : Type} [Field K] {b : K} [CharZero K] [Fact (Irreducible (X ^ 2 - C (b : K)))]

/-- **The relative Brauer group of `K(√b) / K` is trivial exactly when the Hilbert symbol
`⟨a, b⟩` is `1` for every nonzero `a`.**  The quaternion algebra `(a, b / K)` splits for all `a`
precisely when every unit of `K` is a norm from `K(√b)`. -/
theorem relative_sqrtExt_eq_bot_iff_forall_hilbertSymbol (hb : ¬ IsSquare b) :
    BrauerGroup.relative K (sqrtExt K b) = ⊥ ↔ ∀ a : K, a ≠ 0 → hilbertSymbol a b = 1 := by
  rw [relative_sqrtExt_eq_bot_iff]
  constructor
  · intro h a ha
    rw [hilbertSymbol_eq_one_iff_exists_sub_sq hb]
    simpa using h (Units.mk0 a ha)
  · intro h a
    rw [← hilbertSymbol_eq_one_iff_exists_sub_sq hb]
    exact h _ a.ne_zero

end Brauer

end InverseGalois.CFT.Local
