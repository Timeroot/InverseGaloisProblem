import Mathlib
import Mathieu.DefM24
import Mathieu.DefM12

/-!
# The Mathieu groups and the Golay codes / finite geometries

The Mathieu groups arise as automorphism groups of highly symmetric combinatorial objects:

* `M₂₄` is the automorphism group of the **extended binary Golay code** `G₂₄`, the unique
  `[24, 12, 8]` binary linear code, under coordinate permutations.
* `M₁₂` is the automorphism group of the **ternary Golay code** `G₁₂`, the unique
  `[12, 6, 6]` ternary code, under coordinate permutations (more precisely the monomial
  story; here we record the coordinate-permutation version).
* `M₂₄` is the automorphism group of the **Steiner system `S(5, 8, 24)`**.

We give a concrete, correct-by-construction characterisation of the extended binary Golay
code (dimension 12 and minimum Hamming weight 8 pins it down uniquely up to coordinate
permutation), define the coordinate-permutation automorphism group of a code, and state
the relation `M₂₄ ≅ Aut(G₂₄)` as a goal.  See `PLAN.md`.
-/

namespace Mathieu

open Equiv

set_option maxRecDepth 40000

/-- A predicate characterising the **extended binary Golay code** `G₂₄ ⊆ 𝔽₂²⁴`:
it is a 12-dimensional binary linear code whose nonzero codewords all have Hamming
weight at least 8.  A `[24, 12, 8]` binary code is unique up to coordinate permutation,
so this pins down `G₂₄`. -/
structure IsExtendedBinaryGolay (C : Submodule (ZMod 2) (Fin 24 → ZMod 2)) : Prop where
  /-- The code has dimension 12. -/
  dim : Module.finrank (ZMod 2) C = 12
  /-- Every nonzero codeword has Hamming weight at least 8. -/
  minWeight : ∀ v ∈ C, v ≠ 0 → 8 ≤ hammingNorm v

/-- The automorphism group of a binary code `C` under coordinate permutations: those
permutations `σ` of the coordinates that map `C` onto itself. -/
def codeAut (C : Submodule (ZMod 2) (Fin 24 → ZMod 2)) : Subgroup (Perm (Fin 24)) where
  carrier := {σ | ∀ v : Fin 24 → ZMod 2, (v ∘ σ ∈ C) ↔ (v ∈ C)}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro σ τ hσ hτ v
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc]
    rw [hτ, hσ]
  inv_mem' := by
    intro σ hσ v
    have h := hσ (v ∘ (σ⁻¹ : Perm (Fin 24)))
    rw [Function.comp_assoc] at h
    have hcomp : ((σ⁻¹ : Perm (Fin 24)) : Fin 24 → Fin 24) ∘ (σ : Fin 24 → Fin 24) = id := by
      funext x; simp
    rw [hcomp, Function.comp_id] at h
    exact h.symm

/-!
## A concrete extended binary Golay code

We build a concrete `[24, 12, 8]` code as the row span of the standard generator matrix
`[I₁₂ | B]`, where `B` is the bordered quadratic-residue matrix mod `11`.  Its weight
enumerator is `1 + 759 x⁸ + 2576 x¹² + 759 x¹⁶ + x²⁴`, so it has dimension `12` and minimum
weight `8`: it satisfies `IsExtendedBinaryGolay`.
-/

namespace GolayCode

open scoped BigOperators
open Matrix

/-- The quadratic residues mod `11` are `{1, 3, 4, 5, 9}`. -/
def isQR (k : ZMod 11) : Bool := k ∈ ({1, 3, 4, 5, 9} : Finset (ZMod 11))

/-- The `12 × 12` bordered quadratic-residue matrix `B` over `𝔽₂`.
Row/column `0` is the border (the "`∞`" index); rows/columns `1..11` correspond to the
residues `0..10` mod `11`.  The off-border diagonal is `1`, the border off-diagonal is `1`,
the `(∞, ∞)` entry is `0`, and the remaining inner entry `(i, j)` is `1` iff `i - j` is a
nonzero quadratic residue mod `11`. -/
def Bmat (r c : Fin 12) : ZMod 2 :=
  if r = 0 ∧ c = 0 then 0
  else if r = 0 ∨ c = 0 then 1
  else if r = c then 1
  else (if isQR ((r.val - 1 : ℤ) - (c.val - 1 : ℤ) : ZMod 11) then 1 else 0)

/-- The `24 × 12` generator matrix `[I₁₂ | B]ᵀ` (as a column-encoding: row `j`, column `i`).
The first `12` rows are the identity, the last `12` rows are `B`. -/
def Gmat : Matrix (Fin 24) (Fin 12) (ZMod 2) := fun j i =>
  if h : j.val < 12 then (if i = (⟨j.val, h⟩ : Fin 12) then 1 else 0)
  else Bmat i ⟨j.val - 12, by omega⟩

/-- The `12 × 24` projection onto the first `12` coordinates; a left inverse of `Gmat`. -/
def Pmat : Matrix (Fin 12) (Fin 24) (ZMod 2) := fun i j =>
  if j.val = i.val then 1 else 0

/-- The Golay encoding linear map `m ↦ G · m`. -/
noncomputable def golayEnc : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) := Gmat.mulVecLin

/-- The concrete extended binary Golay code: the range of the encoding. -/
noncomputable def golayCode : Submodule (ZMod 2) (Fin 24 → ZMod 2) := LinearMap.range golayEnc

/-
`Pmat` is a left inverse of `Gmat`: a finite matrix identity over `𝔽₂`.
-/
lemma PG_eq_one : Pmat * Gmat = 1 := by
  decide

/-
The encoding is injective (it has the left inverse `Pmat`).
-/
lemma golayEnc_injective : Function.Injective golayEnc := by
  convert Function.LeftInverse.injective _;
  exact fun v => v ∘ ( fun i => ⟨ i.val, by linarith [ Fin.is_lt i ] ⟩ : Fin 12 → Fin 24 );
  intro v; ext i; simp +decide [ golayEnc ] ;
  simp +decide [ Matrix.mulVec, dotProduct, Gmat ]

/-! ### Fast minimum-weight certificate (QR code)

We reduce the minimum-weight statement to a chunked compiled decision over the `4096` bitmasks
`n < 2^12`.  The columns of `Gmat` are precomputed as bit-literals
`colMaskQR` (avoiding `ZMod 11` arithmetic inside the fold). -/

/-- The message `m : Fin 12 → 𝔽₂` encoded by the bitmask `n`. -/
def msgOf (n : ℕ) : Fin 12 → ZMod 2 := fun i => if n.testBit i.val then 1 else 0

/-- The bitmask of a message `m`. -/
def encMsg (m : Fin 12 → ZMod 2) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin 12 => m i = 1), 2 ^ (i : ℕ)

/-- Column `s` of the QR generator matrix `Gmat`, as a `24`-bit mask (precomputed). -/
def colMaskQR (s : ℕ) : ℕ :=
  ([16769025, 12103682, 7434244, 14864392, 12955664, 9138208,
    1503296, 3002496, 6000896, 11997696, 7222272, 14440448] : List ℕ).getD s 0

/-- `Bool` support test for the QR `Gmat`: `Gmat i s = if GbitQR i s then 1 else 0`. -/
def GbitQR (i s : ℕ) : Bool := (colMaskQR s).testBit i

/-- Computable weight of the encoded QR codeword. -/
def wtMask (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin 24 =>
    Odd ((Finset.univ.filter (fun s : Fin 12 => GbitQR i.val s.val && n.testBit s.val)).card))).card

/-- The QR `Gmat` entry equals the precomputed `Bool` support test. -/
lemma Gmat_eq_GbitQR (i : Fin 24) (s : Fin 12) :
    Gmat i s = if GbitQR i.val s.val then 1 else 0 := by revert i s; decide

/-- Value of the encoded QR codeword at coordinate `i` is the parity of hit columns. -/
lemma mulVec_msgOf_apply (n : ℕ) (i : Fin 24) :
    Gmat.mulVec (msgOf n) i =
      ((Finset.univ.filter (fun s : Fin 12 => GbitQR i.val s.val && n.testBit s.val)).card : ZMod 2) := by
  simp +decide [Matrix.mulVec, dotProduct, Gmat_eq_GbitQR]
  rw [Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x hx => by unfold msgOf; aesop

/-- The encoded QR codeword is nonzero at `i` iff the column count there is odd. -/
lemma mulVec_msgOf_ne_zero (n : ℕ) (i : Fin 24) :
    Gmat.mulVec (msgOf n) i ≠ 0 ↔
      Odd ((Finset.univ.filter (fun s : Fin 12 => GbitQR i.val s.val && n.testBit s.val)).card) := by
  rw [mulVec_msgOf_apply]
  rw [Ne, ZMod.natCast_eq_zero_iff]; norm_num [Nat.odd_iff]

set_option maxHeartbeats 800000 in
/-- The Hamming weight of the encoded QR codeword equals the computable `wtMask`. -/
lemma hammingNorm_msgOf (n : ℕ) : hammingNorm (Gmat.mulVec (msgOf n)) = wtMask n := by
  rw [hammingNorm, wtMask]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro i _
  simp only [mulVec_msgOf_ne_zero]

/-- Adding a single power `2 ^ a` whose bit is unset in `M` sets exactly that bit. -/
private theorem bitADD (M a : ℕ) (hMa : M.testBit a = false) (k : ℕ) :
    (2 ^ a + M).testBit k = (decide (k = a) || M.testBit k) := by
  rcases Nat.lt_trichotomy k a with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h, show decide (k = a) = false from by simp; omega]; simp
  · subst h; rw [Nat.testBit_two_pow_add_eq, hMa]; simp
  · rw [show decide (k = a) = false from by simp; omega, Bool.false_or]
    obtain ⟨d, rfl⟩ : ∃ d, k = (d + 1) + a := ⟨k - a - 1, by omega⟩
    rw [Nat.testBit_add (2 ^ a + M) (d+1) a, Nat.testBit_add M (d+1) a]
    have hpos : 0 < 2 ^ a := by positivity
    have hdiv : (2 ^ a + M) / 2 ^ a = M / 2 ^ a + 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hpos]
    rw [hdiv]
    have hteven : (M / 2 ^ a) % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hMa
      simp only [decide_eq_false_iff_not] at hMa; omega
    rw [Nat.testBit_add_one, Nat.testBit_add_one]; congr 1; omega

/-- **Bit bridge.** -/
private theorem testBit_bridge (s : Finset (Fin 12)) (k : ℕ) :
    (∑ i ∈ s, 2 ^ (i : ℕ)).testBit k = decide (∃ i ∈ s, (i : ℕ) = k) := by
  classical
  induction s using Finset.induction generalizing k with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hMa : (∑ i ∈ s, 2 ^ (i : ℕ)).testBit (a:ℕ) = false := by
      rw [ih]; simp only [decide_eq_false_iff_not]; rintro ⟨i, hi, he⟩
      exact ha (by rwa [Fin.val_injective he] at hi)
    rw [bitADD _ _ hMa k, ih]
    simp only [Finset.mem_insert, exists_eq_or_imp]
    rw [Bool.decide_or]; congr 1
    exact decide_eq_decide.mpr eq_comm

/-- `encMsg` is a section of `msgOf`. -/
lemma msgOf_encMsg (m : Fin 12 → ZMod 2) : msgOf (encMsg m) = m := by
  funext j
  have hiff : (∃ i ∈ Finset.univ.filter (fun i : Fin 12 => m i = 1), (i : ℕ) = j.val) ↔ m j = 1 := by
    constructor
    · rintro ⟨i, hi, he⟩
      simp only [Finset.mem_filter] at hi
      have : i = j := Fin.ext he
      rw [← this]; exact hi.2
    · intro hj; exact ⟨j, by simp [hj], rfl⟩
  have hbit : (encMsg m).testBit j.val = decide (m j = 1) := by
    rw [encMsg, testBit_bridge]; exact decide_eq_decide.mpr hiff
  simp only [msgOf, hbit]
  by_cases hj : m j = 1
  · simp [hj]
  · have h0 : m j = 0 := by
      have := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (m j)
      tauto
    simp [h0]

/-- The bitmask of a message is `< 4096`. -/
lemma encMsg_lt (m : Fin 12 → ZMod 2) : encMsg m < 4096 := by
  have h1 : encMsg m ≤ ∑ i : Fin 12, 2 ^ (i : ℕ) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h2 : (∑ i : Fin 12, 2 ^ (i : ℕ)) = 4095 := by decide
  omega

/-- A nonzero message has a nonzero bitmask. -/
lemma encMsg_ne_zero {m : Fin 12 → ZMod 2} (hm : m ≠ 0) : encMsg m ≠ 0 := by
  intro h; apply hm; rw [← msgOf_encMsg m, h]; funext i; simp [msgOf, Nat.zero_testBit]

/-- One chunk of the finite minimum-weight check. -/
def chunkOK (lo len : ℕ) : Bool :=
  (List.range len).all (fun j => let n := lo + j; decide (n = 0) || decide (8 ≤ wtMask n))

section Chunks

/- Each chunk is checked in its own declaration: bundling all `4096` bitmasks into a single
kernel reduction needs several gigabytes, while one chunk at a time is cheap. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

lemma chunk0 : chunkOK 0 512 = true := by decide +kernel
lemma chunk1 : chunkOK 512 512 = true := by decide +kernel
lemma chunk2 : chunkOK 1024 512 = true := by decide +kernel
lemma chunk3 : chunkOK 1536 512 = true := by decide +kernel
lemma chunk4 : chunkOK 2048 512 = true := by decide +kernel
lemma chunk5 : chunkOK 2560 512 = true := by decide +kernel
lemma chunk6 : chunkOK 3072 512 = true := by decide +kernel
lemma chunk7 : chunkOK 3584 512 = true := by decide +kernel

end Chunks

/-- Specification of a passing chunk. -/
lemma chunkOK_spec {lo len : ℕ} (h : chunkOK lo len = true) :
    ∀ j, j < len → lo + j = 0 ∨ 8 ≤ wtMask (lo + j) := by
  intro j hj
  rw [chunkOK, List.all_eq_true] at h
  have := h j (by simp [List.mem_range, hj])
  simpa using this

/-- Every nonzero bitmask below `4096` encodes a QR codeword of weight `≥ 8`. -/
lemma wtMask_ge : ∀ n, n < 4096 → n ≠ 0 → 8 ≤ wtMask n := by
  intro n hn hn0
  have hq : n / 512 < 8 := by omega
  have key : ∀ lo, chunkOK lo 512 = true → lo ≤ n → n < lo + 512 → 8 ≤ wtMask n := by
    intro lo hc hlo hhi
    have := chunkOK_spec hc (n - lo) (by omega)
    rw [Nat.add_sub_cancel' hlo] at this
    rcases this with h | h
    · omega
    · exact h
  interval_cases hqq : (n / 512)
  · exact key 0 chunk0 (by omega) (by omega)
  · exact key 512 chunk1 (by omega) (by omega)
  · exact key 1024 chunk2 (by omega) (by omega)
  · exact key 1536 chunk3 (by omega) (by omega)
  · exact key 2048 chunk4 (by omega) (by omega)
  · exact key 2560 chunk5 (by omega) (by omega)
  · exact key 3072 chunk6 (by omega) (by omega)
  · exact key 3584 chunk7 (by omega) (by omega)

/-- Minimum-weight certificate: every nonzero message encodes to a word of weight `≥ 8`.
Reduced to one bundled compiled check over eight chunks of the `4096` bitmasks. -/
lemma golay_mulVec_minWeight :
    ∀ m : Fin 12 → ZMod 2, m ≠ 0 → 8 ≤ hammingNorm (Gmat.mulVec m) := by
  intro m hm
  have h1 : hammingNorm (Gmat.mulVec (msgOf (encMsg m))) = wtMask (encMsg m) :=
    hammingNorm_msgOf _
  rw [msgOf_encMsg m] at h1
  rw [h1]
  exact wtMask_ge _ (encMsg_lt m) (encMsg_ne_zero hm)

/-
The concrete code has dimension `12`.
-/
lemma golayCode_finrank : Module.finrank (ZMod 2) golayCode = 12 := by
  rw [ golayCode, LinearMap.finrank_range_of_inj ];
  · norm_num;
  · exact golayEnc_injective

/-
The concrete code satisfies `IsExtendedBinaryGolay`.
-/
lemma golayCode_isGolay : IsExtendedBinaryGolay golayCode := by
  refine' ⟨ golayCode_finrank, _ ⟩;
  intro v hv hv_ne_zero
  obtain ⟨m, hm⟩ := hv
  have hm_ne_zero : m ≠ 0 := by
    contrapose! hv_ne_zero; aesop;
  have h_golay_mulVec_minWeight : 8 ≤ hammingNorm (Gmat.mulVec m) := by
    exact golay_mulVec_minWeight m hm_ne_zero
  have h_v_eq_golay_mulVec_m : v = Gmat.mulVec m := by
    exact hm.symm
  rw [h_v_eq_golay_mulVec_m]
  exact h_golay_mulVec_minWeight

end GolayCode

/-- **An extended binary Golay code exists.**  (A `[24, 12, 8]` binary code is unique up to
coordinate permutation.) -/
theorem exists_isExtendedBinaryGolay :
    ∃ C : Submodule (ZMod 2) (Fin 24 → ZMod 2), IsExtendedBinaryGolay C :=
  ⟨GolayCode.golayCode, GolayCode.golayCode_isGolay⟩

/-!
## The `M₂₄`-invariant extended binary Golay code, and `M₂₄ ≤ Aut(G₂₄)`

The concrete code `GolayCode.golayCode` above (QR mod `11`) is *a* `[24,12,8]` code, but its
coordinate labelling is **not** the one stabilised by the standard generators of `M₂₄`.  Here
we build the copy that *is*: the cyclic `[23,12]` binary Golay code — generated by the
degree-`11` factor of `x²³ - 1` over `𝔽₂` with support `{0,2,4,5,6,10,11}` — extended by an
overall parity coordinate at index `23`.  Coordinate `23` is the fixed point of the `23`-cycle
generator `m24a`, which acts as the cyclic shift; all three generators of `M₂₄` preserve this
code.  The code is **self-dual** (`Gᵀ G = 0` and `dim = 12`), so membership is checked by the
parity-check `Gᵀ`.
-/

namespace GolayCode24

open scoped BigOperators
open Matrix

/-- Coefficients of the generator polynomial of the binary Golay code: the degree-`11` factor
of `x²³ - 1` over `𝔽₂` with support `{0,2,4,5,6,10,11}`. -/
def gcoeff (k : ℕ) : ZMod 2 := if k % 23 ∈ ([0, 2, 4, 5, 6, 10, 11] : List ℕ) then 1 else 0

/-- Generator matrix of the cyclic `[23,12]` Golay code extended by an overall parity
coordinate at index `23`.  Column `s` is the `s`-th cyclic shift of the generator polynomial
(on coordinates `0..22`); row `23` (the parity coordinate) is all ones. -/
def Gmat : Matrix (Fin 24) (Fin 12) (ZMod 2) := fun i s =>
  if i.val < 23 then gcoeff (((i.val + 23) - s.val) % 23) else 1

/-- The Golay encoding `m ↦ G · m`. -/
noncomputable def golayEnc : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) := Gmat.mulVecLin

/-- The `M₂₄`-invariant extended binary Golay code: the range of the encoding. -/
noncomputable def golayCode : Submodule (ZMod 2) (Fin 24 → ZMod 2) := LinearMap.range golayEnc

/-- An explicit left inverse of `Gmat`: `Pmat24 * Gmat = 1`.  Its first `12` columns are the
inverse (over `𝔽₂`) of the top `12 × 12` block of `Gmat` (a circulant of the generator
polynomial), the remaining `12` columns are zero.  Since that top block equals the first `12`
rows of `Gmat`, the product `Pmat24 * Gmat` is `B⁻¹ * B = 1`. -/
def Pmat24 : Matrix (Fin 12) (Fin 24) (ZMod 2) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     1,0,1,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     0,1,0,1,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     0,0,1,0,1,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     1,0,0,1,0,1,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     0,1,0,0,1,0,1,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     0,0,1,0,0,1,0,1,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     1,0,0,1,0,0,1,0,1,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     1,1,0,0,1,0,0,1,0,1,0,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     1,1,1,0,0,1,0,0,1,0,1,0, 0,0,0,0,0,0,0,0,0,0,0,0;
     1,1,1,1,0,0,1,0,0,1,0,1, 0,0,0,0,0,0,0,0,0,0,0,0]

/-- `Pmat24` is a left inverse of `Gmat` (a finite matrix identity over `𝔽₂`). -/
lemma PG24_eq_one : Pmat24 * Gmat = 1 := by decide

/-- The encoding has trivial kernel.  Proved via the explicit left inverse `Pmat24`
(no `native_decide`). -/
lemma ker_trivial : ∀ m : Fin 12 → ZMod 2, Gmat.mulVec m = 0 → m = 0 := by
  intro m hm
  have h : Pmat24.mulVec (Gmat.mulVec m) = Pmat24.mulVec 0 := by rw [hm]
  rwa [Matrix.mulVec_mulVec, PG24_eq_one, Matrix.one_mulVec, Matrix.mulVec_zero] at h

/-- The encoding is injective. -/
lemma golayEnc_injective : Function.Injective golayEnc := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  exact ker_trivial m (by simpa [golayEnc] using hm)

/-- The code has dimension `12`. -/
lemma golayCode_finrank : Module.finrank (ZMod 2) golayCode = 12 := by
  rw [golayCode, LinearMap.finrank_range_of_inj golayEnc_injective]
  simp

/-- The code is self-orthogonal: `Gᵀ G = 0`. -/
lemma self_orth : Gmatᵀ * Gmat = 0 := by decide

/-- Membership test via the (self-dual) parity check `Gᵀ`: a word is a codeword iff it is
killed by `Gᵀ`. -/
lemma mem_golayCode {w : Fin 24 → ZMod 2} : w ∈ golayCode ↔ Gmatᵀ.mulVec w = 0 := by
  set H : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) := Gmatᵀ.mulVecLin with hH
  have hle : golayCode ≤ LinearMap.ker H := by
    rintro v ⟨m, rfl⟩
    simp only [LinearMap.mem_ker, hH, golayEnc, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, self_orth, Matrix.zero_mulVec]
  have hrankT : Module.finrank (ZMod 2) (LinearMap.range H) = 12 := by
    have h1 : Module.finrank (ZMod 2) (LinearMap.range H) = Matrix.rank Gmatᵀ := rfl
    rw [h1, Matrix.rank_transpose]
    show Matrix.rank Gmat = 12
    have h2 : Matrix.rank Gmat = Module.finrank (ZMod 2) golayCode := rfl
    rw [h2, golayCode_finrank]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker H) = 12 := by
    have hr := LinearMap.finrank_range_add_finrank_ker H
    simp only [hrankT] at hr
    have h24 : Module.finrank (ZMod 2) (Fin 24 → ZMod 2) = 24 := by simp
    omega
  have heq : golayCode = LinearMap.ker H :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [golayCode_finrank, hker])
  rw [heq, LinearMap.mem_ker, hH, Matrix.mulVecLin_apply]

/-! ### Fast minimum-weight certificate

We reduce the minimum-weight statement to a finite compiled computation over the `4096`
bitmasks `n < 2^12`.  The eight chunks are bundled into one certificate, avoiding repeated
compiler startup and the much slower kernel reduction of the same matrix–vector products. -/

/-- The message `m : Fin 12 → 𝔽₂` encoded by the bitmask `n`: coordinate `i` is `1` iff bit
`i` of `n` is set. -/
def msgOf (n : ℕ) : Fin 12 → ZMod 2 := fun i => if n.testBit i.val then 1 else 0

/-- The bitmask of a message `m` (a one-sided inverse to `msgOf`). -/
def encMsg (m : Fin 12 → ZMod 2) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin 12 => m i = 1), 2 ^ (i : ℕ)

/-- Pure-`Bool` version of the `Gmat` support test: `Gmat i s = if Gbit i s then 1 else 0`. -/
def Gbit (i s : ℕ) : Bool :=
  if i < 23 then decide (((i + 23 - s) % 23) % 23 ∈ ([0, 2, 4, 5, 6, 10, 11] : List ℕ)) else true

/-- Computable weight of the codeword `Gmat · (msgOf n)`: coordinate `i` is nonzero iff an
odd number of selected columns `s` (bits set in `n`) satisfy `Gmat i s = 1`. -/
def wtMask (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin 24 =>
    Odd ((Finset.univ.filter (fun s : Fin 12 => Gbit i.val s.val && n.testBit s.val)).card))).card

/-
The `Gmat` entry equals the `Bool` support test `Gbit`.
-/
lemma Gmat_eq_Gbit (i : Fin 24) (s : Fin 12) :
    Gmat i s = if Gbit i.val s.val then 1 else 0 := by
  by_cases h : i.val < 23 <;> simp [Gmat, Gbit, gcoeff, h]

/-
Value of the encoded codeword at coordinate `i`: it is the parity (cast to `𝔽₂`) of the
number of selected columns hitting row `i`.
-/
lemma mulVec_msgOf_apply (n : ℕ) (i : Fin 24) :
    Gmat.mulVec (msgOf n) i =
      ((Finset.univ.filter (fun s : Fin 12 => Gbit i.val s.val && n.testBit s.val)).card : ZMod 2) := by
  simp +decide [ Matrix.mulVec, dotProduct, Gmat_eq_Gbit ];
  rw [ Finset.card_filter, Nat.cast_sum ];
  exact Finset.sum_congr rfl fun x hx => by unfold msgOf; aesop;

/-
The encoded codeword is nonzero at `i` iff the corresponding column count is odd.
-/
lemma mulVec_msgOf_ne_zero (n : ℕ) (i : Fin 24) :
    Gmat.mulVec (msgOf n) i ≠ 0 ↔
      Odd ((Finset.univ.filter (fun s : Fin 12 => Gbit i.val s.val && n.testBit s.val)).card) := by
  rw [ mulVec_msgOf_apply ];
  erw [ Ne, ZMod.natCast_eq_zero_iff ] ; norm_num [ Nat.odd_iff ]

set_option maxHeartbeats 800000 in
/-- The Hamming weight of the encoded codeword equals the computable `wtMask`. -/
lemma hammingNorm_msgOf (n : ℕ) : hammingNorm (Gmat.mulVec (msgOf n)) = wtMask n := by
  rw [hammingNorm, wtMask]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro i _
  simp only [mulVec_msgOf_ne_zero]

/-- Adding a single power `2 ^ a` whose bit is not already set in `M` sets exactly that bit. -/
private theorem bitADD (M a : ℕ) (hMa : M.testBit a = false) (k : ℕ) :
    (2 ^ a + M).testBit k = (decide (k = a) || M.testBit k) := by
  rcases Nat.lt_trichotomy k a with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h, show decide (k = a) = false from by simp; omega]; simp
  · subst h; rw [Nat.testBit_two_pow_add_eq, hMa]; simp
  · rw [show decide (k = a) = false from by simp; omega, Bool.false_or]
    obtain ⟨d, rfl⟩ : ∃ d, k = (d + 1) + a := ⟨k - a - 1, by omega⟩
    rw [Nat.testBit_add (2 ^ a + M) (d+1) a, Nat.testBit_add M (d+1) a]
    have hpos : 0 < 2 ^ a := by positivity
    have hdiv : (2 ^ a + M) / 2 ^ a = M / 2 ^ a + 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hpos]
    rw [hdiv]
    have hteven : (M / 2 ^ a) % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hMa
      simp only [decide_eq_false_iff_not] at hMa; omega
    rw [Nat.testBit_add_one, Nat.testBit_add_one]; congr 1; omega

/-- **Bit bridge.** The `k`-th binary digit of the bitmask `∑ i ∈ s, 2 ^ i` records membership
of the point with value `k` in `s`. -/
private theorem testBit_bridge (s : Finset (Fin 12)) (k : ℕ) :
    (∑ i ∈ s, 2 ^ (i : ℕ)).testBit k = decide (∃ i ∈ s, (i : ℕ) = k) := by
  classical
  induction s using Finset.induction generalizing k with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hMa : (∑ i ∈ s, 2 ^ (i : ℕ)).testBit (a:ℕ) = false := by
      rw [ih]; simp only [decide_eq_false_iff_not]; rintro ⟨i, hi, he⟩
      exact ha (by rwa [Fin.val_injective he] at hi)
    rw [bitADD _ _ hMa k, ih]
    simp only [Finset.mem_insert, exists_eq_or_imp]
    rw [Bool.decide_or]; congr 1
    exact decide_eq_decide.mpr eq_comm

/-- `encMsg` is a section of `msgOf`. -/
lemma msgOf_encMsg (m : Fin 12 → ZMod 2) : msgOf (encMsg m) = m := by
  funext j
  have hiff : (∃ i ∈ Finset.univ.filter (fun i : Fin 12 => m i = 1), (i : ℕ) = j.val) ↔ m j = 1 := by
    constructor
    · rintro ⟨i, hi, he⟩
      simp only [Finset.mem_filter] at hi
      have : i = j := Fin.ext he
      rw [← this]; exact hi.2
    · intro hj; exact ⟨j, by simp [hj], rfl⟩
  have hbit : (encMsg m).testBit j.val = decide (m j = 1) := by
    rw [encMsg, testBit_bridge]; exact decide_eq_decide.mpr hiff
  simp only [msgOf, hbit]
  by_cases hj : m j = 1
  · simp [hj]
  · have h0 : m j = 0 := by
      have := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (m j)
      tauto
    simp [h0]

/-- The bitmask of a message is `< 2^12 = 4096`. -/
lemma encMsg_lt (m : Fin 12 → ZMod 2) : encMsg m < 4096 := by
  have h1 : encMsg m ≤ ∑ i : Fin 12, 2 ^ (i : ℕ) :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h2 : (∑ i : Fin 12, 2 ^ (i : ℕ)) = 4095 := by decide
  omega

/-
A nonzero message has a nonzero bitmask.
-/
lemma encMsg_ne_zero {m : Fin 12 → ZMod 2} (hm : m ≠ 0) : encMsg m ≠ 0 := by
  intro h; apply hm; rw [← msgOf_encMsg m, h]; funext i; simp [msgOf, Nat.zero_testBit]

/-- One chunk of the finite minimum-weight check. -/
def chunkOK (lo len : ℕ) : Bool :=
  (List.range len).all (fun j => let n := lo + j; decide (n = 0) || decide (8 ≤ wtMask n))

section Chunks

/- Each chunk is checked in its own declaration: bundling all `4096` bitmasks into a single
kernel reduction needs several gigabytes, while one chunk at a time is cheap. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

lemma chunk0 : chunkOK 0 512 = true := by decide +kernel
lemma chunk1 : chunkOK 512 512 = true := by decide +kernel
lemma chunk2 : chunkOK 1024 512 = true := by decide +kernel
lemma chunk3 : chunkOK 1536 512 = true := by decide +kernel
lemma chunk4 : chunkOK 2048 512 = true := by decide +kernel
lemma chunk5 : chunkOK 2560 512 = true := by decide +kernel
lemma chunk6 : chunkOK 3072 512 = true := by decide +kernel
lemma chunk7 : chunkOK 3584 512 = true := by decide +kernel

end Chunks

/-- Specification of a passing chunk: every index in `[lo, lo+len)` is either `0` or has
weight `≥ 8`. -/
lemma chunkOK_spec {lo len : ℕ} (h : chunkOK lo len = true) :
    ∀ j, j < len → lo + j = 0 ∨ 8 ≤ wtMask (lo + j) := by
  intro j hj
  rw [chunkOK, List.all_eq_true] at h
  have := h j (by simp [List.mem_range, hj])
  simpa using this

/-- Every nonzero bitmask below `4096` encodes a codeword of weight `≥ 8`. -/
lemma wtMask_ge : ∀ n, n < 4096 → n ≠ 0 → 8 ≤ wtMask n := by
  intro n hn hn0
  have hq : n / 512 < 8 := by omega
  have key : ∀ lo, chunkOK lo 512 = true → lo ≤ n → n < lo + 512 → 8 ≤ wtMask n := by
    intro lo hc hlo hhi
    have := chunkOK_spec hc (n - lo) (by omega)
    rw [Nat.add_sub_cancel' hlo] at this
    rcases this with h | h
    · omega
    · exact h
  interval_cases hqq : (n / 512)
  · exact key 0 chunk0 (by omega) (by omega)
  · exact key 512 chunk1 (by omega) (by omega)
  · exact key 1024 chunk2 (by omega) (by omega)
  · exact key 1536 chunk3 (by omega) (by omega)
  · exact key 2048 chunk4 (by omega) (by omega)
  · exact key 2560 chunk5 (by omega) (by omega)
  · exact key 3072 chunk6 (by omega) (by omega)
  · exact key 3584 chunk7 (by omega) (by omega)

/-- Minimum-weight certificate: every nonzero message encodes to a word of weight `≥ 8`.
Reduced to one bundled compiled check over eight chunks of the `4096` bitmasks. -/
lemma golay_minWeight :
    ∀ m : Fin 12 → ZMod 2, m ≠ 0 → 8 ≤ hammingNorm (Gmat.mulVec m) := by
  intro m hm
  have h1 : hammingNorm (Gmat.mulVec (msgOf (encMsg m))) = wtMask (encMsg m) :=
    hammingNorm_msgOf _
  rw [msgOf_encMsg m] at h1
  rw [h1]
  exact wtMask_ge _ (encMsg_lt m) (encMsg_ne_zero hm)

/-- The code satisfies `IsExtendedBinaryGolay`. -/
lemma golayCode_isGolay : IsExtendedBinaryGolay golayCode := by
  refine ⟨golayCode_finrank, ?_⟩
  rintro v ⟨m, rfl⟩ hv0
  have hm : m ≠ 0 := by rintro rfl; simp [golayEnc] at hv0
  have he : golayEnc m = Gmat.mulVec m := by simp [golayEnc]
  rw [he]; exact golay_minWeight m hm

end GolayCode24

/-- If a coordinate permutation `σ` maps the Golay code into itself, then `σ` is a genuine
code automorphism: the induced linear map `v ↦ v ∘ σ` is injective on the finite-dimensional
code, hence onto, so the inclusion is an equivalence. -/
lemma mem_codeAut_of_mapsTo {σ : Perm (Fin 24)}
    (h : ∀ w ∈ GolayCode24.golayCode, w ∘ (σ : Fin 24 → Fin 24) ∈ GolayCode24.golayCode) :
    σ ∈ codeAut GolayCode24.golayCode := by
  set F := LinearMap.funLeft (ZMod 2) (ZMod 2) (σ : Fin 24 → Fin 24) with hF
  have hFinj : Function.Injective F :=
    LinearMap.funLeft_injective_of_surjective _ _ _ σ.surjective
  have hmaple : Submodule.map F GolayCode24.golayCode ≤ GolayCode24.golayCode := by
    rintro x ⟨w, hw, rfl⟩; exact h w hw
  have hmapeq : Submodule.map F GolayCode24.golayCode = GolayCode24.golayCode := by
    apply Submodule.eq_of_le_of_finrank_eq hmaple
    exact (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective F hFinj GolayCode24.golayCode)).symm
  show ∀ v, v ∘ (σ : Fin 24 → Fin 24) ∈ GolayCode24.golayCode ↔ v ∈ GolayCode24.golayCode
  intro v
  refine ⟨fun hv => ?_, fun hv => h v hv⟩
  have hv' : F v ∈ Submodule.map F GolayCode24.golayCode := by rw [hmapeq]; exact hv
  obtain ⟨u, hu, hFu⟩ := hv'
  have huv : u = v := hFinj hFu
  rwa [huv] at hu

/-- If every column of `G` composed with `σ` lies in the code, then `σ` maps the whole code
into itself (the code is spanned by the columns and `v ↦ v ∘ σ` is linear). -/
lemma mapsTo_of_columns {σ : Perm (Fin 24)}
    (hcol : ∀ s : Fin 12,
      (fun i => GolayCode24.Gmat i s) ∘ (σ : Fin 24 → Fin 24) ∈ GolayCode24.golayCode) :
    ∀ w ∈ GolayCode24.golayCode, w ∘ (σ : Fin 24 → Fin 24) ∈ GolayCode24.golayCode := by
  rintro w ⟨m, rfl⟩
  have heq : (GolayCode24.golayEnc m) ∘ (σ : Fin 24 → Fin 24)
      = ∑ s : Fin 12, m s • ((fun i => GolayCode24.Gmat i s) ∘ (σ : Fin 24 → Fin 24)) := by
    funext i
    simp [GolayCode24.golayEnc, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [heq]
  exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (hcol s))

/-- **`M₂₄ ≤ Aut(G₂₄)`.** Every element of `M₂₄` is a coordinate automorphism of the
(`M₂₄`-invariant) extended binary Golay code. -/
lemma M24_le_codeAut : M24 ≤ codeAut GolayCode24.golayCode := by
  rw [M24, Subgroup.closure_le]
  intro g hg
  have ha : ∀ s : Fin 12,
      GolayCode24.Gmat.transpose.mulVec ((fun i => GolayCode24.Gmat i s) ∘ (m24a : Fin 24 → Fin 24)) = 0 := by
    decide
  have hb : ∀ s : Fin 12,
      GolayCode24.Gmat.transpose.mulVec ((fun i => GolayCode24.Gmat i s) ∘ (m24b : Fin 24 → Fin 24)) = 0 := by
    decide
  have hc : ∀ s : Fin 12,
      GolayCode24.Gmat.transpose.mulVec ((fun i => GolayCode24.Gmat i s) ∘ (m24c : Fin 24 → Fin 24)) = 0 := by
    decide
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact mem_codeAut_of_mapsTo
      (mapsTo_of_columns (fun s => GolayCode24.mem_golayCode.2 (ha s)))
  · exact mem_codeAut_of_mapsTo
      (mapsTo_of_columns (fun s => GolayCode24.mem_golayCode.2 (hb s)))
  · exact mem_codeAut_of_mapsTo
      (mapsTo_of_columns (fun s => GolayCode24.mem_golayCode.2 (hc s)))

/-!
### Decomposition of the 5-point rigidity `codeAut_stab5_le_M24`

The goal is: any code automorphism of `G₂₄` fixing the five points `0,1,2,3,4` pointwise
already lies in `M₂₄`.  We phrase it as an equality of pointwise `5`-point stabilisers and
split it into two genuinely independent facts, combined by a short finite counting argument:

* **(S1)** the pointwise `5`-point stabiliser *inside `M₂₄`* has order exactly `48`
  (`card_stab5_M24`) — pure group theory (orbit–stabiliser + the proved `5`-transitivity of
  `M₂₄`);
* **(S2)** the pointwise `5`-point stabiliser *inside `Aut(G₂₄)`* has order at most `48`
  (`card_stab5_codeAut_le`) — the deep local content coming from the geometry of the octads
  (`S(5,8,24)`);
* **(combiner)** since `M₂₄ ≤ Aut(G₂₄)` the first stabiliser is contained in the second, and
  two finite sets with `|A| ≤ |B|` and `B ⊆ A` coincide, so the two stabilisers are equal
  (`stab5_codeAut_eq_stab5_M24`).

The final lemma `codeAut_stab5_le_M24` is then a one-line synthesis.
-/

/-- The pointwise stabiliser of the five base points `{0,1,2,3,4}` inside a subgroup `G` of
coordinate permutations: the permutations of `G` fixing each of `0,1,2,3,4`. -/
def stab5 (G : Subgroup (Perm (Fin 24))) : Set (Perm (Fin 24)) :=
  {k | k ∈ G ∧ ∀ i : Fin 24, (i : ℕ) < 5 → k i = i}

/-!
#### Octad infrastructure toward (S2)

The deep bound (S2) is approached through the geometry of the octads (weight-`8` codewords).
We record the concrete octad `octad0` through the five base points and the two facts that
underpin the rigidity argument: the octad through `{0,1,2,3,4}` is *unique* (`octad_unique`),
and every code automorphism fixing those five points fixes that octad setwise
(`stab5_fix_octad0`).
-/

/-- The unique octad (weight-`8` codeword) of `G₂₄` whose support contains the five base points
`0,1,2,3,4`: the indicator function of `{0,1,2,3,4,7,10,12}` (found by enumeration over the
`4096` codewords). -/
def octad0 : Fin 24 → ZMod 2 := fun i => if i.val ∈ ([0,1,2,3,4,7,10,12] : List ℕ) then 1 else 0

/-- `octad0` is a codeword of `G₂₄`. -/
lemma octad0_mem : octad0 ∈ GolayCode24.golayCode := by
  rw [GolayCode24.mem_golayCode]; decide

/-- `octad0` has Hamming weight `8`. -/
lemma octad0_weight : hammingNorm octad0 = 8 := by decide

/-! ### Fast message-level octad uniqueness

As for the minimum-weight certificate, we reduce the uniqueness statement to one bundled
compiled check over eight chunks of the `4096` bitmasks, using the `GolayCode24` bit machinery. -/

/-- Indicator bits of `octad0`. -/
def octad0Bit (i : ℕ) : Bool := i ∈ ([0,1,2,3,4,7,10,12] : List ℕ)

/-- Parity bit of the encoded codeword `Gmat · (msgOf n)` at coordinate `i`. -/
def octOddBit (n : ℕ) (i : Fin 24) : Bool :=
  decide (Odd ((Finset.univ.filter
    (fun s : Fin 12 => GolayCode24.Gbit i.val s.val && n.testBit s.val)).card))

/-- The per-bitmask uniqueness check as a `Bool`: if the codeword has weight `8` and is `1`
on `0,1,2,3,4`, then it agrees with `octad0` everywhere. -/
def octGoodB (n : ℕ) : Bool :=
  decide ((GolayCode24.wtMask n = 8 ∧ (∀ i : Fin 24, i.val < 5 → octOddBit n i = true)) →
    (∀ i : Fin 24, octOddBit n i = octad0Bit i.val))

/-- One chunk of the finite uniqueness check. -/
def octChunkOK (lo len : ℕ) : Bool := (List.range len).all (fun j => octGoodB (lo + j))

section OctChunks

/- As with `chunk0`–`chunk7`, one declaration per chunk keeps the kernel reduction small. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

lemma octChunk0 : octChunkOK 0 512 = true := by decide +kernel
lemma octChunk1 : octChunkOK 512 512 = true := by decide +kernel
lemma octChunk2 : octChunkOK 1024 512 = true := by decide +kernel
lemma octChunk3 : octChunkOK 1536 512 = true := by decide +kernel
lemma octChunk4 : octChunkOK 2048 512 = true := by decide +kernel
lemma octChunk5 : octChunkOK 2560 512 = true := by decide +kernel
lemma octChunk6 : octChunkOK 3072 512 = true := by decide +kernel
lemma octChunk7 : octChunkOK 3584 512 = true := by decide +kernel

end OctChunks

lemma octChunkOK_spec {lo len : ℕ} (h : octChunkOK lo len = true) :
    ∀ j, j < len → octGoodB (lo + j) = true := by
  intro j hj
  rw [octChunkOK, List.all_eq_true] at h
  have := h j (by simp [List.mem_range, hj])
  simpa using this

lemma octGoodB_all : ∀ n, n < 4096 → octGoodB n = true := by
  intro n hn
  have hq : n / 512 < 8 := by omega
  have key : ∀ lo, octChunkOK lo 512 = true → lo ≤ n → n < lo + 512 → octGoodB n = true := by
    intro lo hc hlo hhi
    have := octChunkOK_spec hc (n - lo) (by omega)
    rwa [Nat.add_sub_cancel' hlo] at this
  interval_cases hqq : (n / 512)
  · exact key 0 octChunk0 (by omega) (by omega)
  · exact key 512 octChunk1 (by omega) (by omega)
  · exact key 1024 octChunk2 (by omega) (by omega)
  · exact key 1536 octChunk3 (by omega) (by omega)
  · exact key 2048 octChunk4 (by omega) (by omega)
  · exact key 2560 octChunk5 (by omega) (by omega)
  · exact key 3072 octChunk6 (by omega) (by omega)
  · exact key 3584 octChunk7 (by omega) (by omega)

private lemma zmod2_ne_zero_iff (x : ZMod 2) : x ≠ 0 ↔ x = 1 := by revert x; decide

/-- **Message-level uniqueness of the octad through five points.** Any message whose encoding
has weight `8` and is `1` at each of `0,1,2,3,4` encodes exactly `octad0`.
Reduced to one bundled compiled check over eight chunks of the `4096` bitmasks. -/
lemma octad_unique_msg :
    ∀ m : Fin 12 → ZMod 2, hammingNorm (GolayCode24.Gmat.mulVec m) = 8 →
      (∀ i : Fin 24, (i : ℕ) < 5 → GolayCode24.Gmat.mulVec m i = 1) →
      GolayCode24.Gmat.mulVec m = octad0 := by
  intro m hw h5
  have hme : GolayCode24.msgOf (GolayCode24.encMsg m) = m := GolayCode24.msgOf_encMsg m
  set n := GolayCode24.encMsg m with hn
  have hw' : GolayCode24.wtMask n = 8 := by rw [← GolayCode24.hammingNorm_msgOf, hme]; exact hw
  have h5' : ∀ i : Fin 24, i.val < 5 → octOddBit n i = true := by
    intro i hi
    have hne : GolayCode24.Gmat.mulVec (GolayCode24.msgOf n) i ≠ 0 := by
      rw [hme, h5 i hi]; exact one_ne_zero
    have hodd := (GolayCode24.mulVec_msgOf_ne_zero n i).1 hne
    simp only [octOddBit, decide_eq_true_eq]; exact hodd
  have hg : octGoodB n = true := octGoodB_all n (GolayCode24.encMsg_lt m)
  rw [octGoodB] at hg
  have hmatch := (of_decide_eq_true hg) ⟨hw', h5'⟩
  rw [← hme]
  funext i
  have hb := hmatch i
  by_cases ho : octad0Bit i.val = true
  · have hmem : i.val ∈ ([0,1,2,3,4,7,10,12] : List ℕ) := by simpa [octad0Bit] using ho
    have hbit : octOddBit n i = true := by rw [hb, ho]
    have hodd : Odd ((Finset.univ.filter
        (fun s : Fin 12 => GolayCode24.Gbit i.val s.val && n.testBit s.val)).card) := by
      simp only [octOddBit, decide_eq_true_eq] at hbit; exact hbit
    have hval1 : GolayCode24.Gmat.mulVec (GolayCode24.msgOf n) i = 1 :=
      (zmod2_ne_zero_iff _).1 ((GolayCode24.mulVec_msgOf_ne_zero n i).2 hodd)
    rw [hval1]
    show (1 : ZMod 2) = (if i.val ∈ ([0,1,2,3,4,7,10,12] : List ℕ) then 1 else 0)
    rw [if_pos hmem]
  · have hnmem : i.val ∉ ([0,1,2,3,4,7,10,12] : List ℕ) := by simpa [octad0Bit] using ho
    have hbf : octad0Bit i.val = false := by simpa using ho
    have hbit : octOddBit n i = false := by rw [hb, hbf]
    have hnodd : ¬ Odd ((Finset.univ.filter
        (fun s : Fin 12 => GolayCode24.Gbit i.val s.val && n.testBit s.val)).card) := by
      simp only [octOddBit, decide_eq_false_iff_not] at hbit; exact hbit
    have hz : GolayCode24.Gmat.mulVec (GolayCode24.msgOf n) i = 0 := by
      by_contra hne; exact hnodd ((GolayCode24.mulVec_msgOf_ne_zero n i).1 hne)
    rw [hz]
    show (0 : ZMod 2) = (if i.val ∈ ([0,1,2,3,4,7,10,12] : List ℕ) then 1 else 0)
    rw [if_neg hnmem]

/-
**Uniqueness of the octad through the five base points.** Any weight-`8` codeword equal to
`1` at each of `0,1,2,3,4` is `octad0`.
-/
lemma octad_unique {v : Fin 24 → ZMod 2} (hv : v ∈ GolayCode24.golayCode)
    (hw : hammingNorm v = 8) (h5 : ∀ i : Fin 24, (i : ℕ) < 5 → v i = 1) : v = octad0 := by
  obtain ⟨ m, rfl ⟩ := hv;
  convert octad_unique_msg m hw h5 using 1

/-
**Every 5-point stabiliser element fixes the octad setwise.** If `k` is a code automorphism
fixing `0,1,2,3,4` pointwise, then `octad0 ∘ k = octad0`, i.e. `k` preserves the support of the
unique octad through the five base points.  This is the concrete rigidity mechanism used in the
deep bound (S2): `octad0 ∘ k` is again a weight-`8` codeword equal to `1` on `{0,1,2,3,4}`, so
it equals `octad0` by `octad_unique`.
-/
lemma stab5_fix_octad0 (k : Perm (Fin 24))
    (hk : k ∈ stab5 (codeAut GolayCode24.golayCode)) :
    octad0 ∘ (k : Fin 24 → Fin 24) = octad0 := by
  apply octad_unique;
  · obtain ⟨hkA, hkfix⟩ := hk;
    exact hkA _ |>.2 ( by simpa using octad0_mem );
  · convert octad0_weight using 1;
    simp +decide [ hammingNorm ];
    rw [ Finset.card_filter, Finset.card_filter ];
    conv_rhs => rw [ ← Equiv.sum_comp k ] ;
  · exact fun i hi => by rw [ Function.comp_apply, hk.2 i hi ] ; fin_cases i <;> trivial;

/-!
#### (S2) The `48` bound via octad rigidity

We prove `card_stab5_codeAut_le` **without** the `2⁴:A₈` octad-stabiliser theory, by a direct
rigidity/counting argument over the Steiner system `S(5,8,24)` (octads = weight-`8` codewords):

* **Rigidity** (`stab5_rigid`): a code automorphism fixing the seven points `{0,1,2,3,4,5,7}`
  pointwise is the identity.  Reason: a nine-octad incidence pattern (verified by
  `native_decide`) separates all coordinates except `{10,12}`; a code automorphism fixing
  `{0,1,2,3,4,5,7}` fixes each of those octads setwise (an octad meeting a fixed set in `≥5`
  points is fixed, by minimum-distance uniqueness `octad_eq_of_inter5`), hence preserves the
  pattern and fixes those coordinates; the leftover transposition `(10 12)` is not a code
  automorphism (`swap1012_not_codeAut`).
* **Counting**: by rigidity, `k ↦ (k 5, k 7)` is injective on the stabiliser; its image lands
  in `{a | octad0 a = 0} × {7,10,12}` (using `stab5_fix_octad0`), a set of size `16·3 = 48`.
-/

/-- An **octad**: a weight-`8` codeword of the `M₂₄`-invariant Golay code. -/
def IsOctad (v : Fin 24 → ZMod 2) : Prop :=
  v ∈ GolayCode24.golayCode ∧ hammingNorm v = 8

/-
The Hamming norm is invariant under precomposition with a coordinate permutation.
-/
lemma hammingNorm_comp_perm (v : Fin 24 → ZMod 2) (e : Perm (Fin 24)) :
    hammingNorm (v ∘ (e : Fin 24 → Fin 24)) = hammingNorm v := by
      unfold hammingNorm;
      rw [ Finset.card_filter, Finset.card_filter ];
      conv_rhs => rw [ ← Equiv.sum_comp e ] ;
      rfl

/-- Code automorphisms send octads to octads (under precomposition). -/
lemma isOctad_comp {k : Perm (Fin 24)} (hk : k ∈ codeAut GolayCode24.golayCode)
    {v : Fin 24 → ZMod 2} (hv : IsOctad v) :
    IsOctad (v ∘ (k : Fin 24 → Fin 24)) :=
  ⟨(hk v).2 hv.1, by rw [hammingNorm_comp_perm]; exact hv.2⟩

/-
**Minimum-distance uniqueness of octads.** Two octads whose supports meet in at least
`5` points are equal.  (Their sum lies in the code and has weight `≤ 16 - 2·5 = 6 < 8`, hence
is `0`.)
-/
lemma octad_eq_of_inter5 {v w : Fin 24 → ZMod 2} (hv : IsOctad v) (hw : IsOctad w)
    (h5 : 5 ≤ (Finset.univ.filter (fun i : Fin 24 => v i = 1 ∧ w i = 1)).card) :
    v = w := by
      have h_dist : hammingDist v w ≤ hammingNorm v + hammingNorm w - 2 * (Finset.univ.filter (fun i => v i = 1 ∧ w i = 1)).card := by
        simp +decide only [hammingDist, hammingNorm];
        rw [ Nat.sub_eq_of_eq_add ];
        have h_card : ∀ i : Fin 24, (if v i ≠ 0 then 1 else 0) + (if w i ≠ 0 then 1 else 0) = (if v i ≠ w i then 1 else 0) + 2 * (if v i = 1 ∧ w i = 1 then 1 else 0) := by
          intro i; rcases v i with ( _ | _ | v ) <;> rcases w i with ( _ | _ | w ) <;> trivial;
        simp +decide only [Finset.card_filter];
        simpa only [ Finset.mul_sum _ _ _, Finset.sum_add_distrib ] using Finset.sum_congr rfl fun i _ => h_card i;
      -- Apply the minimum weight property of the Golay code to v - w.
      have h_min_weight : ∀ x : Fin 24 → ZMod 2, x ∈ GolayCode24.golayCode → x ≠ 0 → 8 ≤ hammingNorm x := by
        convert GolayCode24.golayCode_isGolay.minWeight using 1;
      by_cases h : v - w = 0 <;> simp_all +decide [ hammingDist_eq_hammingNorm ];
      · exact eq_of_sub_eq_zero h;
      · exact absurd ( h_min_weight ( v - w ) ( by exact Submodule.sub_mem _ hv.1 hw.1 ) h ) ( by norm_num [ hv.2, hw.2 ] at *; omega )

/-- The seven "base" coordinates used for the rigidity argument. -/
def rigidBase : List ℕ := [0, 1, 2, 3, 4, 5, 7]

/-
**Octads through five fixed base points are fixed setwise.** If `k` is a code automorphism
fixing the base points `{0,1,2,3,4,5,7}` pointwise, and `v` is an octad with at least `5` of
its support points among the base, then `v ∘ k = v`.
-/
lemma octad_setwise_of_fix {k : Perm (Fin 24)} (hk : k ∈ codeAut GolayCode24.golayCode)
    {v : Fin 24 → ZMod 2} (hv : IsOctad v)
    (hfix : ∀ i : Fin 24, (i : ℕ) ∈ rigidBase → k i = i)
    (h5 : 5 ≤ (Finset.univ.filter
        (fun i : Fin 24 => v i = 1 ∧ (i : ℕ) ∈ rigidBase)).card) :
    v ∘ (k : Fin 24 → Fin 24) = v := by
      apply octad_eq_of_inter5 (isOctad_comp hk hv) hv;
      refine' le_trans h5 ( Finset.card_mono _ );
      intro i hi; aesop;

/-- Indicator (`0/1`) function of a list of coordinates. -/
def indic (l : List ℕ) : Fin 24 → ZMod 2 := fun i => if (i : ℕ) ∈ l then 1 else 0

/-- Nine octads (given by their supports) whose incidence pattern separates all coordinates
except `{10,12}`.  Found by enumeration over the `759` octads. -/
def sepOctads : List (List ℕ) :=
  [[0,2,3,5,6,7,8,18], [2,3,4,5,7,16,19,23], [1,3,4,5,7,14,18,20],
   [0,1,2,5,7,11,16,20], [1,2,3,5,7,9,15,21], [0,1,3,4,5,6,16,21],
   [0,2,3,4,5,15,20,22], [0,1,3,5,7,13,19,22], [1,2,4,5,6,7,17,22]]

/-- Each `sepOctads` entry is an octad. -/
lemma sepOctads_isOctad : ∀ l ∈ sepOctads, IsOctad (indic l) := by
  intro l hl
  refine ⟨GolayCode24.mem_golayCode.mpr ?_, ?_⟩ <;> (fin_cases hl <;> decide)

/-- Each `sepOctads` entry has at least `5` support points among the base `{0,1,2,3,4,5,7}`. -/
lemma sepOctads_f1 : ∀ l ∈ sepOctads,
    5 ≤ (Finset.univ.filter
      (fun i : Fin 24 => indic l i = 1 ∧ (i : ℕ) ∈ rigidBase)).card := by
  intro l hl; fin_cases hl <;> decide

/-- The nine octads separate every coordinate other than `10, 12`: any coordinate `q` with the
same `sepOctads`-incidence pattern as some `p ∉ {10,12}` equals `p`. -/
lemma sepOctads_sep : ∀ p : Fin 24, (p : ℕ) ≠ 10 → (p : ℕ) ≠ 12 →
    ∀ q : Fin 24, (∀ l ∈ sepOctads, indic l q = indic l p) → q = p := by decide

/-- The transposition `(10 12)` is **not** a code automorphism (witnessed by the octad
`{1,2,3,10,13,15,17,22}`, which it maps off the code). -/
lemma swap1012_not_codeAut :
    (Equiv.swap (10 : Fin 24) 12) ∉ codeAut GolayCode24.golayCode := by
  intro h
  have hiff := h (indic [1,2,3,10,13,15,17,22])
  have hin : indic [1,2,3,10,13,15,17,22] ∈ GolayCode24.golayCode :=
    GolayCode24.mem_golayCode.mpr (by decide)
  have hout : ¬ (indic [1,2,3,10,13,15,17,22] ∘
      (Equiv.swap (10 : Fin 24) 12 : Fin 24 → Fin 24)) ∈ GolayCode24.golayCode := by
    rw [GolayCode24.mem_golayCode]; decide
  exact hout (hiff.mpr hin)

/-
A permutation fixing every point outside `{a,b}` is either the identity or the
transposition `(a b)`.
-/
lemma perm_eq_of_fix_except (k : Perm (Fin 24)) (a b : Fin 24)
    (hfix : ∀ i : Fin 24, i ≠ a → i ≠ b → k i = i) :
    k = 1 ∨ k = Equiv.swap a b := by
      by_cases ha : k a = a;
      · left; ext i; by_cases hi : i = a <;> by_cases hi' : i = b <;> simp_all +decide ;
        by_contra h_contra;
        exact absurd ( k.injective ( show k ( k b ) = k b from by rw [ hfix _ ( by aesop ) ( by aesop ) ] ) ) ( by aesop );
      · -- Since $k a \neq a$, we have $k a = b$.
        have hka : k a = b := by
          by_contra h_contra;
          have := k.injective ( show k ( k a ) = k a from by aesop ) ; aesop;
        by_cases hb : k b = b;
        · have := k.injective ( hb.trans hka.symm ) ; aesop;
        · have hkb : k b = a := by
            by_contra hkb_ne_a;
            have := k.injective ( show k ( k b ) = k b from by aesop ) ; aesop;
          right; ext i; by_cases hi : i = a <;> by_cases hj : i = b <;> simp_all +decide [ Equiv.swap_apply_def ] ;

/-- **Rigidity of the base.** A code automorphism fixing `{0,1,2,3,4,5,7}` pointwise is the
identity. -/
lemma stab5_rigid {k : Perm (Fin 24)} (hk : k ∈ codeAut GolayCode24.golayCode)
    (hfix : ∀ i : Fin 24, (i : ℕ) ∈ rigidBase → k i = i) : k = 1 := by
  -- Step 1: k fixes every coordinate except possibly 10, 12.
  have hfixmost : ∀ p : Fin 24, (p : ℕ) ≠ 10 → (p : ℕ) ≠ 12 → k p = p := by
    intro p hp10 hp12
    refine sepOctads_sep p hp10 hp12 (k p) ?_
    intro l hl
    have hsw : indic l ∘ (k : Fin 24 → Fin 24) = indic l :=
      octad_setwise_of_fix hk (sepOctads_isOctad l hl) hfix (sepOctads_f1 l hl)
    have := congrFun hsw p
    simpa [Function.comp] using this
  -- Step 2: hence k is 1 or (10 12); the latter is excluded.
  rcases perm_eq_of_fix_except k 10 12 (by
      intro i hi10 hi12
      exact hfixmost i (by simpa [Fin.ext_iff] using hi10) (by simpa [Fin.ext_iff] using hi12))
    with h1 | hswap
  · exact h1
  · exact absurd (hswap ▸ hk) swap1012_not_codeAut

/-- **(S2)** The pointwise stabiliser of the five points `0,1,2,3,4` inside `Aut(G₂₄)` has
order at most `48`.

Proved via the rigidity `stab5_rigid`: the map `k ↦ (k 5, k 7)` is injective on the
stabiliser (two elements agreeing there differ by an element fixing `{0,1,2,3,4,5,7}`, hence
by rigidity are equal), and its image lands in `{a | octad0 a = 0} × {7,10,12}` (each element
fixes `octad0` setwise by `stab5_fix_octad0`), a set of cardinality `16 · 3 = 48`. -/
lemma card_stab5_codeAut_le :
    Nat.card (stab5 (codeAut GolayCode24.golayCode)) ≤ 48 := by
  classical
  -- the size-48 finite type the stabiliser injects into
  let Tt := {x : Fin 24 × Fin 24 // octad0 x.1 = 0 ∧ (x.2 = 7 ∨ x.2 = 10 ∨ x.2 = 12)}
  have hcard : Nat.card Tt = 48 := by
    rw [Nat.card_eq_fintype_card]; decide
  -- the image of `k ↦ (k 5, k 7)` lands in `Tt`
  have hmap : ∀ k : (stab5 (codeAut GolayCode24.golayCode)),
      octad0 ((k : Perm (Fin 24)) 5) = 0 ∧
        ((k : Perm (Fin 24)) 7 = 7 ∨ (k : Perm (Fin 24)) 7 = 10 ∨ (k : Perm (Fin 24)) 7 = 12) := by
    intro k
    refine ⟨?_, ?_⟩
    · have := congrFun (stab5_fix_octad0 k.1 k.2) 5
      simp only [Function.comp] at this
      rw [this]; decide
    · have h7 : octad0 ((k : Perm (Fin 24)) 7) = 1 := by
        have := congrFun (stab5_fix_octad0 k.1 k.2) 7
        simp only [Function.comp] at this
        rw [this]; decide
      have hne : ∀ j : Fin 24, (j : ℕ) < 5 → (k : Perm (Fin 24)) 7 ≠ j := by
        intro j hj hcontra
        have hEq : (k : Perm (Fin 24)) 7 = (k : Perm (Fin 24)) j := by
          rw [hcontra]; exact (k.2.2 j hj).symm
        have h7j := k.1.injective hEq
        rw [← h7j] at hj; exact absurd hj (by decide)
      have key : ∀ x : Fin 24, octad0 x = 1 →
          (∀ j : Fin 24, (j : ℕ) < 5 → x ≠ j) → (x = 7 ∨ x = 10 ∨ x = 12) := by decide
      exact key _ h7 hne
  -- the map, and its injectivity via rigidity
  let f : (stab5 (codeAut GolayCode24.golayCode)) → Tt :=
    fun k => ⟨((k : Perm (Fin 24)) 5, (k : Perm (Fin 24)) 7), hmap k⟩
  have hinj : Function.Injective f := by
    rintro ⟨k, hk⟩ ⟨k', hk'⟩ heq
    have hpair := congrArg Subtype.val heq
    simp only [f] at hpair
    have h5 : (k : Perm (Fin 24)) 5 = (k' : Perm (Fin 24)) 5 := congrArg Prod.fst hpair
    have h7 : (k : Perm (Fin 24)) 7 = (k' : Perm (Fin 24)) 7 := congrArg Prod.snd hpair
    have hg : (k⁻¹ * k' : Perm (Fin 24)) ∈ codeAut GolayCode24.golayCode :=
      (codeAut GolayCode24.golayCode).mul_mem
        ((codeAut GolayCode24.golayCode).inv_mem hk.1) hk'.1
    have hbase : ∀ i : Fin 24, (i : ℕ) ∈ rigidBase → (k⁻¹ * k' : Perm (Fin 24)) i = i := by
      intro i hi
      have hki : (k' : Perm (Fin 24)) i = (k : Perm (Fin 24)) i := by
        rw [rigidBase] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h|h|h|h|h|h|h
        · rw [hk'.2 i (by omega), hk.2 i (by omega)]
        · rw [hk'.2 i (by omega), hk.2 i (by omega)]
        · rw [hk'.2 i (by omega), hk.2 i (by omega)]
        · rw [hk'.2 i (by omega), hk.2 i (by omega)]
        · rw [hk'.2 i (by omega), hk.2 i (by omega)]
        · have : i = (5 : Fin 24) := Fin.ext (by simpa using h)
          rw [this]; exact h5.symm
        · have : i = (7 : Fin 24) := Fin.ext (by simpa using h)
          rw [this]; exact h7.symm
      show (k⁻¹ * k' : Perm (Fin 24)) i = i
      rw [Equiv.Perm.mul_apply, hki]; simp
    have h1 : (k⁻¹ * k' : Perm (Fin 24)) = 1 := stab5_rigid hg hbase
    have hkk : (k' : Perm (Fin 24)) = k := by
      have h2 : k * (k⁻¹ * k') = k * 1 := congrArg (fun g => k * g) h1
      simpa [mul_assoc] using h2
    exact Subtype.ext hkk.symm
  calc Nat.card (stab5 (codeAut GolayCode24.golayCode))
      ≤ Nat.card Tt := Nat.card_le_card_of_injective f hinj
    _ = 48 := hcard


end Mathieu
