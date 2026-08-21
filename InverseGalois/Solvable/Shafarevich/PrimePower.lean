/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.SemidirectAssoc
import InverseGalois.Solvable.Shafarevich.Reduction

/-!
# From prime power kernels to nilpotent kernels

A finite nilpotent group is the direct product of its Sylow subgroups, and each of those factors
is characteristic.  Splitting off one prime at a time therefore turns a split extension with
nilpotent kernel into a tower of split extensions whose kernels have prime power order: if `H` is
finite nilpotent and `p` divides its order, then `H` is the internal direct product of a
characteristic `p`-subgroup `A` and a characteristic `p'`-subgroup `B`, and

`H ⋊ U ≅ A ⋊ (B ⋊ U)`,

with `B` strictly smaller than `H`.  Consequently the arithmetic hypothesis `SplitNilpotentEP`
follows from its special case for kernels of prime power order.

## Main results

* `Shafarevich.SplitPrimePowerEP` — the statement that every split embedding problem over `ℚ`
  whose kernel has prime power order is solvable.
* `Shafarevich.exists_subgroup_pow_eq_one` — in a finite nilpotent group whose order factors as
  a product of two coprime numbers, the elements annihilated by either factor form a subgroup.
* `Shafarevich.semidirectProductEquivOfProd` — the two stage decomposition of a semidirect
  product whose kernel is the internal direct product of two characteristic subgroups.
* `Shafarevich.splitNilpotentEP_of_splitPrimePowerEP` — split embedding problems with nilpotent
  kernel reduce to split embedding problems with kernel of prime power order.
-/

namespace Shafarevich

open SemidirectProduct

/-! ## Coprime splittings of a finite nilpotent group -/

/-- **A subgroup whose elements are exactly those annihilated by a fixed exponent is
characteristic.**  An automorphism preserves the equation `x ^ n = 1`, hence preserves the
subgroup. -/
theorem characteristic_of_forall_pow {H : Type*} [Group H] (n : ℕ) (A : Subgroup H)
    (hA : ∀ x : H, x ∈ A ↔ x ^ n = 1) : A.Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun e => ?_
  ext y
  rw [Subgroup.mem_map_equiv, hA, hA]
  constructor
  · intro hy
    have : e ((e.symm y) ^ n) = e 1 := by rw [hy]
    rwa [map_pow, e.apply_symm_apply, map_one] at this
  · intro hy
    have : e.symm (y ^ n) = e.symm 1 := by rw [hy]
    rwa [map_pow, map_one] at this

/-- **A coprime factorisation of the order of a finite nilpotent group splits the group.**

If the order of a finite nilpotent group `H` is `m * k` with `m` and `k` coprime, then the
elements `x` of `H` satisfying `x ^ m = 1` form a subgroup: they are exactly the elements whose
components in the Sylow decomposition of `H` vanish at every prime not dividing `m`. -/
theorem exists_subgroup_pow_eq_one {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {m k : ℕ} (hmk : m * k = Nat.card H) (hco : Nat.Coprime m k) :
    ∃ A : Subgroup H, ∀ x : H, x ∈ A ↔ x ^ m = 1 := by
  classical
  have hnormal : ∀ (q : ℕ) (_ : Fact q.Prime) (P : Sylow q H), (↑P : Subgroup H).Normal :=
    (isNilpotent_of_finite_tfae.out 0 3 rfl rfl).mp ‹Group.IsNilpotent H›
  let e : (∀ q : (Nat.card H).primeFactors, ∀ P : Sylow (q : ℕ) H, ↥(P : Subgroup H)) ≃* H :=
    Sylow.directProductOfNormal fun P => hnormal _ ‹_› P
  -- The order of the Sylow `q`-subgroup is the `q`-part of the order of `H`.
  have hcardP : ∀ (q : (Nat.card H).primeFactors) (P : Sylow (q : ℕ) H),
      Nat.card ↥(P : Subgroup H) = (q : ℕ) ^ (Nat.card H).factorization (q : ℕ) := by
    intro q P
    haveI : Fact (q : ℕ).Prime := Fact.mk (Nat.prime_of_mem_primeFactors q.2)
    exact Sylow.card_eq_multiplicity P
  -- A prime dividing `m` contributes its whole part of the order to `m`.
  have hdvdm : ∀ q : (Nat.card H).primeFactors, ((q : ℕ) ∣ m) →
      (q : ℕ) ^ (Nat.card H).factorization (q : ℕ) ∣ m := by
    intro q hq
    have h1 : Nat.Coprime ((q : ℕ) ^ (Nat.card H).factorization (q : ℕ)) k :=
      Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_left hq hco)
    have h2 : (q : ℕ) ^ (Nat.card H).factorization (q : ℕ) ∣ m * k := by
      rw [hmk]
      exact Nat.ordProj_dvd (Nat.card H) (q : ℕ)
    exact h1.dvd_of_dvd_mul_right h2
  -- Elements of a Sylow `q`-subgroup with `q ∣ m` are annihilated by `m`.
  have hkill : ∀ (q : (Nat.card H).primeFactors) (P : Sylow (q : ℕ) H) (y : ↥(P : Subgroup H)),
      ((q : ℕ) ∣ m) → y ^ m = 1 := by
    intro q P y hq
    refine orderOf_dvd_iff_pow_eq_one.mp (dvd_trans ?_ (hdvdm q hq))
    rw [← hcardP q P]
    exact orderOf_dvd_natCard y
  -- Elements of a Sylow `q`-subgroup with `q ∤ m` are annihilated by `m` only if trivial.
  have hone : ∀ (q : (Nat.card H).primeFactors) (P : Sylow (q : ℕ) H) (y : ↥(P : Subgroup H)),
      ¬((q : ℕ) ∣ m) → y ^ m = 1 → y = 1 := by
    intro q P y hq hy
    have h1 : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hy
    have h2 : orderOf y ∣ (q : ℕ) ^ (Nat.card H).factorization (q : ℕ) := by
      rw [← hcardP q P]
      exact orderOf_dvd_natCard y
    have hg : Nat.gcd m ((q : ℕ) ^ (Nat.card H).factorization (q : ℕ)) = 1 :=
      Nat.Coprime.pow_right _
        ((Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors q.2)).mpr hq).symm
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd h1 h2))
  -- Being annihilated by `m` may be tested componentwise.
  have hpi : ∀ f : ∀ q : (Nat.card H).primeFactors, ∀ P : Sylow (q : ℕ) H, ↥(P : Subgroup H),
      f ^ m = 1 ↔ ∀ q P, (f q P) ^ m = 1 := by
    intro f
    constructor
    · intro hf q P
      simpa using congrFun (congrFun hf q) P
    · intro hf
      funext q P
      simpa using hf q P
  refine ⟨Subgroup.map e.toMonoidHom
    (Subgroup.pi {q : (Nat.card H).primeFactors | ¬((q : ℕ) ∣ m)} fun _ => ⊥), fun x => ?_⟩
  rw [Subgroup.mem_map_equiv, Subgroup.mem_pi]
  constructor
  · intro hx
    have h1 : (e.symm x) ^ m = 1 := by
      rw [hpi]
      intro q P
      by_cases hq : (q : ℕ) ∣ m
      · exact hkill q P _ hq
      · rw [Subgroup.mem_bot.mp (hx q hq)]
        simp
    have h2 : e ((e.symm x) ^ m) = e 1 := by rw [h1]
    rwa [map_pow, e.apply_symm_apply, map_one] at h2
  · intro hx q hq
    have h1 : e.symm (x ^ m) = e.symm 1 := by rw [hx]
    rw [map_pow, map_one] at h1
    rw [Subgroup.mem_bot]
    funext P
    exact hone q P _ hq ((hpi _).mp h1 q P)

/-! ## Splitting a semidirect product along an internal direct product -/

/-- **A semidirect product whose kernel is the internal direct product of two characteristic
subgroups splits in two stages.**

If a group `H` is the internal direct product of characteristic subgroups `A` and `B`, then any
semidirect product `H ⋊ U` is isomorphic to `A ⋊ (B ⋊ U)`, the outer factor acting on `A`
through its projection to `U`. -/
def semidirectProductEquivOfProd {H U : Type*} [Group H] [Group U] (A B : Subgroup H)
    [A.Characteristic] [B.Characteristic] (φ : U →* MulAut H) (θ : ↥A × ↥B ≃* H)
    (hθ : ∀ y : ↥A × ↥B, θ y = (y.1 : H) * (y.2 : H)) :
    H ⋊[φ] U ≃*
      ↥A ⋊[(((MulAut.restrictChar A).comp φ).comp
        (rightHom : ↥B ⋊[(MulAut.restrictChar B).comp φ] U →* U))]
          (↥B ⋊[(MulAut.restrictChar B).comp φ] U) := by
  have hnat : ∀ (u : U) (y : ↥A × ↥B),
      θ ((((MulAut.restrictChar A).comp φ).prodAut ((MulAut.restrictChar B).comp φ)) u y)
        = φ u (θ y) := by
    rintro u ⟨a, b⟩
    simp only [hθ, map_mul, MonoidHom.prodAut_apply, MonoidHom.coe_comp, Function.comp_apply]
    rfl
  have hcongr : ∀ u : U, (φ u).trans θ.symm = θ.symm.trans
      ((((MulAut.restrictChar A).comp φ).prodAut ((MulAut.restrictChar B).comp φ))
        ((MulEquiv.refl U) u)) := by
    intro u
    refine MulEquiv.ext fun x => θ.injective ?_
    simp only [MulEquiv.coe_trans, Function.comp_apply, MulEquiv.apply_symm_apply,
      MulEquiv.refl_apply, hnat]
  exact (SemidirectProduct.congr
      (φ₂ := ((MulAut.restrictChar A).comp φ).prodAut ((MulAut.restrictChar B).comp φ))
      θ.symm (MulEquiv.refl U) hcongr).trans
    (SemidirectProduct.prodAssoc ((MulAut.restrictChar A).comp φ)
      ((MulAut.restrictChar B).comp φ))

/-! ## The reduction -/

/-- **Every split embedding problem over `ℚ` with kernel of prime power order is solvable.**

If a finite group `U` is a Galois group over `ℚ`, then so is any semidirect product `H ⋊[φ] U`
in which `H` is a finite `p`-group. -/
def SplitPrimePowerEP : Prop :=
  ∀ (H U : Type) [Group H] [Finite H] [Group U] [Finite U] (p : ℕ) [Fact p.Prime],
    IsPGroup p H → ∀ φ : U →* MulAut H, IsInverseGalois U → IsInverseGalois (H ⋊[φ] U)

/-- **A semidirect product with trivial kernel is its own outer factor.** -/
def rightEquivOfSubsingleton {N G : Type*} [Group N] [Subsingleton N] [Group G]
    (φ : G →* MulAut N) : N ⋊[φ] G ≃* G where
  toFun := rightHom
  invFun := inr
  left_inv x := by
    refine SemidirectProduct.ext ?_ rfl
    exact Subsingleton.elim _ _
  right_inv _ := rfl
  map_mul' _ _ := map_mul rightHom _ _

/-- **Split embedding problems with nilpotent kernel reduce to kernels of prime power order.**

A finite nilpotent kernel splits as the direct product of a characteristic Sylow subgroup and a
characteristic complement, both invariant under the given action; adjoining the two factors one
after the other expresses the semidirect product as a tower whose bottom step has a kernel of
prime power order and whose top step has a strictly smaller nilpotent kernel. -/
theorem splitNilpotentEP_of_splitPrimePowerEP (h : SplitPrimePowerEP) : SplitNilpotentEP := by
  suffices key : ∀ (n : ℕ) (H U : Type) [Group H] [Finite H] [Group.IsNilpotent H] [Group U]
      [Finite U] (φ : U →* MulAut H), Nat.card H ≤ n → IsInverseGalois U →
      IsInverseGalois (H ⋊[φ] U) by
    intro H U _ _ _ _ _ φ hU
    exact key (Nat.card H) H U φ le_rfl hU
  intro n
  induction n with
  | zero =>
    intro H U _ _ _ _ _ _ hcard _
    exact absurd hcard (not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro H U _ _ _ _ _ φ hcard hU
    rcases subsingleton_or_nontrivial H with hs | hs
    · haveI := hs
      exact hU.of_mulEquiv (rightEquivOfSubsingleton φ).symm
    · -- Choose a prime dividing the order of the kernel and split off its Sylow subgroup.
      have hN : Nat.card H ≠ 0 := Nat.card_pos.ne'
      obtain ⟨p, hp, hpdvd⟩ := (Nat.card H).exists_prime_and_dvd Finite.one_lt_card.ne'
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨m, k, hm, hmk, hco⟩ : ∃ m k : ℕ, m = p ^ (Nat.card H).factorization p ∧
          m * k = Nat.card H ∧ Nat.Coprime m k :=
        ⟨_, _, rfl, Nat.ordProj_mul_ordCompl_eq_self (Nat.card H) p,
          Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN)⟩
      obtain ⟨A, hA⟩ := exists_subgroup_pow_eq_one hmk hco
      obtain ⟨B, hB⟩ := exists_subgroup_pow_eq_one (H := H) (m := k) (k := m)
        (by rw [mul_comm]; exact hmk) hco.symm
      haveI : A.Characteristic := characteristic_of_forall_pow _ A hA
      haveI : B.Characteristic := characteristic_of_forall_pow _ B hB
      haveI : A.Normal := Subgroup.normal_of_characteristic A
      haveI : B.Normal := Subgroup.normal_of_characteristic B
      -- The two subgroups intersect trivially, hence commute elementwise.
      have hdisj : Disjoint A B := by
        rw [Subgroup.disjoint_def]
        intro x hxA hxB
        have h1 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one ((hA x).mp hxA)
        have h2 : orderOf x ∣ k := orderOf_dvd_of_pow_eq_one ((hB x).mp hxB)
        have hg : Nat.gcd m k = 1 := hco
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd h1 h2))
      have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := fun a b =>
        Subgroup.commute_of_normal_of_disjoint A B ‹_› ‹_› hdisj _ _ a.2 b.2
      -- Every element factors as a product of an `A`-part and a `B`-part.
      obtain ⟨θ, hθ⟩ : ∃ θ : ↥A × ↥B ≃* H, ∀ y : ↥A × ↥B, θ y = (y.1 : H) * (y.2 : H) := by
        refine ⟨MulEquiv.ofBijective (A.subtype.noncommCoprod B.subtype hcomm) ⟨?_, ?_⟩,
          fun _ => rfl⟩
        · rw [injective_iff_map_eq_one]
          rintro ⟨a, b⟩ hab
          have hab' : (a : H) * (b : H) = 1 := hab
          have ha : (a : H) = ((b : H))⁻¹ := mul_eq_one_iff_eq_inv.mp hab'
          have haB : (a : H) ∈ B := ha ▸ B.inv_mem b.2
          have ha1 : (a : H) = 1 := Subgroup.disjoint_def.mp hdisj a.2 haB
          have hb1 : (b : H) = 1 := by rw [ha1, one_mul] at hab'; exact hab'
          simp [Prod.ext_iff, Subtype.ext_iff, ha1, hb1]
        · intro x
          obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (m : ℤ) + v * (k : ℤ) = 1 :=
            Int.isCoprime_iff_nat_coprime.mpr (by simpa using hco)
          have hmkZ : (m : ℤ) * (k : ℤ) = (Nat.card H : ℤ) := by exact_mod_cast hmk
          have hxN : x ^ (Nat.card H : ℤ) = 1 := by
            rw [zpow_natCast]
            exact pow_card_eq_one'
          have hmemA : x ^ (v * (k : ℤ)) ∈ A := by
            refine (hA _).mpr ?_
            rw [← zpow_natCast (x ^ (v * (k : ℤ))) m, ← zpow_mul,
              show v * (k : ℤ) * (m : ℤ) = (Nat.card H : ℤ) * v by linear_combination v * hmkZ,
              zpow_mul, hxN, one_zpow]
          have hmemB : x ^ (u * (m : ℤ)) ∈ B := by
            refine (hB _).mpr ?_
            rw [← zpow_natCast (x ^ (u * (m : ℤ))) k, ← zpow_mul,
              show u * (m : ℤ) * (k : ℤ) = (Nat.card H : ℤ) * u by linear_combination u * hmkZ,
              zpow_mul, hxN, one_zpow]
          refine ⟨(⟨_, hmemA⟩, ⟨_, hmemB⟩), ?_⟩
          have hx : x ^ (v * (k : ℤ)) * x ^ (u * (m : ℤ)) = x := by
            rw [← zpow_add, show v * (k : ℤ) + u * (m : ℤ) = 1 by linarith [huv], zpow_one]
          exact hx
      -- The `p`-part is nontrivial, so the complement is strictly smaller.
      have hcard2 : Nat.card ↥A * Nat.card ↥B = Nat.card H := by
        rw [← Nat.card_prod]
        exact Nat.card_congr θ.toEquiv
      have hA1 : 1 < Nat.card ↥A := by
        obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) p hpdvd
        have hgA : g ∈ A := by
          refine (hA g).mpr (orderOf_dvd_iff_pow_eq_one.mp ?_)
          rw [hg, hm]
          exact dvd_pow_self p (hp.factorization_pos_of_dvd hN hpdvd).ne'
        have hgne : g ≠ 1 := by
          intro hh
          rw [hh, orderOf_one] at hg
          exact hp.one_lt.ne hg
        haveI : Nontrivial ↥A := ⟨⟨⟨g, hgA⟩, 1, by simpa [Subtype.ext_iff] using hgne⟩⟩
        exact Finite.one_lt_card
      have hBle : Nat.card ↥B ≤ n := by
        have hBpos : 0 < Nat.card ↥B := Nat.card_pos
        have : Nat.card ↥B < Nat.card H := by
          rw [← hcard2]
          nlinarith
        omega
      -- The `p`-part is a `p`-group.
      have hpA : IsPGroup p ↥A := by
        intro a
        refine ⟨(Nat.card H).factorization p, ?_⟩
        have ha := (hA (a : H)).mp a.2
        rw [← hm]
        exact Subtype.ext (by simpa using ha)
      -- Assemble the tower.
      haveI : Finite (↥B ⋊[(MulAut.restrictChar B).comp φ] U) :=
        Finite.of_equiv _ SemidirectProduct.equivProd.symm
      have hBU : IsInverseGalois (↥B ⋊[(MulAut.restrictChar B).comp φ] U) :=
        ih ↥B U ((MulAut.restrictChar B).comp φ) hBle hU
      exact (h ↥A (↥B ⋊[(MulAut.restrictChar B).comp φ] U) p hpA _ hBU).of_mulEquiv
        (semidirectProductEquivOfProd A B φ θ hθ).symm

end Shafarevich
