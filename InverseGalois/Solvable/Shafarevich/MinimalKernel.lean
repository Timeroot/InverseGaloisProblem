/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.AbelianKernel

/-!
# From minimal elementary abelian kernels to abelian kernels

An embedding problem with abelian kernel can be filtered: inside the kernel one picks a subgroup
that is normal in the whole group, nontrivial, and of least possible order.  Such a subgroup is a
minimal normal subgroup, and a minimal normal abelian subgroup is elementary abelian, because its
`p`-torsion is again normal in the whole group for any prime `p` dividing its order and is
nontrivial by Cauchy's theorem.  Dividing it out leaves an embedding problem with abelian kernel of
strictly smaller order, so an induction reduces the arithmetic input of Shafarevich's theorem to
embedding problems whose kernel is a *minimal* elementary abelian group.

## Main results

* `Shafarevich.isMulCommutative_of_le` — a subgroup of a commutative subgroup is commutative.
* `Shafarevich.exists_prime_forall_pow_eq_one` — a minimal normal abelian subgroup of a finite
  group is elementary abelian.
* `Shafarevich.ElementaryAbelianKernelEP` — the statement that every embedding problem over `ℚ`
  whose kernel is a minimal elementary abelian normal subgroup is solvable.
* `Shafarevich.abelianKernel_of_elementaryAbelianKernel` — for an arbitrary quotient-closed
  realization predicate, embedding problems with abelian kernel follow from those with minimal
  elementary abelian kernel.
* `Shafarevich.abelianKernelEP_of_elementaryAbelianKernelEP` — its specialization to realizability
  over `ℚ`.
* `Shafarevich.isSolvable_isInverseGalois_of_elementaryAbelianKernelEP` — every finite solvable
  group is a Galois group over `ℚ`, granted `ElementaryAbelianKernelEP`.
* `Shafarevich.ElementaryAbelianKernelEPRegular`,
  `Shafarevich.abelianKernelEPRegular_of_elementaryAbelianKernelEPRegular` and
  `Shafarevich.isSolvable_isRegularInverseGalois_of_elementaryAbelianKernelEPRegular` — the regular
  analogues over `ℚ(T)`.
-/

namespace Shafarevich

/-! ## Minimal normal abelian subgroups are elementary abelian -/

/-- **A subgroup of a commutative subgroup is commutative.** -/
theorem isMulCommutative_of_le {G : Type*} [Group G] {H K : Subgroup G} [IsMulCommutative ↥K]
    (hle : H ≤ K) : IsMulCommutative ↥H :=
  ⟨⟨fun a b =>
    Subtype.ext (Subgroup.mul_comm_of_mem_isMulCommutative K (hle a.2) (hle b.2))⟩⟩

/-- **A minimal normal abelian subgroup of a finite group is elementary abelian.**

If `N` is a nontrivial abelian normal subgroup of a finite group `G` that contains no normal
subgroup of `G` other than `⊥` and `N` itself, then there is a prime `p` with `x ^ p = 1` for every
`x ∈ N`: indeed the `p`-torsion of `N`, for any prime `p` dividing the order of `N`, is a normal
subgroup of `G` inside `N`, and it is nontrivial by Cauchy's theorem. -/
theorem exists_prime_forall_pow_eq_one {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] [IsMulCommutative ↥N] (hN : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    ∃ p : ℕ, p.Prime ∧ ∀ x ∈ N, x ^ p = 1 := by
  have hcard : Nat.card ↥N ≠ 1 := fun hh => hN (Subgroup.eq_bot_of_card_eq N hh)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, ?_⟩
  -- The `p`-torsion of `N`.
  let M : Subgroup G :=
    { carrier := {x : G | x ∈ N ∧ x ^ p = 1}
      one_mem' := ⟨one_mem N, one_pow p⟩
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        have hc : Commute a b := Subgroup.mul_comm_of_mem_isMulCommutative N ha hb
        exact ⟨mul_mem ha hb, by rw [hc.mul_pow, hap, hbp, one_mul]⟩
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        exact ⟨inv_mem ha, by rw [inv_pow, hap, inv_one]⟩ }
  have hmem : ∀ x : G, x ∈ M ↔ x ∈ N ∧ x ^ p = 1 := fun _ => Iff.rfl
  haveI hMnormal : M.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hmem] at ha ⊢
    exact ⟨Subgroup.Normal.conj_mem ‹N.Normal› a ha.1 g,
      by rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩
  have hMle : M ≤ N := fun _ hx => ((hmem _).mp hx).1
  -- Cauchy's theorem makes the `p`-torsion nontrivial.
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpd
  have hyM : (y : G) ∈ M := by
    refine (hmem _).mpr ⟨y.2, ?_⟩
    have : y ^ p = 1 := hy ▸ pow_orderOf_eq_one y
    simpa using congrArg (Subgroup.subtype N) this
  have hMbot : M ≠ ⊥ := by
    intro hbot
    have hy1 : (y : G) = 1 := by rw [hbot] at hyM; simpa using hyM
    have : y = 1 := Subtype.ext (by simpa using hy1)
    rw [this, orderOf_one] at hy
    exact hp.one_lt.ne hy
  rcases hmin M hMnormal hMle with hbot | heq
  · exact absurd hbot hMbot
  · intro x hx
    exact ((hmem x).mp (heq ▸ hx)).2

/-! ## Embedding problems with minimal elementary abelian kernel -/

/-- **Every embedding problem over `ℚ` with minimal elementary abelian kernel is solvable.**

If a finite group `W` is a Galois group over `ℚ` and `π : E →* W` is a surjection of finite groups
whose kernel is abelian, killed by a prime `p`, and minimal among the nontrivial normal subgroups
of `E`, then `E` too is a Galois group over `ℚ`. -/
def ElementaryAbelianKernelEP : Prop :=
  ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (p : ℕ) [Fact p.Prime] (π : E →* W),
    Function.Surjective ⇑π → IsMulCommutative ↥π.ker →
    (∀ x : ↥π.ker, x ^ p = 1) →
    (∀ N : Subgroup E, N.Normal → N ≤ π.ker → N = ⊥ ∨ N = π.ker) →
    IsInverseGalois W → IsInverseGalois E

/-- **Every embedding problem with minimal elementary abelian kernel is solvable regularly over
`ℚ(T)`.**

The regular analogue of `ElementaryAbelianKernelEP`. -/
def ElementaryAbelianKernelEPRegular : Prop :=
  ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (p : ℕ) [Fact p.Prime] (π : E →* W),
    Function.Surjective ⇑π → IsMulCommutative ↥π.ker →
    (∀ x : ↥π.ker, x ^ p = 1) →
    (∀ N : Subgroup E, N.Normal → N ≤ π.ker → N = ⊥ ∨ N = π.ker) →
    IsRegularInverseGalois W → IsRegularInverseGalois E

/-! ## The reduction -/

/-- **Embedding problems with abelian kernel reduce to embedding problems with minimal elementary
abelian kernel.**

The statement is for an arbitrary realization predicate `P` that is inherited by quotients.  The
argument is an induction on the order of the kernel: if the kernel is trivial the surjection is an
isomorphism, and otherwise one picks a nontrivial normal subgroup `N` of `E` inside the kernel of
least possible order.  It is abelian, minimal, and hence elementary abelian, the induced surjection
`E ⧸ N →* W` again has abelian kernel but of strictly smaller order, and `E →* E ⧸ N` is an
embedding problem with minimal elementary abelian kernel. -/
theorem abelianKernel_of_elementaryAbelianKernel {P : ∀ (G : Type) [Group G], Prop}
    (hquot : IsQuotientClosed P)
    (h : ∀ (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (p : ℕ) [Fact p.Prime]
      (π : E →* W), Function.Surjective ⇑π → IsMulCommutative ↥π.ker →
      (∀ x : ↥π.ker, x ^ p = 1) →
      (∀ N : Subgroup E, N.Normal → N ≤ π.ker → N = ⊥ ∨ N = π.ker) → P W → P E)
    (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (π : E →* W)
    (hπ : Function.Surjective ⇑π) (hcomm : IsMulCommutative ↥π.ker) (hW : P W) : P E := by
  classical
  suffices key : ∀ (n : ℕ) (E W : Type) [Group E] [Finite E] [Group W] [Finite W] (π : E →* W),
      Function.Surjective ⇑π → IsMulCommutative ↥π.ker → Nat.card ↥π.ker ≤ n → P W → P E from
    key (Nat.card ↥π.ker) E W π hπ hcomm le_rfl hW
  clear! E W
  -- The order of a kernel over a surjection.
  have hcount : ∀ (A B : Type) [Group A] [Finite A] [Group B] (f : A →* B),
      Function.Surjective ⇑f → Nat.card A = Nat.card B * Nat.card ↥f.ker := by
    intro A B _ _ _ f hf
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  intro n
  induction n with
  | zero =>
    intro E W _ _ _ _ π _ _ hcard _
    exact absurd hcard (not_le.mpr Nat.card_pos)
  | succ n ih =>
    intro E W _ _ _ _ π hπ hcomm hcard hW
    haveI := hcomm
    by_cases hbot : π.ker = ⊥
    · exact hquot.of_mulEquiv
        (MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hbot, hπ⟩).symm hW
    -- A nontrivial normal subgroup of `E` inside the kernel, of least possible order.
    have hex : ∃ m : ℕ, ∃ N : Subgroup E, N.Normal ∧ N ≤ π.ker ∧ N ≠ ⊥ ∧ Nat.card ↥N = m :=
      ⟨_, π.ker, inferInstance, le_rfl, hbot, rfl⟩
    obtain ⟨N, hNnormal, hNle, hNbot, hNcard⟩ := Nat.find_spec hex
    have hfind : ∀ M : Subgroup E, M.Normal → M ≤ π.ker → M ≠ ⊥ → Nat.find hex ≤ Nat.card ↥M :=
      fun M h₁ h₂ h₃ => Nat.find_min' hex ⟨M, h₁, h₂, h₃, rfl⟩
    haveI := hNnormal
    haveI : IsMulCommutative ↥N := isMulCommutative_of_le hNle
    have hminN : ∀ M : Subgroup E, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
      intro M hM hMN
      by_cases hMbot : M = ⊥
      · exact Or.inl hMbot
      · refine Or.inr (Subgroup.eq_of_le_of_card_ge hMN ?_)
        have := hfind M hM (hMN.trans hNle) hMbot
        omega
    obtain ⟨p, hp, hpow⟩ := exists_prime_forall_pow_eq_one N hNbot hminN
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite (E ⧸ N) := Quotient.finite _
    -- The induced surjection onto `W`.
    set π' : E ⧸ N →* W :=
      QuotientGroup.lift N π fun x hx => MonoidHom.mem_ker.mp (hNle hx) with hπ'def
    have hlift : ∀ x : E, π' (QuotientGroup.mk' N x) = π x := by
      intro x; rw [hπ'def]; rfl
    have hπ'surj : Function.Surjective ⇑π' := by
      intro w
      obtain ⟨x, rfl⟩ := hπ w
      exact ⟨QuotientGroup.mk' N x, hlift x⟩
    have hkereq : π'.ker = π.ker.map (QuotientGroup.mk' N) := by
      ext x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
      simp only [MonoidHom.mem_ker, Subgroup.mem_map, hlift]
      refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have hzN : z⁻¹ * y ∈ N := QuotientGroup.eq.mp hzy
      have hy : y = z * (z⁻¹ * y) := by group
      rw [hy]
      exact mul_mem hz (hNle hzN)
    haveI : IsMulCommutative ↥π'.ker := by rw [hkereq]; infer_instance
    -- The new kernel is strictly smaller.
    have h₁ : Nat.card E = Nat.card W * Nat.card ↥π.ker := hcount E W π hπ
    have h₂ : Nat.card (E ⧸ N) = Nat.card W * Nat.card ↥π'.ker := hcount _ W π' hπ'surj
    have h₃ : Nat.card E = Nat.card (E ⧸ N) * Nat.card ↥N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hWpos : 0 < Nat.card W := Nat.card_pos
    have hcancel : Nat.card ↥π.ker = Nat.card ↥π'.ker * Nat.card ↥N := by
      refine Nat.eq_of_mul_eq_mul_left hWpos ?_
      rw [← mul_assoc, ← h₂, ← h₃, h₁]
    have hN1 : Nat.card ↥N ≠ 1 := fun hh => hNbot (Subgroup.eq_bot_of_card_eq N hh)
    have hNpos : 0 < Nat.card ↥N := Nat.card_pos
    have hkpos : 0 < Nat.card ↥π'.ker := Nat.card_pos
    have hN2 : 2 ≤ Nat.card ↥N := by omega
    have hcard' : Nat.card ↥π'.ker ≤ n := by nlinarith
    -- The kernel of `E →* E ⧸ N` is exactly `N`.
    have hkq : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
    refine h E (E ⧸ N) p (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      (by rw [hkq]; infer_instance) (fun x => ?_) (fun M hM hMle => ?_)
      (ih (E ⧸ N) W π' hπ'surj inferInstance hcard' hW)
    · have hx : (x : E) ∈ N := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)
      exact Subtype.ext (by simpa using hpow (x : E) hx)
    · rw [hkq] at hMle ⊢
      exact hminN M hM hMle

/-- **Embedding problems over `ℚ` with abelian kernel reduce to embedding problems with minimal
elementary abelian kernel.** -/
theorem abelianKernelEP_of_elementaryAbelianKernelEP (h : ElementaryAbelianKernelEP) :
    AbelianKernelEP :=
  fun E W _ _ _ _ π hπ hcomm hW =>
    abelianKernel_of_elementaryAbelianKernel isQuotientClosed_isInverseGalois
      (fun E W _ _ _ _ p _ π hπ hcomm hpow hmin hW => h E W p π hπ hcomm hpow hmin hW)
      E W π hπ hcomm hW

/-- **Embedding problems with abelian kernel reduce to embedding problems with minimal elementary
abelian kernel, regularly over `ℚ(T)`.** -/
theorem abelianKernelEPRegular_of_elementaryAbelianKernelEPRegular
    (h : ElementaryAbelianKernelEPRegular) : AbelianKernelEPRegular :=
  fun E W _ _ _ _ π hπ hcomm hW =>
    abelianKernel_of_elementaryAbelianKernel isQuotientClosed_isRegularInverseGalois
      (fun E W _ _ _ _ p _ π hπ hcomm hpow hmin hW => h E W p π hπ hcomm hpow hmin hW)
      E W π hπ hcomm hW

/-! ## Shafarevich's theorem, granted embedding problems with minimal elementary abelian kernel -/

/-- **Shafarevich's theorem, granted the solvability of embedding problems with minimal elementary
abelian kernel.**

If every embedding problem over `ℚ` whose kernel is a minimal elementary abelian normal subgroup is
solvable, then every finite solvable group is a Galois group over `ℚ`. -/
theorem isSolvable_isInverseGalois_of_elementaryAbelianKernelEP (h : ElementaryAbelianKernelEP)
    (G : Type) [Group G] [Finite G] [IsSolvable G] : IsInverseGalois G :=
  isSolvable_isInverseGalois_of_abelianKernelEP (abelianKernelEP_of_elementaryAbelianKernelEP h) G

/-- **The regular form of Shafarevich's theorem, granted the solvability of embedding problems with
minimal elementary abelian kernel.**

If every embedding problem whose kernel is a minimal elementary abelian normal subgroup is solvable
regularly over `ℚ(T)`, then every finite solvable group is the Galois group of a regular extension
of `ℚ(T)`. -/
theorem isSolvable_isRegularInverseGalois_of_elementaryAbelianKernelEPRegular
    (h : ElementaryAbelianKernelEPRegular) (G : Type) [Group G] [Finite G] [IsSolvable G] :
    IsRegularInverseGalois G :=
  isSolvable_isRegularInverseGalois_of_abelianKernelEPRegular
    (abelianKernelEPRegular_of_elementaryAbelianKernelEPRegular h) G

end Shafarevich
