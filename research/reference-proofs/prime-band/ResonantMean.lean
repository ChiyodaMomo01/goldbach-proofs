import NonresonantBand

namespace GoldbachMinor
open Finset

/-- Exact mean on a progression of step d and length M that closes modulo q.
No coprimality assumption on the step or the conductor. -/
theorem ram_closed_progression (q d M s : ℕ) (hq : 0<q) (hclose : q ∣ M*d) :
    ∑ j ∈ range M, ram q (s+j*d) =
      if q ∣ d then (M:ℝ)*ram q s else 0 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [ram_trace]
  rw [sum_comm]
  have one_root (z : ℂ) (hz : z∈primitiveRoots q ℂ) :
      (∑ j ∈ range M, z^(s+j*d)) = if q∣d then (M:ℂ)*z^s else 0 := by
    have prim := (mem_primitiveRoots hq).mp hz
    have eq : (∑ j ∈ range M, z^(s+j*d)) = z^s * ∑ j ∈ range M, (z^d)^j := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by rw [pow_add,Nat.mul_comm j d,pow_mul]
    rw [eq]
    by_cases hd : q∣d
    · simp [hd,(prim.pow_eq_one_iff_dvd d).mpr hd,mul_comm]
    · have cyc : (z^d)^M=1 := by
        rw [← pow_mul,Nat.mul_comm]
        exact (prim.pow_eq_one_iff_dvd _).mpr hclose
      simp [hd,geom_sum_eq ((prim.pow_eq_one_iff_dvd d).not.mpr hd),cyc]
  rw [sum_congr rfl one_root]
  by_cases hd : q∣d
  · simp [hd,ram_trace,mul_sum]
  · simp [hd]

/-- Extract a single residue in a rectangular listing of a complete period. -/
private theorem sum_one_residue (M d s : ℕ) (hs : s<d) (f : ℕ→ℝ) :
    (∑ k ∈ range (M*d), if k%d=s then f k else 0) = ∑ j ∈ range M, f (j*d+s) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]
    congr 1
    refine (sum_congr rfl fun k hk => ?_).trans
      (show (∑ k ∈ range d, if k=s then f (M*d+k) else 0) = f (M*d+s) by simp [hs])
    simp [Nat.add_mod,Nat.mod_eq_of_lt (mem_range.mp hk)]

/-- The contribution from a single residue row at any conductor dividing the
period. Only the conductors dividing the row's modulus see that row's mean. -/
theorem ram_residue_row (P d q s : ℕ) (hd : d∣P) (hq : 0<q) (hQ : q∣P) (hs : s<d) :
    (∑ k ∈ range P, if k%d=s then ram q k else 0) =
      if q∣d then ((P/d:ℕ):ℝ)*ram q s else 0 := by
  have split := Nat.div_mul_cancel hd
  conv_lhs => rw [← split]
  rw [sum_one_residue _ _ _ hs]
  simpa only [Nat.add_comm s] using ram_closed_progression q d (P/d) s hq (by rw [split]; exact hQ)

/-- Exact complete-period average of the two translated divisibility indicators. -/
theorem paired_divisor_row (P d q n : ℕ) (hP : 0<P) (hd : d∣P) (hq : 0<q) (hQ : q∣P) (hn : P≤n) :
    (∑ k ∈ range P, ((if d∣n-k then 1 else 0)+(if d∣n+k then 1 else 0):ℝ)*ram q k) =
      if q∣d then 2*((P/d:ℕ):ℝ)*ram q n else 0 := by
  have hd0 : 0<d := Nat.pos_of_dvd_of_pos hd hP
  let s := (d-n%d)%d
  have hns : d ∣ n+s := by
    apply Nat.modEq_zero_iff_dvd.mp
    calc
      n+s ≡ n%d+(d-n%d) [MOD d] := (Nat.mod_modEq n d).symm.add (Nat.mod_modEq ..)
      _ = d := by have := Nat.mod_lt n hd0; omega
      _ ≡ 0 [MOD d] := Nat.modulus_modEq_zero
  have neg (k : ℕ) (hk : k<P) : d∣n-k ↔ k%d=n%d := (Nat.modEq_iff_dvd' (by omega : k≤n)).symm
  have pos (k : ℕ) : d∣n+k ↔ k%d=s := by
    have eq : d∣n+k ↔ k ≡ s [MOD d] := by
      constructor
      · intro h
        exact Nat.ModEq.add_left_cancel' n (h.modEq_zero_nat.trans hns.modEq_zero_nat.symm)
      · intro h
        exact Nat.modEq_zero_iff_dvd.mp ((h.add_left n).trans hns.modEq_zero_nat)
    exact eq.trans (by dsimp only [Nat.ModEq]; rw [Nat.mod_eq_of_lt (show s<d from Nat.mod_lt _ hd0)])
  have rows :
      (∑ k ∈ range P, ((if d∣n-k then 1 else 0)+(if d∣n+k then 1 else 0):ℝ)*ram q k) =
      (∑ k ∈ range P, if k%d=n%d then ram q k else 0) +
      (∑ k ∈ range P, if k%d=s then ram q k else 0) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    simp only [neg k (mem_range.mp hk),pos k,add_mul,ite_mul,one_mul,zero_mul]
  rw [rows,ram_residue_row P d q (n%d) hd hq hQ (Nat.mod_lt _ hd0),
    ram_residue_row P d q s hd hq hQ (Nat.mod_lt _ hd0)]
  by_cases hqd : q∣d
  · have minus : ram q (n%d) = ram q n := by
      unfold ram
      apply sum_congr rfl
      intro j hj
      simp only [Nat.dvd_mod_iff ((Nat.dvd_of_mem_divisors hj).trans hqd)]
    have plus : ram q s = ram q n := by
      unfold ram
      apply sum_congr rfl
      intro j hj
      have hjd := (Nat.dvd_of_mem_divisors hj).trans hqd
      have hsum := hjd.trans hns
      have iff : j∣s ↔ j∣n := by
        constructor
        · intro h; exact (Nat.dvd_add_iff_left h).mpr hsum
        · intro h; exact (Nat.dvd_add_iff_right h).mpr hsum
      simp only [iff]
    simp only [hqd,ite_true,minus,plus]
    ring
  · simp [hqd]

/-- A support contains the prime two in every term of the binary shape. -/
def evenSupport (A : Finset ℕ) := factorDivisor (insert 2 A)

private theorem support_dvd (y m : ℕ) (A : Finset ℕ) (hA : A⊆shapePrimes y) :
    evenSupport A ∣ m ↔ 2∣m ∧ ∀ p∈A, p∣m := by
  constructor
  · intro h
    exact ⟨(dvd_prod_of_mem id (mem_insert_self 2 A)).trans h,
      fun p hp => (dvd_prod_of_mem id (mem_insert_of_mem hp)).trans h⟩
  · rintro ⟨h2,hp⟩
    apply prod_primes_dvd
    · intro p h
      rcases mem_insert.mp h with rfl|h
      · exact Nat.prime_two.prime
      · exact (Nat.mem_primesLE.mp (mem_filter.mp (hA h)).1).2.prime
    · intro p h
      rcases mem_insert.mp h with rfl|h
      · exact h2
      · exact hp _ h

private theorem shape_divisor_sum (y m : ℕ) : binaryShape y m =
    ∑ A ∈ (shapePrimes y).powerset,
      if evenSupport A ∣ m then ∏ p ∈ A, goldbachFactor p else 0 := by
  by_cases h : 2∣m
  · let S := shapePrimes y
    change (if 2∣m then oddFactorProduct S m else 0) = _
    rw [ite_eq_left h,oddFactorProduct,support_expansion S (fun _ hp =>
      (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2)]
    apply sum_congr rfl
    intro A hA
    have sub := mem_powerset.mp hA
    have eq : factorDivisor A ∣ m ↔ evenSupport A ∣ m := by
      rw [support_dvd y m A sub]
      refine ⟨fun hd => ⟨h,fun p hp => (dvd_prod_of_mem id hp).trans hd⟩,?_⟩
      exact fun hh => prod_primes_dvd m (fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp (sub hp)).1).2.prime) hh.2
    simp only [eq]
  · change (if 2∣m then _ else 0) = _
    rw [ite_eq_right h]
    symm
    refine sum_eq_zero fun A hA => ite_eq_right ?_
    exact fun hd => h ((support_dvd _ _ _ (mem_powerset.mp hA)).mp hd).1

/-- Exact arithmetic mean of the two translated cutoff shapes against a
Ramanujan sum on the common factorial period. -/
theorem paired_shape_period_sum (y q n : ℕ) (hy : 2≤y) (hq : 0<q)
    (hQ : q∣y.factorial) (hn : y.factorial≤n) :
    (∑ k ∈ range y.factorial, (binaryShape y (n-k)+binaryShape y (n+k))*ram q k) =
    (2*ram q n)*∑ A ∈ (shapePrimes y).powerset,
      if q∣evenSupport A then ((y.factorial/evenSupport A:ℕ):ℝ)*(∏ p ∈ A, goldbachFactor p) else 0 := by
  let W (A : Finset ℕ) := ∏ p ∈ A, goldbachFactor p
  let I (A : Finset ℕ) (m : ℕ) : ℝ := if evenSupport A ∣ m then 1 else 0
  have expand (m : ℕ) : binaryShape y m = ∑ A ∈ (shapePrimes y).powerset, W A*I A m := by
    rw [shape_divisor_sum]
    apply sum_congr rfl
    intro A _
    simp [I,W,mul_ite]
  simp_rw [expand, ← sum_add_distrib,sum_mul]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro A hA
  have div : evenSupport A ∣ y.factorial := (support_dvd _ _ _ (mem_powerset.mp hA)).mpr
    ⟨Nat.dvd_factorial (by decide) hy,fun p hp => by
      have hh := Nat.mem_primesLE.mp (mem_filter.mp ((mem_powerset.mp hA) hp)).1
      exact Nat.dvd_factorial hh.2.pos hh.1⟩
  simp_rw [← mul_add,mul_assoc,← mul_sum]
  have row := paired_divisor_row y.factorial (evenSupport A) q n (Nat.factorial_pos _) div hq hQ hn
  change W A * (∑ k ∈ range y.factorial, _) = _
  rw [show (∑ k ∈ range y.factorial, (I A (n-k)+I A (n+k))*ram q k) = _ from row]
  by_cases hd : q∣evenSupport A
  · simp [hd,W]; ring
  · simp [hd]

/-- Although the factorial contains prime powers, no nonsquarefree conductor
has a nonzero complete-period mean. -/
theorem nonsquarefree_shape_mean_zero (y q n : ℕ) (hy : 2≤y) (hq : 0<q)
    (hQ : q∣y.factorial) (hn : y.factorial≤n) (hsq : ¬ Squarefree q) :
    (∑ k ∈ range y.factorial, (binaryShape y (n-k)+binaryShape y (n+k))*ram q k) = 0 := by
  rw [paired_shape_period_sum y q n hy hq hQ hn]
  suffices z : (∑ A ∈ (shapePrimes y).powerset,
      if q∣evenSupport A then ((y.factorial/evenSupport A:ℕ):ℝ)*(∏ p ∈ A, goldbachFactor p) else 0) = 0 by
    rw [z,mul_zero]
  apply sum_eq_zero
  intro A hA
  apply ite_eq_right
  intro hd
  apply hsq
  have primes (p) (hp : p∈insert 2 A) : Nat.Prime p := by
    rcases mem_insert.mp hp with rfl|hp
    · exact Nat.prime_two
    · exact (Nat.mem_primesLE.mp (mem_filter.mp ((mem_powerset.mp hA) hp)).1).2
  have sq : Squarefree (evenSupport A) := squarefree_prod_of_pairwise_isCoprime
    (fun i hi j hj hij => Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (primes i hi) (primes j hj)).mpr hij))
    (fun p hp => (primes p hp).prime.squarefree)
  exact sq.squarefree_of_dvd hd

/-- Centring an arbitrary periodic real sequence by its complete-period mean leaves
at most a single incomplete block on every shifted window. -/
theorem period_mean_prefix (P K H : ℕ) (u : ℕ→ℝ) (C : ℝ) (hp : 0<P) (hC : 0≤C)
    (period : ∀ k, u (k+P)=u k) (bound : ∀ k, |u k|≤C) :
    let m := (∑ k ∈ range P, u k)/P
    |∑ k ∈ Ioc K H, (u k-m)| ≤ 2*P*C := by
  let m := (∑ k ∈ range P, u k)/P
  have hpr : (0:ℝ)<P := by exact_mod_cast hp
  have mean : |m|≤C := by
    rw [show |m|=|∑ k ∈ range P, u k|/(P:ℝ) by rw [abs_div,abs_of_pos hpr],div_le_iff₀ hpr]
    calc
      _ ≤ _ := abs_sum_le_sum_abs ..
      _ ≤ ∑ _k ∈ range P, C := sum_le_sum (fun k _ => bound k)
      _ = _ := by simp [mul_comm]
  have block (s : ℕ) : ∑ k ∈ range P, u (s+k) = ∑ k ∈ range P, u k := by
    induction s with
    | zero => simp
    | succ s ih =>
      have tail := sum_range_succ' (fun k => u (s+k)) P
      rw [sum_range_succ,period] at tail
      simp only [Nat.add_zero] at tail
      simp_rw [show ∀ k, s+1+k=s+(k+1) by intro; omega]
      linarith only [tail,ih]
  have centred (s : ℕ) : ∑ k ∈ range P, (u (s+k)-m)=0 := by
    rw [sum_sub_distrib,block,sum_const,card_range,nsmul_eq_mul]
    dsimp [m]; field_simp; simp
  change |∑ k ∈ Ioc K H, (u k-m)| ≤ _
  exact (zero_block_window (fun k => u k-m) P K H (C+C) hp (by positivity)
    (fun k => (abs_sub ..).trans (add_le_add (bound k) mean)) centred).trans_eq (by ring)

/-- The part of the normalized local density visible to a given conductor. -/
noncomputable def conductorWeight (y q : ℕ) : ℝ :=
  ∑ A ∈ (shapePrimes y).powerset, if q∣evenSupport A then ∏ p ∈ A, goldbachFactor p/p else 0

theorem conductorWeight_bounds (y q : ℕ) : 0≤conductorWeight y q ∧ conductorWeight y q≤Real.exp 9 := by
  let S := shapePrimes y
  have prime (p : ℕ) (hp : p∈S) : 3≤p := (mem_filter.mp hp).2
  have nonneg (A : Finset ℕ) (ha : A∈S.powerset) : 0≤∏ p ∈ A, goldbachFactor p/p := by
    apply prod_nonneg
    intro p hp
    have hr : (3:ℝ)≤p := by exact_mod_cast prime p ((mem_powerset.mp ha) hp)
    unfold goldbachFactor
    exact div_nonneg (one_div_nonneg.mpr (by linarith)) (by positivity)
  constructor
  · exact sum_nonneg fun A ha => by split_ifs <;> first | exact nonneg A ha | exact le_rfl
  · calc
      _ ≤ ∑ A ∈ S.powerset, ∏ p ∈ A, goldbachFactor p/p := sum_le_sum fun A ha => by
        split_ifs <;> first | exact le_rfl | exact nonneg A ha
      _ = ∏ p ∈ S, factorMean p := (prod_one_add _).symm
      _ ≤ _ := factor_mean_uniform S prime

/-- After normalization the arithmetic average factors into the Ramanujan sum
at the target and a nonnegative local weight depending only on y and q. -/
theorem paired_shape_mean (y q n : ℕ) (hy : 2≤y) (hq : 0<q) (hQ : q∣y.factorial)
    (hn : y.factorial≤n) :
    (∑ k ∈ range y.factorial, (binaryShape y (n-k)+binaryShape y (n+k))*ram q k)/(y.factorial:ℝ)
      = ram q n*conductorWeight y q := by
  rw [paired_shape_period_sum y q n hy hq hQ hn,conductorWeight,div_eq_mul_inv]
  rw [show (2*ram q n)*(∑ A ∈ (shapePrimes y).powerset,
      if q∣evenSupport A then ((y.factorial/evenSupport A:ℕ):ℝ)*(∏ p ∈ A, goldbachFactor p) else 0)*
      (y.factorial:ℝ)⁻¹ = ram q n*(∑ A ∈ (shapePrimes y).powerset,
      2*(if q∣evenSupport A then ((y.factorial/evenSupport A:ℕ):ℝ)*(∏ p ∈ A, goldbachFactor p) else 0)/
        (y.factorial:ℝ)) by simp_rw [div_eq_mul_inv,← sum_mul,← mul_sum]; ring]
  congr 1
  apply sum_congr rfl
  intro A hA
  by_cases h : q∣evenSupport A
  · simp only [h,ite_true,prod_div_distrib]
    have two : 2∉A := fun hm => by
      have h3 : 3≤2 := (mem_filter.mp (mem_powerset.mp hA hm)).2
      omega
    have hd : evenSupport A ∣ y.factorial := (support_dvd _ _ _ (mem_powerset.mp hA)).mpr
      ⟨Nat.dvd_factorial (by decide) hy,fun p hp => by
        have hh := Nat.mem_primesLE.mp (mem_filter.mp ((mem_powerset.mp hA) hp)).1
        exact Nat.dvd_factorial hh.2.pos hh.1⟩
    have prod : (evenSupport A:ℝ) = 2*(∏ p ∈ A, (p:ℝ)) := by simp [evenSupport,factorDivisor,prod_insert two]
    have pos : 0<(∏ p ∈ A, (p:ℝ)) := prod_pos fun p hp => by
      exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp (mem_powerset.mp hA hp)).1).2.pos
    have mul : ((y.factorial/evenSupport A:ℕ):ℝ)*(evenSupport A:ℝ)=y.factorial := by
      exact_mod_cast Nat.div_mul_cancel hd
    have fac : (0:ℝ)<y.factorial := by exact_mod_cast Nat.factorial_pos y
    rw [prod] at mul
    field_simp
    nlinarith only [congrArg (fun t : ℝ => t * ∏ p ∈ A, goldbachFactor p) mul]
  · simp [h]

#print axioms nonsquarefree_shape_mean_zero
#print axioms paired_shape_period_sum
#print axioms paired_shape_mean
end GoldbachMinor
