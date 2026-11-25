import FirstBand

namespace GoldbachMinor

open Finset GoldbachWeight Filter
open scoped Topology

private theorem ram_trace (q k : ℕ) : (ram q k : ℂ) = ∑ z ∈ primitiveRoots q ℂ, z^k := by
  rw [GoldbachRamanujan.primitive_power_sum]
  unfold ram
  push_cast
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp

private theorem abs_ram_le (q k : ℕ) (hq : 0 < q) : |ram q k| ≤ q := by
  calc
    _ = ‖(ram q k:ℂ)‖ := by simp
    _ ≤ ∑ z ∈ primitiveRoots q ℂ, ‖z^k‖ := by rw [ram_trace]; exact norm_sum_le ..
    _ = ((primitiveRoots q ℂ).card:ℝ) := by
      calc
        _ = ∑ _z ∈ primitiveRoots q ℂ, (1:ℝ) := sum_congr rfl (fun z hz => by
          rw [norm_pow,((mem_primitiveRoots hq).mp hz).norm'_eq_one hq.ne',one_pow])
        _ = _ := by simp
    _ ≤ _ := by rw [Complex.card_primitiveRoots]; exact_mod_cast Nat.totient_le q

/-- The full period along a progression cancels unless its step is divisible by the conductor. -/
theorem ram_progression_period (q P s : ℕ) (hq : 0<q) (h : ¬ q ∣ P) :
    ∑ j ∈ range q, ram q (s+j*P) = 0 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_zero,ram_trace]
  rw [sum_comm]
  apply sum_eq_zero
  intro z hz
  have prim := (mem_primitiveRoots hq).mp hz
  have ne := (prim.pow_eq_one_iff_dvd P).not.mpr h
  have cyc : (z^P)^q=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul,prim.pow_eq_one,one_pow]
  calc
    _ = z^s * ∑ j ∈ range q, (z^P)^j := by
      rw [mul_sum]; apply sum_congr rfl; intro j _; rw [pow_add,Nat.mul_comm j P,pow_mul]
    _ = 0 := by simp [geom_sum_eq ne,cyc]

private theorem block_rows (a : ℕ → ℝ) (s P q : ℕ) :
    ∑ k ∈ range (q*P), a (s+k) = ∑ r ∈ range P, ∑ j ∈ range q, a (s+j*P+r) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul,sum_range_add,ih]
    simp_rw [sum_range_succ (n:=q),sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro r _
    rw [Nat.add_assoc]

private theorem periodic_block (b : ℕ→ℝ) (q P s : ℕ) (hq : 0<q) (h : ¬q ∣ P) :
    ∑ k ∈ range (q*P), b ((s+k)%P) * ram q (s+k) = 0 := by
  rw [block_rows (fun k => b (k%P)*ram q k)]
  apply sum_eq_zero
  intro r _
  have shifted (j : ℕ) : (s+j*P+r)%P = (s+r)%P := by
    rw [show s+j*P+r=s+r+j*P by omega, Nat.add_mul_mod_self_right]
  simp_rw [shifted,show ∀ j : ℕ, s+j*P+r=s+r+j*P by intro; omega, ← mul_sum]
  rw [ram_progression_period q P _ hq h,mul_zero]

/-- Only the final incomplete period contributes on an arbitrary window. -/
theorem periodic_window_bound (b : ℕ→ℝ) (q P K H : ℕ) (C : ℝ)
    (hp : 0<P) (hq : 0<q) (h : ¬q ∣ P) (hC : 0≤C) (hb : ∀ r<P, |b r|≤C) :
    |∑ k ∈ Ioc K H, b (k%P)*ram q k| ≤ C*(P:ℝ)*q^2 := by
  let G := q*P
  let f (k : ℕ) := b (k%P)*ram q k
  have zero (m s : ℕ) : ∑ k ∈ range (m*G), f (s+k) = 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.succ_mul,sum_range_add,ih,zero_add]
      simp_rw [← Nat.add_assoc]
      exact periodic_block b q P _ hq h
  have bound (s T : ℕ) : |∑ k ∈ range T, f (s+k)| ≤ C*P*q^2 := by
    have split : T = (T/G)*G + T%G := (Nat.div_add_mod' T G).symm
    conv_lhs => rw [split,sum_range_add,zero,zero_add]
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _k ∈ range (T%G), C*(q:ℝ) := by
        apply sum_le_sum
        intro k _
        unfold f
        rw [abs_mul]
        exact mul_le_mul (hb _ (Nat.mod_lt _ hp)) (abs_ram_le q _ hq) (abs_nonneg _) hC
      _ = (T%G:ℕ)*(C*(q:ℝ)) := by simp
      _ ≤ (G:ℝ)*(C*(q:ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt T (Nat.mul_pos hq hp)).le) (by positivity)
      _ = _ := by unfold G; push_cast; ring
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range]
  exact bound _ _

/-- The signed linearized contribution from denominators above B on an offset window. -/
noncomputable def largeDenominatorSum (Q n B K H : ℕ) (mass : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Ioc B Q, (2*(Q:ℝ)/((q:ℝ)*n)) * ∑ k ∈ Ioc K H, mass k*ram q k

theorem large_denominator_center (Q n B K H P : ℕ) (mass b : ℕ → ℝ)
    (C : ℝ) (hn : 0<n) (hp : 0<P) (hpB : P≤B) (hC : 0≤C) (hb : ∀ r<P, |b r|≤C) :
    |largeDenominatorSum Q n B K H mass -
      largeDenominatorSum Q n B K H (fun k => mass k - b (k%P))| ≤
      2*C*P*(Q:ℝ)^3/n := by
  have identity : largeDenominatorSum Q n B K H mass -
      largeDenominatorSum Q n B K H (fun k => mass k - b (k%P)) =
      largeDenominatorSum Q n B K H (fun k => b (k%P)) := by
    unfold largeDenominatorSum
    simp_rw [sub_mul,sum_sub_distrib,mul_sub,sum_sub_distrib]
    ring
  rw [identity]
  let D := (2*C*P*(Q:ℝ)^2/n)
  have hD : 0≤D := by dsimp [D]; positivity
  unfold largeDenominatorSum
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _q ∈ Ioc B Q, D := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hbq,hqQ⟩ := mem_Ioc.mp hq
      have hqp : P<q := lt_of_le_of_lt hpB hbq
      have hqr : 0<(q:ℝ) := by exact_mod_cast (lt_trans hp hqp)
      have hnr : 0<(n:ℝ) := by exact_mod_cast hn
      have hnot : ¬ q ∣ P := fun hd => (not_le_of_gt hqp) (Nat.le_of_dvd hp hd)
      have hh := periodic_window_bound b q P K H C hp (lt_trans hp hqp) hnot hC hb
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*(Q:ℝ)/((q:ℝ)*n))]
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
        _ = (2*C*P*Q/n)*(q:ℝ) := by field_simp
        _ ≤ (2*C*P*Q/n)*(Q:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hqQ) (by positivity)
        _ = D := by dsimp [D]; ring
    _ = ((Q-B:ℕ):ℝ)*D := by simp
    _ ≤ (Q:ℝ)*D := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le Q B) hD
    _ = _ := by dsimp [D]; ring

/-- Use the observed mean on each residue class of the actual first frequency window. -/
def residueWindow (K H P r : ℕ) := (Ioc K H).filter (fun k => k%P=r)

noncomputable def residueMean (n P r : ℕ) : ℝ :=
  let T := residueWindow (primeBandWidth n) (firstBandEnd n) P r
  (∑ k ∈ T, pairMass n k (high n)) / T.card

/-- Above the cube threshold the even target has no mass at odd absolute offsets. -/
theorem odd_offset_mass_zero (n k : ℕ) (hn : 8≤n) (he : Even n) (hk : Odd k) :
    pairMass n k (high n) = 0 := by
  have odd_factor (p : ℕ) (h : high n p ≠ 0) : Odd p := by
    unfold high at h
    split_ifs at h with hlo hprime
    · contradiction
    · rcases hprime.eq_two_or_odd with rfl | odd
      · norm_num at hlo; omega
      · exact Nat.odd_iff.mpr odd
    · contradiction
  unfold pairMass
  apply sum_eq_zero
  intro p _
  apply sum_eq_zero
  intro r _
  by_cases hp : high n p = 0
  · simp [hp]
  by_cases hr : high n r = 0
  · simp [hr]
  have hpr := odd_factor p hp
  have hrr := odd_factor r hr
  have hne : (offset n p r).natAbs ≠ k := by
    intro h
    have hs := Int.natAbs_eq_natAbs_iff.mp (show (offset n p r).natAbs = (k:ℤ).natAbs by simpa using h)
    obtain ⟨a,ha⟩ := hpr
    obtain ⟨b,hb⟩ := hrr
    obtain ⟨c,hc⟩ := he
    obtain ⟨d,hd⟩ := hk
    unfold offset at hs
    omega
  simp [hne]

theorem centered_class_sum (n P r : ℕ) :
    ∑ k ∈ residueWindow (primeBandWidth n) (firstBandEnd n) P r,
      (pairMass n k (high n) - residueMean n P r) = 0 := by
  unfold residueMean
  set T := residueWindow (primeBandWidth n) (firstBandEnd n) P r
  by_cases he : T = ∅
  · simp [he]
  · have hc : (T.card:ℝ) ≠ 0 := by exact_mod_cast (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr he))
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
    field_simp
    ring

noncomputable def classDeviation (n P k : ℕ) :=
  pairMass n k (high n) - residueMean n P (k%P)

/-- A divisor of the period tests a union of whole residue classes, so its deviation is exactly zero. -/
theorem divisor_of_period_zero (n P d : ℕ) (hp : 0<P) (hd : d ∣ P) :
    ∑ k ∈ (Ioc (primeBandWidth n) (firstBandEnd n)).filter (d ∣ ·), classDeviation n P k = 0 := by
  let T := Ioc (primeBandWidth n) (firstBandEnd n)
  have maps : ∀ k ∈ T.filter (d ∣ ·), k%P ∈ range P :=
    fun k _ => mem_range.mpr (Nat.mod_lt k hp)
  rw [← sum_fiberwise_of_maps_to maps]
  apply sum_eq_zero
  intro r _
  by_cases hr : d ∣ r
  · have keep : ((T.filter (d ∣ ·)).filter (fun k => k%P=r)) =
        residueWindow (primeBandWidth n) (firstBandEnd n) P r := by
      ext k
      simp only [mem_filter,residueWindow,T]
      constructor
      · rintro ⟨⟨ht,_⟩,hk⟩; exact ⟨ht,hk⟩
      · rintro ⟨ht,hk⟩
        exact ⟨⟨ht,(Nat.dvd_mod_iff hd).mp (hk ▸ hr)⟩,hk⟩
    rw [keep, ← centered_class_sum n P r]
    apply sum_congr rfl
    intro k hk
    rw [classDeviation,(mem_filter.mp hk).2]
  · apply sum_eq_zero
    intro k hk
    have hf := mem_filter.mp hk
    exact False.elim (hr (hf.2 ▸ (Nat.dvd_mod_iff hd).mpr (mem_filter.mp hf.1).2))

/-- Only divisors of q that fail to divide P survive in the large-denominator arithmetic sum. -/
theorem centered_divisor_formula (n P q : ℕ) (hp : 0<P) :
    (∑ k ∈ Ioc (primeBandWidth n) (firstBandEnd n), classDeviation n P k * ram q k) =
    ∑ d ∈ q.divisors.filter (fun d => ¬d ∣ P), ((d:ℝ)*(ArithmeticFunction.moebius (q/d):ℝ)) *
      ∑ k ∈ (Ioc (primeBandWidth n) (firstBandEnd n)).filter (d ∣ ·), classDeviation n P k := by
  rw [ram_weighted_divisors,sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : d ∣ P
  · simp [hd,divisor_of_period_zero n P d hp hd]
  · simp [hd]

private theorem mean_bound (n P r : ℕ) (hn : 0<n) :
    |residueMean n P r| ≤ (Real.log 4*n)*(2*Real.log n) := by
  unfold residueMean
  set T := residueWindow (primeBandWidth n) (firstBandEnd n) P r
  let C := (Real.log 4*n)*(2*Real.log n)
  have hC : 0≤C := by dsimp [C]; have := Real.log_nonneg (by exact_mod_cast hn : (1:ℝ)≤n); positivity
  by_cases he : T=∅
  · simpa [he] using hC
  · have hc : 0<(T.card:ℝ) := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr he)
    rw [abs_div,abs_of_pos hc,div_le_iff₀ hc]
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _k ∈ T, C := sum_le_sum (fun k _ => pair_mass_bound n k hn)
      _ = _ := by simp [C,mul_comm]

private noncomputable def smallDenCo (n k : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 (logWidth n), ram q k *
    (Real.sin (2*Real.pi*(k:ℝ)*((catalogueCutoff n:ℝ)/(q*n))) / (Real.pi*k))

/-- Higher offsets and the small-denominator sine terms retain their full signed weights. -/
noncomputable def outerAndSmall (n : ℕ) : ℝ :=
  firstBandSum n (firstBandEnd n) n (majorCoefficient (catalogueCutoff n) n) +
    firstBandSum n (primeBandWidth n) (firstBandEnd n) (smallDenCo n)

private theorem model_decomposition (n : ℕ) (hn : 2≤n) :
    modelLoss n = outerAndSmall n + largeDenominatorSum (catalogueCutoff n) n
      (logWidth n) (primeBandWidth n) (firstBandEnd n) (fun k => pairMass n k (high n)) := by
  let Q := catalogueCutoff n
  let B := logWidth n
  let K := primeBandWidth n
  let H := firstBandEnd n
  have hlog := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^2≤n+2 by omega)
  have hBQ : B≤Q := by dsimp [B,Q,logWidth,catalogueCutoff]; nlinarith
  have hQ : 0<Q := by dsimp [Q,catalogueCutoff]; positivity
  have hKH : K≤H := by
    apply Nat.div_le_div_left _ hQ
    dsimp [Q,logWidth,catalogueCutoff]
    exact (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide : 2≤4))
  have hH : H≤n := Nat.div_le_self ..
  unfold modelLoss firstBandSum
  rw [← sum_Ioc_consecutive _ hKH hH]
  have lower : ∀ k ∈ Ioc K H, k ≤ firstBandEnd n := fun k hk => (mem_Ioc.mp hk).2
  have upper : ∀ k ∈ Ioc H n, ¬ k ≤ firstBandEnd n := fun k hk => not_le.mpr (mem_Ioc.mp hk).1
  simp only [sum_congr rfl (fun k hk => congrArg _ (ite_eq_left (lower k hk))),
    sum_congr rfl (fun k hk => congrArg _ (ite_eq_right (upper k hk)))]
  change firstBandSum n K H (firstBandCoefficient Q n B) +
      firstBandSum n H n (majorCoefficient Q n) = _
  rw [first_band_residue_formula Q n B K H (by exact Nat.succ_pos _) hBQ]
  unfold outerAndSmall largeDenominatorSum smallDenCo
  simp_rw [← ram_against_mass]
  ring

/-- The large denominators act only on deviations from the mean of each residue class. -/
noncomputable def centeredLoss (n P : ℕ) : ℝ :=
  outerAndSmall n + largeDenominatorSum (catalogueCutoff n) n (logWidth n)
    (primeBandWidth n) (firstBandEnd n) (classDeviation n P)

theorem catalogue_center_error (n P : ℕ) (hn : 2≤n) (hp : 0<P) (hPL : P≤logWidth n) :
    |modelLoss n - centeredLoss n P| ≤ 4*Real.log 4*(logWidth n:ℝ)^8 := by
  have hn' : 0<n := by omega
  have hnr : (0:ℝ)<n := by exact_mod_cast hn'
  let L := (logWidth n:ℝ)
  have hQ : (catalogueCutoff n:ℝ) ≤ L^2 := by
    dsimp [L,catalogueCutoff,logWidth]
    push_cast
    nlinarith [show 0 ≤ (Nat.log 2 (n+2):ℝ) by positivity]
  have hC : 0≤(Real.log 4*n)*(2*Real.log n) := by
    have := Real.log_nonneg (by exact_mod_cast hn' : (1:ℝ)≤n); positivity
  rw [model_decomposition n hn]
  unfold centeredLoss classDeviation
  rw [add_sub_add_left_eq_sub]
  refine (large_denominator_center _ _ _ _ _ _ _ _ _ hn' hp hPL hC
    (fun r _ => mean_bound n P r hn')).trans ?_
  calc
    _ = 4*Real.log 4*Real.log n*(P:ℝ)*(catalogueCutoff n:ℝ)^3 := by field_simp; ring
    _ ≤ 4*Real.log 4*L*L*(L^2)^3 := by
      gcongr
      · exact log_n_le_width n hn'
      · dsimp only [L]; exact_mod_cast hPL
    _ = _ := by change _ = 4*Real.log 4*L^8; ring

private theorem log_budget (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, ∀ n≥N,
    4*Real.log 4*(logWidth n:ℝ)^8 ≤ ε*n := by
  have hpos : 0 < ε/(16*Real.log 4) := by positivity
  have lim := tendsto_pow_const_div_const_pow_of_one_lt 8 (by norm_num : (1:ℝ)<2)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (logWidth_tends.eventually (lim.eventually_lt_const hpos))
  refine ⟨max 2 N,fun n hn => ?_⟩
  have hsmall := hN n (by omega)
  have hp := Nat.pow_log_le_self 2 (show n+2≠0 by omega)
  have he : 2^(logWidth n) ≤ 4*n := by unfold logWidth; rw [pow_succ]; omega
  have hexp : (2:ℝ)^(logWidth n) ≤ 4*n := by exact_mod_cast he
  have hden : 0 < 16*Real.log 4 := by positivity
  have lhs := (div_lt_div_iff₀ (by positivity : 0<(2:ℝ)^(logWidth n)) hden).mp hsmall
  nlinarith only [lhs,mul_le_mul_of_nonneg_left hexp hε.le]

/-- The modulus can change with the target, up to the retained denominator cutoff. -/
theorem catalogue_centered_iff (period : ℕ→ℕ)
    (hp : ∀ n≥2, 0<period n ∧ period n≤logWidth n) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      centeredLoss n (period n) ≤ pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  rw [catalogue_first_band_iff]
  constructor <;> intro h ε he <;>
    obtain ⟨N,hN⟩ := h (ε/2) (half_pos he) <;>
    obtain ⟨M,hM⟩ := log_budget (ε/2) (half_pos he) <;>
    refine ⟨max 2 (max M N),fun n hn hev => ?_⟩ <;>
    have hn' : 2≤n := by omega
  all_goals
    have herr := (catalogue_center_error n (period n) hn' (hp n hn').1 (hp n hn').2).trans (hM n (by omega))
    obtain ⟨hl,hu⟩ := abs_le.mp herr
    linarith only [hl,hu,hN n (by omega) hev]

/-- Use the largest factorial that fits the denominator cutoff as a single growing period. -/
def factorialIndex (n : ℕ) := Nat.findGreatest (fun j => j.factorial ≤ logWidth n) (logWidth n)

def factorialPeriod (n : ℕ) := (factorialIndex n).factorial

theorem factorialPeriod_fits (n : ℕ) : 0<factorialPeriod n ∧ factorialPeriod n≤logWidth n := by
  refine ⟨Nat.factorial_pos _, ?_⟩
  exact Nat.findGreatest_spec (P := fun j => j.factorial ≤ logWidth n) (Nat.zero_le _)
    (show Nat.factorial 0 ≤ logWidth n by exact Nat.succ_pos _)

theorem factorialIndex_tends : Tendsto factorialIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro j
  filter_upwards [logWidth_tends.eventually (eventually_ge_atTop j.factorial)] with n hn
  exact Nat.le_findGreatest ((Nat.self_le_factorial j).trans hn) hn

/-- With this one choice, the offset sum on multiples of every bounded positive divisor
is eventually identically zero, uniformly over the entire finite set of divisors. -/
theorem eventually_small_divisors_zero (D : ℕ) : ∀ᶠ n in atTop, ∀ d, 0<d → d≤D →
    ∑ k ∈ (Ioc (primeBandWidth n) (firstBandEnd n)).filter (d ∣ ·),
      classDeviation n (factorialPeriod n) k = 0 := by
  filter_upwards [factorialIndex_tends.eventually (eventually_ge_atTop D)] with n hn
  intro d hd hD
  exact divisor_of_period_zero n _ d (factorialPeriod_fits n).1 (Nat.dvd_factorial hd (hD.trans hn))

theorem catalogue_factorial_centered_iff : FrozenBulk.BulkFloor ↔
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      centeredLoss n (factorialPeriod n) ≤
        pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n :=
  catalogue_centered_iff factorialPeriod (fun n _ => factorialPeriod_fits n)

#print axioms catalogue_centered_iff
#print axioms centered_divisor_formula
#print axioms eventually_small_divisors_zero

end GoldbachMinor
