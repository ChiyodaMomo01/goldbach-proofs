import PeriodicMass

namespace GoldbachMinor

open Finset Filter GoldbachWeight
open scoped Topology

private theorem move_sum_inside {ι α β R : Type*} [AddCommMonoid R]
    (I : Finset ι) (A : Finset α) (B : Finset β) (f : ι → α → β → R) :
    (∑ i ∈ I, ∑ a ∈ A, ∑ b ∈ B, f i a b) = ∑ a ∈ A, ∑ b ∈ B, ∑ i ∈ I, f i a b := by
  rw [sum_comm]
  apply sum_congr rfl
  intro _ _
  rw [sum_comm]

/-- Only inverse pairs of primitive roots survive the square over a complete period. -/
theorem ram_square_block (q s : ℕ) (hq : 0<q) :
    (∑ j ∈ range q, (ram q (s+j))^2) = (q:ℝ)*q.totient := by
  classical
  let R := primitiveRoots q ℂ
  have inner (z w : ℂ) (hz : z ∈ R) (hw : w ∈ R) :
      (∑ j ∈ range q, z^(s+j)*w^(s+j)) = if z⁻¹=w then (q:ℂ) else 0 := by
    have prim := (mem_primitiveRoots hq).mp hz
    have pw := (mem_primitiveRoots hq).mp hw
    have hn : z≠0 := by
      intro h
      have hnorm := prim.norm'_eq_one hq.ne'
      simp [h] at hnorm
    simp_rw [← mul_pow,pow_add,← mul_sum]
    by_cases heq : z⁻¹=w
    · simp [(mul_eq_one_iff_inv_eq₀ hn).mpr heq,heq]
    · have hne := (mul_eq_one_iff_inv_eq₀ hn).not.mpr heq
      have cyc : (z*w)^q = 1 := by rw [mul_pow,prim.pow_eq_one,pw.pow_eq_one,one_mul]
      rw [geom_sum_eq hne,cyc]
      simp [heq]
  apply Complex.ofReal_injective
  push_cast
  calc
    _ = ∑ j ∈ range q, ∑ z ∈ R, ∑ w ∈ R, z^(s+j)*w^(s+j) := by
      simp only [ram_trace,pow_two,sum_mul,mul_sum,R]
      simp_rw [mul_comm]
    _ = ∑ z ∈ R, ∑ w ∈ R, ∑ j ∈ range q, z^(s+j)*w^(s+j) := move_sum_inside ..
    _ = ∑ _z ∈ R, (q:ℂ) := by
      apply sum_congr rfl
      intro z hz
      have hin : z⁻¹ ∈ R := (mem_primitiveRoots hq).mpr ((mem_primitiveRoots hq).mp hz).inv
      calc
        _ = ∑ w ∈ R, if z⁻¹=w then (q:ℂ) else 0 := sum_congr rfl (fun w hw => inner z w hz hw)
        _ = _ := by simp [hin]
    _ = _ := by simp [R,Complex.card_primitiveRoots,mul_comm]

private theorem ram_mod (q k : ℕ) : ram q (k%q) = ram q k := by
  unfold ram
  apply sum_congr rfl
  intro d hd
  simp only [Nat.dvd_mod_iff (Nat.dvd_of_mem_divisors hd)]

private theorem distinct_orders (q s K H : ℕ) (hs : 0<s) (hsq : s<q) :
    |∑ k ∈ Ioc K H, ram s k*ram q k| ≤ ((s:ℝ)*q)^2 := by
  have hz := periodic_window_bound (ram s) q s K H s hs (hs.trans hsq)
    (fun h => (not_le_of_gt hsq) (Nat.le_of_dvd hs h)) (by positivity) (fun r _ => abs_ram_le s r hs)
  simp_rw [ram_mod] at hz
  convert hz using 1
  ring

private theorem square_window (q K H : ℕ) (hq : 0<q) :
    |(∑ k ∈ Ioc K H, (ram q k)^2) - ((H-K:ℕ):ℝ)*q.totient| ≤ (q:ℝ)^3 := by
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hphi : (q.totient:ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have bound (k : ℕ) : |(ram q k)^2 - q.totient| ≤ (q:ℝ)^2 := by
    have hram := abs_ram_le q k hq
    have hsq : (ram q k)^2 ≤ (q:ℝ)^2 := by
      rw [← sq_abs (ram q k)]
      gcongr
    rw [abs_le]
    constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) q.totient, sq_nonneg (ram q k),
      mul_nonneg (sub_nonneg.mpr hqr) (show (0:ℝ)≤q by positivity)]
  have block (t : ℕ) : (∑ k ∈ range q, ((ram q (t+k))^2 - q.totient))=0 := by
    rw [sum_sub_distrib,ram_square_block q t hq]
    simp
  have h := zero_block_window _ q K H ((q:ℝ)^2) hq (by positivity) bound block
  simpa [sum_sub_distrib,pow_succ,mul_assoc] using h

/-- Mean square on an arbitrary integer window. The error includes both incomplete diagonal
periods and mixed products of distinct Ramanujan sums. -/
noncomputable def denominatorKernel (Q B k : ℕ) : ℝ :=
  ∑ q ∈ Ioc B Q, ram q k / q

noncomputable def diagonalEnergy (Q B : ℕ) : ℝ :=
  ∑ q ∈ Ioc B Q, (q.totient:ℝ) / (q:ℝ)^2

theorem kernel_energy (Q B K H : ℕ) :
    |(∑ k ∈ Ioc K H, (denominatorKernel Q B k)^2) -
      ((H-K:ℕ):ℝ)*diagonalEnergy Q B| ≤ (Q:ℝ)^4 := by
  classical
  let S := Ioc B Q
  let T := Ioc K H
  let G (q s : ℕ) := (∑ k ∈ T, ram q k*ram s k)/((q:ℝ)*s)
  let D (q s : ℕ) := if q=s then ((H-K:ℕ):ℝ)*q.totient/(q:ℝ)^2 else 0
  have expand : (∑ k ∈ T, (denominatorKernel Q B k)^2) = ∑ q ∈ S, ∑ s ∈ S, G q s := by
    unfold denominatorKernel
    simp_rw [pow_two,sum_mul,mul_sum,div_mul_div_comm]
    rw [move_sum_inside]
    simp only [G,T,S,sum_div]
  have diag : ((H-K:ℕ):ℝ)*diagonalEnergy Q B = ∑ q ∈ S, ∑ s ∈ S, D q s := by
    unfold diagonalEnergy
    rw [mul_sum]
    apply sum_congr rfl
    intro q hq
    simp [D,S,hq,mul_div_assoc]
  have cell (q s : ℕ) (hq : q∈S) (hs : s∈S) : |G q s - D q s| ≤ (Q:ℝ)^2 := by
    have hq' : 0<q := Nat.zero_lt_of_lt (mem_Ioc.mp hq).1
    have hs' : 0<s := Nat.zero_lt_of_lt (mem_Ioc.mp hs).1
    have hqQ : (q:ℝ)≤Q := by exact_mod_cast (mem_Ioc.mp hq).2
    have hsQ : (s:ℝ)≤Q := by exact_mod_cast (mem_Ioc.mp hs).2
    by_cases he : q=s
    · subst s
      have hqr : (0:ℝ)<q := by exact_mod_cast hq'
      dsimp [G,D,T]
      simp only [ite_true, ← sq, ← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hqr)]
      calc
        _ ≤ (q:ℝ)^3/q^2 := div_le_div_of_nonneg_right (square_window q K H hq') (by positivity)
        _ = q := by field_simp
        _ ≤ (Q:ℝ)^2 := by
          have hone : (1:ℝ)≤Q := by exact_mod_cast (hq'.trans_le (mem_Ioc.mp hq).2)
          nlinarith [mul_nonneg (sub_nonneg.mpr hone) (show (0:ℝ)≤Q by positivity)]
    · have hqr : 0<(q:ℝ)*(s:ℝ) := by positivity
      have hcross : |∑ k ∈ T, ram q k*ram s k| ≤ ((q:ℝ)*s)^2 := by
        rcases lt_or_gt_of_ne he with hlt|hgt
        · exact distinct_orders s q K H hq' hlt
        · simpa only [mul_comm] using distinct_orders q s K H hs' hgt
      simp only [G,D,he,ite_false,sub_zero,abs_div,abs_of_pos hqr]
      calc
        _ ≤ ((q:ℝ)*s)^2 / (q*s) := div_le_div_of_nonneg_right hcross hqr.le
        _ = (q:ℝ)*s := by field_simp
        _ ≤ (Q:ℝ)^2 := by rw [sq]; gcongr
  change |(∑ k ∈ T, _) - _| ≤ _
  rw [expand,diag,← sum_sub_distrib]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ q ∈ S, ∑ _s ∈ S, (Q:ℝ)^2 := by
      apply sum_le_sum
      intro q hq
      rw [← sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun s hs => cell q s hq hs)
    _ = ((Q-B:ℕ):ℝ)^2 * (Q:ℝ)^2 := by simp [S,sq]; ring
    _ ≤ (Q:ℝ)^4 := by
      have le : ((Q-B:ℕ):ℝ)≤Q := by exact_mod_cast Nat.sub_le Q B
      calc
        _ ≤ (Q:ℝ)^2 * Q^2 := by gcongr
        _ = _ := by ring

theorem diagonalEnergy_le_harmonic (Q B : ℕ) : diagonalEnergy Q B ≤ harmonicCutoff Q := by
  unfold diagonalEnergy harmonicCutoff
  calc
    _ ≤ ∑ q ∈ Ioc B Q, 1/(q:ℝ) := by
      apply sum_le_sum
      intro q hq
      have hp : 0<(q:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt (mem_Ioc.mp hq).1)
      have hh : (q.totient:ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
      calc
        _ ≤ (q:ℝ)/q^2 := div_le_div_of_nonneg_right hh (sq_nonneg _)
        _ = _ := by field_simp
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
      intro q hq
      obtain ⟨_,_⟩ := mem_Ioc.mp hq
      apply mem_Icc.mpr
      omega

/-- A signed denominator sum is the inner product with one real kernel on the offset window. -/
theorem large_as_kernel (Q n B K H : ℕ) (u : ℕ→ℝ) :
    largeDenominatorSum Q n B K H u = (2*(Q:ℝ)/n)*
      ∑ k ∈ Ioc K H, u k*denominatorKernel Q B k := by
  unfold largeDenominatorSum denominatorKernel
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro q _
  simp only [div_eq_mul_inv,mul_inv]
  ring

theorem denominator_window_cauchy (Q n B K H : ℕ) (u : ℕ→ℝ) :
    (largeDenominatorSum Q n B K H u)^2 ≤
    (2*(Q:ℝ)/n)^2 * (∑ k ∈ Ioc K H, (u k)^2) *
      (((H-K:ℕ):ℝ)*diagonalEnergy Q B + (Q:ℝ)^4) := by
  have he := (abs_le.mp (kernel_energy Q B K H)).2
  rw [large_as_kernel,mul_pow,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ _ := sum_mul_sq_le_sq_mul_sq (Ioc K H) u (denominatorKernel Q B)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The unnormalized sum of squared deviations of the ordered prime-pair mass. -/
noncomputable def classEnergy (n P : ℕ) : ℝ :=
  ∑ k ∈ Ioc (primeBandWidth n) (firstBandEnd n), (classDeviation n P k)^2

theorem cutoff_power_budget (ε : ℝ) (hε : 0<ε) : ∀ᶠ n in atTop,
    (catalogueCutoff n:ℝ)^5 ≤ ε*n := by
  have lim := tendsto_pow_const_div_const_pow_of_one_lt 10 (by norm_num : (1:ℝ)<2)
  filter_upwards [logWidth_tends.eventually (lim.eventually_lt_const (show 0<ε/4 by positivity)),
    eventually_ge_atTop 2] with n h hn
  have hpow := Nat.pow_log_le_self 2 (show n+2≠0 by omega)
  have h2 : 2^(logWidth n) ≤ 4*n := by unfold logWidth; rw [pow_succ]; omega
  have he : (2:ℝ)^(logWidth n) ≤ 4*(n:ℝ) := by exact_mod_cast h2
  have h1 := (div_lt_div_iff₀ (by positivity : 0<(2:ℝ)^(logWidth n)) (by norm_num : (0:ℝ)<4)).mp h
  have hl : (logWidth n:ℝ)^10 ≤ ε*n := by nlinarith only [h1,mul_le_mul_of_nonneg_left he hε.le]
  apply le_trans _ hl
  have hc : (catalogueCutoff n)^5 ≤ (logWidth n)^10 := by
    unfold catalogueCutoff logWidth
    rw [← pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_succ _) 10
  exact_mod_cast hc

private theorem window_length (n : ℕ) (hn : 0<n) (h4 : 4*catalogueCutoff n≤n) :
    n ≤ 4*((firstBandEnd n - primeBandWidth n)*catalogueCutoff n) := by
  let Q := catalogueCutoff n
  let L := logWidth n
  let H := firstBandEnd n
  let K := primeBandWidth n
  have hlog := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1 ≤ n+2 by omega)
  have hQ : 0<Q := by dsimp [Q,catalogueCutoff]; positivity
  have hnH : n=H*Q+n%Q := (Nat.div_add_mod' n Q).symm
  have hr := Nat.mod_lt n hQ
  have hk : K*L^4≤n := Nat.div_mul_le_self n _
  have hden : 2*Q≤L^4 := by
    dsimp [Q,L,catalogueCutoff,logWidth]
    nlinarith [sq_nonneg ((Nat.log 2 (n+2):ℝ))]
  have hkQ : 2*(K*Q)≤n := by
    calc
      _ = K*(2*Q) := by ring
      _ ≤ K*L^4 := Nat.mul_le_mul_left K hden
      _ ≤ n := hk
  change n ≤ 4*((H-K)*Q)
  rw [Nat.sub_mul]
  change 4*Q≤n at h4
  omega

/-- The per-offset mean square on the actual growing band equals the diagonal sum up to o(1). -/
theorem catalogue_kernel_energy_accuracy (ε : ℝ) (hε : 0<ε) : ∃ N:ℕ, ∀ n≥N,
    let Q := catalogueCutoff n
    let B := logWidth n
    let K := primeBandWidth n
    let H := firstBandEnd n
    |(∑ k ∈ Ioc K H, (denominatorKernel Q B k)^2) / ((H-K:ℕ):ℝ) - diagonalEnergy Q B| ≤ ε := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (cutoff_power_budget (min (ε/4) (1/4)) (by positivity))
  refine ⟨max 2 N,fun n hn => ?_⟩
  let Q := catalogueCutoff n
  let T := firstBandEnd n - primeBandWidth n
  have hn' : 0<n := by omega
  have hn0 : 0≤(n:ℝ) := by positivity
  have hb := hN n (by omega)
  have he : (Q:ℝ)^5 ≤ ε/4*n := hb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hq : (Q:ℝ)^5 ≤ 1/4*n := hb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hqQ : Q≤Q^5 := Nat.le_self_pow (by decide) _
  have h4 : 4*Q≤n := by
    have hs : (Q:ℝ)≤(Q:ℝ)^5 := by exact_mod_cast hqQ
    exact_mod_cast (show 4*(Q:ℝ)≤n by linarith)
  have len := window_length n hn' h4
  change n≤4*(T*Q) at len
  have htq : 0<T*Q := by
    by_contra! hzero
    omega
  have hTr : 0<(T:ℝ) := by exact_mod_cast (Nat.pos_of_mul_pos_right htq)
  have hQr : 0<(Q:ℝ) := by exact_mod_cast (Nat.pos_of_mul_pos_left htq)
  have hlen : (n:ℝ)≤4*((T:ℝ)*Q) := by exact_mod_cast len
  have scale : (Q:ℝ)^4≤ε*T := by
    apply (mul_le_mul_iff_left₀ hQr).mp
    nlinarith only [he,mul_le_mul_of_nonneg_left hlen hε.le]
  have h := (kernel_energy Q (logWidth n) (primeBandWidth n) (firstBandEnd n)).trans scale
  change |_/ (T:ℝ) - _| ≤ _
  rw [div_sub' hTr.ne',abs_div,abs_of_pos hTr,div_le_iff₀ hTr]
  exact h

/-- A variance estimate for each even target makes its large-denominator term sublinear. -/
theorem large_negligible_of_variance (period : ℕ→ℕ)
    (hv : ∀ δ:ℝ, 0<δ → ∃ N:ℕ, ∀ n≥N, Even n →
      (catalogueCutoff n:ℝ)*classEnergy n (period n)*(1+diagonalEnergy (catalogueCutoff n) (logWidth n))
        ≤ δ*(n:ℝ)^3) (ε : ℝ) (hε : 0<ε) : ∃ N:ℕ, ∀ n≥N, Even n →
    |largeDenominatorSum (catalogueCutoff n) n (logWidth n) (primeBandWidth n) (firstBandEnd n)
        (classDeviation n (period n))| ≤ ε*n := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (cutoff_power_budget 1 zero_lt_one)
  obtain ⟨A,hA⟩ := hv (ε^2/4) (by positivity)
  refine ⟨max 2 (max A M),fun n hn hev => ?_⟩
  let Q := catalogueCutoff n
  let B := logWidth n
  let K := primeBandWidth n
  let H := firstBandEnd n
  let V := classEnergy n (period n)
  let J := diagonalEnergy Q B
  have hnr : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hV : 0≤V := by dsimp [V,classEnergy]; positivity
  have hJ : 0≤J := by dsimp [J,diagonalEnergy]; positivity
  have h5 : (Q:ℝ)^5 ≤ n := by simpa only [one_mul] using hM n (by omega)
  have ht : (H-K)*Q ≤ n := (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans (Nat.div_mul_le_self n Q)
  have ht' : ((H-K:ℕ):ℝ)*Q ≤ n := by exact_mod_cast ht
  have hscale : (Q:ℝ)*(((H-K:ℕ):ℝ)*J+Q^4) ≤ n*(1+J) := by
    nlinarith only [mul_le_mul_of_nonneg_right ht' hJ,h5]
  have var : (Q:ℝ)*V*(1+J) ≤ (ε^2/4)*(n:ℝ)^3 := hA n (by omega) hev
  let S := largeDenominatorSum Q n B K H (classDeviation n (period n))
  have hsq : S^2 ≤ (ε*n)^2 := by
    calc
      S^2 ≤ _ := denominator_window_cauchy Q n B K H (classDeviation n (period n))
      _ = (4*(Q:ℝ)*V/n^2)*(Q*(((H-K:ℕ):ℝ)*J+Q^4)) := by
        change (2*(Q:ℝ)/n)^2*V*(((H-K:ℕ):ℝ)*J+Q^4) = _
        ring
      _ ≤ (4*(Q:ℝ)*V/n^2)*(n*(1+J)) := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (4/(n:ℝ))*(Q*V*(1+J)) := by field_simp
      _ ≤ (4/(n:ℝ))*((ε^2/4)*(n:ℝ)^3) := mul_le_mul_of_nonneg_left var (by positivity)
      _ = (ε*n)^2 := by field_simp
  change |S| ≤ _
  have hp : 0≤ε*(n:ℝ) := by positivity
  exact (sq_le_sq₀ (abs_nonneg S) hp).mp (by simpa only [sq_abs] using hsq)

/-- Conditional reduction. It keeps the small-denominator and higher-frequency input explicit. -/
theorem outer_iff_of_variance (period : ℕ→ℕ)
    (hp : ∀ n≥2, 0<period n ∧ period n ≤ logWidth n)
    (hv : ∀ δ:ℝ, 0<δ → ∃ N:ℕ, ∀ n≥N, Even n →
      (catalogueCutoff n:ℝ)*classEnergy n (period n)*(1+diagonalEnergy (catalogueCutoff n) (logWidth n))
        ≤ δ*(n:ℝ)^3) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      outerAndSmall n ≤ pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  rw [catalogue_centered_iff period hp]
  unfold centeredLoss
  constructor <;> intro h ε he <;>
    obtain ⟨N,hN⟩ := h (ε/2) (half_pos he) <;>
    obtain ⟨M,hM⟩ := large_negligible_of_variance period hv (ε/2) (half_pos he) <;>
    refine ⟨max M N,fun n hn hev => ?_⟩ <;>
    obtain ⟨hl,hu⟩ := abs_le.mp (hM n (by omega) hev) <;>
    linarith only [hl,hu,hN n (by omega) hev]

#print axioms kernel_energy
#print axioms catalogue_kernel_energy_accuracy
#print axioms outer_iff_of_variance

end GoldbachMinor
