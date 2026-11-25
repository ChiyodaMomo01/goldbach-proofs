import ResonantMean
import FirstBandSineIntegral

namespace GoldbachMinor
open Finset Filter GoldbachWeight

/-- Summation by parts for a periodic sequence centred at its period average.
The sine weight is regular at zero, so the variation costs at most one mesh
square per offset even when the period is incomplete at both ends. -/
theorem averaged_sinc_error (P K H : ℕ) (u : ℕ→ℝ) (D a : ℝ) (hp : 0<P) (hD : 0≤D)
    (ha : 0≤a) (period : ∀ k, u (k+P)=u k) (bound : ∀ k, |u k|≤D) :
    let m := (∑ k ∈ range P, u k)/P
    |∑ k ∈ Ioc K H, (a*Real.sinc (a*k))*(u k-m)| ≤ (2*P*D)*(a+H*a^2) := by
  let m := (∑ k ∈ range P, u k)/P
  let S (t : ℕ) := ∑ k ∈ Ioc K t, (u k-m)
  let w (k : ℕ) := a*Real.sinc (a*k)
  let C := 2*P*D
  have hC : 0≤C := by dsimp [C]; positivity
  have prefixBound (t) : |S t|≤C := period_mean_prefix P K t u D hp hD period bound
  have step (k : ℕ) : |w k-w (k+1)|≤a^2 := by
    dsimp only [w]
    rw [← mul_sub,abs_mul,abs_of_nonneg ha,pow_two]
    apply mul_le_mul_of_nonneg_left _ ha
    apply (sinc_difference ..).trans_eq
    push_cast
    rw [show a*k-a*((k:ℝ)+1) = -a by ring,abs_neg,abs_of_nonneg ha]
  have last : |w H*S H|≤a*C := by
    rw [abs_mul]
    apply mul_le_mul _ (prefixBound H) (abs_nonneg _) ha
    simpa only [w,abs_mul,abs_of_nonneg ha,mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one (a*H)) ha
  have tail : |∑ k ∈ Ioo K H, (w k-w (k+1))*S k|≤(H:ℝ)*(a^2*C) := by
    calc
      _ ≤ _ := abs_sum_le_sum_abs ..
      _ ≤ ∑ _k ∈ Ioo K H, a^2*C := sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul (step k) (prefixBound k) (abs_nonneg _) (sq_nonneg _)
      _ = ((Ioo K H).card:ℝ)*(a^2*C) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show (Ioo K H).card≤H by simp; omega)
  change |∑ k ∈ Ioc K H, w k*(u k-m)| ≤ _
  rw [weighted_prefix_identity]
  exact (abs_add_le ..).trans ((add_le_add last tail).trans_eq (by dsimp only [C]; ring))

/-- Finite first-band estimate for a single periodic arithmetic weight.
The second error is proportional to the actual mean, so it vanishes on
non-squarefree conductors of the Goldbach profile. -/
theorem mean_wave_integral_error (b : ℕ→ℝ) (Q n P K q : ℕ) (D : ℝ)
    (hn : 0<n) (hQ : 0<Q) (hp : 0<P) (hq : 0<q) (hd : q∣P) (hk : K≤n/Q)
    (hD : 0≤D) (bound : ∀ k, |b (k%P)*ram q k|≤D) :
    let H := n/Q
    let a := 2*Real.pi*Q/((q:ℝ)*n)
    let m := (∑ k ∈ range P, b (k%P)*ram q k)/P
    |denominatorWave b Q n P K H q - m*sineIntegralWeight q| ≤
      ((2*P*D)*(a+H*a^2)+|m| *(((H-K:ℕ):ℝ)*a^2+a*((K:ℝ)+1)))/Real.pi := by
  let H := n/Q
  let a := 2*Real.pi*Q/((q:ℝ)*n)
  let w (k : ℕ) := a*Real.sinc (a*k)
  let u (k : ℕ) := b (k%P)*ram q k
  let m := (∑ k ∈ range P, u k)/P
  let I := ∫ t in (0:ℝ)..(2*Real.pi/q), Real.sinc t
  have ha : 0<a := by dsimp [a]; positivity
  have period (k : ℕ) : u (k+P)=u k := by
    have eq : ram q (k+P)=ram q k := by
      unfold ram
      apply sum_congr rfl
      intro j hj
      have eq : j∣k+P ↔ j∣k := (Nat.dvd_add_iff_left ((Nat.dvd_of_mem_divisors hj).trans hd)).symm
      simp only [eq]
    simp [u,eq]
  have point (k : ℕ) (hk' : k ∈ Ioc K H) : w k=Real.sin (a*k)/k := by
    have kr : 0<(k:ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le K) (mem_Ioc.mp hk').1
    dsimp only [w]
    rw [Real.sinc_of_ne_zero (mul_pos ha kr).ne']; field_simp
  have mesh : |(∑ k ∈ Ioc K H, w k)-I| ≤ ((H-K:ℕ):ℝ)*a^2+a*((K:ℝ)+1) := by
    rw [sum_congr rfl point]
    exact first_band_denominator_integral Q n q K hn hq hQ hk
  have error := averaged_sinc_error P K H u D a hp hD ha.le period bound
  have id : denominatorWave b Q n P K H q - m*sineIntegralWeight q =
      ((∑ k ∈ Ioc K H, w k*(u k-m))+m*((∑ k ∈ Ioc K H, w k)-I))/Real.pi := by
    have wave : denominatorWave b Q n P K H q = (∑ k ∈ Ioc K H, w k*u k)/Real.pi := by
      rw [denominatorWave,sum_div]
      apply sum_congr rfl
      intro k hk'
      rw [point k hk']
      simp only [u,a,show 2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))=2*Real.pi*Q/((q:ℝ)*n)*k by ring]
      ring
    rw [wave]
    simp only [mul_sub,sum_sub_distrib,← sum_mul,sineIntegralWeight,I]
    ring
  change |denominatorWave b Q n P K H q - m*sineIntegralWeight q|≤_
  rw [id,abs_div,abs_of_pos Real.pi_pos]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  apply (abs_add_le ..).trans (add_le_add error ?_)
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left mesh (abs_nonneg _)

/-- The finite arithmetic main term uses only squarefree conductors and the
sine integral at 2π/q. Its only dependence on the target within each arithmetic
coefficient is the explicit Ramanujan sum. -/
noncomputable def arithmeticBandLoss (c : ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 (catalogueCutoff n)).filter (fun q => q∣factorialPeriod n ∧ Squarefree q),
    c*n*ram q n*conductorWeight (factorialIndex n) q*sineIntegralWeight q

noncomputable def bandErrorConstant (c : ℝ) :=
  8*|c| *(1+2*Real.pi) + 2*|c| *Real.exp 9*(1+2*Real.pi)

private theorem bandErrorConstant_nonneg (c : ℝ) : 0≤bandErrorConstant c := by
  unfold bandErrorConstant; positivity

set_option maxHeartbeats 1200000 in
private theorem catalogue_mean_error (c : ℝ) (n q : ℕ) (hn : 0<n) (hq : 0<q)
    (hd : q∣factorialPeriod n) (hy : 2≤factorialIndex n) (hPn : factorialPeriod n≤n) :
    let Q := catalogueCutoff n
    let P := factorialPeriod n
    let K := primeBandWidth n
    let H := firstBandEnd n
    let L := (logWidth n:ℝ)
    let main := if Squarefree q then c*n*ram q n*conductorWeight (factorialIndex n) q*sineIntegralWeight q else 0
    |denominatorWave (pairedProfile c n) Q n P K H q-main| ≤ bandErrorConstant c*(L^4+L^2*K) := by
  let Q := catalogueCutoff n
  let P := factorialPeriod n
  let K := primeBandWidth n
  let H := firstBandEnd n
  let L := (logWidth n:ℝ)
  let y := factorialIndex n
  let a := 2*Real.pi*Q/((q:ℝ)*n)
  let u (k : ℕ) := pairedProfile c n (k%P)*ram q k
  let D := 2*|c| *n*L*q
  let m := (∑ k ∈ range P, u k)/P
  let Z := 1+2*Real.pi
  let E := Real.exp 9
  have hpr : (0:ℝ)<P := by exact_mod_cast (factorialPeriod_fits n).1
  have hqr : (1:ℝ)≤q := by exact_mod_cast hq
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have hq0 : 0<Q := by
    unfold Q catalogueCutoff
    exact pow_pos (Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1≤n+2 by omega)) _
  have hL : 1≤L := by dsimp [L]; exact_mod_cast Nat.succ_pos (Nat.log 2 (n+2))
  have hP : (P:ℝ)≤L := by dsimp only [P,L]; exact_mod_cast (factorialPeriod_fits n).2
  have hQ : (Q:ℝ)≤L^2 := by
    dsimp [Q,L,catalogueCutoff,logWidth]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2))]
  have kh : K≤H := by
    apply Nat.div_le_div_left _ hq0
    change (Nat.log 2 (n+2))^2 ≤ (Nat.log 2 (n+2)+1)^4
    exact (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide : 2≤4))
  have sum : (∑ k ∈ range P, u k) = (c*n)*∑ k ∈ range P,
      (binaryShape y (n-k)+binaryShape y (n+k))*ram q k := by
    rw [mul_sum]
    exact sum_congr rfl fun k hk => by simp only [u,pairedProfile,Nat.mod_eq_of_lt (mem_range.mp hk),mul_assoc,y]
  have arithmetic : m = c*n*ram q n*conductorWeight y q := by
    rw [show m=(∑ k ∈ range P, u k)/P from rfl,sum,mul_div_assoc,show P=y.factorial from rfl,paired_shape_mean y q n hy hq hd hPn]
    ring
  have main : (if Squarefree q then c*n*ram q n*conductorWeight y q*sineIntegralWeight q else 0) =
      m*sineIntegralWeight q := by
    by_cases h : Squarefree q
    · simp [h,arithmetic]
    · have zero : m=0 := by
        dsimp only [m]
        rw [sum,show P=y.factorial from rfl,nonsquarefree_shape_mean_zero y q n hy hq hd hPn h,mul_zero,zero_div]
      simp [h,zero]
  have meanBound : |m| ≤ |c| *n*q*E := by
    rw [arithmetic,abs_mul,abs_mul,abs_mul,Nat.abs_cast,abs_of_nonneg (conductorWeight_bounds y q).1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (abs_ram_le q n hq) (by positivity))
      (conductorWeight_bounds y q).2 (conductorWeight_bounds y q).1 (by positivity)
  have bound (k : ℕ) : |u k|≤D := by
    simp only [u,pairedProfile,abs_mul,Nat.abs_cast]
    have shape (t : ℕ) : |binaryShape y t|≤L := (abs_binaryShape_le_factorial y t).trans hP
    have h := (abs_add_le ..).trans (add_le_add (shape (n-k%P)) (shape (n+k%P)))
    exact (mul_le_mul (mul_le_mul_of_nonneg_left h (by positivity : 0≤|c| *n))
      (abs_ram_le q k hq) (abs_nonneg _) (by positivity)).trans_eq (by dsimp only [D]; ring)
  have ha : 0≤a := by dsimp [a]; positivity
  have hZ : 1≤Z := by dsimp [Z]; linarith [Real.pi_pos]
  have hE : 0≤E := (Real.exp_pos _).le
  have mesh : H*a≤2*Real.pi := by
    have mult : (H:ℝ)*Q≤n := by exact_mod_cast Nat.div_mul_le_self n Q
    dsimp [a]
    rw [mul_div_assoc',div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left mult (by positivity : 0≤2*Real.pi),
      mul_le_mul_of_nonneg_right hqr (by positivity : 0≤2*Real.pi*n)]
  have window : ((H-K:ℕ):ℝ)≤H := by exact_mod_cast Nat.sub_le H K
  have variation : a+H*a^2≤a*Z := by dsimp [Z]; nlinarith only [mul_le_mul_of_nonneg_right mesh ha]
  have integral : ((H-K:ℕ):ℝ)*a^2+a*((K:ℝ)+1)≤a*(K+Z) := by
    dsimp [Z]; nlinarith only [mul_le_mul_of_nonneg_right mesh ha,mul_le_mul_of_nonneg_right window (sq_nonneg a)]
  have h := mean_wave_integral_error (pairedProfile c n) Q n P K q D hn hq0 (factorialPeriod_fits n).1
    hq hd kh (by dsimp [D]; positivity) bound
  change |denominatorWave _ Q n P K H q-_|≤_
  rw [main]
  apply h.trans
  change ((2*P*D)*(a+H*a^2)+|m| *(((H-K:ℕ):ℝ)*a^2+a*((K:ℝ)+1)))/Real.pi≤_
  calc
    _ ≤ ((2*P*D)*(a*Z)+(|c| *n*q*E)*(a*(K+Z)))/Real.pi := by gcongr
    _ = 8*|c| *Z*L*P*Q + 2*|c| *E*(K+Z)*Q := by dsimp only [D,a]; field_simp; ring
    _ ≤ 8*|c| *Z*L*L*L^2 + 2*|c| *E*(K+Z)*L^2 := by gcongr
    _ ≤ bandErrorConstant c*(L^4+L^2*K) := by
      change _ ≤ (8*|c| *Z+2*|c| *E*Z)*(L^4+L^2*K)
      have L2 : L^2≤L^4 := pow_le_pow_right₀ hL (by decide)
      nlinarith only [mul_le_mul_of_nonneg_left L2 (show 0≤2*|c| *E*Z by positivity),
        mul_le_mul_of_nonneg_left hZ (show 0≤2*|c| *E*L^2*K by positivity),
        show 0≤8*|c| *Z*L^2*K by positivity]

/-- Finite edge and mesh errors after summing all resonant denominators. -/
theorem arithmetic_band_bound (c : ℝ) (n : ℕ) (hn : 0<n) (hy : 2≤factorialIndex n)
    (hp : factorialPeriod n≤n) :
    let L := (logWidth n:ℝ)
    |resonantBandLoss c n-arithmeticBandLoss c n| ≤
      bandErrorConstant c*(L^5+L^3*primeBandWidth n) := by
  classical
  let P := factorialPeriod n
  let S := (Icc 1 (catalogueCutoff n)).filter (· ∣ P)
  let f (q : ℕ) := c*n*ram q n*conductorWeight (factorialIndex n) q*sineIntegralWeight q
  let d (q : ℕ) := denominatorWave (pairedProfile c n) (catalogueCutoff n) n P
    (primeBandWidth n) (firstBandEnd n) q
  let L := (logWidth n:ℝ)
  let B := bandErrorConstant c
  have hB : 0≤B := bandErrorConstant_nonneg c
  have card : (S.card:ℝ)≤L := by
    have sub : S ⊆ Icc 1 P := by
      intro q hq
      obtain ⟨hi,hd⟩ := mem_filter.mp hq
      exact mem_Icc.mpr ⟨(mem_Icc.mp hi).1,Nat.le_of_dvd (factorialPeriod_fits n).1 hd⟩
    have cnt : S.card≤P := by simpa using card_le_card sub
    dsimp only [L]; exact_mod_cast cnt.trans (factorialPeriod_fits n).2
  have groups : arithmeticBandLoss c n = ∑ q ∈ S, if Squarefree q then f q else 0 := by
    rw [← sum_filter,filter_filter]
    rfl
  rw [groups]
  change |(∑ q ∈ S, d q)-_| ≤ _
  rw [← sum_sub_distrib]
  let K := primeBandWidth n
  calc
    _ ≤ ∑ q ∈ S, |d q-(if Squarefree q then f q else 0)| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _q ∈ S, B*(L^4+L^2*K) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hi,hd⟩ := mem_filter.mp hq
      exact catalogue_mean_error c n q hn (mem_Icc.mp hi).1 hd hy hp
    _ = (S.card:ℝ)*(B*(L^4+L^2*K)) := by simp
    _ ≤ L*(B*(L^4+L^2*K)) := mul_le_mul_of_nonneg_right card (by dsimp [L]; positivity)
    _ = _ := by dsimp only [L,B,K]; ring

private theorem width_fifth_budget (ε : ℝ) (he : 0<ε) : ∀ᶠ n in atTop,
    (logWidth n:ℝ)^5 ≤ ε*n := by
  have lim := tendsto_pow_const_div_const_pow_of_one_lt 5 (by norm_num : (1:ℝ)<2)
  filter_upwards [logWidth_tends.eventually (lim.eventually_lt_const (show 0<ε/4 by positivity)),
    eventually_ge_atTop 2] with n hs hn
  have hpow := Nat.pow_log_le_self 2 (show n+2≠0 by omega)
  have grow : (2:ℝ)^(logWidth n)≤4*n := by
    exact_mod_cast (show 2^(logWidth n)≤4*n by unfold logWidth; rw [pow_succ]; omega)
  have rhs := (div_lt_iff₀ (by positivity : 0<(2:ℝ)^logWidth n)).mp hs
  nlinarith only [rhs,mul_le_mul_of_nonneg_left grow he.le]

/-- The complete squarefree arithmetic term approximates the model on the
actual catalogue windows, uniformly in the target. -/
theorem arithmetic_band_negligible (c ε : ℝ) (he : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |resonantBandLoss c n-arithmeticBandLoss c n|≤ε*n := by
  let B := bandErrorConstant c
  have hB : 0≤B := bandErrorConstant_nonneg c
  have pos : 0<2*(B+1) := by positivity
  have ht := (tendsto_natCast_atTop_atTop.comp logWidth_tends).eventually_ge_atTop (2*B/ε)
  filter_upwards [width_fifth_budget (ε/(2*(B+1))) (by positivity),ht,width_fifth_budget 1 zero_lt_one,
    factorialIndex_tends.eventually (eventually_ge_atTop 2),eventually_ge_atTop 2] with n hs hl hw hy hn
  let L := (logWidth n:ℝ)
  let K := primeBandWidth n
  have hL : 1≤L := by dsimp [L]; exact_mod_cast Nat.succ_pos (Nat.log 2 (n+2))
  have hl5 : L≤L^5 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1≤5)
  have hp : factorialPeriod n≤n := by
    have h := hl5.trans (show L^5≤n by simpa only [one_mul] using hw)
    exact (factorialPeriod_fits n).2.trans (by exact_mod_cast (show (logWidth n:ℝ)≤n from h))
  have threshold : B ≤ (ε/2)*L := by
    have h := (div_le_iff₀ he).mp hl
    change 2*B≤L*ε at h
    linarith
  have k : (K:ℝ)*L^4≤n := by dsimp [K,L,primeBandWidth]; exact_mod_cast Nat.div_mul_le_self n ((logWidth n)^4)
  have mesh : B*L^3*K≤ε/2*n := by
    have h := mul_le_mul_of_nonneg_right threshold (show 0≤L^3*K by dsimp [L]; positivity)
    nlinarith only [h,mul_le_mul_of_nonneg_left k (by positivity : 0≤ε/2)]
  have edge : B*L^5≤ε/2*n := by
    have h : L^5*(2*(B+1))≤ε*n := (le_div_iff₀ pos).mp (by
      change (logWidth n:ℝ)^5≤ε*n/(2*(B+1))
      simpa only [div_mul_eq_mul_div] using hs)
    nlinarith only [h,pow_nonneg (zero_le_one.trans hL) 5]
  exact (arithmetic_band_bound c n (by omega) hy hp).trans (by
    change B*(L^5+L^3*K)≤ε*n
    linarith only [mesh,edge])

/-- Under the single classical mean-square assumption, the entire first-band
term in the frozen floor is an explicit finite arithmetic sum of sine integrals. -/
theorem outer_arithmetic_iff (c : ℝ) (hc : ClassicalMeanSquare c) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      firstBandSum n (firstBandEnd n) n (majorCoefficient (catalogueCutoff n) n) +
        arithmeticBandLoss c n ≤ pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  rw [outer_resonant_iff c hc]
  constructor <;> intro h ε he <;>
    obtain ⟨A,hA⟩ := h (ε/2) (half_pos he) <;>
    obtain ⟨M,hM⟩ := eventually_atTop.mp (arithmetic_band_negligible c (ε/2) (half_pos he)) <;>
    refine ⟨max A M,fun n hn hev => ?_⟩ <;>
    obtain ⟨hl,hu⟩ := abs_le.mp (hM n (by omega)) <;>
    linarith only [hl,hu,hA n (by omega) hev]

#print axioms arithmetic_band_bound
#print axioms outer_arithmetic_iff
end GoldbachMinor
