import ExactFirstBand

namespace GoldbachMinor
open Finset Filter GoldbachWeight

private noncomputable def wave (a : ℝ) (k : ℕ) := Real.sin (a*k)/k

private theorem abs_wave (a : ℝ) (k : ℕ) (ha : 0≤a) : |wave a k| ≤ a := by
  by_cases hk : k=0
  · simpa [hk,wave] using ha
  have hr : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [wave,abs_div,abs_of_pos hr,div_le_iff₀ hr]
  exact Real.abs_sin_le_abs.trans (abs_of_nonneg (mul_nonneg ha hr.le)).le

/-- A discrete variation estimate that retains the small angular scale. -/
private theorem wave_step (a : ℝ) (k : ℕ) (ha : 0≤a) (hk : 0<k) :
    |wave a k-wave a (k+1)| ≤ 2*a/(k:ℝ) := by
  have hr : (0:ℝ)<k := by exact_mod_cast hk
  have hs : |Real.sin (a*k)-Real.sin (a*((k:ℝ)+1))| ≤ a := by
    apply (Real.abs_sin_sub_sin_le ..).trans_eq
    rw [show a*k-a*((k:ℝ)+1) = -a by ring,abs_neg,abs_of_nonneg ha]
  have id : wave a k-wave a (k+1) =
      (Real.sin (a*k)-Real.sin (a*((k:ℝ)+1)) + wave a k)/((k:ℝ)+1) := by
    simp only [wave,Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  rw [id,abs_div,abs_of_pos (show 0<(k:ℝ)+1 by positivity)]
  calc
    _ ≤ (a+a)/((k:ℝ)+1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (abs_add_le ..).trans (add_le_add hs (abs_wave a k ha))
    _ ≤ (a+a)/(k:ℝ) := by gcongr; linarith
    _ = _ := by ring

/-- A periodic mass times a nonresonant Ramanujan sum has bounded prefixes.
Summation by parts transfers that bound to the exact sine weight. -/
theorem periodic_wave_bound (b : ℕ→ℝ) (q P K H : ℕ) (C a : ℝ)
    (hp : 0<P) (hq : 0<q) (h : ¬q ∣ P) (hC : 0≤C) (ha : 0≤a) (hb : ∀ r<P, |b r|≤C) :
    |∑ k ∈ Ioc K H, wave a k*(b (k%P)*ram q k)| ≤ C*P*q^2*a*(1+2*harmonicCutoff H) := by
  let f (k : ℕ) := b (k%P)*ram q k
  let S (t : ℕ) := ∑ k ∈ Ioc K t, f k
  let D := C*P*q^2
  have hD : 0≤D := by dsimp [D]; positivity
  have bound (t : ℕ) : |S t|≤D := periodic_window_bound b q P K t C hp hq h hC hb
  have tail : (∑ k ∈ Ioo K H, |(wave a k-wave a (k+1))*S k|) ≤ (2*a*D)*harmonicCutoff H := by
    calc
      _ ≤ ∑ k ∈ Ioo K H, (2*a*D)*(1/(k:ℝ)) := by
        refine sum_le_sum fun k hk => ?_
        have hk' : 0<k := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioo.mp hk).1
        rw [abs_mul]
        exact (mul_le_mul (wave_step a k ha hk') (bound k) (abs_nonneg _) (by positivity)).trans_eq (by ring)
      _ = (2*a*D)*(∑ k ∈ Ioo K H, 1/(k:ℝ)) := (mul_sum ..).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
        intro k hk
        have := mem_Ioo.mp hk
        exact mem_Icc.mpr ⟨by omega,by omega⟩
  rw [weighted_prefix_identity]
  change |wave a H*S H + ∑ k ∈ Ioo K H, (wave a k-wave a (k+1))*S k| ≤ _
  have endpoint : |wave a H*S H|≤a*D := by
    rw [abs_mul]; exact mul_le_mul (abs_wave a H ha) (bound H) (abs_nonneg _) ha
  exact (abs_add_le ..).trans ((add_le_add endpoint ((abs_sum_le_sum_abs ..).trans tail)).trans_eq
    (by dsimp [D]; ring))

/-- Exact contribution of one denominator to an offset window with periodic mass. -/
noncomputable def denominatorWave (b : ℕ→ℝ) (Q n P K H q : ℕ) : ℝ :=
  ∑ k ∈ Ioc K H, b (k%P)*ram q k*
    (Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n)))/(Real.pi*k))

theorem nonresonant_denominator (b : ℕ→ℝ) (Q n P K H q : ℕ) (C : ℝ)
    (hn : 0<n) (hp : 0<P) (hq : 0<q) (h : ¬q ∣ P) (hC : 0≤C) (hb : ∀ r<P, |b r|≤C) :
    |denominatorWave b Q n P K H q| ≤ (2*C*P*Q*q/n)*(1+2*harmonicCutoff H) := by
  let a := 2*Real.pi*Q/((q:ℝ)*n)
  have ha : 0≤a := by dsimp [a]; positivity
  have id : denominatorWave b Q n P K H q =
      (∑ k ∈ Ioc K H, wave a k*(b (k%P)*ram q k))/Real.pi := by
    rw [denominatorWave,sum_div]
    apply sum_congr rfl
    intro k _
    simp only [wave,a,show 2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))=2*Real.pi*Q/((q:ℝ)*n)*k by ring]
    ring
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  rw [id,abs_div,abs_of_pos Real.pi_pos,div_le_iff₀ Real.pi_pos]
  exact (periodic_wave_bound b q P K H C a hp hq h hC ha hb).trans_eq (by dsimp [a]; field_simp)

/-- Only denominators dividing the period are retained in the first-band model. -/
noncomputable def resonantBandLoss (c : ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 (catalogueCutoff n)).filter (· ∣ factorialPeriod n),
    denominatorWave (pairedProfile c n) (catalogueCutoff n) n (factorialPeriod n)
      (primeBandWidth n) (firstBandEnd n) q

private theorem periodic_by_denominator (c : ℝ) (n : ℕ) :
    periodicBandLoss c n = ∑ q ∈ Icc 1 (catalogueCutoff n),
      denominatorWave (pairedProfile c n) (catalogueCutoff n) n (factorialPeriod n)
        (primeBandWidth n) (firstBandEnd n) q := by
  unfold periodicBandLoss denominatorWave majorCoefficient
  simp_rw [mul_sum,← mul_assoc]
  rw [sum_comm]

theorem periodic_resonance_bound (c : ℝ) (n : ℕ) (hn : 0<n) :
    |periodicBandLoss c n-resonantBandLoss c n| ≤ 20*|c| *(logWidth n:ℝ)^9 := by
  let P := factorialPeriod n
  let Q := catalogueCutoff n
  let H := firstBandEnd n
  let L : ℝ := logWidth n
  let C := 2*|c| *n*L
  let f := denominatorWave (pairedProfile c n) Q n P (primeBandWidth n) H
  let S := (Icc 1 Q).filter (fun q => ¬q ∣ P)
  have hL : 1≤L := by dsimp [L]; exact_mod_cast (Nat.succ_pos (Nat.log 2 (n+2)))
  have hP : (P:ℝ)≤L := by dsimp only [P,L]; exact_mod_cast (factorialPeriod_fits n).2
  have hl : 0≤L := zero_le_one.trans hL
  have hC : 0≤C := by dsimp [C]; positivity
  have hQ : (Q:ℝ)≤L^2 := by
    dsimp [Q,L,catalogueCutoff,logWidth]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2))]
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have hb (r : ℕ) (_ : r<P) : |pairedProfile c n r| ≤ C := by
    simp only [pairedProfile,abs_mul, Nat.abs_cast]
    have shape (m : ℕ) : |binaryShape (factorialIndex n) m|≤L := (abs_binaryShape_le_factorial _ _).trans hP
    have h := (abs_add_le ..).trans (add_le_add (shape (n-r)) (shape (n+r)))
    exact (mul_le_mul_of_nonneg_left h (by positivity : 0≤|c| *n)).trans_eq (by dsimp [C]; ring)
  have hh : harmonicCutoff H ≤ 1+L := by
    have hh' : harmonicCutoff H ≤ harmonicCutoff n := by
      apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
      exact Icc_subset_Icc (le_refl _) (Nat.div_le_self ..)
    have hharm : harmonicCutoff n ≤ 1+Real.log n := by
      simpa only [harmonicCutoff,one_div,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
        using harmonic_le_one_add_log n
    exact hh'.trans (hharm.trans (add_le_add_right (log_n_le_width n hn) _))
  have hW : 1+2*harmonicCutoff H≤5*L := by linarith
  have split : periodicBandLoss c n-resonantBandLoss c n = ∑ q ∈ S, f q := by
    rw [periodic_by_denominator]
    exact sub_eq_iff_eq_add.mpr (by
      change ∑ q ∈ Icc 1 Q, f q = _+_
      rw [add_comm]
      exact (sum_filter_add_sum_filter_not _ _ f).symm)
  have each (q : ℕ) (hq : q∈S) : |f q| ≤ 20*|c| *L^7 := by
    obtain ⟨hm,hnd⟩ := mem_filter.mp hq
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hm
    have hqL : (q:ℝ)≤L^2 := (show (q:ℝ)≤Q by exact_mod_cast hqQ).trans hQ
    have h := nonresonant_denominator (pairedProfile c n) Q n P (primeBandWidth n) H q C
      hn (factorialPeriod_fits n).1 hq0 hnd hC hb
    apply h.trans
    have coef : 2*C*P*Q*q/n ≤ 4*|c| *L*L*(L^2)*(L^2) := by
      rw [show 2*C*P*Q*q/n = 4*|c| *L*P*Q*q by dsimp [C]; field_simp; ring]
      gcongr
    exact (mul_le_mul coef hW (by unfold harmonicCutoff; positivity) (by positivity)).trans_eq (by ring)
  have card : (S.card:ℝ)≤L^2 := by
    have h := card_le_card (filter_subset (fun q => ¬q∣P) (Icc 1 Q))
    have h' : S.card≤Q := by simpa [S] using h
    exact (show (S.card:ℝ)≤Q by exact_mod_cast h').trans hQ
  rw [split]
  calc
    _ ≤ ∑ q ∈ S, |f q| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _q ∈ S, 20*|c| *L^7 := sum_le_sum each
    _ = (S.card:ℝ)*(20*|c| *L^7) := by simp
    _ ≤ L^2*(20*|c| *L^7) := mul_le_mul_of_nonneg_right card (by positivity)
    _ = _ := by dsimp only [L]; ring

private theorem resonance_negligible (c ε : ℝ) (he : 0<ε) :
    ∃ N:ℕ, ∀ n≥N, |periodicBandLoss c n-resonantBandLoss c n| ≤ ε*n := by
  let D := 20*|c|+1
  have hD : 0<D := by dsimp [D]; positivity
  have lim := tendsto_pow_const_div_const_pow_of_one_lt 9 (by norm_num : (1:ℝ)<2)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (logWidth_tends.eventually
    (lim.eventually_lt_const (show 0<ε/(4*D) by positivity)))
  refine ⟨max 2 M,fun n hn => (periodic_resonance_bound c n (by omega)).trans ?_⟩
  have h := (div_lt_div_iff₀ (by positivity : 0<(2:ℝ)^logWidth n) (by positivity : 0<4*D)).mp (hM n (by omega))
  have hp := Nat.pow_log_le_self 2 (show n+2≠0 by omega)
  have hr : (2:ℝ)^(logWidth n)≤4*n := by
    exact_mod_cast (show 2^(logWidth n)≤4*n by unfold logWidth; rw [pow_succ]; omega)
  dsimp only [D] at h
  nlinarith only [h,mul_le_mul_of_nonneg_left hr he.le,show 0≤(logWidth n:ℝ)^9 by positivity]

/-- Every prime-pair mass remaining on the left is at an offset above the first band.
The explicit first-band term retains precisely the denominators dividing the period. -/
theorem outer_resonant_iff (c : ℝ) (hc : ClassicalMeanSquare c) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      firstBandSum n (firstBandEnd n) n (majorCoefficient (catalogueCutoff n) n) +
        resonantBandLoss c n ≤ pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  rw [outer_periodic_iff c hc]
  constructor <;> intro h ε he <;>
    obtain ⟨A,hA⟩ := h (ε/2) (half_pos he) <;>
    obtain ⟨M,hM⟩ := resonance_negligible c (ε/2) (half_pos he) <;>
    refine ⟨max A M,fun n hn hev => ?_⟩ <;>
    obtain ⟨hl,hu⟩ := abs_le.mp (hM n (by omega)) <;>
    linarith only [hl,hu,hA n (by omega) hev]

#print axioms periodic_resonance_bound
#print axioms outer_resonant_iff
end GoldbachMinor
