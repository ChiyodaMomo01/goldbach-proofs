import SingularSeriesTransfer

namespace GoldbachMinor
open Finset

/-- The cubic sine remainder, with the q dependence retained at every denominator. -/
private theorem exact_wave_remainder (Q n k q : ℕ) (hn : 0<n) (hk : 0<k) (hq : 0<q)
    (hband : k*Q≤n) :
    |Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n)))/(Real.pi*k)-2*(Q:ℝ)/(q*n)| ≤
      (2*(Q:ℝ)/n)*((2*Real.pi)^2/6)/(q:ℝ)^3 := by
  let x := 2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hx : 0≤x := by dsimp [x]; positivity
  have hxle : x≤2*Real.pi/(q:ℝ) := by
    have hmul : (k:ℝ)*Q≤n := by exact_mod_cast hband
    unfold x
    field_simp
    exact hmul
  have he : 2*(Q:ℝ)/(q*n) = x/(Real.pi*k) := by dsimp [x]; field_simp
  change |Real.sin x/_-_| ≤ _
  rw [he,← sub_div,abs_div,abs_of_pos (mul_pos Real.pi_pos hkr), abs_sub_comm]
  have hs := Real.abs_sub_sin_le x
  rw [abs_of_nonneg hx] at hs
  calc
    _ ≤ (x^3/6)/(Real.pi*k) := div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ (x*(2*Real.pi/q)^2/6)/(Real.pi*k) := by
      rw [show x^3=x*x^2 by ring]
      gcongr
    _ = _ := by dsimp [x]; field_simp

/-- Uniform pointwise control of the exact first-band kernel around its fully linear
Ramanujan kernel. The constant includes the q=1 term. -/
theorem exact_first_band_kernel (Q n k : ℕ) (hn : 0<n) (hk : 0<k) (hb : k*Q≤n) :
    |majorCoefficient Q n k - (2*(Q:ℝ)/n)*denominatorKernel Q 0 k| ≤
      (2*(Q:ℝ)/n)*(Real.pi^4/9) := by
  let D := 2*(Q:ℝ)/n
  let C := (2*Real.pi)^2/6
  have hD : 0≤D := by dsimp [D]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have sets : Ioc 0 Q = Icc 1 Q := by ext p; simp; omega
  unfold majorCoefficient denominatorKernel
  rw [sets,mul_sum,← sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, (D*C)*(1/(q:ℝ)^2) := by
      refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun q hq => ?_)
      have hq0 : 0<q := (mem_Icc.mp hq).1
      have hrq : (0:ℝ)<q := by exact_mod_cast hq0
      rw [show 2*(Q:ℝ)/n*(ram q k/q) = ram q k*(2*(Q:ℝ)/(q*n)) by ring,← mul_sub,abs_mul]
      refine (mul_le_mul (abs_ram_le q k hq0) (exact_wave_remainder _ _ _ _ hn hk hq0 hb)
        (abs_nonneg _) hrq.le).trans_eq ?_
      dsimp [D,C]; field_simp
    _ = (D*C)*∑ q ∈ Icc 1 Q, 1/(q:ℝ)^2 := (mul_sum ..).symm
    _ ≤ (D*C)*(Real.pi^2/6) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD hC)
      rw [← hasSum_zeta_two.tsum_eq]
      exact hasSum_zeta_two.summable.sum_le_tsum _ (by intros; positivity)
    _ = _ := by dsimp [D,C]; ring

/-- The exact first-band kernel, including all small denominators, has a finite
square-sum bound with the same diagonal logarithmic scale. -/
theorem exact_first_band_energy (Q n K H : ℕ) (hn : 0<n) (hb : H*Q≤n) :
    (∑ k ∈ Ioc K H, (majorCoefficient Q n k)^2) ≤
      2*(2*(Q:ℝ)/n)^2*(((H-K:ℕ):ℝ)*(diagonalEnergy Q 0+(Real.pi^4/9)^2)+Q^4) := by
  let D := 2*(Q:ℝ)/n
  let C := Real.pi^4/9
  let W := Ioc K H
  have hD : 0≤D := by dsimp [D]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hden := (abs_le.mp (kernel_energy Q 0 K H)).2
  have point (k) (hk : k∈W) : (majorCoefficient Q n k)^2 ≤
      2*D^2*(denominatorKernel Q 0 k)^2+2*D^2*C^2 := by
    obtain ⟨hk',hkH⟩ := mem_Ioc.mp hk
    have err := exact_first_band_kernel Q n k hn (by omega) ((Nat.mul_le_mul_right Q hkH).trans hb)
    have sq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD hC)).mpr err
    change |majorCoefficient Q n k-D*denominatorKernel Q 0 k|^2 ≤ (D*C)^2 at sq
    rw [sq_abs] at sq
    nlinarith only [sq,sq_nonneg (majorCoefficient Q n k-2*D*denominatorKernel Q 0 k)]
  calc
    _ ≤ _ := sum_le_sum point
    _ ≤ _ := by
      simp only [W,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,Nat.card_Ioc]
      change _ ≤ 2*D^2*(_*(diagonalEnergy Q 0+C^2)+_)
      nlinarith only [mul_le_mul_of_nonneg_left hden (show 0≤2*D^2 by positivity)]

open Filter GoldbachWeight

/-- The first-band model uses only the fixed centre and the offset modulo the factorial period. -/
noncomputable def periodicBandLoss (c : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (primeBandWidth n) (firstBandEnd n),
    pairedProfile c n (k % factorialPeriod n)*majorCoefficient (catalogueCutoff n) n k

/-- Replacing every first-band prime-pair mass by the periodic profile costs o(n)
against the exact sine weights, including the denominator one. -/
theorem exact_band_profile_error (c : ℝ) (hc : ClassicalMeanSquare c) (ε : ℝ) (he : 0<ε) :
    ∃ N:ℕ, ∀ n≥N, Even n →
      |firstBandSum n (primeBandWidth n) (firstBandEnd n) (majorCoefficient (catalogueCutoff n) n) -
        periodicBandLoss c n| ≤ ε*n := by
  let C := (Real.pi^4/9)^2
  let F := 8*(1+C)
  have hC : 0≤C := sq_nonneg _
  have hF : 0<F := by dsimp only [F]; positivity
  obtain ⟨M,hM⟩ := eventually_atTop.mp (cutoff_power_budget 1 zero_lt_one)
  obtain ⟨A,hA⟩ := profile_variance_of_classical_mean_square c hc (fun _ => 0) (ε^2/F) (by positivity)
  refine ⟨max 2 (max M A), fun n hn hev => ?_⟩
  let Q := catalogueCutoff n
  let K := primeBandWidth n
  let H := firstBandEnd n
  let T : ℝ := ((H-K:ℕ):ℝ)
  let J := diagonalEnergy Q 0
  let u (k : ℕ) := pairMass n k (high n)-pairedProfile c n (k % factorialPeriod n)
  let V := ∑ k ∈ Ioc K H, (u k)^2
  have hn' : 0<n := by omega
  have hnr : 0<(n:ℝ) := by exact_mod_cast hn'
  have hJ : 0≤J := by dsimp [J,diagonalEnergy]; positivity
  have hV : 0≤V := by dsimp only [V]; positivity
  have h5 : (Q:ℝ)^5≤n := by simpa only [one_mul] using hM n (by omega)
  have hb : H*Q≤n := Nat.div_mul_le_self ..
  have ht : T*Q≤n := by dsimp only [T]; exact_mod_cast (Nat.mul_le_mul_right Q (Nat.sub_le H K)).trans hb
  have scale : (Q:ℝ)*(T*(J+C)+Q^4) ≤ (n:ℝ)*(1+C)*(1+J) := by
    nlinarith only [mul_le_mul_of_nonneg_right ht (add_nonneg hJ hC),h5,
      mul_nonneg (mul_nonneg hnr.le hC) hJ]
  have var : (Q:ℝ)*V*(1+J) ≤ ε^2/F*(n:ℝ)^3 := hA n (by omega) hev
  let w := majorCoefficient Q n
  let S := ∑ k ∈ Ioc K H, u k*w k
  have sq : S^2 ≤ (ε*n)^2 := by
    calc
      _ ≤ V*(∑ k ∈ Ioc K H, (w k)^2) := sum_mul_sq_le_sq_mul_sq _ u w
      _ ≤ V*(2*(2*(Q:ℝ)/n)^2*(T*(J+C)+Q^4)) :=
        mul_le_mul_of_nonneg_left (exact_first_band_energy Q n K H hn' hb) hV
      _ = (8*Q*V/(n:ℝ)^2)*(Q*(T*(J+C)+Q^4)) := by ring
      _ ≤ (8*Q*V/(n:ℝ)^2)*((n:ℝ)*(1+C)*(1+J)) :=
        mul_le_mul_of_nonneg_left scale (by positivity)
      _ = (F/n)*(Q*V*(1+J)) := by dsimp only [F]; field_simp
      _ ≤ (F/n)*(ε^2/F*(n:ℝ)^3) := mul_le_mul_of_nonneg_left var (by positivity)
      _ = _ := by field_simp
  unfold periodicBandLoss firstBandSum
  rw [← sum_sub_distrib]
  simp_rw [← sub_mul]
  exact (sq_le_sq₀ (abs_nonneg S) (by positivity : 0≤ε*(n:ℝ))).mp (by simpa only [sq_abs] using sq)

/-- The original one-sided floor now needs an upper bound only for the outer
prime-pair frequencies plus the explicit, periodic first-band model. -/
theorem outer_periodic_iff (c : ℝ) (hc : ClassicalMeanSquare c) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      firstBandSum n (firstBandEnd n) n (majorCoefficient (catalogueCutoff n) n) +
        periodicBandLoss c n ≤ pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  rw [catalogue_prime_band_iff]
  simp_rw [trimmed_as_loss]
  have split (n : ℕ) :
      firstBandSum n (primeBandWidth n) n (majorCoefficient (catalogueCutoff n) n) =
      firstBandSum n (primeBandWidth n) (firstBandEnd n) (majorCoefficient (catalogueCutoff n) n) +
      firstBandSum n (firstBandEnd n) n (majorCoefficient (catalogueCutoff n) n) := by
    have hq : 0<catalogueCutoff n := by
      unfold catalogueCutoff
      exact pow_pos (Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1≤n+2 by omega)) _
    have kh : primeBandWidth n≤firstBandEnd n := by
      apply Nat.div_le_div_left _ hq
      change (Nat.log 2 (n+2))^2 ≤ (Nat.log 2 (n+2)+1)^4
      exact (Nat.pow_le_pow_left (Nat.le_succ _) 2).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide : 2≤4))
    exact (sum_Ioc_consecutive _ kh (Nat.div_le_self n _)).symm
  simp_rw [split]
  constructor <;> intro h ε he <;>
    obtain ⟨M,hM⟩ := h (ε/2) (half_pos he) <;>
    obtain ⟨A,hA⟩ := exact_band_profile_error c hc (ε/2) (half_pos he) <;>
    refine ⟨max A M, fun n hn hev => ?_⟩ <;>
    obtain ⟨hl,hu⟩ := abs_le.mp (hA n (by omega) hev) <;>
    linarith only [hl,hu,hM n (by omega) hev]

#print axioms exact_band_profile_error
#print axioms outer_periodic_iff
end GoldbachMinor
