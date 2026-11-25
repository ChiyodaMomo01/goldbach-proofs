import CommonModelMean

namespace GoldbachMinor
open Finset Filter
open scoped Topology

/-- The ordered log-weighted count agrees with the classical singular-series
main term in weighted mean absolute error, with no mean-square assumption. -/
theorem dyadic_count_absolute_classical (d : ℕ) (hd : 0<d) :
    Tendsto (dyadicRatio d (fun n => |goldbachCount n-2*twinPrimeConstant*n*binaryShape n n|))
      atTop (𝓝 0) := by
  let X (j : ℕ) := 2*d*j
  have grow : Tendsto X atTop atTop := tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by omega : 0<2*d)) tendsto_id
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let δ := ε/4
  have dp : 0<δ := by dsimp [δ]; positivity
  filter_upwards [grow.eventually (common_count_projection δ dp),
    (dyadic_common_minor_mean d hd).eventually_lt_const dp,
    (dyadic_common_model_mean d hd).eventually_lt_const dp,
    eventually_ge_atTop 1] with j projection minor model jp
  let T := Ico j (2*j)
  let W := ∑ i ∈ T, (d:ℝ)*i
  let A (n : ℕ) := (commonArcModel (wideCutoff (X j)) (X j) n).re
  let main (n : ℕ) := 2*twinPrimeConstant*n*binaryShape n n
  have card : T.card=j := by simp [T]; omega
  have dr : 0<(d:ℝ) := by exact_mod_cast hd
  have jr : 0<(j:ℝ) := by exact_mod_cast jp
  have scale : (d:ℝ)*j*j ≤ W := by
    have h := sum_le_sum (s:=T) fun i hi =>
      mul_le_mul_of_nonneg_left (show (j:ℝ) ≤ i by exact_mod_cast (mem_Ico.mp hi).1) dr.le
    simpa [W,card,mul_comm,mul_left_comm] using h
  have wp := (mul_pos (mul_pos dr jr) jr).trans_le scale
  have row (i) (hi : i ∈ T) : |goldbachCount (d*i)-main (d*i)| ≤
      ‖commonMinor (X j) (d*i)‖ + δ*(X j) + |A (d*i)-main (d*i)| := by
    have upper : d*i ≤ X j := (Nat.mul_le_mul_left d (mem_Ico.mp hi).2.le).trans_eq (by dsimp [X]; ring)
    have h := (Complex.abs_re_le_norm _).trans (projection (d*i) upper)
    simp only [Complex.sub_re,Complex.ofReal_re] at h
    exact (abs_sub_le _ (A (d*i)) _).trans (add_le_add_left h _)
  change (∑ i ∈ T, ‖commonMinor (X j) (d*i)‖)/W < δ at minor
  change (∑ i ∈ T, |A (d*i)-main (d*i)|)/W < δ at model
  have total := sum_le_sum row
  simp only [sum_add_distrib,sum_const,card,nsmul_eq_mul] at total
  have constant : (j:ℝ)*(δ*(X j)) ≤ 2*δ*W := by
    simpa only [X,Nat.cast_mul,Nat.cast_ofNat] using
      (show (j:ℝ)*(δ*(2*d*j)) ≤ 2*δ*W by
        calc
          _ = (2*δ)*((d:ℝ)*j*j) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left scale (by positivity))
  change dist ((∑ i ∈ T, |goldbachCount (d*i)-main (d*i)|)/W) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) wp.le), div_lt_iff₀ wp]
  have m := (div_lt_iff₀ wp).mp minor
  have a := (div_lt_iff₀ wp).mp model
  dsimp only [δ] at total constant m a
  linarith only [total,constant,m,a]

/-- Fraction failing the finite-model count floor at each fixed tolerance. -/
theorem dyadic_count_exceptional_density (d : ℕ) (hd : 0<d) (ε : ℝ) (he : 0<ε) :
    Tendsto (shortfallFrequency d ε) atTop (𝓝 0) :=
  (density_iff_classical_absolute_mean d hd).mpr (dyadic_count_absolute_classical d hd) ε he

/-- Even the absolute value of the frozen real part has vanishing weighted
mean. The minor-arc width is the target-dependent catalogue width here. -/
theorem dyadic_frozen_absolute_mean (d : ℕ) (hd : 0<d) :
    Tendsto (dyadicRatio d (fun n =>
      |(FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re|)) atTop (𝓝 0) := by
  let I (n : ℕ) := (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re
  let g (n : ℕ) := goldbachCount n-catalogueMajorModel n
  have short := (shortfall_mean_iff_density d hd).mpr (dyadic_count_exceptional_density d hd)
  have count := (absolute_mean_iff_shortfall d hd).mpr short
  have negligible := dyadic_mean_of_sublinear d hd (fun n => |I n|-|g n|) (by
    intro ε ep
    filter_upwards [frozen_count_error_sublinear ε ep] with n h
    exact (abs_abs_sub_abs_le_abs_sub (I n) (g n)).trans h)
  have diff : Tendsto (fun j => dyadicRatio d (fun n => |I n|) j-dyadicRatio d (fun n => |g n|) j) atTop (𝓝 0) := by
    simpa only [dyadicRatio,sum_sub_distrib,sub_div] using negligible
  change Tendsto (dyadicRatio d (fun n => |g n|)) atTop (𝓝 0) at count
  simpa only [sub_add_cancel,zero_add] using diff.add count

/-- Fraction failing the actual signed high-prime floor of the frozen catalogue. -/
theorem dyadic_frozen_exceptional_density (d : ℕ) (hd : 0<d) (ε : ℝ) (he : 0<ε) :
    Tendsto (fun j : ℕ => (((Ico j (2*j)).filter (fun i =>
      (FrozenBulk.deskI (d*i) (FrozenBulk.deskHigh (d*i)) (FrozenBulk.deskHigh (d*i))).re <
        -(ε*(d*i:ℕ)))).card:ℝ)/j) atTop (𝓝 0) :=
  dyadic_frozen_exceptional_density_of_count d hd (dyadic_count_exceptional_density d hd) ε he

#print axioms dyadic_count_absolute_classical
#print axioms dyadic_count_exceptional_density
#print axioms dyadic_frozen_absolute_mean
#print axioms dyadic_frozen_exceptional_density
end GoldbachMinor
