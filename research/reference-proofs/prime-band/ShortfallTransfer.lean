import ShortfallDensity

namespace GoldbachMinor
open Finset Filter
open scoped Topology

/-- The repository's classical mean-square input controls the absolute error
of the true pair count relative to the singular series on any fixed progression. -/
theorem classical_dyadic_absolute_mean (c : ℝ) (hc : ClassicalMeanSquare c) (d : ℕ) (hd : 0 < d) :
    Tendsto (dyadicRatio d (fun n => |goldbachCount n-c*n*binaryShape n n|)) atTop (𝓝 0) := by
  obtain ⟨A, a0, moment⟩ := hc
  let e (n : ℕ) := |goldbachCount n-c*n*binaryShape n n|
  have grows : Tendsto (fun j : ℕ => 2*d*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by omega : 0 < 2*d)) tendsto_id
  have logs := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).comp grows
  have powers := (tendsto_pow_atTop (α:=ℝ) (by decide : 4 ≠ 0)).comp logs
  have dp : 0 < (d:ℝ) := by exact_mod_cast hd
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  filter_upwards [grows.eventually moment, powers.eventually_gt_atTop (8*A*d/ε^2),
    eventually_ge_atTop 1] with j raw saving hj
  let T := Ico j (2*j)
  let X := 2*d*j
  let W := ∑ i ∈ T, (d:ℝ)*i
  let S := ∑ i ∈ T, e (d*i)
  let L := (Real.log X)^4
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  have card : T.card = j := by simp [T]; omega
  have scale : (d:ℝ)*j*j ≤ W := by
    have h := sum_le_sum (s:=T) fun i hi =>
      mul_le_mul_of_nonneg_left (show (j:ℝ) ≤ i by exact_mod_cast (mem_Ico.mp hi).1) dp.le
    simpa [W,card,mul_comm,mul_left_comm] using h
  have wp := (mul_pos (mul_pos dp jp) jp).trans_le scale
  have inj : (∑ i ∈ T, (e (d*i))^2) ≤ ∑ n ∈ Icc 1 X, (e n)^2 := by
    apply sum_le_sum_of_injOn (fun i => d*i)
    · intro i _ k _ h; exact Nat.eq_of_mul_eq_mul_left hd h
    · intro n hn
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
      have h := mem_Ico.mp hi
      exact mem_Icc.mpr ⟨Nat.mul_pos hd (hj.trans h.1),
        (Nat.mul_le_mul_left d h.2.le).trans_eq (by dsimp [X]; ring)⟩
    · intro _ _; rfl
    · intro _ _ _; exact sq_nonneg _
  have quad := sum_mul_sq_le_sq_mul_sq T (fun _ => (1:ℝ)) (fun i => e (d*i))
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,card] at quad
  have localEnergy : (∑ i ∈ T, (e (d*i))^2)*L ≤ A*((2:ℝ)*d*j)^3 := by
    apply (mul_le_mul_of_nonneg_right inj (by dsimp [L]; positivity)).trans
    simpa only [L, X, e, sq_abs, Nat.cast_mul, Nat.cast_ofNat] using raw
  change 8*A*d/ε^2 < L at saving
  have hL : 8*A*d < ε^2*L := by
    rw [mul_comm (ε^2) L]
    exact (div_lt_iff₀ (sq_pos_of_pos ep)).mp saving
  have lp : 0 < L := lt_of_le_of_lt (by positivity : 0 ≤ 8*A*d/ε^2) saving
  have upper : S^2*L ≤ (j:ℝ)*(A*(2*d*j)^3) := by
    exact (mul_le_mul_of_nonneg_right quad lp.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left localEnergy jp.le)
  have strict : S < ε*((d:ℝ)*j*j) := by
    apply lt_of_not_ge
    intro ge
    have pos : 0 ≤ ε*((d:ℝ)*j*j) := by positivity
    have sq := mul_self_le_mul_self pos ge
    have contradiction := mul_lt_mul_of_pos_right hL (by positivity : 0 < (d:ℝ)^2*(j:ℝ)^4)
    nlinarith only [upper, mul_le_mul_of_nonneg_right sq lp.le, contradiction]
  change dist (S/W) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) wp.le),
    div_lt_iff₀ wp]
  exact strict.trans_le (mul_le_mul_of_nonneg_left scale ep.le)

private theorem triangle_transfer (d : ℕ) (f g h : ℕ → ℝ)
    (fg : Tendsto (dyadicRatio d (fun n => |f n-g n|)) atTop (𝓝 0))
    (gh : Tendsto (dyadicRatio d (fun n => |g n-h n|)) atTop (𝓝 0)) :
    Tendsto (dyadicRatio d (fun n => |f n-h n|)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (sum_nonneg fun _ _ => by positivity))
    _ (by simpa only [zero_add] using fg.add gh)
  intro j
  simp only [dyadicRatio, ← add_div, ← sum_add_distrib]
  exact div_le_div_of_nonneg_right (sum_le_sum fun i _ => abs_sub_le (f (d*i)) (g (d*i)) (h (d*i)))
    (sum_nonneg fun _ _ => by positivity)

/-- Under the explicit classical count hypothesis, the open density problem
is equivalent to comparing the two deterministic main terms in mean absolute error. -/
theorem density_iff_model_matches_classical (c : ℝ) (hc : ClassicalMeanSquare c) (d : ℕ) (hd : 0 < d) :
    (∀ ε : ℝ, 0 < ε → Tendsto (shortfallFrequency d ε) atTop (𝓝 0)) ↔
    Tendsto (dyadicRatio d (fun n => |catalogueMajorModel n-c*n*binaryShape n n|)) atTop (𝓝 0) := by
  let main (n : ℕ) := c*n*binaryShape n n
  have h := classical_dyadic_absolute_mean c hc d hd
  rw [← shortfall_mean_iff_density d hd, ← absolute_mean_iff_shortfall d hd]
  constructor
  · intro hm
    exact triangle_transfer d catalogueMajorModel goldbachCount main (by simpa only [abs_sub_comm] using hm) h
  · intro hm
    exact triangle_transfer d goldbachCount main catalogueMajorModel h (by simpa only [abs_sub_comm] using hm)

#print axioms density_iff_model_matches_classical
end GoldbachMinor
