import WideKernel
import WideVaughan

namespace GoldbachMinor
open Finset MeasureTheory GoldbachEstermannKernel

/-- The geometric sum is controlled by the inverse distance to the centre
on the centred unit period. -/
private theorem kernel_off_center (X : ℕ) (t : ℝ) (ht : 0 < |t|) (hh : |t| ≤ 1/2) :
    ‖kernel X t‖ ≤ 1/|t| := by
  have hp : |Real.pi*t| ≤ Real.pi/2 := by rw [abs_mul,abs_of_pos Real.pi_pos]; nlinarith only [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]
  have sine := Real.mul_abs_le_abs_sin hp
  rw [abs_mul,abs_of_pos Real.pi_pos] at sine
  have eq : 2/Real.pi*(Real.pi*|t|) = 2*|t| := by field_simp
  rw [eq] at sine
  have positive : 0 < |Real.sin (Real.pi*t)| := by linarith
  have terms (k : ℕ) : phase ((k:ℝ)*t) = (Complex.exp (Complex.I*(2*Real.pi*t:ℝ)))^k := by
    rw [← Complex.exp_nat_mul]
    unfold phase
    congr 1
    push_cast; ring
  simp only [kernel, terms]
  exact (OAI.Problem337.norm_geometric_phase_sum_le (abs_pos.mp positive) _).trans
    (one_div_le_one_div_of_le ht (by linarith))

private theorem twisted_cont (X n : ℕ) : Continuous (twisted X n) := by unfold twisted kernel phase; fun_prop

private theorem twisted_norm (X n : ℕ) (t : ℝ) : ‖twisted X n t‖ = ‖kernel X t‖^2 := by
  simp only [twisted,norm_mul,norm_pow,phase,Complex.norm_exp_ofReal_mul_I,mul_one]

private theorem one_wing (f : ℝ → ℂ) (hf : Continuous f) {b : ℝ} (hb : 0 < b) (hh : b ≤ 1/2)
    (h : ∀ t ∈ Set.Icc b (1/2:ℝ), ‖f t‖ ≤ t^(-2:ℤ)) :
    ‖∫ t in b..1/2, f t‖ ≤ 1/b := by
  have nz (t) (ht : t ∈ Set.uIcc b (1/2:ℝ)) : t ≠ 0 :=
    (hb.trans_le ((Set.uIcc_of_le hh ▸ ht).1)).ne'
  have cont : ContinuousOn (fun t : ℝ => t^(-2:ℤ)) (Set.uIcc b (1/2:ℝ)) :=
    continuousOn_id.zpow₀ (-2) (fun t ht => Or.inl (nz t ht))
  apply (intervalIntegral.norm_integral_le_integral_norm hh).trans
  apply (intervalIntegral.integral_mono_on hh (hf.norm.intervalIntegrable ..) cont.intervalIntegrable h).trans
  rw [integral_zpow (Or.inr ⟨by decide,fun ht => nz _ ht rfl⟩ : (0:ℤ) ≤ -2 ∨ (-2:ℤ) ≠ -1 ∧ (0:ℝ) ∉ Set.uIcc b (1/2:ℝ))]
  norm_num [one_div, div_neg]

/-- A single spectrum of length X recovers the coefficient n+1 in one period.
Truncating to [-b,b] costs at most 2/b, uniformly in the mode n≤X. -/
theorem truncated_kernel_error (X n : ℕ) (hn : n ≤ X) {b : ℝ} (hb : 0 < b) (hh : b ≤ 1/2) :
    ‖(∫ t in -b..b, twisted X n t) - ((n:ℂ)+1)‖ ≤ 2/b := by
  let F := twisted X n
  have fc := twisted_cont X n
  have major (t : ℝ) (hp : 0 < |t|) (ht : |t| ≤ 1/2) : ‖F t‖ ≤ (|t|)^(-2:ℤ) := by
    calc
      _ = ‖kernel X t‖^(2:ℕ) := twisted_norm ..
      _ ≤ (1/|t|)^(2:ℕ) := pow_le_pow_left₀ (norm_nonneg _) (kernel_off_center X t hp ht) 2
      _ = _ := by norm_num [one_div, inv_pow]
  have right := one_wing F fc hb hh fun t ht => by
    have tp := hb.trans_le ht.1
    simpa only [abs_of_pos tp] using major t (abs_pos.mpr tp.ne') ((abs_of_pos tp).trans_le ht.2)
  have left := one_wing (fun t => F (-t)) (fc.comp continuous_neg) hb hh fun t ht => by
    have tp := hb.trans_le ht.1
    simpa only [abs_neg,abs_of_pos tp] using major (-t) (by simpa only [abs_neg,abs_of_pos tp]) (by simpa only [abs_neg,abs_of_pos tp] using ht.2)
  rw [intervalIntegral.integral_comp_neg] at left
  have cut := intervalIntegral.integral_add_adjacent_intervals (fc.intervalIntegrable (μ:=volume) (-(1/2)) (-b)) (fc.intervalIntegrable (-b) b)
  have full := intervalIntegral.integral_add_adjacent_intervals (fc.intervalIntegrable (μ:=volume) (-(1/2)) b) (fc.intervalIntegrable b (1/2))
  rw [full_coefficient X n hn] at full
  change ‖(∫ t in -b..b, F t) - ((n:ℂ)+1)‖ ≤ _
  have id : (∫ t in -b..b, F t) - ((n:ℂ)+1) =
      -((∫ t in -(1/2:ℝ)..-b, F t) + ∫ t in b..1/2, F t) := by
    dsimp only [F] at *
    rw [← full, ← cut]; abel
  rw [id,norm_neg]
  exact (norm_add_le ..).trans ((add_le_add left right).trans_eq (by ring))

/-- Uniform domination for all arc radii, including those of large denominators. -/
theorem truncated_kernel_norm (X n : ℕ) {b : ℝ} (hb : 0 ≤ b) (hh : b ≤ 1/2) :
    ‖∫ t in -b..b, twisted X n t‖ ≤ (X:ℝ)+1 := by
  have cont : Continuous (fun t => ‖kernel X t‖^2) := by unfold kernel phase; fun_prop
  have loss := (loss_on_interval X X le_rfl (a:=-(1/2)) (b:=1/2) le_rfl (by norm_num) le_rfl).2
  have real := intervalIntegral.intervalIntegral_re (𝕜:=ℂ) ((twisted_cont X X).intervalIntegrable (μ:=volume) (-(1/2)) (1/2))
  change (∫ t in -(1/2:ℝ)..1/2, (twisted X X t).re) = (∫ t in -(1/2:ℝ)..1/2, twisted X X t).re at real
  rw [real,full_coefficient X X le_rfl] at loss
  simp only [Complex.add_re,Complex.natCast_re,Complex.one_re,sub_self] at loss
  apply (intervalIntegral.norm_integral_le_integral_norm (show -b ≤ b by linarith)).trans
  simp only [twisted_norm]
  exact (intervalIntegral.integral_mono_interval (neg_le_neg hh) (by linarith) hh
    (Filter.Eventually.of_forall fun t => sq_nonneg ‖kernel X t‖) (cont.intervalIntegrable ..)).trans (by linarith only [loss])

#print axioms truncated_kernel_error
end GoldbachMinor
