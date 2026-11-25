import OuterArcModel

namespace GoldbachMinor
open GoldbachWeight MeasureTheory Filter
open scoped Topology

private noncomputable def density (x : ℝ) := (Real.sinc (Real.pi*x))^2

private theorem density_integrable : Integrable density := by
  apply (integrable_inv_one_add_sq.const_mul 2).mono'
    ((by fun_prop : Continuous (fun x : ℝ => (Real.sinc (Real.pi*x))^2)).aestronglyMeasurable)
  filter_upwards with x
  change ‖(Real.sinc (Real.pi*x))^2‖ ≤ 2 * (1+x^2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : (Real.sinc (Real.pi*x))^2 ≤ 1 := by
    have h := Real.abs_sinc_le_one (Real.pi*x)
    nlinarith only [sq_abs (Real.sinc (Real.pi*x)), mul_self_le_mul_self (abs_nonneg _) h]
  by_cases hx : x=0
  · simp [hx]
  have nz := mul_ne_zero Real.pi_ne_zero hx
  have h2 : (Real.sinc (Real.pi*x))^2*x^2 ≤ 1 := by
    rw [Real.sinc_of_ne_zero nz, div_pow, mul_pow, mul_comm, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    have h := Real.sin_sq_le_one (Real.pi*x)
    nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg x),
      mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ Real.pi^2 by nlinarith [Real.pi_gt_three]) (sq_nonneg x)]
  linarith only [h1,h2]

private theorem density_periodization (x : ℝ) : ∑' k : ℤ, density (x+k) = 1 := by
  let f (t : ℝ) := phase (-x*t)
  have l2 : MemLp f 2 (volume.restrict (Set.Ioc 0 1)) := by
    apply (memLp_const (c:=(1:ℝ))).mono' (by dsimp [f,phase]; fun_prop)
    exact ae_of_all _ fun t => (phase_unit _).le
  have coeff (k : ℤ) : ‖fourierCoeffOn (zero_lt_one : (0:ℝ)<1) f k‖^2 = density (x+k) := by
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero, div_one, one_smul, smul_eq_mul]
    have pt (t : ℝ) : fourier (-k) (t : AddCircle (1:ℝ)) * f t = phase ((-(x+k))*t) := by
      rw [fourier_coe_apply]
      dsimp [f,phase]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [fourier_coe_apply, sub_zero]
    simp only [fourier_coe_apply] at pt
    simp_rw [pt]
    have h := continuousSpectrum_integral 1 (-(x+k))
    simp only [Nat.cast_one] at h
    rw [h, continuousSpectrum, norm_mul, phase_unit]
    simp [density, sq_abs]
    rw [show Real.pi * (-(k:ℝ) + -x) = -(Real.pi*(x+k)) by ring, Real.sinc_neg]
  simp_rw [← coeff]
  rw [tsum_sq_fourierCoeffOn zero_lt_one l2]
  simp [f, phase_unit]

/-- The sinc-square density has full mass one with the catalogue's pi scaling. -/
theorem integral_catalogue_sinc_square : (∫ x : ℝ, (Real.sinc (Real.pi*x))^2) = 1 := by
  have sum := density_integrable.hasSum_intervalIntegral_comp_add_int
  simp only [intervalIntegral.integral_of_le zero_le_one] at sum
  let μ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have terms (k : ℤ) : Integrable (fun x : ℝ => density (x+k)) μ := by
    exact (density_integrable.comp_add_right (k:ℝ)).integrableOn
  have norm (k : ℤ) (x : ℝ) : ‖density (x+k)‖ = density (x+k) := abs_of_nonneg (sq_nonneg _)
  change (∫ x, density x) = 1
  rw [← sum.tsum_eq, integral_tsum_of_summable_integral_norm terms (by simpa only [norm] using sum.summable)]
  simp [μ, density_periodization]

theorem archimedean_mass_tends_to_one : Tendsto archimedeanMass atTop (𝓝 1) := by
  rw [← integral_catalogue_sinc_square]
  exact intervalIntegral_tendsto_integral density_integrable tendsto_neg_atTop_atBot tendsto_id

theorem archimedean_mass_le_one (x : ℝ) (hx : 0 ≤ x) : archimedeanMass x ≤ 1 := by
  rw [archimedeanMass, intervalIntegral.integral_of_le (by linarith), ← integral_catalogue_sinc_square]
  exact setIntegral_le_integral density_integrable (ae_of_all _ fun t => sq_nonneg _)

#print axioms archimedean_mass_tends_to_one
end GoldbachMinor
