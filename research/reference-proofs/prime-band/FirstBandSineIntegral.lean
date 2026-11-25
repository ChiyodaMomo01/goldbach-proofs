import ExactFirstBand

namespace GoldbachMinor
open Finset intervalIntegral

private theorem sinc_integral (x : ℝ) : Real.sinc x = ∫ t in (0:ℝ)..1, Real.cos (t*x) := by
  by_cases hx : x=0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx, integral_comp_mul_right Real.cos hx]
    simp [integral_cos,div_eq_inv_mul]

/-- Global Lipschitz bound, also at the removable singularity. -/
theorem sinc_difference (x z : ℝ) : |Real.sinc x-Real.sinc z| ≤ |x-z| := by
  rw [sinc_integral,sinc_integral,← integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
  have h := norm_integral_le_of_norm_le_const (a:=0) (b:=1) (C:=|x-z|)
    (f:=fun t : ℝ => Real.cos (t*x)-Real.cos (t*z)) (by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [Real.norm_eq_abs]
      refine (Real.abs_cos_sub_cos_le ..).trans ?_
      rw [← mul_sub,abs_mul,abs_of_nonneg ht.1.le]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (abs_nonneg (x-z)))
  simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using h

/-- On each mesh interval the right-endpoint approximation to the sine integral
has absolute error at most the square of the mesh. -/
theorem sinc_mesh_cell (a : ℝ) (ha : 0≤a) (k : ℕ) :
    |a*Real.sinc (a*((k:ℝ)+1)) -
      ∫ t in (a*k)..(a*((k:ℝ)+1)), Real.sinc t| ≤ a^2 := by
  let l := a*(k:ℝ)
  let r := a*((k:ℝ)+1)
  have len : r-l=a := by dsimp [r,l]; ring
  have hle : l≤r := by linarith
  have const : (∫ _t in l..r, Real.sinc r) = a*Real.sinc r := by
    rw [integral_const,len,smul_eq_mul]
  change |a*Real.sinc r-∫ t in l..r, Real.sinc t| ≤ _
  rw [← const,← integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
  have h := norm_integral_le_of_norm_le_const (a:=l) (b:=r) (C:=a)
    (f:=fun t => Real.sinc r-Real.sinc t) (by
      intro t ht
      rw [Set.uIoc_of_le hle] at ht
      rw [Real.norm_eq_abs]
      exact (sinc_difference ..).trans (by rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith [ht.1]))
  simpa only [Real.norm_eq_abs,len,abs_of_nonneg ha,pow_two] using h

/-- A right-endpoint sine sum on the whole offset interval has error at most
one square of the mesh size per sample. -/
theorem sinc_mesh_window (a : ℝ) (ha : 0≤a) (K H : ℕ) (hKH : K≤H) :
    |(∑ k ∈ Ioc K H, a*Real.sinc (a*k)) - ∫ t in (a*K)..(a*H), Real.sinc t| ≤
      ((H-K:ℕ):ℝ)*a^2 := by
  induction H, hKH using Nat.le_induction with
  | base => simp
  | succ H hKH ih =>
    have s : Ioc K (H+1) = insert (H+1) (Ioc K H) := by ext k; simp; omega
    have count : H+1-K=H-K+1 := by omega
    rw [s,sum_insert (by simp),← integral_add_adjacent_intervals (b:=a*H)
      (Real.continuous_sinc.intervalIntegrable ..) (Real.continuous_sinc.intervalIntegrable ..),
      count,Nat.cast_add,Nat.cast_one]
    rw [show (a*Real.sinc (a*((H:ℝ)+1))+(∑ k ∈ Ioc K H, a*Real.sinc (a*k)))-
        ((∫ t in a*K..a*H, Real.sinc t)+(∫ t in a*H..a*((H:ℝ)+1), Real.sinc t)) =
        ((∑ k ∈ Ioc K H, a*Real.sinc (a*k))-(∫ t in a*K..a*H, Real.sinc t))+
        (a*Real.sinc (a*((H:ℝ)+1))-(∫ t in a*H..a*((H:ℝ)+1), Real.sinc t)) by ring]
    exact (abs_add_le ..).trans ((add_le_add ih (sinc_mesh_cell a ha H)).trans_eq (by push_cast; ring))

private theorem integral_sinc_bound (x z : ℝ) : |∫ t in x..z, Real.sinc t|≤|z-x| := by
  simpa only [Real.norm_eq_abs,one_mul] using norm_integral_le_of_norm_le_const
    (a:=x) (b:=z) (C:=1) (f:=Real.sinc) (fun t _ => Real.abs_sinc_le_one t)

/-- Uniform comparison with the continuous sine integral including the omitted
initial offsets and a partial mesh cell at the upper end. -/
theorem sine_sum_integral (a z : ℝ) (ha : 0<a) (K H : ℕ) (kh : K≤H)
    (lo : a*H≤z) (hi : z≤a*((H:ℝ)+1)) :
    |(∑ k ∈ Ioc K H, Real.sin (a*k)/k) - ∫ t in (0:ℝ)..z, Real.sinc t| ≤
      ((H-K:ℕ):ℝ)*a^2+a*((K:ℝ)+1) := by
  let S := ∑ k ∈ Ioc K H, a*Real.sinc (a*k)
  have eq : (∑ k ∈ Ioc K H, Real.sin (a*k)/k) = S := by
    apply sum_congr rfl
    intro k hk
    have hk' : 0<(k:ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le K) (mem_Ioc.mp hk).1
    rw [Real.sinc_of_ne_zero (mul_pos ha hk').ne']; field_simp
  let F (x z : ℝ) := ∫ t in x..z, Real.sinc t
  have int (x z : ℝ) := Real.continuous_sinc.intervalIntegrable (μ:=MeasureTheory.volume) x z
  have split : F 0 z = F 0 (a*K)+F (a*K) (a*H)+F (a*H) z := by
    dsimp only [F]
    rw [integral_add_adjacent_intervals (int ..) (int ..),integral_add_adjacent_intervals (int ..) (int ..)]
  have left : |F 0 (a*K)|≤a*K := by
    simpa only [sub_zero,abs_of_nonneg (mul_nonneg ha.le (Nat.cast_nonneg K))] using integral_sinc_bound 0 (a*K)
  have right : |F (a*H) z|≤a := (integral_sinc_bound ..).trans (by rw [abs_of_nonneg (sub_nonneg.mpr lo)]; linarith)
  rw [eq]
  change |S-F 0 z| ≤ _
  rw [split,show S-(F 0 (a*K)+F (a*K) (a*H)+F (a*H) z) =
    ((S-F (a*K) (a*H))-F 0 (a*K))-F (a*H) z by ring]
  apply (abs_sub ..).trans
  apply le_trans (add_le_add ((abs_sub ..).trans (add_le_add (sinc_mesh_window a ha.le K H kh) left)) right)
  ring_nf
  exact le_rfl

/-- The upper endpoint of the actual first band produces the sine integral with
argument 2π/q, including when the upper mesh is incomplete. -/
theorem first_band_denominator_integral (Q n q K : ℕ) (hn : 0<n) (hq : 0<q) (hQ : 0<Q)
    (hk : K≤n/Q) :
    let a := 2*Real.pi*Q/((q:ℝ)*n)
    |(∑ k ∈ Ioc K (n/Q), Real.sin (a*k)/k) - ∫ t in (0:ℝ)..(2*Real.pi/q), Real.sinc t| ≤
      ((n/Q-K:ℕ):ℝ)*a^2+a*((K:ℝ)+1) := by
  let a := 2*Real.pi*Q/((q:ℝ)*n)
  have ha : 0<a := by dsimp [a]; positivity
  have hqr : 0<(q:ℝ) := by exact_mod_cast hq
  have hnr : 0<(n:ℝ) := by exact_mod_cast hn
  apply sine_sum_integral a _ ha K _ hk
  · have h : ((n/Q:ℕ):ℝ)*Q≤n := by exact_mod_cast Nat.div_mul_le_self n Q
    dsimp [a]
    field_simp
    nlinarith only [h]
  · have h : n < (((n/Q:ℕ):ℝ)+1)*Q := by
      exact_mod_cast (Nat.lt_div_mul_add hQ : n < n/Q*Q+Q) |>.trans_eq (by ring : n/Q*Q+Q=(n/Q+1)*Q)
    dsimp [a]
    field_simp
    nlinarith only [h]

noncomputable def sineIntegralWeight (q : ℕ) : ℝ :=
  (∫ t in (0:ℝ)..(2*Real.pi/q), Real.sinc t)/Real.pi

/-- The sine integral is positive at every first-band denominator. For q=1
the negative half period is paired with the preceding positive half period. -/
theorem sineIntegralWeight_pos (q : ℕ) (hq : 0<q) : 0<sineIntegralWeight q := by
  apply div_pos _ Real.pi_pos
  by_cases h : q=1
  · subst q
    simp only [Nat.cast_one,div_one]
    let f (x : ℝ) := Real.sinc x+Real.sinc (x+Real.pi)
    have pos : 0 < ∫ t in (0:ℝ)..Real.pi, f t := by
      apply integral_pos Real.pi_pos (by dsimp [f]; fun_prop)
      · intro x hx
        have hx0 := hx.1
        have hxpi := hx.2
        dsimp [f]
        rw [Real.sinc_of_ne_zero hx0.ne',Real.sinc_of_ne_zero (by positivity),Real.sin_add_pi,neg_div]
        have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx0.le hxpi
        have le := div_le_div_of_nonneg_left hs hx0 (show x≤x+Real.pi by linarith [Real.pi_pos])
        linarith
      · refine ⟨0,⟨le_rfl,Real.pi_pos.le⟩,?_⟩
        simp [f,Real.sinc_of_ne_zero Real.pi_ne_zero]
    have eq : (∫ t in (0:ℝ)..Real.pi, f t) = ∫ t in (0:ℝ)..(2*Real.pi), Real.sinc t := by
      dsimp [f]
      rw [integral_add (Real.continuous_sinc.intervalIntegrable ..) (by apply Continuous.intervalIntegrable; fun_prop),
        integral_comp_add_right Real.sinc Real.pi,zero_add, integral_add_adjacent_intervals
        (Real.continuous_sinc.intervalIntegrable ..) (Real.continuous_sinc.intervalIntegrable ..),two_mul]
    rwa [← eq]
  · have two : (2:ℝ)≤q := by exact_mod_cast (show 2≤q by omega)
    have hqr : (0:ℝ)<q := by exact_mod_cast hq
    have bound : 2*Real.pi/q≤Real.pi := (div_le_iff₀ hqr).mpr (by nlinarith only [mul_le_mul_of_nonneg_right two Real.pi_pos.le])
    apply integral_pos (by positivity) Real.continuous_sinc.continuousOn
    · intro x hx
      rw [Real.sinc_of_ne_zero hx.1.ne']
      exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le (hx.2.trans bound)) hx.1.le
    · exact ⟨0,⟨le_rfl,by positivity⟩,by simp⟩

#print axioms sineIntegralWeight_pos
#print axioms first_band_denominator_integral
#print axioms sine_sum_integral
#print axioms sinc_mesh_window
#print axioms sinc_mesh_cell
end GoldbachMinor
