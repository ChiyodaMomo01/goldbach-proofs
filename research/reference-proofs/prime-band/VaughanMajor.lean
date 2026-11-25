import OuterArcModel
import GoldbachTruncation

namespace GoldbachMinor
open Finset Filter GoldbachWeight
open scoped Topology

/-- The exponential sum in Vaughan's major-arc main term runs from 1 to n. -/
noncomputable def discreteSpectrum (n : ℕ) (β : ℝ) : ℂ :=
  ∑ j ∈ range n, phase (β*((j:ℝ)+1))

private theorem phase_lipschitz (x y : ℝ) : ‖phase x-phase y‖ ≤ 2*Real.pi*|x-y| := by
  have h := (lipschitzWith_circleMap (0:ℂ) 1).dist_le_mul (2*Real.pi*x) (2*Real.pi*y)
  simpa only [circleMap_zero,Complex.ofReal_one,one_mul,dist_eq_norm,Real.coe_nnabs,abs_one,
    ← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi),phase] using h

/-- Replacing right endpoints by integration costs at most one mesh width per term. -/
theorem discrete_continuous_bound (n : ℕ) (β : ℝ) :
    ‖discreteSpectrum n β-continuousSpectrum n β‖ ≤ (n:ℝ)*(2*Real.pi*|β|) := by
  let f (x : ℝ) := phase (β*x)
  have hcon : Continuous f := by dsimp [f,phase]; fun_prop
  rw [← continuousSpectrum_integral]
  change ‖discreteSpectrum n β-(∫ x in (0:ℝ)..↑n, f x)‖ ≤ _
  induction n with
  | zero => simp [discreteSpectrum]
  | succ n ih =>
    have edge : ‖f (n+1)-(∫ x in (n:ℝ)..(n+1), f x)‖ ≤ 2*Real.pi*|β| := by
      have one : (∫ _x in (n:ℝ)..(n+1), f (n+1)) = f (n+1) := by simp
      rw [← one,← intervalIntegral.integral_sub (continuous_const.intervalIntegrable ..) (hcon.intervalIntegrable ..)]
      apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=2*Real.pi*|β|) ?_).trans_eq
      · simp
      intro x hx
      rw [Set.uIoc_of_le (by linarith : (n:ℝ)≤n+1)] at hx
      have d : |(n:ℝ)+1-x|≤1 := abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩
      apply (phase_lipschitz _ _).trans
      rw [← mul_sub,abs_mul]
      nlinarith only [mul_le_mul_of_nonneg_left d (show 0≤2*Real.pi*|β| by positivity)]
    rw [Nat.cast_succ,← intervalIntegral.integral_add_adjacent_intervals
      (hcon.intervalIntegrable 0 (n:ℝ)) (hcon.intervalIntegrable (n:ℝ) (n+1))]
    change ‖(∑ j ∈ range (n+1), f (j+1))- _‖ ≤ _
    rw [sum_range_succ,show (∑ j ∈ range n, f (j+1))=discreteSpectrum n β by rfl,
      add_sub_add_comm]
    exact (norm_add_le ..).trans ((add_le_add ih edge).trans_eq (by ring))

/-- This is the entire cost of dropping the primes with p³ ≤ n, uniformly in frequency. -/
theorem high_spectrum_truncation (n : ℕ) (t : ℝ) :
    ‖spectrum n (high n) t-spectrum n primeLog t‖ ≤ Real.log 4 * cubeCutoff n := by
  let M := cubeCutoff n
  have mem (p : ℕ) (h : p∈range (n+1)) (hpow : p^3≤n) : p∈range (M+1) :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.le_findGreatest (Nat.le_of_lt_succ (mem_range.mp h)) hpow))
  unfold GoldbachWeight.spectrum
  rw [← sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply le_trans _ (primeLog_sum M)
  calc
    _ = ∑ p ∈ (range (n+1)).filter (fun p => p^3≤n), primeLog p := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases hp : p^3≤n
      · simp [high,hp,phase_unit,Real.norm_eq_abs,abs_of_nonneg (primeLog_nonneg p)]
      · simp [high,primeLog,hp]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun p hp => mem p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
      (fun p _ _ => primeLog_nonneg p)

/-- The case A = 3 of Vaughan's Theorem 5, with positive-integer mesh points.
The number-theoretic estimate is an explicit external input. -/
def VaughanMajorArcEstimate : Prop :=
  ∃ c C : ℝ, 0<c ∧ 0≤C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ q a : ℕ, 0<q → (q:ℝ)≤(Real.log n)^3 → a.Coprime q →
    ∀ β : ℝ, |β|≤(Real.log n)^3/n →
    ‖GoldbachWeight.spectrum n primeLog ((a:ℝ)/q+β)-
      ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*discreteSpectrum n β)‖ ≤
      C*n*Real.exp (-c*Real.sqrt (Real.log n))

private theorem arc_transfer (n q a : ℕ) (w : ℕ→ℝ) (β D : ℝ) (hq : 0<q)
    (close : ∀ t, ‖GoldbachWeight.spectrum n w t-GoldbachWeight.spectrum n primeLog t‖ ≤ Real.log 4*cubeCutoff n)
    (h : ‖GoldbachWeight.spectrum n primeLog ((a:ℝ)/q+β)-
        ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*discreteSpectrum n β)‖ ≤ D) :
    ‖GoldbachWeight.spectrum n w ((a:ℝ)/q+β)-
        ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*continuousSpectrum n β)‖ ≤
      Real.log 4*cubeCutoff n+D+(n:ℝ)*(2*Real.pi*|β|) := by
  let b : ℂ := (((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)
  let t := (a:ℝ)/q+β
  calc
    _ ≤ ‖GoldbachWeight.spectrum n w t-GoldbachWeight.spectrum n primeLog t‖ +
        ‖GoldbachWeight.spectrum n primeLog t-b*discreteSpectrum n β‖ +
        ‖b*(discreteSpectrum n β-continuousSpectrum n β)‖ := by
      rw [mul_sub]
      exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add (norm_sub_le_norm_sub_add_norm_sub _ _ _) le_rfl)
    _ ≤ _ := by
      apply add_le_add (add_le_add (close t) h)
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (moebius_coefficient_bound q hq) (norm_nonneg _)).trans
        (by simpa using discrete_continuous_bound n β)

private theorem log_nat_tendsto : Tendsto (fun n:ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem cutoff_le_log_cube : ∀ᶠ n : ℕ in atTop, (catalogueCutoff n:ℝ)≤(Real.log n)^3 := by
  let b := Real.log 2
  have hb : 0<b := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop 2,log_nat_tendsto.eventually_ge_atTop ((2/b)^2)] with n hn hl
  let d := Nat.log 2 (n+2)
  have pos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have bd : (2:ℝ)^d ≤ (2:ℝ)*n := by
    exact_mod_cast (Nat.pow_log_le_self 2 (show n+2≠0 by omega)).trans (show n+2≤2*n by omega)
  have l := Real.log_le_log (by positivity) bd
  rw [Real.log_pow,Real.log_mul (by norm_num) pos.ne'] at l
  have ln := Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤n by exact_mod_cast hn)
  have dsmall : (d:ℝ)≤(2/b)*Real.log n := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hb]
    dsimp [b]; linarith
  change (↑(d^2):ℝ) ≤ _
  rw [Nat.cast_pow]
  have sq := pow_le_pow_left₀ (Nat.cast_nonneg _) dsmall 2
  rw [mul_pow] at sq
  exact sq.trans ((mul_le_mul_of_nonneg_right hl (sq_nonneg _)).trans_eq (by ring))

private theorem decay_budget (k : ℕ) (C b : ℝ) (hb : 0<b) :
    ∀ᶠ x : ℝ in atTop, C*(x^k*Real.exp (-b*x))≤1 := by
  have h : Tendsto (fun x : ℝ => C*(x^k*Real.exp (-b*x))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) b hb).const_mul C
  exact (h.eventually_lt_const zero_lt_one).mono fun _ hx => hx.le

private theorem three_errors (c C : ℝ) (hc : 0<c) : ∀ᶠ n : ℕ in atTop,
    Real.log 4*cubeCutoff n+C*n*Real.exp (-c*Real.sqrt (Real.log n))+
      2*Real.pi*(Real.log n)^3 ≤ 3*n/(Real.log n)^7 := by
  filter_upwards [eventually_ge_atTop 2, log_nat_tendsto.eventually_ge_atTop 1,
    (Real.tendsto_sqrt_atTop.comp log_nat_tendsto).eventually (decay_budget 14 C c hc),
    log_nat_tendsto.eventually (decay_budget 7 (Real.log 4) (1/2) (by norm_num)),
    log_nat_tendsto.eventually (decay_budget 10 (2*Real.pi) 1 one_pos)] with n hn hz h1 h2 h3
  let z := Real.log n
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have zp : 0<z := by dsimp [z]; linarith
  have en : Real.exp z = n := Real.exp_log np
  have ex : Real.exp (-(1/2)*z)*(n:ℝ)=Real.sqrt n := by
    rw [← en,← Real.exp_add,← Real.exp_half]; congr 1; ring
  have ex' : Real.exp (-(1:ℝ)*z)*(n:ℝ)=1 := by
    rw [← en,← Real.exp_add]; simp
  have root : (Real.sqrt z)^14=z^7 := by
    calc
      _ = ((Real.sqrt z)^2)^7 := by ring
      _ = _ := by rw [Real.sq_sqrt zp.le]
  change C*((Real.sqrt z)^14*Real.exp (-c*Real.sqrt z))≤1 at h1
  rw [root] at h1
  change Real.log 4*(z^7*Real.exp (-(1/2)*z))≤1 at h2
  change 2*Real.pi*(z^10*Real.exp (-(1:ℝ)*z))≤1 at h3
  have a : (Real.log 4*cubeCutoff n)*z^7 ≤ n := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cubeCutoff_le_sqrt n)
      (Real.log_nonneg (by norm_num))) (pow_nonneg zp.le 7)).trans
    rw [← ex]
    nlinarith only [mul_le_mul_of_nonneg_right h2 np.le]
  have b : (C*n*Real.exp (-c*Real.sqrt z))*z^7 ≤ n := by
    nlinarith only [mul_le_mul_of_nonneg_right h1 np.le]
  have d : (2*Real.pi*z^3)*z^7 ≤ n := by
    calc
      _ = (2*Real.pi*(z^10*Real.exp (-(1:ℝ)*z)))*n := by
        rw [show (2*Real.pi*(z^10*Real.exp (-(1:ℝ)*z)))*n =
          (2*Real.pi*z^10)*(Real.exp (-(1:ℝ)*z)*n) by ring,ex']; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right h3 np.le).trans_eq (one_mul _)
  apply (le_div_iff₀ (pow_pos zp 7)).mpr
  change (_ + _ + _)*z^7 ≤ 3*(n:ℝ)
  linarith only [a,b,d]

/-- Uniform conversion of Vaughan's full-prime, discrete estimate to the
catalogue's continuous estimate for a weight with controlled truncation at every point of every actual arc. -/
private theorem catalogue_arc_bound (v : VaughanMajorArcEstimate) (w : ℕ→ℕ→ℝ)
    (close : ∀ n t, ‖GoldbachWeight.spectrum n (w n) t-GoldbachWeight.spectrum n primeLog t‖ ≤ Real.log 4*cubeCutoff n) : ∀ᶠ n : ℕ in atTop,
    ∀ q ∈ Icc 1 (catalogueCutoff n), ∀ a ∈ (range q).filter (·.Coprime q),
      ∀ β : ℝ, |β|≤(catalogueCutoff n:ℝ)/(q*n) →
      ‖GoldbachWeight.spectrum n (w n) ((a:ℝ)/q+β)-
        ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*continuousSpectrum n β)‖ ≤
          3*n/(Real.log n)^7 := by
  obtain ⟨c,C,hc,_,approx⟩ := v
  filter_upwards [eventually_ge_atTop 2,cutoff_le_log_cube,three_errors c C hc,approx] with n hn hQ budget ha
  intro q hq a ha' β hβ
  obtain ⟨ql,qu⟩ := mem_Icc.mp hq
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have qo : (1:ℝ)≤q := by exact_mod_cast ql
  have qp : (0:ℝ)<q := by linarith
  have qbound : (q:ℝ)≤(Real.log n)^3 := (by exact_mod_cast qu : (q:ℝ)≤catalogueCutoff n).trans hQ
  have betan : |β| *n ≤ (Real.log n)^3 := by
    have h := (le_div_iff₀ (mul_pos qp np)).mp hβ
    have qa : (n:ℝ)≤q*n := by simpa only [one_mul] using mul_le_mul_of_nonneg_right qo np.le
    exact (mul_le_mul_of_nonneg_left qa (abs_nonneg β)).trans (h.trans hQ)
  have full := ha q a ql qbound (mem_filter.mp ha').2 β ((le_div_iff₀ np).mpr betan)
  apply (arc_transfer n q a (w n) β _ ql (close n) full).trans
  apply le_trans _ budget
  exact add_le_add le_rfl (by nlinarith only [mul_le_mul_of_nonneg_left betan (show 0≤2*Real.pi by positivity)])

noncomputable def catalogueMajorModel (n : ℕ) : ℝ :=
  n*∑ q ∈ Icc 1 (catalogueCutoff n), ram q n*((ArithmeticFunction.moebius q:ℝ)/q.totient)^2*
    archimedeanMass ((catalogueCutoff n:ℝ)/q)

/-- Uniform error in the complete major-arc projection of the given spectrum. -/
private theorem projection_of_truncation (v : VaughanMajorArcEstimate) (w : ℕ→ℕ→ℝ)
    (close : ∀ n t, ‖GoldbachWeight.spectrum n (w n) t-GoldbachWeight.spectrum n primeLog t‖ ≤ Real.log 4*cubeCutoff n) : ∀ᶠ n : ℕ in atTop,
    ‖catalogueMajorValue (catalogueCutoff n) n (w n)-(catalogueMajorModel n:ℂ)‖ ≤
      18*n/Real.log n := by
  obtain ⟨S,hS⟩ : ∃ S:ℕ, ∀ n≥S, 2*(catalogueCutoff n)^2<n :=
    PEqualNP.Outside.L_goldbach_arc_cutoff_scale
  filter_upwards [eventually_ge_atTop S,log_nat_tendsto.eventually_ge_atTop 3,
    cutoff_le_log_cube,catalogue_arc_bound v w close] with n hn hz hQ bound
  let z := Real.log n
  let D := 3*n/z^7
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by have := hS n hn; omega)
  have zp : 0<z := by dsimp [z]; linarith
  have D0 : 0≤D := by dsimp only [D]; positivity
  have small : D≤n := by
    apply (div_le_iff₀ (pow_pos zp 7)).mpr
    have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hz 7
    change (3:ℝ)^7≤z^7 at hpow
    nlinarith only [mul_le_mul_of_nonneg_left hpow np.le,np]
  have Qbound : (catalogueCutoff n:ℝ)^2≤z^6 := by
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 2).trans_eq (by dsimp [z]; ring)
  apply (catalogue_major_perturbation _ n (hS n hn) (w n) D D0 bound).trans
  calc
    _ ≤ (2*z^6/n)*(D*(3*n)) := by
      apply mul_le_mul ((total_arc_width_bound _ n (by exact_mod_cast np)).trans ?_)
        (mul_le_mul_of_nonneg_left (by linarith only [small]) D0) (by positivity) (by positivity)
      gcongr
    _ = _ := by dsimp [D,z]; field_simp; ring

theorem major_model_projection (v : VaughanMajorArcEstimate) : ∀ᶠ n : ℕ in atTop,
    ‖catalogueMajorValue (catalogueCutoff n) n (high n)-(catalogueMajorModel n:ℂ)‖ ≤ 18*n/Real.log n :=
  projection_of_truncation v high high_spectrum_truncation

theorem full_major_model_projection (v : VaughanMajorArcEstimate) : ∀ᶠ n : ℕ in atTop,
    ‖catalogueMajorValue (catalogueCutoff n) n primeLog-(catalogueMajorModel n:ℂ)‖ ≤ 18*n/Real.log n := by
  apply projection_of_truncation v (fun _ => primeLog)
  intro n t
  simp only [sub_self,norm_zero]
  positivity

theorem major_model_negligible (v : VaughanMajorArcEstimate) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖catalogueMajorValue (catalogueCutoff n) n (high n)-(catalogueMajorModel n:ℂ)‖ ≤ ε*n := by
  filter_upwards [major_model_projection v,log_nat_tendsto.eventually_ge_atTop (18/ε)] with n h hx
  have hz : 0<Real.log n := lt_of_lt_of_le (by positivity : 0<18/ε) hx
  apply h.trans ((div_le_iff₀ hz).mpr ?_)
  have := (div_le_iff₀ hε).mp hx
  nlinarith only [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (α:=ℝ) n)]

#print axioms major_model_negligible
#print axioms full_major_model_projection
#print axioms cutoff_le_log_cube
#print axioms high_spectrum_truncation
#print axioms discrete_continuous_bound
end GoldbachMinor
