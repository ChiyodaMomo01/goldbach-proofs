import BandPairs

namespace GoldbachMinor
open Finset GoldbachWeight
open scoped ComplexConjugate

/-- Integral of the steady prime density on [0,n] in centred form. -/
noncomputable def continuousSpectrum (n : ℕ) (β : ℝ) : ℂ :=
  phase (n*β/2)*((n*Real.sinc (Real.pi*n*β):ℝ):ℂ)

private theorem phase_add (s t : ℝ) : phase (s+t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem phase_minus (s : ℝ) : phase (-s)=conj (phase s) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1; push_cast; ring

theorem continuousSpectrum_integral (n : ℕ) (β : ℝ) :
    (∫ t in (0:ℝ)..n, phase (β*t)) = continuousSpectrum n β := by
  by_cases hn : n=0
  · simp [hn,continuousSpectrum]
  by_cases hz : β=0
  · simp [hz,continuousSpectrum,phase]
  let N := (n:ℝ)/2
  let ω := 2*Real.pi*β
  have hw : ω ≠ 0 := by dsimp [ω]; exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hz
  have hβ : Real.pi*n*β≠0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hn)) hz
  have shift := intervalIntegral.integral_comp_add_right (a := -N) (b := N) (fun t => phase (β*t)) N
  rw [neg_add_cancel,show N+N=(n:ℝ) by dsimp [N]; ring] at shift
  rw [← shift]
  have pt (x : ℝ) : phase (β*(x+N)) =
      phase (β*N)*(fun t : ℝ => Complex.exp ((t:ℂ)*Complex.I)) (ω*x) := by
    rw [show β*(x+N)=β*N+β*x by ring,phase_add]
    unfold phase ω
    congr 2
    push_cast
    ring
  simp_rw [pt]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => Complex.exp ((t:ℂ)*Complex.I)) hw,mul_neg,integral_exp_mul_I_eq_sin]
  unfold continuousSpectrum
  rw [show β*N=n*β/2 by dsimp [N]; ring, Real.sinc_of_ne_zero hβ]
  congr 1
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_inv]
  rw [show ω*N=Real.pi*n*β by dsimp [ω,N]; ring]
  dsimp [ω]
  push_cast
  field_simp

/-- Removing the target phase from the squared continuous model leaves the
square of a real sinc envelope and a constant phase at the rational centre. -/
theorem continuous_square_phase (n : ℕ) (x β : ℝ) :
    phase (-(n:ℝ)*(x+β))*(continuousSpectrum n β)^2 =
    phase (-(n:ℝ)*x)*(((n:ℝ)^2*(Real.sinc (Real.pi*n*β))^2:ℝ):ℂ) := by
  unfold continuousSpectrum
  rw [mul_pow,pow_two (phase _),← phase_add,← mul_assoc,← phase_add]
  push_cast
  rw [show -(n:ℝ)*(x+β)+(n*β/2+n*β/2) = -n*x by ring]
  ring

/-- B(z) is the remaining mass of the sinc square over the two symmetric arc radii. -/
noncomputable def archimedeanMass (z : ℝ) := ∫ t in -z..z, (Real.sinc (Real.pi*t))^2

noncomputable def modelArc (Q n q a : ℕ) : ℂ :=
  let x := (a:ℝ)/q
  let R := (Q:ℝ)/(q*n)
  let b : ℝ := (ArithmeticFunction.moebius q:ℝ)/q.totient
  ∫ β in -R..R, phase (-(n:ℝ)*(x+β))*((b:ℂ)*continuousSpectrum n β)^2

theorem model_arc_exact (Q n q a : ℕ) (hn : 0<n) (hq : 0<q) :
    modelArc Q n q a =
      phase (-(n:ℝ)*((a:ℝ)/q))*
        (( ((ArithmeticFunction.moebius q:ℝ)/q.totient)^2*n*archimedeanMass ((Q:ℝ)/q):ℝ):ℂ) := by
  let b : ℝ := (ArithmeticFunction.moebius q:ℝ)/q.totient
  let x := (a:ℝ)/q
  let R := (Q:ℝ)/(q*n)
  let f (t : ℝ) := (Real.sinc (Real.pi*t))^2
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have radius : (n:ℝ)*R=(Q:ℝ)/q := by dsimp [R]; field_simp
  have integral : (∫ β in -R..R, f ((n:ℝ)*β)) = (n:ℝ)⁻¹*archimedeanMass ((Q:ℝ)/q) := by
    rw [intervalIntegral.integral_comp_mul_left f hnr.ne',mul_neg,radius,smul_eq_mul]
    rfl
  have pt (β : ℝ) : phase (-(n:ℝ)*(x+β))*((b:ℂ)*continuousSpectrum n β)^2 =
      (phase (-(n:ℝ)*x)*((b:ℂ)^2*(n:ℂ)^2))*((f ((n:ℝ)*β):ℝ):ℂ) := by
    calc
      _ = (b:ℂ)^2*(phase (-(n:ℝ)*(x+β))*(continuousSpectrum n β)^2) := by ring
      _ = _ := by rw [continuous_square_phase]; dsimp [f]; push_cast; ring_nf
  change (∫ β in -R..R, phase (-(n:ℝ)*(x+β))*((b:ℂ)*continuousSpectrum n β)^2) = _
  simp_rw [pt]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,integral]
  push_cast
  dsimp only [b,x]
  push_cast
  field_simp

theorem center_trace (q n : ℕ) (hq : 0<q) :
    (∑ a ∈ (range q).filter (·.Coprime q), phase (-(n:ℝ)*((a:ℝ)/q))) = (ram q n:ℂ) := by
  have pos : (∑ a ∈ (range q).filter (·.Coprime q), phase ((n:ℝ)*((a:ℝ)/q))) = (ram q n:ℂ) := by
    calc
      _ = ∑ a ∈ (range q).filter (·.Coprime q), Complex.exp (((2*Real.pi*(n:ℝ)*a/q:ℝ):ℂ)*Complex.I) := by
        apply sum_congr rfl
        intro a _
        unfold phase; congr 3; ring
      _ = _ := by
        rw [GoldbachRamanujan.all_frequencies hq n,ram]
        push_cast
        apply sum_congr rfl
        intro d _
        split_ifs <;> simp
  simp_rw [neg_mul,phase_minus,← map_sum,pos,Complex.conj_ofReal]

theorem model_major_exact (Q n : ℕ) (hn : 0<n) :
    (∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (·.Coprime q), modelArc Q n q a) =
    (( (n:ℝ)*∑ q ∈ Icc 1 Q, ram q n*((ArithmeticFunction.moebius q:ℝ)/q.totient)^2*
      archimedeanMass ((Q:ℝ)/q):ℝ):ℂ) := by
  rw [mul_sum]
  push_cast
  apply sum_congr rfl
  intro q hq
  have hp := (mem_Icc.mp hq).1
  simp_rw [model_arc_exact Q n q _ hn hp,← sum_mul,center_trace q n hp]
  push_cast
  ring

theorem phase_unit (x : ℝ) : ‖phase x‖=1 := by
  simp [phase,Complex.norm_exp]

theorem moebius_coefficient_bound (q : ℕ) (hq : 0<q) :
    ‖(((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)‖≤1 := by
  have hφ : (1:ℝ)≤q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have m : |(ArithmeticFunction.moebius q:ℝ)|≤1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q))
  rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) q.totient),
    div_le_iff₀ (by linarith : (0:ℝ)<q.totient),one_mul]
  exact m.trans hφ

private theorem spectrum_model_bound (n q : ℕ) (hq : 0<q) (β : ℝ) :
    ‖(((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*continuousSpectrum n β‖≤n := by
  have coef := moebius_coefficient_bound q hq
  rw [Complex.norm_real,Real.norm_eq_abs] at coef
  simp only [continuousSpectrum,norm_mul,phase_unit,one_mul,Complex.norm_real,Real.norm_eq_abs,Nat.abs_cast]
  calc
    _ ≤ 1*((n:ℝ)*1) := by
      apply mul_le_mul coef _ (by positivity) zero_le_one
      exact mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (Nat.cast_nonneg _)
    _ = _ := by ring

noncomputable def actualArc (Q n q a : ℕ) (w : ℕ→ℝ) : ℂ :=
  let x := (a:ℝ)/q
  let R := (Q:ℝ)/(q*n)
  ∫ β in -R..R, phase (-(n:ℝ)*(x+β))*(GoldbachWeight.spectrum n w (x+β))^2

/-- On a single arc a uniform additive error for the prime exponential sum
integrates with its actual arc length and with one copy of the phase. -/
theorem single_arc_perturbation (Q n q a : ℕ) (w : ℕ→ℝ) (D : ℝ) (hq : 0<q) (hD : 0≤D)
    (approximation : ∀ β : ℝ, |β|≤(Q:ℝ)/(q*n) →
      ‖GoldbachWeight.spectrum n w ((a:ℝ)/q+β)-
        ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*continuousSpectrum n β)‖ ≤ D) :
    ‖actualArc Q n q a w-modelArc Q n q a‖ ≤ (2*(Q:ℝ)/(q*n))*(D*(2*n+D)) := by
  let R := (Q:ℝ)/(q*n)
  let x := (a:ℝ)/q
  let S (β : ℝ) := GoldbachWeight.spectrum n w (x+β)
  let M (β : ℝ) := ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*continuousSpectrum n β)
  let u (β : ℝ) := phase (-(n:ℝ)*(x+β))
  have R0 : 0≤R := by dsimp [R]; positivity
  have integrableS : Continuous (fun β => u β*(S β)^2) := by
    dsimp [u,S,GoldbachWeight.spectrum,phase]; fun_prop
  have integrableM : Continuous (fun β => u β*(M β)^2) := by
    dsimp [u,M,continuousSpectrum,phase]; fun_prop
  change ‖(∫ β in -R..R, u β*(S β)^2)-(∫ β in -R..R, u β*(M β)^2)‖ ≤ _
  rw [← intervalIntegral.integral_sub (integrableS.intervalIntegrable ..) (integrableM.intervalIntegrable ..)]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=D*(2*n+D)) ?_).trans_eq
  · rw [sub_neg_eq_add,abs_of_nonneg (by positivity : 0≤R+R)]
    dsimp [R]; ring
  intro β hβ
  rw [Set.uIoc_of_le (by linarith : -R≤R)] at hβ
  have h := approximation β (abs_le.mpr ⟨hβ.1.le,hβ.2⟩)
  change ‖S β-M β‖≤D at h
  have m : ‖M β‖≤n := spectrum_model_bound n q hq β
  have s : ‖S β‖≤D+n := by
    calc
      ‖S β‖ = ‖(S β-M β)+M β‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le ..).trans (add_le_add h m)
  rw [← mul_sub,show (S β)^2-(M β)^2=(S β+M β)*(S β-M β) by ring, norm_mul, phase_unit,one_mul,norm_mul]
  rw [mul_comm D]
  exact mul_le_mul (by linarith only [norm_add_le (S β) (M β),s,m]) h (norm_nonneg _) (by positivity)

noncomputable def catalogueMajorValue (Q n : ℕ) (w : ℕ → ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator
    (fun u => phase (-(n:ℝ)*u)*(GoldbachWeight.spectrum n w u)^2) t

private theorem phase_mode_periodic (k : ℤ) :
    Function.Periodic (fun t : ℝ => phase ((k:ℝ)*t)) 1 := by
  intro t
  change phase ((k:ℝ)*(t+1))=phase ((k:ℝ)*t)
  rw [mul_add,mul_one,phase_add]
  have hk : phase (k:ℝ)=1 := by
    unfold phase
    convert Complex.exp_int_mul_two_pi_mul_I k using 2
    push_cast
    ring
  rw [hk,mul_one]

private theorem majorValue_decomposition (Q n : ℕ) (scale : 2*Q^2<n) (w : ℕ→ℝ) :
    catalogueMajorValue Q n w = ∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (·.Coprime q), actualArc Q n q a w := by
  let f (t : ℝ) := phase (-(n:ℝ)*t)*(GoldbachWeight.spectrum n w t)^2
  have con : Continuous f := by dsimp [f,GoldbachWeight.spectrum,phase]; fun_prop
  have per : Function.Periodic f 1 := by
    intro t
    have negmode : phase (-(n:ℝ)*(t+1)) = phase (-(n:ℝ)*t) := by
      simpa only [Int.cast_neg,Int.cast_natCast] using phase_mode_periodic (-(n:ℤ)) t
    have posmode (k : ℕ) : phase ((k:ℝ)*(t+1))=phase ((k:ℝ)*t) := by
      simpa only [Int.cast_natCast] using phase_mode_periodic (k:ℤ) t
    simp only [f,GoldbachWeight.spectrum,negmode,posmode]
  change (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator f t) = _
  rw [catalogue_major_periodic Q n scale f con per]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro a _
  symm
  simpa only [actualArc,sub_eq_add_neg,f] using
    intervalIntegral.integral_comp_add_left (a := -((Q:ℝ)/(q*n))) (b := (Q:ℝ)/(q*n)) f ((a:ℝ)/q)

theorem catalogue_major_perturbation (Q n : ℕ) (scale : 2*Q^2<n) (w : ℕ→ℝ) (D : ℝ) (hD : 0≤D)
    (approximation : ∀ q ∈ Icc 1 Q, ∀ a ∈ (range q).filter (·.Coprime q),
      ∀ β : ℝ, |β|≤(Q:ℝ)/(q*n) →
      ‖GoldbachWeight.spectrum n w ((a:ℝ)/q+β)-
        ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*continuousSpectrum n β)‖ ≤ D) :
    ‖catalogueMajorValue Q n w-
      (( (n:ℝ)*∑ q ∈ Icc 1 Q, ram q n*((ArithmeticFunction.moebius q:ℝ)/q.totient)^2*
        archimedeanMass ((Q:ℝ)/q):ℝ):ℂ)‖ ≤ arcLength Q n*(D*(2*n+D)) := by
  rw [majorValue_decomposition Q n scale w,← model_major_exact Q n (by omega),← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  apply (norm_sum_le ..).trans
  unfold arcLength
  rw [sum_mul]
  apply sum_le_sum
  intro q hq
  apply (norm_sum_le ..).trans
  have card : ((range q).filter (·.Coprime q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]; congr 1; ext a
    simp only [mem_filter]; exact and_congr_right fun _ => Nat.coprime_comm
  calc
    _ ≤ ∑ a ∈ (range q).filter (·.Coprime q), (2*(Q:ℝ)/(q*n))*(D*(2*n+D)) :=
      sum_le_sum fun a ha => single_arc_perturbation Q n q a w D (mem_Icc.mp hq).1 hD (approximation q hq a ha)
    _ = _ := by simp only [sum_const,nsmul_eq_mul,card]; ring

theorem total_arc_width_bound (Q n : ℕ) (hn : 0<n) :
    arcLength Q n ≤ 2*(Q:ℝ)^2/n := by
  unfold arcLength
  have npos : 0<(n:ℝ) := by exact_mod_cast hn
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, 2*(Q:ℝ)/n := by
      apply sum_le_sum
      intro q hq
      have pos : 0<(q:ℝ) := by exact_mod_cast (show 0<q from (mem_Icc.mp hq).1)
      have φle : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
      calc
        _ ≤ (q:ℝ)*(2*(Q:ℝ)/(q*n)) := by gcongr
        _ = _ := by field_simp
    _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]; ring

#print axioms total_arc_width_bound
#print axioms catalogue_major_perturbation
#print axioms single_arc_perturbation
#print axioms model_major_exact
end GoldbachMinor
