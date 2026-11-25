import ConductorEuler
import VaughanAlignment

namespace GoldbachMinor
open Finset Filter
open scoped Topology

private theorem conductor_trace_bound (q n : ℕ) (hq : 0<q) : |ram q n|≤q.totient := by
  calc
    _ = ‖(ram q n:ℂ)‖ := by simp
    _ ≤ ∑ z ∈ primitiveRoots q ℂ, ‖z^n‖ := by rw [ram_trace]; exact norm_sum_le ..
    _ = ∑ _z ∈ primitiveRoots q ℂ, (1:ℝ) := sum_congr rfl fun z hz => by
      rw [norm_pow,((mem_primitiveRoots hq).mp hz).norm'_eq_one hq.ne',one_pow]
    _ = _ := by simp [Complex.card_primitiveRoots]

theorem squarefree_totient_lower (q : ℕ) (sq : Squarefree q) : q≤2*q.totient^2 := by
  let T := q.primeFactors.erase 2
  have phi : q.totient = ∏ p ∈ q.primeFactors, (p-1) := by
    have h := Nat.totient_mul_prod_primeFactors q
    rw [Nat.prod_primeFactors_of_squarefree sq,Nat.mul_comm q.totient] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero sq.ne_zero) h
  have odd : (∏ p ∈ T, p) ≤ ∏ p ∈ T, (p-1)^2 := by
    apply prod_le_prod₀ (by intros; omega)
    intro p hp
    obtain ⟨ne,hm⟩ := mem_erase.mp hp
    have := (Nat.prime_of_mem_primeFactors hm).two_le
    have e : 3≤p := by omega
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le e
    subst p
    simp
    nlinarith
  rw [phi, ← prod_pow]
  calc
    q = ∏ p ∈ q.primeFactors, p := (Nat.prod_primeFactors_of_squarefree sq).symm
    _ ≤ 2*(∏ p ∈ T, p) := by
      by_cases h : 2∈q.primeFactors
      · exact (by simpa only [T,mul_comm 2] using (prod_erase_mul q.primeFactors (fun p => p) h).symm.le)
      · simp [T,erase_eq_of_notMem h]; omega
    _ ≤ 2*(∏ p ∈ T, (p-1)^2) := Nat.mul_le_mul_left _ odd
    _ = _ := by
      by_cases h : 2∈q.primeFactors
      · apply congrArg (2*·)
        have e := prod_erase_mul q.primeFactors (fun p => (p-1)^2) h
        norm_num at e
        exact e
      · simp [T,erase_eq_of_notMem h]

noncomputable def bandSeriesTerm (n q : ℕ) : ℝ :=
  if Squarefree q then ram q n/(q.totient:ℝ)^2*sineIntegralWeight q else 0

noncomputable def bandEnvelope (q : ℕ) : ℝ := 4*(1/(q:ℝ)^(3/2:ℝ))

theorem series_term_bound (n q : ℕ) : |bandSeriesTerm n q|≤bandEnvelope q := by
  by_cases sq : Squarefree q
  · have hq : 0<q := Nat.pos_of_ne_zero sq.ne_zero
    have hqr : (0:ℝ)<q := by exact_mod_cast hq
    have ht : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have root : Real.sqrt q ≤ 2*q.totient := by
      have h : (q:ℝ) ≤ 2*(q.totient:ℝ)^2 := by exact_mod_cast squarefree_totient_lower q sq
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity,by nlinarith [sq_nonneg (q.totient:ℝ)]⟩
    have sint : |sineIntegralWeight q|≤2/(q:ℝ) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=2*Real.pi/q) (C:=1)
        (f:=Real.sinc) (fun t _ => Real.abs_sinc_le_one t)
      have h' : |∫ t in (0:ℝ)..(2*Real.pi/q), Real.sinc t| ≤ 2*Real.pi/q := by
        simpa only [Real.norm_eq_abs,sub_zero,one_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi/q)] using h
      rw [sineIntegralWeight,abs_div,abs_of_pos Real.pi_pos,div_le_iff₀ Real.pi_pos]
      exact h'.trans_eq (by ring)
    have exponent : (q:ℝ)^(3/2:ℝ) = (q:ℝ)*Real.sqrt q := by
      rw [Real.sqrt_eq_rpow,show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hqr,Real.rpow_one]
    rw [bandSeriesTerm,ite_eq_left sq,abs_mul,abs_div,abs_of_nonneg (sq_nonneg (q.totient:ℝ))]
    calc
      _ ≤ ((q.totient:ℝ)/(q.totient:ℝ)^2)*(2/q) := by
        exact mul_le_mul (div_le_div_of_nonneg_right (conductor_trace_bound q n hq) (sq_nonneg _))
          sint (abs_nonneg _) (by positivity)
      _ ≤ _ := by
        dsimp only [bandEnvelope]
        rw [exponent]
        have hs := Real.sqrt_pos.mpr hqr
        field_simp
        linarith only [root]
  · simp [bandSeriesTerm,sq,bandEnvelope,Real.rpow_nonneg]

theorem bandEnvelope_summable : Summable bandEnvelope := ((Real.summable_one_div_nat_rpow
  (p:=(3/2:ℝ))).mpr (by norm_num)).mul_left 4

noncomputable def infiniteBandShape (n : ℕ) := ∑' q : ℕ, bandSeriesTerm n q

theorem infinite_band_uniform_bound (n : ℕ) : |infiniteBandShape n| ≤ ∑' q, bandEnvelope q := by
  have hs : Summable (bandSeriesTerm n) := bandEnvelope_summable.of_norm_bounded (fun q => series_term_bound n q)
  exact (norm_tsum_le_tsum_norm hs.norm).trans (hs.norm.tsum_le_tsum (fun q => series_term_bound n q) bandEnvelope_summable)

def visibleConductors (n : ℕ) := (Icc 1 (catalogueCutoff n)).filter (·∣factorialPeriod n)

private theorem eventually_visible (q : ℕ) (hq : 0<q) : ∀ᶠ n in atTop, q∈visibleConductors n := by
  filter_upwards [factorialIndex_tends.eventually (eventually_ge_atTop q),eventually_ge_atTop 2] with n hy hn
  have hd : q∣factorialPeriod n := Nat.dvd_factorial hq hy
  have width := (Nat.le_of_dvd (factorialPeriod_fits n).1 hd).trans (factorialPeriod_fits n).2
  have hlog := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^2≤n+2 by omega)
  have cutoff : logWidth n≤catalogueCutoff n := by unfold logWidth catalogueCutoff; nlinarith
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hq,width.trans cutoff⟩,hd⟩

/-- The arithmetic shape has a uniformly convergent conductor expansion even
when the target and the truncation scale are allowed to vary independently. -/
theorem conductor_sums_uniform (ε : ℝ) (he : 0<ε) : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
    |infiniteBandShape m - ∑ q ∈ visibleConductors n, bandSeriesTerm m q|≤ε := by
  let tail (n q : ℕ) := if q∈visibleConductors n then 0 else bandEnvelope q
  have nonneg (n q) : 0≤tail n q := by dsimp [tail,bandEnvelope]; split_ifs <;> positivity
  have dom (n q) : ‖tail n q‖≤bandEnvelope q := by
    rw [Real.norm_eq_abs,abs_of_nonneg (nonneg n q)]
    dsimp [tail,bandEnvelope]; split_ifs <;> first | positivity | exact le_rfl
  have lim (q) : Tendsto (fun n => tail n q) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    by_cases h : q=0
    · subst q
      exact Eventually.of_forall (fun n => by simp [tail,bandEnvelope])
    · filter_upwards [eventually_visible q (Nat.pos_of_ne_zero h)] with n hn
      simp [tail,hn]
  have small : Tendsto (fun n => ∑' q, tail n q) atTop (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence bandEnvelope_summable lim
      (Eventually.of_forall dom)
  filter_upwards [small.eventually_lt_const he] with n hn
  intro m
  let take (q : ℕ) := if q∈visibleConductors n then bandSeriesTerm m q else 0
  have keep : HasSum take (∑ q ∈ visibleConductors n, bandSeriesTerm m q) := by
    have h : HasSum take (∑ q ∈ visibleConductors n, take q) :=
      hasSum_sum_of_ne_finset_zero fun q hq => by simp [take,hq]
    convert h using 1
    exact sum_congr rfl fun q hq => by simp [take,hq]
  have full : Summable (bandSeriesTerm m) := bandEnvelope_summable.of_norm_bounded (fun q => series_term_bound m q)
  have diff := full.hasSum.sub keep
  have bd (q : ℕ) : ‖bandSeriesTerm m q-take q‖ ≤ tail n q := by
    by_cases hq : q∈visibleConductors n
    · simp [take,tail,hq]
    · simpa [take,tail,hq] using series_term_bound m q
  rw [show infiniteBandShape m-(∑ q ∈ visibleConductors n, bandSeriesTerm m q) =
    ∑' q, (bandSeriesTerm m q-take q) from diff.tsum_eq.symm]
  exact (norm_tsum_le_tsum_norm diff.summable.norm).trans ((diff.summable.norm.tsum_le_tsum bd
    (bandEnvelope_summable.of_norm_bounded (dom n))).trans hn.le)

/-- The inverse local mean exactly cancels the truncated twin-prime product. -/
theorem finite_twin_cancel (y : ℕ) :
    twinPartial y * (∏ p ∈ shapePrimes y, factorMean p) = 1 := by
  change (∏ p ∈ shapePrimes y, (1-1/((p:ℝ)-1)^2))*(∏ p ∈ shapePrimes y, factorMean p)=1
  rw [← prod_mul_distrib]
  apply prod_eq_one
  intro p hp
  have h3 : (3:ℝ)≤p := by exact_mod_cast (mem_filter.mp hp).2
  have h0 : (p:ℝ)≠0 := by linarith
  have h1 : (p:ℝ)-1≠0 := by linarith
  have h2 : (p:ℝ)-2≠0 := by linarith
  unfold factorMean goldbachFactor
  field_simp
  ring

private theorem finite_band_series (c : ℝ) (n : ℕ) : eulerBandLoss c n =
    c*n*(∏ p ∈ shapePrimes (factorialIndex n), factorMean p)*
      ∑ q ∈ visibleConductors n, bandSeriesTerm n q := by
  unfold eulerBandLoss
  congr 1
  unfold bandSeriesTerm visibleConductors
  rw [← sum_filter,filter_filter]

theorem normalized_euler_error (ε : ℝ) (he : 0<ε) : ∀ᶠ n : ℕ in atTop,
    |eulerBandLoss (2*twinPrimeConstant) n-2*n*infiniteBandShape n|≤ε*n := by
  let M := (∑' q, bandEnvelope q)+1
  let E := Real.exp 9
  have hM : 0<M := by
    have h := (abs_nonneg _).trans (infinite_band_uniform_bound 0)
    dsimp [M]; linarith
  have hE : 0<E := Real.exp_pos _
  have δ : 0<ε/(4*M*E) := by positivity
  have ht := Metric.tendsto_nhds.mp (twinPartial_tends.comp factorialIndex_tends) _ δ
  filter_upwards [conductor_sums_uniform (ε/4) (by positivity),conductor_sums_uniform 1 zero_lt_one,ht]
    with n herr hunit htwin
  let y := factorialIndex n
  let Z := ∏ p ∈ shapePrimes y, factorMean p
  let F := ∑ q ∈ visibleConductors n, bandSeriesTerm n q
  have hu : |F|≤M := by
    calc
      _ = |infiniteBandShape n - (infiniteBandShape n-F)| := by ring_nf
      _ ≤ _ := abs_sub ..
      _ ≤ _ := add_le_add (infinite_band_uniform_bound n) (hunit n)
  have Z0 : 0≤Z := prod_nonneg fun p hp => by
    have h3 : (3:ℝ)≤p := by exact_mod_cast (mem_filter.mp hp).2
    dsimp [factorMean,goldbachFactor]
    have h : 0≤(p:ℝ)-2 := by linarith
    positivity
  have Zle : Z≤E := factor_mean_uniform _ (fun _ hp => (mem_filter.mp hp).2)
  have eps : |twinPrimeConstant-twinPartial y|≤ε/(4*M*E) := by
    rw [abs_sub_comm]
    exact htwin.le
  have mult : |(twinPrimeConstant-twinPartial y)*Z*F|≤ε/4 := by
    rw [abs_mul,abs_mul,abs_of_nonneg Z0]
    exact (mul_le_mul (mul_le_mul eps Zle Z0 (by positivity)) hu (abs_nonneg _) (by positivity)).trans_eq (by field_simp)
  rw [finite_band_series]
  change |2*twinPrimeConstant*n*Z*F-2*n*infiniteBandShape n|≤_
  rw [show 2*twinPrimeConstant*n*Z*F-2*n*infiniteBandShape n = (2*n)*
      ((twinPrimeConstant-twinPartial y)*Z*F+(F-infiniteBandShape n)) by
    have eq : twinPartial y*Z=1 := finite_twin_cancel y
    linear_combination 2*(n:ℝ)*F*eq]
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*(n:ℝ))]
  have bound : |(twinPrimeConstant-twinPartial y)*Z*F+(F-infiniteBandShape n)|≤ε/2 := by
    apply (abs_add_le ..).trans
    rw [abs_sub_comm F]
    linarith only [mult,herr n]
  exact (mul_le_mul_of_nonneg_left bound (by positivity)).trans_eq (by ring)

theorem outer_series_iff (hc : ClassicalMeanSquare (2*twinPrimeConstant)) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      firstBandSum n (firstBandEnd n) n (majorCoefficient (catalogueCutoff n) n) +
        2*n*infiniteBandShape n ≤ pairMass n 0 (GoldbachWeight.high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  rw [outer_euler_iff _ hc]
  constructor <;> intro h ε he <;>
    obtain ⟨A,hA⟩ := h (ε/2) (half_pos he) <;>
    obtain ⟨M,hM⟩ := eventually_atTop.mp (normalized_euler_error (ε/2) (half_pos he)) <;>
    refine ⟨max A M,fun n hn hev => ?_⟩ <;>
    obtain ⟨hl,hu⟩ := abs_le.mp (hM n (by omega)) <;>
    linarith only [hl,hu,hA n (by omega) hev]

/-- Approximation of the actual signed first-band loss for every sufficiently
large even target in the normalization of Vaughan's binary theorem. -/
theorem exact_band_series_error (hc : ClassicalMeanSquare (2*twinPrimeConstant))
    (ε : ℝ) (he : 0<ε) : ∀ᶠ n : ℕ in atTop, Even n →
    |firstBandSum n (primeBandWidth n) (firstBandEnd n) (majorCoefficient (catalogueCutoff n) n) -
      2*n*infiniteBandShape n|≤ε*n := by
  let c := 2*twinPrimeConstant
  obtain ⟨A,hA⟩ := exact_band_profile_error c hc (ε/4) (by positivity)
  obtain ⟨B,hB⟩ := resonance_negligible c (ε/4) (by positivity)
  filter_upwards [eventually_ge_atTop (max A B),arithmetic_band_negligible c (ε/4) (by positivity),
    normalized_euler_error (ε/4) (by positivity)] with n hn hmean hnorm
  intro hev
  rw [arithmetic_band_euler] at hmean
  obtain ⟨h1,h2⟩ := abs_le.mp (hA n (by omega) hev)
  obtain ⟨h3,h4⟩ := abs_le.mp (hB n (by omega))
  obtain ⟨h5,h6⟩ := abs_le.mp hmean
  obtain ⟨h7,h8⟩ := abs_le.mp hnorm
  dsimp only [c] at *
  exact abs_le.mpr ⟨by linarith only [h1,h3,h5,h7],by linarith only [h2,h4,h6,h8]⟩

private theorem ram_divisible (q n : ℕ) (hq : 0<q) (hd : q∣n) : ram q n=q.totient := by
  apply Complex.ofReal_injective
  rw [ram_trace]
  push_cast
  have eq : (∑ z ∈ primitiveRoots q ℂ, z^n) = ∑ _z ∈ primitiveRoots q ℂ, (1:ℂ) :=
    sum_congr rfl fun z hz => (((mem_primitiveRoots hq).mp hz).pow_eq_one_iff_dvd n).mpr hd
  rw [eq]; simp [Complex.card_primitiveRoots]

/-- At zero every squarefree Ramanujan sum has its positive principal value.
The index zero here specifies an arithmetic residue, not a Goldbach target. -/
theorem infinite_band_at_zero_pos : 0 < infiniteBandShape 0 := by
  have nonneg (q : ℕ) : 0≤bandSeriesTerm 0 q := by
    by_cases sq : Squarefree q
    · have hq := Nat.pos_of_ne_zero sq.ne_zero
      rw [bandSeriesTerm,ite_eq_left sq,ram_divisible q 0 hq (dvd_zero _)]
      exact mul_nonneg (by positivity) (sineIntegralWeight_pos q hq).le
    · simp [bandSeriesTerm,sq]
  have hs : Summable (bandSeriesTerm 0) := bandEnvelope_summable.of_norm_bounded (fun q => series_term_bound 0 q)
  have one : bandSeriesTerm 0 1 = sineIntegralWeight 1 := by
    simp [bandSeriesTerm,ram_divisible 1 0 (by decide) (dvd_zero _)]
  exact (sineIntegralWeight_pos 1 (by decide)).trans_le (one ▸ hs.le_tsum 1 (fun q _ => nonneg q))

theorem factorial_band_shape_limit : Tendsto (fun j : ℕ => infiniteBandShape j.factorial) atTop
    (𝓝 (infiniteBandShape 0)) := by
  apply tendsto_tsum_of_dominated_convergence bandEnvelope_summable
  · intro q
    apply tendsto_const_nhds.congr'
    by_cases sq : Squarefree q
    · have hq := Nat.pos_of_ne_zero sq.ne_zero
      filter_upwards [eventually_ge_atTop q] with j hj
      simp only [bandSeriesTerm,sq,ite_true,ram_divisible _ _ hq (Nat.dvd_factorial hq hj),
        ram_divisible _ 0 hq (dvd_zero _)]
    · exact Eventually.of_forall fun j => by simp [bandSeriesTerm,sq]
  · exact Eventually.of_forall fun j q => series_term_bound j.factorial q

/-- On factorial targets the true first-band contribution divided by the target
has a strictly positive limit under the classical global estimate. -/
theorem factorial_first_band_limit (hc : ClassicalMeanSquare (2*twinPrimeConstant)) :
    Tendsto (fun j : ℕ => let n := j.factorial
      firstBandSum n (primeBandWidth n) (firstBandEnd n) (majorCoefficient (catalogueCutoff n) n)/(n:ℝ))
      atTop (𝓝 (2*infiniteBandShape 0)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have small := factorial_tendsto_atTop.eventually (exact_band_series_error hc (ε/3) (by positivity))
  have shape := Metric.tendsto_nhds.mp (factorial_band_shape_limit.const_mul 2) (ε/3) (by positivity)
  filter_upwards [small,shape,eventually_ge_atTop 2] with j herr hs hj
  let n := j.factorial
  let S := firstBandSum n (primeBandWidth n) (firstBandEnd n) (majorCoefficient (catalogueCutoff n) n)
  have hn : (0:ℝ)<n := by exact_mod_cast Nat.factorial_pos j
  have ev : Even n := even_iff_two_dvd.mpr (Nat.dvd_factorial (by decide) hj)
  have er : |S/(n:ℝ)-2*infiniteBandShape n| ≤ ε/3 := by
    rw [div_sub' hn.ne',abs_div,abs_of_pos hn,div_le_iff₀ hn]
    convert herr ev using 2; ring
  change |2*infiniteBandShape n-2*infiniteBandShape 0| < ε/3 at hs
  change |S/(n:ℝ)-2*infiniteBandShape 0|<ε
  have t := abs_sub_le (S/(n:ℝ)) (2*infiniteBandShape n) (2*infiniteBandShape 0)
  linarith only [t,er,hs,he]

#print axioms infinite_band_at_zero_pos
#print axioms factorial_first_band_limit
#print axioms exact_band_series_error
#print axioms outer_series_iff
#print axioms conductor_sums_uniform
#print axioms infinite_band_uniform_bound
end GoldbachMinor
