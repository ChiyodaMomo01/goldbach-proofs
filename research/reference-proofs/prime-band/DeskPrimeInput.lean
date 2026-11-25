import UpstreamMajor316
import MajorPositivity

namespace GoldbachMinor
open Finset Filter GoldbachWeight
open scoped Topology

private theorem desk_unit_mean (q a : ℕ) (hq : 0<q) (ha : a.Coprime q) :
    GoldbachMajorArc.unitMean q a=(((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ) := by
  rw [GoldbachMajorArc.unitMean_eq_ram ha]
  push_cast
  congr 1
  unfold GoldbachMajorArc.ram GoldbachMajorArc.phase
  simp_rw [mul_div_assoc',← mul_assoc]
  rw [GoldbachRamanujan.all_frequencies hq 1,sum_eq_single_of_mem 1 (Nat.one_mem_divisors.mpr hq.ne')]
  · simp
  · intro d _ h
    simp [show ¬d∣1 from fun hd => h (Nat.dvd_one.mp hd)]

private theorem desk_kernel_mesh (n : ℕ) (β : ℝ) :
    GoldbachMajorArc.kernel n β=discreteSpectrum n β+1 := by
  rw [GoldbachMajorArc.kernel,sum_range_succ']
  change _+GoldbachWeight.phase ((0:ℝ)*β)=_
  simp only [zero_mul,GoldbachWeight.phase,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero]
  congr 1
  apply sum_congr rfl
  intro j _
  change GoldbachWeight.phase ((↑(j+1):ℝ)*β)=GoldbachWeight.phase (β*(↑j+1))
  congr 1; push_cast; ring

/-- The pinned proof on the research desk gives the required discrete estimate
on the precise rational arcs without importing a stronger general theorem. -/
theorem desk_discrete_arc_bound : ∀ᶠ n : ℕ in atTop,
    ∀ q ∈ Icc 1 (catalogueCutoff n), ∀ a ∈ (range q).filter (·.Coprime q),
    ∀ β : ℝ, |β|≤(catalogueCutoff n:ℝ)/(q*n) →
    ‖GoldbachWeight.spectrum n primeLog ((a:ℝ)/q+β)-
      ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*discreteSpectrum n β)‖≤n/(Real.log n)^7+1 := by
  obtain ⟨M,hM,pref⟩ := GoldbachMajorArc.uniform_prefix_error
  have C : 0<(1+2*Real.pi) := by positivity
  have small := (GoldbachMajorArc.envelope_saving M).eventually_lt_const (one_div_pos.mpr C)
  have logs : Tendsto (fun n:ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [pref,small,cutoff_le_log_cube,logs.eventually_ge_atTop 1,eventually_ge_atTop 2] with n pf hs qc l hn
  intro q hq a ha β hb
  obtain ⟨qp,qQ⟩ := mem_Icc.mp hq
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have qr : 0<(q:ℝ) := by exact_mod_cast qp
  let z := Real.log n
  let E := GoldbachMajorArc.errorEnvelope M n
  have E0 : 0≤E := by unfold E GoldbachMajorArc.errorEnvelope; positivity
  have z0 : 0<z := by dsimp [z]; linarith
  have qc' : (q:ℝ)≤catalogueCutoff n := by exact_mod_cast qQ
  have up := (GoldbachMajorArc.rational_arc_error (by omega : 0<n) qp (a:=a) hb).trans
    (mul_le_mul_of_nonneg_right (pf q a qp qQ) (by positivity))
  change ‖GoldbachWeight.spectrum n primeLog _-GoldbachMajorArc.unitMean q a*GoldbachMajorArc.kernel n β‖≤
    ((q:ℝ)*E)*(1+2*Real.pi*((catalogueCutoff n:ℝ)/q)) at up
  have coeff := desk_unit_mean q a qp (mem_filter.mp ha).2
  rw [coeff,desk_kernel_mesh] at up
  let b : ℂ := (((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)
  have amplified : ((q:ℝ)*E)*(1+2*Real.pi*((catalogueCutoff n:ℝ)/q)) ≤ n/z^7 := by
    calc
      _ = ((q:ℝ)+2*Real.pi*(catalogueCutoff n))*E := by field_simp
      _ ≤ ((1+2*Real.pi)*z^3)*E := by
        apply mul_le_mul_of_nonneg_right _ E0
        nlinarith only [qc'.trans qc,mul_le_mul_of_nonneg_left qc (show 0≤2*Real.pi by positivity)]
      _ ≤ _ := by
        apply (le_div_iff₀ (pow_pos z0 7)).mpr
        have h := (div_lt_div_iff₀ np C).mp hs
        change z^10*E*(1+2*Real.pi)<1*(n:ℝ) at h
        nlinarith only [h]
  have endpt : ‖b*(discreteSpectrum n β+1)-b*discreteSpectrum n β‖≤1 := by
    rw [mul_add,mul_one,add_sub_cancel_left]
    exact moebius_coefficient_bound q qp
  exact (norm_sub_le_norm_sub_add_norm_sub _ (b*(discreteSpectrum n β+1)) _).trans
    (add_le_add (up.trans amplified) endpt)

private theorem log_pow_seven_small : ∀ᶠ n : ℕ in atTop, (Real.log n)^7 ≤ (n:ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (7:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
  have h' : Tendsto (fun x : ℝ => (Real.log x)^7/x) atTop (𝓝 0) := by simpa using h
  filter_upwards [(h'.comp tendsto_natCast_atTop_atTop).eventually_lt_const zero_lt_one,
    eventually_ge_atTop 1] with n hn hp
  exact ((div_lt_one (by exact_mod_cast hp : 0<(n:ℝ))).mp hn).le

/-- On every catalogue arc, transfer the existing prime-sum proof to the
actual high-prime weight, with a uniform continuous-model error. -/
theorem desk_high_arc_bound : ∀ᶠ n : ℕ in atTop,
    ∀ q ∈ Icc 1 (catalogueCutoff n), ∀ a ∈ (range q).filter (·.Coprime q),
    ∀ β : ℝ, |β|≤(catalogueCutoff n:ℝ)/(q*n) →
    ‖GoldbachWeight.spectrum n (high n) ((a:ℝ)/q+β)-
      ((((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)*continuousSpectrum n β)‖ ≤ 5*n/(Real.log n)^7 := by
  filter_upwards [desk_discrete_arc_bound,truncation_mesh_envelope,log_pow_seven_small,
    cutoff_le_log_cube,eventually_ge_atTop 2] with n hd mesh meshOne cut hn
  intro q hq a ha β hb
  have qp := (mem_Icc.mp hq).1
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have qr : 0<(q:ℝ) := by exact_mod_cast qp
  have q1 : (1:ℝ)≤q := by exact_mod_cast qp
  have lp : 0<Real.log n := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have bn : |β| *n ≤ (Real.log n)^3 := by
    have qa : (n:ℝ)≤q*n := by simpa only [one_mul] using mul_le_mul_of_nonneg_right q1 np.le
    exact (mul_le_mul_of_nonneg_left qa (abs_nonneg β)).trans (((le_div_iff₀ (mul_pos qr np)).mp hb).trans cut)
  have one : 1≤(n:ℝ)/(Real.log n)^7 := (one_le_div (pow_pos lp 7)).mpr meshOne
  apply (arc_transfer n q a (high n) β _ qp (high_spectrum_truncation n) (hd q hq a ha β hb)).trans
  have scale := mul_le_mul_of_nonneg_left bn (show 0≤2*Real.pi by positivity)
  rw [show 5*(n:ℝ)/(Real.log n)^7=3*n/(Real.log n)^7+2*(n/(Real.log n)^7) by ring]
  linarith only [mesh,one,scale]

theorem certified_major_model_fit : MajorModelFits := by
  intro ε ep
  have logs : Tendsto (fun n:ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [desk_high_arc_bound,cutoff_le_log_cube,GoldbachMajorArc.cutoff_separated,
    logs.eventually_ge_atTop 5,logs.eventually_ge_atTop (30/ε)] with n bound hq sep l lim
  let z := Real.log n
  let D := 5*n/z^7
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have zp : 0<z := by dsimp [z]; linarith
  have D0 : 0≤D := by dsimp [D]; positivity
  have small : D≤n := by
    apply (div_le_iff₀ (pow_pos zp 7)).mpr
    have pw := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5) l 7
    change (5:ℝ)^7≤z^7 at pw
    nlinarith only [mul_le_mul_of_nonneg_left pw np.le,np]
  have q2 : (catalogueCutoff n:ℝ)^2≤z^6 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hq 2).trans_eq (by dsimp [z]; ring)
  change 2*(catalogueCutoff n)^2<n at sep
  apply (catalogue_major_perturbation _ n sep (high n) D D0 bound).trans
  calc
    _ ≤ (2*z^6/n)*(D*(3*n)) := by
      apply mul_le_mul ((total_arc_width_bound _ n (by exact_mod_cast np)).trans ?_)
        (mul_le_mul_of_nonneg_left (by linarith only [small]) D0) (by positivity) (by positivity)
      gcongr
    _ = 30*n/z := by dsimp [D]; field_simp; ring
    _ ≤ ε*n := by
      apply (div_le_iff₀ zp).mpr
      have hz : 30≤z*ε := (div_le_iff₀ ep).mp lim
      nlinarith only [mul_le_mul_of_nonneg_right hz np.le]

/-- No external analytic assumption remains. The original bulk floor is
equivalent to a pointwise lower bound on the ordinary weighted Goldbach count. -/
theorem certified_bulk_iff_count_floor :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      catalogueMajorModel n ≤ goldbachCount n+ε*n :=
  bulk_iff_count_of_fit certified_major_model_fit

theorem certified_bulk_implies_eventual_goldbach (bulk : FrozenBulk.BulkFloor) :
    ∃ N:ℕ, ∀ n≥N, Even n → ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p+r=n :=
  bulk_implies_eventual_goldbach_of_fit certified_major_model_fit bulk

#print axioms certified_bulk_implies_eventual_goldbach
#print axioms certified_bulk_iff_count_floor
#print axioms desk_discrete_arc_bound
end GoldbachMinor
