import VaughanMajor

namespace GoldbachMinor
open Finset Filter GoldbachWeight Set MeasureTheory

/-- With no major arcs the entire circle integral picks out the exact target. -/
private theorem full_projection (n : ℕ) (hn : 0<n) (w : ℕ→ℝ) :
    (∫ t in (0:ℝ)..1, GoldbachWeight.spectrum n w t * GoldbachWeight.spectrum n w t *
      phase (-(n:ℝ)*t)) = (pairMass n 0 w:ℂ) := by
  have empty : catalogueArcs 0 n = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro t ⟨q,a,hl,hu,_⟩
    omega
  have h := integral_eq_arithmeticBulk 0 n (by simpa using hn) w
  rw [empty,Set.compl_empty,indicator_univ] at h
  apply h.trans
  congr 1
  unfold arithmeticBulk pairMass
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  by_cases eq : (offset n p r).natAbs=0 <;> simp [minorCoefficient,majorCoefficient,arcLength,eq]

theorem major_plus_minor (Q n : ℕ) (scale : 2*Q^2<n) (w : ℕ→ℝ) :
    (arithmeticBulk Q n w:ℂ)+catalogueMajorValue Q n w=(pairMass n 0 w:ℂ) := by
  let f := fun t : ℝ => GoldbachWeight.spectrum n w t * GoldbachWeight.spectrum n w t * phase (-(n:ℝ)*t)
  have con : Continuous f := by dsimp [f,GoldbachWeight.spectrum,phase]; fun_prop
  have integ (A : Set ℝ) (hA : MeasurableSet A) :
      IntervalIntegrable (A.indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (con.integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hA
  have hm : catalogueMajorValue Q n w = ∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator f t := by
    unfold catalogueMajorValue
    congr 1
    ext t
    by_cases h : t∈catalogueArcs Q n <;> simp [h,f,pow_two,mul_comm]
  rw [hm,← integral_eq_arithmeticBulk Q n scale w]
  change (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator f t)+
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator f t) = _
  rw [← intervalIntegral.integral_add (integ _ (measurable_catalogue Q n).compl)
    (integ _ (measurable_catalogue Q n))]
  have eq (t : ℝ) : (catalogueArcs Q n)ᶜ.indicator f t+(catalogueArcs Q n).indicator f t=f t := by
    by_cases h : t∈catalogueArcs Q n <;> simp [h]
  simp_rw [eq]
  exact full_projection n (by omega) w

def MajorModelFits : Prop := ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
  ‖catalogueMajorValue (catalogueCutoff n) n (high n)-(catalogueMajorModel n:ℂ)‖ ≤ ε*n

theorem bulk_pair_model_error (fit : MajorModelFits) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, |(FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re-
      (pairMass n 0 (high n)-catalogueMajorModel n)|≤ε*n := by
  obtain ⟨S,hS⟩ : ∃ S:ℕ, ∀ n≥S, 2*(catalogueCutoff n)^2<n :=
    PEqualNP.Outside.L_goldbach_arc_cutoff_scale
  filter_upwards [eventually_ge_atTop S,fit ε hε] with n hn err
  have exactValue := congrArg Complex.re (major_plus_minor _ n (hS n hn) (high n))
  simp only [Complex.add_re,Complex.ofReal_re] at exactValue
  rw [catalogue_bulk_arithmetic n (hS n hn)]
  have he := (Complex.abs_re_le_norm (catalogueMajorValue (catalogueCutoff n) n (high n)-(catalogueMajorModel n:ℂ))).trans err
  simp only [Complex.sub_re,Complex.ofReal_re] at he
  rw [show arithmeticBulk (catalogueCutoff n) n (high n) - (pairMass n 0 (high n)-catalogueMajorModel n) =
    -( (catalogueMajorValue (catalogueCutoff n) n (high n)).re-catalogueMajorModel n) by linarith only [exactValue],abs_neg]
  exact he

/-- The frozen signed minor-arc floor is precisely a one-sided estimate on the
diagonal prime pairs against the finite, actual-width major-arc model. -/
theorem bulk_iff_pair_floor (fit : MajorModelFits) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      catalogueMajorModel n ≤ pairMass n 0 (high n)+ε*n := by
  change (∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
    -(ε*n) ≤ (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re) ↔ _
  constructor <;> intro h ε ep <;>
    obtain ⟨A,hA⟩ := h (ε/2) (half_pos ep) <;>
    obtain ⟨M,hM⟩ := eventually_atTop.mp (bulk_pair_model_error fit (ε/2) (half_pos ep)) <;>
    refine ⟨max A M,fun n hn he => ?_⟩ <;>
    obtain ⟨l,u⟩ := abs_le.mp (hM n (by omega)) <;>
    linarith only [l,u,hA n (by omega) he]

theorem diagonal_error (ε : ℝ) (ep : 0<ε) : ∀ᶠ n : ℕ in atTop,
    0≤goldbachCount n-pairMass n 0 (high n) ∧
    goldbachCount n-pairMass n 0 (high n)≤ε*n := by
  have lim : Tendsto (fun z : ℝ => (2*Real.log 4)*(z*Real.exp (-(1/2)*z))) atTop (nhds 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/2) (by norm_num)).const_mul (2*Real.log 4)
  have logs : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,logs.eventually (lim.eventually_lt_const ep)] with n hn hε
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hlog := Real.log_nonneg (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega))
  obtain ⟨lo,up⟩ := diagonal_truncation n (by omega)
  refine ⟨lo,up.trans ?_⟩
  calc
    _ ≤ 2*(Real.log 4*Real.sqrt n*Real.log n) := by gcongr; exact cubeCutoff_le_sqrt n
    _ = ((2*Real.log 4)*(Real.log n*Real.exp (-(1/2)*Real.log n)))*n := by
      have h : Real.exp (-(1/2)*Real.log n)*(n:ℝ)=Real.sqrt n := by
        conv_lhs => rhs; rw [← Real.exp_log np]
        rw [← Real.exp_add,show -(1/2)*Real.log n+Real.log n=Real.log n/2 by ring,
          Real.exp_half,Real.exp_log np]
      rw [← h]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hε.le np.le

/-- The equivalent remaining lower bound uses the ordinary ordered, log-weighted
binary Goldbach count, and the exact widths used in the catalogue's main term. -/
theorem bulk_iff_count_of_fit (fit : MajorModelFits) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      catalogueMajorModel n ≤ goldbachCount n+ε*n := by
  rw [bulk_iff_pair_floor fit]
  constructor <;> intro h ε ep <;>
    obtain ⟨A,hA⟩ := h (ε/2) (half_pos ep) <;>
    obtain ⟨M,hM⟩ := eventually_atTop.mp (diagonal_error (ε/2) (half_pos ep)) <;>
    refine ⟨max A M,fun n hn he => ?_⟩ <;>
    obtain ⟨l,u⟩ := hM n (by omega) <;>
    nlinarith only [l,u,hA n (by omega) he,mul_nonneg ep.le (Nat.cast_nonneg (α:=ℝ) n)]

theorem bulk_iff_classical_count_floor (v : VaughanMajorArcEstimate) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      catalogueMajorModel n ≤ goldbachCount n+ε*n :=
  bulk_iff_count_of_fit (major_model_negligible v)

#print axioms bulk_iff_classical_count_floor
#print axioms major_plus_minor
#print axioms bulk_iff_pair_floor
end GoldbachMinor
