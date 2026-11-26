import TargetConductorMoment
import ShortfallTransfer

namespace GoldbachMinor
open Finset Filter
open scoped Topology

private noncomputable def lostMass (n q : ℕ) := 1-windowKernel (catalogueCutoff n) q

private theorem lost_range (n q : ℕ) : 0 ≤ lostMass n q ∧ lostMass n q ≤ 1 := by
  obtain ⟨lo,hi⟩ := kernel_bounds (catalogueCutoff n) q
  exact ⟨sub_nonneg.mpr hi, sub_le_self _ lo⟩

private theorem model_as_damped_series (n : ℕ) :
    catalogueMajorModel n = n*∑' q, ramWeight q n * windowKernel (catalogueCutoff n) q := by
  rw [tsum_eq_sum (s:=Icc 1 (catalogueCutoff n)) (fun q h => by
    by_cases pos : 0 < q
    · have out : ¬ q ≤ catalogueCutoff n := fun le => h (mem_Icc.mpr ⟨pos,le⟩)
      simp [windowKernel,out]
    · have eq : q = 0 := by omega
      simp [eq,ramWeight,ram])]
  apply congrArg ((n:ℝ)*·)
  exact sum_congr rfl fun q h => by simp only [windowKernel, (mem_Icc.mp h).2, ite_true, ramWeight]

private noncomputable def rowMajorant (m n q : ℕ) : ℝ :=
  ((n:ℝ)*|ramWeight q n|)*lostMass m q

private theorem row_nonneg (m n q : ℕ) : 0 ≤ rowMajorant m n q :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (lost_range ..).1

private theorem row_summable (m n : ℕ) (hn : 0 < n) : Summable (rowMajorant m n) :=
  ((ramWeight_abs_summable n hn).mul_left (n:ℝ)).of_nonneg_of_le (row_nonneg m n)
    fun _ => mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (lost_range ..).2

private theorem point_error (m n : ℕ) (hn : 0 < n) (hm : m ≤ n) :
    |catalogueMajorModel n-2*twinPrimeConstant*n*binaryShape n n| ≤ ∑' q, rowMajorant m n q := by
  let a := fun q => ramWeight q n
  let k := fun q => windowKernel (catalogueCutoff n) q
  have sa : Summable a := summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using ramWeight_abs_summable n hn)
  have sk : Summable (fun q => a q*k q) := (ramWeight_abs_summable n hn).of_norm_bounded fun q => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_bounds ..).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (kernel_bounds ..).2
  have eq : catalogueMajorModel n-2*twinPrimeConstant*n*binaryShape n n =
      ∑' q, (n:ℝ)*(a q*k q - a q) := by
    rw [tsum_mul_left, sk.tsum_sub sa, model_as_damped_series, mul_sub]
    change _ - _ = _ - (n:ℝ)*∑' q, ramWeight q n
    rw [ramWeight_tsum_eq_classical n hn]; ring
  have term (q) : ‖(n:ℝ)*(a q*k q-a q)‖ ≤ rowMajorant m n q := by
    have mono := catalogue_kernel_mono q hm
    have identity : a q*k q-a q = -(a q*lostMass n q) := by dsimp [k,lostMass]; ring
    rw [Real.norm_eq_abs, identity, abs_mul, abs_neg, abs_mul, abs_of_nonneg (lost_range ..).1,
      abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n), ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left mono 1) (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  have norms := (row_summable m n hn).of_nonneg_of_le (fun _ => norm_nonneg _) term
  rw [eq, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm norms).trans (norms.tsum_le_tsum term (row_summable m n hn))

private noncomputable def columnMajorant (d j q : ℕ) : ℝ :=
  4*d*conductorMass q*lostMass (d*j) q

private theorem column_bound (d j q : ℕ) :
    0 ≤ columnMajorant d j q ∧ columnMajorant d j q ≤ 4*d*conductorMass q := by
  have z : 0 ≤ conductorMass q := by unfold conductorMass; positivity
  have pos : 0 ≤ 4*(d:ℝ)*conductorMass q := by positivity
  exact ⟨mul_nonneg pos (lost_range ..).1, mul_le_of_le_one_right pos (lost_range ..).2⟩

private theorem window_error (d j : ℕ) (hd : 0 < d) (hj : 0 < j) :
    dyadicRatio d (fun n => |catalogueMajorModel n-2*twinPrimeConstant*n*binaryShape n n|) j ≤
      ∑' q, columnMajorant d j q := by
  let T := Ico j (2*j)
  let W := ∑ i ∈ T, (d:ℝ)*i
  have pos (i) (hi : i∈T) : 0 < d*i := Nat.mul_pos hd (hj.trans_le (mem_Ico.mp hi).1)
  have wp : 0 ≤ W := sum_nonneg fun _ _ => by positivity
  let b (i q : ℕ) := rowMajorant (d*j) (d*i) q
  have sb (i) (hi : i ∈ T) : Summable (b i) := row_summable _ _ (pos i hi)
  have sumcol : Summable (fun q => (∑ i ∈ T, b i q)/W) :=
    (summable_sum (s:=T) sb).div_const W
  have sc := (conductorMass_summable.mul_left (4*(d:ℝ))).of_nonneg_of_le
    (fun q => (column_bound d j q).1) (fun q => (column_bound d j q).2)
  calc
    _ ≤ (∑ i ∈ T, ∑' q, b i q)/W := div_le_div_of_nonneg_right
      (sum_le_sum fun i hi => point_error _ _ (pos i hi) (Nat.mul_le_mul_left d (mem_Ico.mp hi).1)) wp
    _ = ∑' q, (∑ i ∈ T, b i q)/W := by rw [tsum_div_const, Summable.tsum_finsetSum sb]
    _ ≤ _ := by
      apply sumcol.tsum_le_tsum _ sc
      intro q
      simp only [b,rowMajorant, ← sum_mul, mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right (dyadic_ramWeight_bound d j q hd hj) (lost_range ..).1

private theorem lost_slope (n : ℕ) (hQ : 0 < catalogueCutoff n) (q : ℕ) (hp : 0 < q) :
    lostMass n q * catalogueCutoff n ≤ 2*(q:ℝ) := by
  let Q := catalogueCutoff n
  have pos : (0:ℝ) < Q := by exact_mod_cast hQ
  change lostMass n q * Q ≤ _
  have rp : (0:ℝ) < q := by exact_mod_cast hp
  by_cases inside : q ≤ Q
  · have bound := archimedean_mass_loss_le (div_pos pos rp)
    have ratio : (2:ℝ)/((Q:ℝ)/q) = (2*q)/Q := by field_simp
    rw [ratio] at bound
    simpa only [lostMass,windowKernel,show catalogueCutoff n = Q from rfl,inside,ite_true]
      using (le_div_iff₀ pos).mp bound
  · have order : (Q:ℝ) ≤ q := by exact_mod_cast (Nat.le_of_not_ge inside)
    simp only [lostMass,windowKernel,show catalogueCutoff n = Q from rfl,inside,ite_false,sub_zero,one_mul]
    linarith

theorem catalogue_pointwise_rate (n : ℕ) (hn : 0<n) (hQ : 0<catalogueCutoff n) :
    |catalogueMajorModel n-2*twinPrimeConstant*n*binaryShape n n| ≤
      n*(2*targetFactor n*conductorSqrtMoment / Real.sqrt (catalogueCutoff n)) := by
  have loss := target_cutoff_rate n _ hn hQ 2 (by norm_num) (lostMass n)
    (fun q => (lost_range ..).1) (fun q _ => (lost_range n q).2.trans (by norm_num)) (lost_slope n hQ)
  apply (point_error n n hn le_rfl).trans
  simpa only [rowMajorant,mul_assoc,tsum_mul_left] using
    (mul_le_mul_of_nonneg_left loss (Nat.cast_nonneg (α:=ℝ) n))

/-- A square-root saving in the moving catalogue denominator cutoff. -/
theorem dyadic_catalogue_model_rate (d j : ℕ) (hd : 0 < d) (hj : 0 < j)
    (hQ : 0 < catalogueCutoff (d*j)) :
    dyadicRatio d (fun n => |catalogueMajorModel n-2*twinPrimeConstant*n*binaryShape n n|) j ≤
      8*d*conductorSqrtMoment / Real.sqrt (catalogueCutoff (d*j)) := by
  let Q := catalogueCutoff (d*j)
  have loss := conductor_cutoff_rate Q hQ 2 (by norm_num) (lostMass (d*j))
    (fun q => (lost_range ..).1) (fun q _ => (lost_range (d*j) q).2.trans (by norm_num)) (lost_slope (d*j) hQ)
  apply (window_error d j hd hj).trans
  simp only [columnMajorant,mul_assoc,tsum_mul_left]
  dsimp only [Q] at loss
  convert! (mul_le_mul_of_nonneg_left loss (by positivity : 0 ≤ 4*(d:ℝ))) using 1 <;> ring

#print axioms dyadic_catalogue_model_rate

/-- The finite major-arc model agrees in weighted mean absolute error with
the complete singular-series main term on every fixed progression of multiples. -/
theorem dyadic_model_absolute_classical (d : ℕ) (hd : 0 < d) :
    Tendsto (dyadicRatio d (fun n => |catalogueMajorModel n-2*twinPrimeConstant*n*binaryShape n n|))
      atTop (𝓝 0) := by
  have grows : Tendsto (fun j : ℕ => d*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j hd) tendsto_id
  have single (q : ℕ) : Tendsto (fun j => columnMajorant d j q) atTop (𝓝 0) := by
    by_cases h : 0 < q
    · have lim := ((tendsto_const_nhds (x:=(1:ℝ))).sub ((catalogue_kernel_tends q h).comp grows)).const_mul
        (4*d*conductorMass q)
      simpa only [sub_self, mul_zero, Function.comp_apply, columnMajorant, lostMass] using lim
    · have eq : q = 0 := by omega
      simp [eq,columnMajorant,conductorMass]
  have lim := tendsto_tsum_of_dominated_convergence (conductorMass_summable.mul_left (4*(d:ℝ))) single
    (Eventually.of_forall (fun j q => (by rw [Real.norm_eq_abs,abs_of_nonneg (column_bound d j q).1];
                                          exact (column_bound d j q).2)))
  apply squeeze_zero' (Eventually.of_forall fun j =>
    div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (sum_nonneg fun _ _ => by positivity))
    ((eventually_ge_atTop 1).mono fun j hj => window_error d j hd hj)
  simpa only [tsum_zero] using lim

/-- Exact remaining prime-count criterion. For this equivalence the count
requires no assumed mean-square estimate or logarithmic rate. -/
theorem density_iff_classical_absolute_mean (d : ℕ) (hd : 0 < d) :
    (∀ ε : ℝ, 0 < ε → Tendsto (shortfallFrequency d ε) atTop (𝓝 0)) ↔
    Tendsto (dyadicRatio d (fun n => |goldbachCount n-2*twinPrimeConstant*n*binaryShape n n|))
      atTop (𝓝 0) := by
  let main (n : ℕ) := 2*twinPrimeConstant*n*binaryShape n n
  have model := dyadic_model_absolute_classical d hd
  rw [← shortfall_mean_iff_density d hd, ← absolute_mean_iff_shortfall d hd]
  constructor
  · intro count
    exact dyadic_absolute_triangle_transfer d goldbachCount catalogueMajorModel main count model
  · intro count
    exact dyadic_absolute_triangle_transfer d goldbachCount main catalogueMajorModel count
      (by simpa only [abs_sub_comm] using model)

/-- The only external count input is the explicitly stated classical mean-square estimate. -/
theorem dyadic_exceptional_density_of_classical (hc : ClassicalMeanSquare (2*twinPrimeConstant))
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (he : 0 < ε) :
    Tendsto (shortfallFrequency d ε) atTop (𝓝 0) :=
  (density_iff_model_matches_classical _ hc d hd).mpr (dyadic_model_absolute_classical d hd) ε he

/-- Exceptional fraction for the original real part of the catalogue's
high-prime minor-arc integral, using the same strict lower-floor failure. -/
theorem dyadic_frozen_exceptional_density_of_count
    (d : ℕ) (hd : 0 < d) (density : ∀ ε : ℝ, 0 < ε → Tendsto (shortfallFrequency d ε) atTop (𝓝 0))
    (ε : ℝ) (he : 0 < ε) :
    Tendsto (fun j : ℕ => (((Ico j (2*j)).filter (fun i =>
      (FrozenBulk.deskI (d*i) (FrozenBulk.deskHigh (d*i)) (FrozenBulk.deskHigh (d*i))).re <
        -(ε*(d*i:ℕ)))).card:ℝ)/j) atTop (𝓝 0) := by
  have half := half_pos he
  obtain ⟨N,hN⟩ := eventually_atTop.mp (frozen_count_error_sublinear (ε/2) half)
  apply squeeze_zero' (Eventually.of_forall fun j => by positivity) _
    (density (ε/2) half)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with j hj jp
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg j)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro i hi
  obtain ⟨mem,bad⟩ := mem_filter.mp hi
  refine mem_filter.mpr ⟨mem,?_⟩
  have lo := (mem_Ico.mp mem).1
  have lower := lo.trans (Nat.le_mul_of_pos_left i hd)
  have bound := (abs_le.mp (hN (d*i) (hj.trans lower))).1
  have pos : (0:ℝ) < (d*i:ℕ) := by exact_mod_cast jp.trans lower
  change ε/2 < countShortfall (d*i)/(d*i:ℕ)
  rw [lt_div_iff₀ pos]
  apply lt_of_lt_of_le _ (le_max_left _ 0)
  linarith only [bound,bad]

theorem dyadic_frozen_exceptional_density_of_classical
    (hc : ClassicalMeanSquare (2*twinPrimeConstant)) (d : ℕ) (hd : 0 < d) (ε : ℝ) (he : 0 < ε) :
    Tendsto (fun j : ℕ => (((Ico j (2*j)).filter (fun i =>
      (FrozenBulk.deskI (d*i) (FrozenBulk.deskHigh (d*i)) (FrozenBulk.deskHigh (d*i))).re <
        -(ε*(d*i:ℕ)))).card:ℝ)/j) atTop (𝓝 0) :=
  dyadic_frozen_exceptional_density_of_count d hd (dyadic_exceptional_density_of_classical hc d hd) ε he

#print axioms dyadic_model_absolute_classical
#print axioms density_iff_classical_absolute_mean
#print axioms dyadic_exceptional_density_of_classical
#print axioms dyadic_frozen_exceptional_density_of_classical
end GoldbachMinor
