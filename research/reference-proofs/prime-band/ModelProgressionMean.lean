import ArcMassNormalization
import ProgressionConductors
import ProgressionMean

namespace GoldbachMinor
open Finset Filter ArithmeticFunction
open scoped Topology

private noncomputable def coeff (q : ℕ) := ((moebius q:ℝ)/q.totient)^2

private theorem cutoff_mono : Monotone catalogueCutoff := fun _ _ h =>
  Nat.pow_le_pow_left (Nat.log_mono_right (Nat.add_le_add_right h 2)) 2

private theorem cutoff_tends : Tendsto catalogueCutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (2^k)] with n hn
  have h : k ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  simpa [catalogueCutoff, pow_two] using h.trans (Nat.le_mul_self _)

theorem kernel_bounds (Q q : ℕ) : 0 ≤ windowKernel Q q ∧ windowKernel Q q ≤ 1 := by
  unfold windowKernel
  split_ifs
  · exact ⟨archimedean_nonneg _ (by positivity), archimedean_mass_le_one _ (by positivity)⟩
  · exact ⟨le_rfl, zero_le_one⟩

private theorem kernel_mono (q : ℕ) : Monotone (fun Q => windowKernel Q q) := by
  intro a b h
  change windowKernel a q ≤ windowKernel b q
  by_cases ha : q ≤ a
  · simp only [windowKernel, ha, ha.trans h, ite_true]
    exact archimedean_mono _ _ (by positivity) (div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity))
  · rw [show windowKernel a q = 0 by simp [windowKernel,ha]]
    exact (kernel_bounds b q).1

theorem catalogue_kernel_mono (q : ℕ) : Monotone (fun n => windowKernel (catalogueCutoff n) q) :=
  (kernel_mono q).comp cutoff_mono

theorem catalogue_kernel_tends (q : ℕ) (qp : 0 < q) :
    Tendsto (fun n => windowKernel (catalogueCutoff n) q) atTop (𝓝 1) := by
  have h : Tendsto (fun n => ((catalogueCutoff n:ℕ):ℝ)/q) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp cutoff_tends).atTop_div_const (by exact_mod_cast qp)
  apply (archimedean_mass_tends_to_one.comp h).congr'
  filter_upwards [cutoff_tends.eventually_ge_atTop q] with n hn
  simp [windowKernel, hn]

/-- The finite-window contribution of conductors dividing the progression modulus. -/
noncomputable def resonantRatio (d n : ℕ) : ℝ :=
  ∑ q ∈ d.divisors, (ram q 0 * coeff q) * windowKernel (catalogueCutoff n) q

private theorem resonant_tends (d : ℕ) (hd : 0 < d) :
    Tendsto (resonantRatio d) atTop (𝓝 ((d:ℝ)/d.totient)) := by
  rw [← progression_resonance d hd]
  apply tendsto_finsetSum
  intro q hq
  have qp := Nat.pos_of_mem_divisors hq
  have k := catalogue_kernel_tends q qp
  simpa [coeff] using k.const_mul (ram q 0 * coeff q)

private theorem split_target (d n Q : ℕ) (hd : 0 < d) (h : d ∣ n)
    (hdQ : d ≤ Q) (hnQ : catalogueCutoff n ≤ Q) :
    catalogueMajorModel n - n*resonantRatio d n =
      ∑ q ∈ (Icc 1 Q).filter (fun q => ¬q ∣ d),
        ((n:ℝ)*windowKernel (catalogueCutoff n) q) * ram q n * coeff q := by
  let f (q : ℕ) := (n:ℝ)*windowKernel (catalogueCutoff n) q*ram q n*coeff q
  have extended : catalogueMajorModel n = ∑ q ∈ Icc 1 Q, f q := by
    unfold catalogueMajorModel
    rw [mul_sum]
    calc
      _ = ∑ q ∈ Icc 1 (catalogueCutoff n), f q := by
        apply sum_congr rfl
        intro q hq
        simp only [f, windowKernel, (mem_Icc.mp hq).2, ite_true, coeff]
        ring
      _ = _ := sum_subset_zero_on_sdiff (Icc_subset_Icc_right hnQ)
        (fun q hq => by
          have h' := mem_sdiff.mp hq
          have out : ¬q ≤ catalogueCutoff n := fun e => h'.2 (mem_Icc.mpr ⟨(mem_Icc.mp h'.1).1,e⟩)
          simp [f,windowKernel,out]) (fun _ _ => rfl)
  have units : (Icc 1 Q).filter (· ∣ d) = d.divisors := by
    ext q
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    exact ⟨fun h => ⟨h.2,hd.ne'⟩, fun ⟨dvd,_⟩ => ⟨⟨Nat.pos_of_dvd_of_pos dvd hd, (Nat.le_of_dvd hd dvd).trans hdQ⟩,dvd⟩⟩
  have main : (∑ q ∈ (Icc 1 Q).filter (· ∣ d), f q) = n*resonantRatio d n := by
    rw [units, resonantRatio, mul_sum]
    apply sum_congr rfl
    intro q hq
    have dvd := (Nat.dvd_of_mem_divisors hq).trans h
    have zero : ram q n = ram q 0 := by
      unfold ram
      apply sum_congr rfl
      intro a ha
      simp [(Nat.dvd_of_mem_divisors ha).trans dvd]
    dsimp only [f]; rw [zero]; ring
  rw [extended, ← sum_filter_add_sum_filter_not (Icc 1 Q) (· ∣ d) f, main]
  dsimp [f]
  ring

/-- Total model error after keeping just the conductors dividing the modulus.
The cutoff and the integration radius vary with the target inside the sum. -/
theorem nonresonant_model_window (d j : ℕ) (hd : 0 < d)
    (hQ : d ≤ catalogueCutoff (2*d*j)) :
    |∑ i ∈ range j, (catalogueMajorModel (d*(j+i)) -
      (d*(j+i):ℕ)*resonantRatio d (d*(j+i)))| ≤
        2*(2*d*j:ℕ)*(catalogueCutoff (2*d*j):ℝ)^3 := by
  let n (i : ℕ) := d*(j+i)
  let X := 2*d*j
  let Q := catalogueCutoff X
  let A := (Icc 1 Q).filter (fun q => ¬q ∣ d)
  have mono : Monotone n := fun _ _ h => Nat.mul_le_mul_left _ (Nat.add_le_add_left h _)
  have top : n j = X := by dsimp [n,X]; ring
  let w (q i : ℕ) := (n i:ℝ)*windowKernel (catalogueCutoff (n i)) q
  have pos (q i) : 0 ≤ w q i := mul_nonneg (Nat.cast_nonneg _) (kernel_bounds ..).1
  have inc (q) : Monotone (w q) := by
    intro a b h
    exact mul_le_mul (by exact_mod_cast mono h) (kernel_mono q (cutoff_mono (mono h)))
      (kernel_bounds ..).1 (Nat.cast_nonneg _)
  have endWeight q : w q j ≤ X := by
    dsimp [w]; rw [top]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (kernel_bounds ..).2
  have row (q) (hq : q ∈ A) :
      |∑ i ∈ range j, w q i * ram q (n i) * coeff q| ≤ 2*X*(Q:ℝ)^2 := by
    obtain ⟨mem, nd⟩ := mem_filter.mp hq
    obtain ⟨qp, qb⟩ := mem_Icc.mp mem
    have bound (k) : |∑ i ∈ range k, ram q (n i)| ≤ (q:ℝ)^2 := by
      simpa only [n, Nat.mul_comm d _, Nat.add_mul] using
        nonresonant_prefix q d (j*d) k qp nd
    have cancel := increasing_weight_prefix_bound (fun i => ram q (n i)) (w q) j _ (sq_nonneg _) bound (pos q) (inc q)
    have c := moebius_coefficient_bound q qp
    rw [Complex.norm_real, Real.norm_eq_abs] at c
    have c1 : coeff q ≤ 1 := by
      dsimp [coeff]
      nlinarith only [sq_abs ((moebius q:ℝ)/q.totient), mul_self_le_mul_self (abs_nonneg _) c]
    rw [← sum_mul, abs_mul, abs_of_nonneg (show 0 ≤ coeff q from sq_nonneg _)]
    apply (mul_le_of_le_one_right (abs_nonneg _) c1).trans (cancel.trans ?_)
    gcongr
    exact endWeight q
  have expand : (∑ i ∈ range j, (catalogueMajorModel (n i) - n i*resonantRatio d (n i))) =
      ∑ q ∈ A, ∑ i ∈ range j, w q i * ram q (n i) * coeff q := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    exact split_target d (n i) Q hd (dvd_mul_right ..) hQ
      (cutoff_mono ((mono (mem_range.mp hi).le).trans_eq top))
  change |∑ i ∈ range j, (catalogueMajorModel (n i) - n i*resonantRatio d (n i))| ≤ _
  rw [expand]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum row).trans
  have card : A.card ≤ Q := (card_le_card (filter_subset ..)).trans_eq (by simp)
  simp only [sum_const, nsmul_eq_mul]
  change A.card * (2*(X:ℝ)*Q^2) ≤ 2*(X:ℝ)*Q^3
  calc
    _ ≤ (Q:ℝ)*(2*(X:ℝ)*Q^2) := by gcongr
    _ = _ := by ring

/-- The moving-cutoff model has the same modulus-to-totient mean as the actual
ordered prime-pair count on every fixed progression of multiples. -/
theorem dyadic_model_mean (d : ℕ) (hd : 0 < d) :
    Tendsto (fun j : ℕ => (∑ i ∈ Ico j (2*j), catalogueMajorModel (d*i)) /
      (∑ i ∈ Ico j (2*j), (d:ℝ)*i)) atTop (𝓝 ((d:ℝ)/d.totient)) := by
  let L := (d:ℝ)/d.totient
  have dp : 0 < (d:ℝ) := by exact_mod_cast hd
  have grows : Tendsto (fun j : ℕ => 2*d*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by omega : 0 < 2*d)) tendsto_id
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  have small := cutoff_power_budget (ε/(32*d)) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp (resonant_tends d hd)
    (ε/4) (by positivity))
  filter_upwards [grows.eventually small, (cutoff_tends.comp grows).eventually_ge_atTop d,
    eventually_ge_atTop N, eventually_ge_atTop 1] with j budget big hj hj1
  let n (i : ℕ) := d*(j+i)
  let W := ∑ i ∈ range j, (n i:ℝ)
  let Q := catalogueCutoff (2*d*j)
  have jp : (0:ℝ) < j := by exact_mod_cast hj1
  have weight : (d:ℝ)*j*j ≤ W := by
    have each (i : ℕ) : (d:ℝ)*j ≤ n i := by
      exact_mod_cast Nat.mul_le_mul_left d (Nat.le_add_right j i)
    simpa [W, mul_comm, mul_left_comm] using sum_le_sum (s:=range j) (fun i _ => each i)
  have wp : 0 < W := lt_of_lt_of_le (by positivity : 0 < (d:ℝ)*j*j) weight
  have cap : (Q:ℝ)^3 ≤ ε/16*j := by
    have e : 1 ≤ Q := (show 1 ≤ d by omega).trans big
    have pw := pow_le_pow_right₀ (show (1:ℝ) ≤ Q by exact_mod_cast e) (by decide : 3 ≤ 5)
    change (Q:ℝ)^5 ≤ ε/(32*d)*((2*d*j:ℕ):ℝ) at budget
    apply pw.trans (budget.trans_eq ?_)
    push_cast
    field_simp
    ring
  have off : |∑ i ∈ range j, (catalogueMajorModel (n i) - (n i:ℝ)*resonantRatio d (n i))| ≤ ε/4*W := by
    apply (nonresonant_model_window d j hd big).trans
    change 2*((2*d*j:ℕ):ℝ)*Q^3 ≤ ε/4*W
    push_cast
    have h := mul_le_mul_of_nonneg_left cap (by positivity : (0:ℝ) ≤ 2*(2*d*j))
    nlinarith only [h, mul_le_mul_of_nonneg_left weight (by positivity : (0:ℝ) ≤ ε/4)]
  have onRes : |∑ i ∈ range j, (n i:ℝ)*(resonantRatio d (n i)-L)| ≤ ε/4*W := by
    apply (abs_sum_le_sum_abs ..).trans
    rw [show ε/4*W = ∑ i ∈ range j, ε/4*(n i:ℝ) from mul_sum ..]
    apply sum_le_sum
    intro i _
    have idx : N ≤ n i := hj.trans ((Nat.le_add_right j i).trans (Nat.le_mul_of_pos_left _ hd))
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_comm (ε/4)]
    exact mul_le_mul_of_nonneg_left (hN _ idx).le (Nat.cast_nonneg _)
  have whole : (∑ i ∈ range j, catalogueMajorModel (n i)) - L*W =
      (∑ i ∈ range j, (catalogueMajorModel (n i) - (n i:ℝ)*resonantRatio d (n i))) +
      ∑ i ∈ range j, (n i:ℝ)*(resonantRatio d (n i)-L) := by
    simp only [W, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [Real.dist_eq, sum_Ico_eq_sum_range, sum_Ico_eq_sum_range,
    show 2*j-j=j by omega]
  simp_rw [← Nat.cast_mul]
  change |(∑ i ∈ range j, catalogueMajorModel (n i))/W - L| < ε
  rw [div_sub' wp.ne', abs_div, abs_of_pos wp, div_lt_iff₀ wp, mul_comm W L, whole]
  apply (abs_add_le ..).trans_lt
  nlinarith only [off, onRes, mul_pos ep wp]

/-- The signed difference of true counts and model has vanishing weighted
mean on these intervals. This estimate allows cancellation between targets. -/
theorem dyadic_count_minus_model_mean (d : ℕ) (hd : 0 < d) :
    Tendsto (fun j : ℕ =>
      ((progressionTotal (2*d*j) d - progressionTotal (d*j) d) -
        ∑ i ∈ Ico j (2*j), catalogueMajorModel (d*i)) /
        (∑ i ∈ Ico j (2*j), (d:ℝ)*i)) atTop (𝓝 0) := by
  simpa only [← sub_div, sub_self] using (dyadic_progression_mean d hd).sub (dyadic_model_mean d hd)

private theorem progression_prefix_multiples (d k : ℕ) (hd : 0 < d) :
    progressionTotal (d*k) d = ∑ i ∈ range k, goldbachCount (d*i) := by
  have eq : (range (d*k)).filter (d ∣ ·) = (range k).image (d*·) := by
    ext n
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨lt, i, rfl⟩
      exact ⟨i, (Nat.mul_lt_mul_left hd).mp lt, rfl⟩
    · rintro ⟨i, lt, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left lt hd, dvd_mul_right ..⟩
  rw [progressionTotal, eq, sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hd h)]

/-- The two pointwise discrepancies differ by a sublinear error at all large targets. -/
theorem frozen_count_error_sublinear (ε : ℝ) (ep : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |(FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re -
      (goldbachCount n-catalogueMajorModel n)| ≤ ε*n := by
  filter_upwards [bulk_pair_model_error certified_major_model_fit (ε/2) (half_pos ep),
    diagonal_error (ε/2) (half_pos ep)] with n arc diag
  obtain ⟨lo, hi⟩ := abs_le.mp arc
  exact abs_le.mpr ⟨by linarith only [lo,diag.2], by
    linarith only [hi, diag.1, mul_nonneg ep.le (Nat.cast_nonneg (α:=ℝ) n)]⟩

/-- A pointwise sublinear error stays negligible after summing over a dyadic progression. -/
theorem dyadic_mean_of_sublinear (d : ℕ) (hd : 0 < d) (e : ℕ → ℝ)
    (small : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |e n| ≤ ε*n) :
    Tendsto (fun j : ℕ => (∑ i ∈ Ico j (2*j), e (d*i)) /
      (∑ i ∈ Ico j (2*j), (d:ℝ)*i)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨N,hN⟩ := eventually_atTop.mp (small (ε/2) (half_pos ep))
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with j hj hj1
  let W := ∑ i ∈ Ico j (2*j), (d:ℝ)*i
  have wp : 0 < W := sum_pos' (fun i _ => by positivity) ⟨j, mem_Ico.mpr ⟨le_rfl,by omega⟩,
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast hj1)⟩
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos wp, div_lt_iff₀ wp]
  apply (abs_sum_le_sum_abs ..).trans_lt
  calc
    _ ≤ ∑ i ∈ Ico j (2*j), (ε/2)*((d:ℝ)*i) := by
      apply sum_le_sum
      intro i hi
      simpa only [Nat.cast_mul] using hN (d*i) (hj.trans ((mem_Ico.mp hi).1.trans (Nat.le_mul_of_pos_left _ hd)))
    _ = ε/2*W := (mul_sum ..).symm
    _ < _ := mul_lt_mul_of_pos_right (by linarith) wp

theorem progression_count_window (d j : ℕ) (hd : 0 < d) :
    progressionTotal (2*d*j) d - progressionTotal (d*j) d =
      ∑ i ∈ Ico j (2*j), goldbachCount (d*i) := by
  rw [show 2*d*j = d*(2*j) by ring, progression_prefix_multiples d _ hd,
    progression_prefix_multiples d _ hd, sum_Ico_eq_sub _ (by omega)]

/-- The actual frozen high-prime minor-arc integral has zero signed weighted
mean on the multiples of any fixed positive modulus. -/
theorem dyadic_minor_arc_mean (d : ℕ) (hd : 0 < d) :
    Tendsto (fun j : ℕ => (∑ i ∈ Ico j (2*j),
      (FrozenBulk.deskI (d*i) (FrozenBulk.deskHigh (d*i)) (FrozenBulk.deskHigh (d*i))).re) /
      (∑ i ∈ Ico j (2*j), (d:ℝ)*i)) atTop (𝓝 0) := by
  let F (n : ℕ) := (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re
  let e (n : ℕ) := F n - (goldbachCount n - catalogueMajorModel n)
  have remainder := dyadic_mean_of_sublinear d hd e frozen_count_error_sublinear
  have lim := (dyadic_count_minus_model_mean d hd).add remainder
  simp only [fun j => progression_count_window d j hd, zero_add, ← add_div, ← sum_sub_distrib, ← sum_add_distrib] at lim
  simpa only [e, add_sub_cancel] using lim

#print axioms nonresonant_model_window
#print axioms dyadic_model_mean
#print axioms dyadic_count_minus_model_mean
#print axioms dyadic_minor_arc_mean
end GoldbachMinor
