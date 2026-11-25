import ShortfallEnergy

namespace GoldbachMinor
open Finset Filter
open scoped Topology

/-- Sum of the observable over multiples, divided by the sum of the targets. -/
noncomputable def dyadicRatio (d : ℕ) (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ Ico j (2*j), f (d*i)) / (∑ i ∈ Ico j (2*j), (d:ℝ)*i)

private noncomputable def deficitRatio (n : ℕ) : ℝ := countShortfall n / n

private noncomputable def badIndices (d j : ℕ) (ε : ℝ) :=
  (Ico j (2*j)).filter (fun i => ε < deficitRatio (d*i))

/-- Fraction of indices with a deficit strictly larger than ε times their target. -/
noncomputable def shortfallFrequency (d : ℕ) (ε : ℝ) (j : ℕ) : ℝ :=
  ((badIndices d j ε).card:ℝ)/j

private theorem ratio_nonneg (n : ℕ) : 0 ≤ deficitRatio n :=
  div_nonneg (le_max_right ..) (Nat.cast_nonneg _)

private noncomputable def blockMean (d j : ℕ) : ℝ :=
  (∑ i ∈ Ico j (2*j), deficitRatio (d*i))/(j:ℝ)

private theorem window_comparison (d j : ℕ) (hd : 0 < d) (hj : 0 < j) :
    blockMean d j ≤ 2*dyadicRatio d countShortfall j ∧
    dyadicRatio d countShortfall j ≤ 2*blockMean d j := by
  let T := Ico j (2*j)
  let S := ∑ i ∈ T, deficitRatio (d*i)
  let D := ∑ i ∈ T, countShortfall (d*i)
  let W := ∑ i ∈ T, (d:ℝ)*i
  let L : ℝ := d*j
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  have lp : 0 < L := mul_pos (by exact_mod_cast hd) jp
  have card : T.card = j := by simp [T]; omega
  have posS : 0 ≤ S := sum_nonneg fun i _ => ratio_nonneg _
  have bounds (i) (hi : i ∈ T) : L ≤ (d:ℝ)*i ∧ (d:ℝ)*i ≤ 2*L := by
    obtain ⟨lo,up⟩ := mem_Ico.mp hi
    have lower := Nat.mul_le_mul_left d lo
    have upper := Nat.mul_le_mul_left d up.le
    change (d:ℝ)*j ≤ d*i ∧ (d:ℝ)*i ≤ 2*((d:ℝ)*j)
    constructor
    · exact_mod_cast lower
    · calc
        _ ≤ (d:ℝ)*(2*j) := by exact_mod_cast upper
        _ = _ := by ring
  have wlo : L*j ≤ W := by
    simpa [W,card,mul_comm] using sum_le_sum (s:=T) (fun i hi => (bounds i hi).1)
  have whi : W ≤ (2*L)*j := by
    simpa [W,card,mul_comm] using sum_le_sum (s:=T) (fun i hi => (bounds i hi).2)
  have eq (i) (hi : i ∈ T) : countShortfall (d*i) = ((d:ℝ)*i)*deficitRatio (d*i) := by
    have pos : 0 < (d:ℝ)*i := lp.trans_le (bounds i hi).1
    simp only [deficitRatio, Nat.cast_mul]
    rw [mul_comm ((d:ℝ)*i), div_mul_cancel₀ _ pos.ne']
  have dlo : L*S ≤ D := by
    rw [show L*S = ∑ i ∈ T, L*deficitRatio (d*i) from mul_sum ..]
    apply sum_le_sum
    intro i hi
    rw [eq i hi]
    exact mul_le_mul_of_nonneg_right (bounds i hi).1 (ratio_nonneg _)
  have dhi : D ≤ (2*L)*S := by
    rw [show (2*L)*S = ∑ i ∈ T, (2*L)*deficitRatio (d*i) from mul_sum ..]
    apply sum_le_sum
    intro i hi
    rw [eq i hi]
    exact mul_le_mul_of_nonneg_right (bounds i hi).2 (ratio_nonneg _)
  have wp := (mul_pos lp jp).trans_le wlo
  change S/j ≤ 2*(D/W) ∧ D/W ≤ 2*(S/j)
  simp only [← mul_div_assoc, div_le_div_iff₀ jp wp, div_le_div_iff₀ wp jp]
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left whi posS, mul_le_mul_of_nonneg_right dlo jp.le]
  · nlinarith only [mul_le_mul_of_nonneg_right dhi jp.le, mul_le_mul_of_nonneg_left wlo posS]

private theorem finite_markov (d j : ℕ) {ε : ℝ} (ep : 0 < ε) :
    shortfallFrequency d ε j ≤ blockMean d j / ε := by
  let B := badIndices d j ε
  have h := sum_le_sum (s:=B) (fun i hi => (mem_filter.mp hi).2.le)
  have bound : (B.card:ℝ)*ε ≤ ∑ i ∈ Ico j (2*j), deficitRatio (d*i) := by
    apply le_trans (by simpa using h)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => ratio_nonneg _)
  apply (le_div_iff₀ ep).mpr
  change (B.card:ℝ)/j*ε ≤ _ / j
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right bound (Nat.cast_nonneg _)

/-- A vanishing exceptional proportion suffices because the squared normalized
downward error has bounded window mean. Markov gives the converse. -/
theorem shortfall_mean_iff_density (d : ℕ) (hd : 0 < d) :
    Tendsto (dyadicRatio d countShortfall) atTop (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → Tendsto (shortfallFrequency d ε) atTop (𝓝 0) := by
  have nonneg (j : ℕ) : 0 ≤ dyadicRatio d countShortfall j :=
    div_nonneg (sum_nonneg fun _ _ => le_max_right ..) (sum_nonneg fun _ _ => by positivity)
  constructor
  · intro lim ε ep
    have hlim := (lim.const_mul 2).div_const ε
    apply squeeze_zero' (Eventually.of_forall fun _ => by unfold shortfallFrequency; positivity) _
      (by simpa using hlim)
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (finite_markov d j ep).trans (div_le_div_of_nonneg_right (window_comparison d j hd hj).1 ep.le)
  · intro density
    obtain ⟨C,cp,energy⟩ := dyadic_shortfall_energy d hd
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    let t := ε/8
    have tp : 0 < t := by dsimp [t]; positivity
    have prob := (density t tp).eventually_lt_const (by positivity : 0 < t^2/C)
    filter_upwards [energy,prob,eventually_ge_atTop 1] with j en rare hj
    let T := Ico j (2*j)
    let B := badIndices d j t
    let f (i : ℕ) := deficitRatio (d*i)
    have jp : (0:ℝ) < j := by exact_mod_cast hj
    have card : T.card = j := by simp [T]; omega
    have cs := sum_mul_sq_le_sq_mul_sq B (fun _ => (1:ℝ)) f
    have eB : (∑ i ∈ B, (f i)^2) ≤ C*j := (sum_le_sum_of_subset_of_nonneg
      (filter_subset ..) (fun _ _ _ => sq_nonneg _)).trans en
    have big : (∑ i ∈ B, f i) < t*j := by
      have freq : (B.card:ℝ)*C < t^2*j := by
        change (B.card:ℝ)/j < t^2/C at rare
        exact (div_lt_div_iff₀ jp cp).mp rare
      simp only [one_mul,one_pow,sum_const, nsmul_eq_mul,mul_one] at cs
      nlinarith only [cs,mul_le_mul_of_nonneg_left eB (Nat.cast_nonneg (α:=ℝ) B.card),
        mul_lt_mul_of_pos_right freq jp, mul_pos tp jp, sq_nonneg ((∑ i ∈ B, f i)-t*j)]
    have little : (∑ i ∈ T.filter (fun i => ¬t < f i), f i) ≤ (j:ℝ)*t := by
      have h := sum_le_sum (s:=T.filter (fun i => ¬t < f i))
        (fun i hi => le_of_not_gt (mem_filter.mp hi).2)
      refine h.trans ?_
      simp only [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (card_le_card (filter_subset ..)).trans_eq card) tp.le
    have total := sum_filter_add_sum_filter_not T (fun i => t < f i) f
    have avg : blockMean d j < 2*t := by
      apply (div_lt_iff₀ jp).mpr
      change (∑ i ∈ T, f i) < _
      change (∑ i ∈ B, f i) + _ = _ at total
      linarith only [total,big,little]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (nonneg _)]
    exact (window_comparison d j hd hj).2.trans_lt (by dsimp [t] at avg; linarith)

/-- With the signed mean already zero, the absolute-error mean vanishes
exactly when the downward-error mean does. -/
theorem absolute_mean_iff_shortfall (d : ℕ) (hd : 0 < d) :
    Tendsto (dyadicRatio d (fun n => |goldbachCount n-catalogueMajorModel n|)) atTop (𝓝 0) ↔
      Tendsto (dyadicRatio d countShortfall) atTop (𝓝 0) := by
  let err (n : ℕ) := goldbachCount n-catalogueMajorModel n
  have signed : Tendsto (dyadicRatio d err) atTop (𝓝 0) := by
    change Tendsto (fun j : ℕ => (∑ i ∈ Ico j (2*j), (goldbachCount (d*i)-catalogueMajorModel (d*i))) / _) _ _
    simpa only [sum_sub_distrib, fun j => progression_count_window d j hd] using
      dyadic_count_minus_model_mean d hd
  have identity (j) : dyadicRatio d (fun n => |err n|) j =
      dyadicRatio d err j + 2*dyadicRatio d countShortfall j := by
    simp only [dyadicRatio, ← mul_div_assoc, ← add_div, mul_sum, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    dsimp [err,countShortfall]
    rcases le_total (goldbachCount (d*i)) (catalogueMajorModel (d*i)) with lo|hi
    · rw [abs_of_nonpos (sub_nonpos.mpr lo), max_eq_left (sub_nonneg.mpr lo)]; ring
    · rw [abs_of_nonneg (sub_nonneg.mpr hi), max_eq_right (sub_nonpos.mpr hi)]; ring
  constructor
  · intro absolute
    have lim := (absolute.sub signed).div_const 2
    apply (show Tendsto _ _ (𝓝 (0:ℝ)) from (by simpa using lim)).congr'
    exact Eventually.of_forall fun j => by
      change (dyadicRatio d (fun n => |err n|) j - dyadicRatio d err j)/2 = _
      rw [identity]; ring
  · intro deficit
    have lim := signed.add (deficit.const_mul 2)
    apply (show Tendsto _ _ (𝓝 (0:ℝ)) from (by simpa only [mul_zero,add_zero] using lim)).congr'
    exact Eventually.of_forall fun j => (identity j).symm

/-- Taking negative parts is 1-Lipschitz, so the frozen minor-arc shortfall
and the count shortfall have the same vanishing-mean criterion. -/
theorem frozen_shortfall_iff_count_shortfall (d : ℕ) (hd : 0 < d) :
    Tendsto (dyadicRatio d (fun n => max
      (-(FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re) 0)) atTop (𝓝 0) ↔
      Tendsto (dyadicRatio d countShortfall) atTop (𝓝 0) := by
  let I (n : ℕ) := (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re
  let a (n : ℕ) := max (-I n) 0
  have negligible := dyadic_mean_of_sublinear d hd (fun n => a n-countShortfall n) (by
    intro ε ep
    filter_upwards [frozen_count_error_sublinear ε ep] with n bound
    apply (abs_max_sub_max_le_abs (-I n) (catalogueMajorModel n-goldbachCount n) 0).trans
    rw [show -I n - (catalogueMajorModel n-goldbachCount n) = -(I n-(goldbachCount n-catalogueMajorModel n)) by ring,
      abs_neg]
    exact bound)
  have diff : Tendsto (fun j => dyadicRatio d a j - dyadicRatio d countShortfall j) atTop (𝓝 0) := by
    simpa only [dyadicRatio, sum_sub_distrib, sub_div] using negligible
  constructor
  · intro ha
    change Tendsto (dyadicRatio d a) atTop (𝓝 0) at ha
    have t := ha.sub diff
    simpa only [sub_sub_cancel,sub_zero] using t
  · intro hc
    have t := diff.add hc
    simpa only [sub_add_cancel,zero_add] using t

#print axioms shortfall_mean_iff_density
#print axioms absolute_mean_iff_shortfall
#print axioms frozen_shortfall_iff_count_shortfall
end GoldbachMinor
