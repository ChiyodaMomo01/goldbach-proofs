import WideExceptionalCount
import CommonModelMean

namespace GoldbachMinor
open Finset Filter GoldbachWeight

/-- The even targets in [j,2j) that violate the original, target-dependent signed floor. -/
noncomputable def frozenFailures (ε : ℝ) (j : ℕ) : Finset ℕ :=
  ((range (2*j)).filter (fun n => Even n ∧ 2*j ≤ 2*n)).filter (fun (n : ℕ) =>
    (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re < -(ε*n))

/-- Both major-arc models have weighted mean error bounded by a constant
divided by the binary logarithm at the lower endpoint. -/
private theorem model_errors (j : ℕ) (hj : 0 < j)
    (sep : 2*(wideCutoff (2*j))^2 < 2*j) :
    let main := fun (n : ℕ) => 2*twinPrimeConstant*n*binaryShape n n
    let A := fun (n : ℕ) => (commonArcModel (wideCutoff (2*j)) (2*j) n).re
    dyadicRatio 1 (fun n => |catalogueMajorModel n-main n|) j +
      dyadicRatio 1 (fun n => |A n-main n|) j ≤
        32*conductorSqrtMoment / (Nat.log 2 (j+2)) := by
  let L := Nat.log 2 (j+2)
  have lp : 0 < L := Nat.le_log_of_pow_le (by decide) (by omega : 2^1 ≤ j+2)
  have pos : 0 < catalogueCutoff j := Nat.pow_pos lp
  have mono : L ≤ Nat.log 2 (2*j+2) := Nat.log_mono_right (by omega)
  have size : catalogueCutoff j ≤ wideCutoff (2*j) :=
    (Nat.pow_le_pow_left mono 2).trans (Nat.pow_le_pow_right (lp.trans_le mono) (by decide : 2 ≤ 20))
  have root : Real.sqrt (catalogueCutoff j) = L := by
    simp only [catalogueCutoff,Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg _),L]
  have lower := Real.sqrt_le_sqrt (show (catalogueCutoff j:ℝ) ≤ wideCutoff (2*j) by exact_mod_cast size)
  rw [root] at lower
  have c := dyadic_catalogue_model_rate 1 j (by decide) hj (by simpa using pos)
  have w := dyadic_common_model_rate 1 j (wideCutoff (2*j)) (by decide) hj (pos.trans_le size) (by simpa using sep)
  simp only [one_mul, Nat.cast_one, mul_one, root] at c w
  have mass : 0 ≤ conductorSqrtMoment := tsum_nonneg (fun q => by unfold conductorMass; positivity)
  have w' := w.trans (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) mass)
    (by exact_mod_cast lp : (0:ℝ) < L) lower)
  dsimp only
  change _ ≤ 32*conductorSqrtMoment/(L:ℝ)
  exact (add_le_add c w').trans_eq (by ring)

set_option maxHeartbeats 1000000 in
/-- Unconditional quantitative exceptional count with the original sign,
prime cutoff, and minor arcs. The asymptotic threshold may depend on ε. -/
theorem frozen_failure_rate (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ((frozenFailures ε j).card:ℝ) ≤
      256*j*conductorSqrtMoment / (ε*(Nat.log 2 (j+2))) +
      256*j / (ε^2*(Real.log (2*j:ℕ))^2) := by
  have grow : Tendsto (fun j : ℕ => 2*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by decide)) tendsto_id
  filter_upwards [grow.eventually (frozen_failure_count ε he), grow.eventually wide_scale,
    eventually_ge_atTop 1] with j split sep hj
  let T := Ico j (2*j)
  let E := (range (2*j)).filter (fun n => Even n ∧ 2*j ≤ 2*n)
  let A := fun n => (commonArcModel (wideCutoff (2*j)) (2*j) n).re
  let B := E.filter (fun (n : ℕ) => ε*n/4 < catalogueMajorModel n - A n)
  let main := fun (n : ℕ) => 2*twinPrimeConstant*n*binaryShape n n
  let u := fun n => |catalogueMajorModel n-main n|
  let v := fun n => |A n-main n|
  let W := ∑ n ∈ T, (n:ℝ)
  have jp : 0 < (j:ℝ) := by exact_mod_cast hj
  have lp : 0 < (Nat.log 2 (j+2):ℝ) := by exact_mod_cast (Nat.le_log_of_pow_le (by decide : 1<2) (by omega : 2^1 ≤ j+2))
  have mass : 0 ≤ conductorSqrtMoment := tsum_nonneg (fun q => by unfold conductorMass; positivity)
  have sub : B ⊆ T := by
    intro n h
    obtain ⟨rn, _, half⟩ := mem_filter.mp (mem_filter.mp h).1
    exact mem_Ico.mpr ⟨by omega, mem_range.mp rn⟩
  have card : T.card = j := by simp [T]; omega
  have ww : W ≤ j*(2*(j:ℝ)) := by
    have ub := sum_le_sum (s:=T) (g:=fun _ => 2*(j:ℝ)) fun n hn =>
      (show (n:ℝ) ≤ 2*j by exact_mod_cast (mem_Ico.mp hn).2.le)
    simpa only [sum_const, nsmul_eq_mul,card] using ub
  have wp : 0 < W := sum_pos' (fun _ _ => Nat.cast_nonneg _) ⟨j,mem_Ico.mpr ⟨le_rfl, by omega⟩,jp⟩
  have counted : (B.card:ℝ)*(ε*j/4) ≤ ∑ n ∈ T, (u n+v n) := by
    calc
      _ = ∑ _n ∈ B, ε*(j:ℝ)/4 := by simp
      _ ≤ ∑ n ∈ B, (u n+v n) := by
        apply sum_le_sum
        intro n hn
        have lo := mul_le_mul_of_nonneg_left (show (j:ℝ) ≤ n by exact_mod_cast (mem_Ico.mp (sub hn)).1) he.le
        have a := (mem_filter.mp hn).2
        have b := le_abs_self (catalogueMajorModel n-main n)
        have c := neg_le_abs (A n-main n)
        dsimp only [u,v]
        linarith only [lo,a,b,c]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have model := model_errors j hj sep
  simp only [dyadicRatio,one_mul,Nat.cast_one] at model
  change (∑ n ∈ T, u n)/W + (∑ n ∈ T, v n)/W ≤ _ at model
  rw [← add_div, ← sum_add_distrib, div_le_iff₀ wp] at model
  let L : ℝ := Nat.log 2 (j+2)
  have bound : (B.card:ℝ) ≤ 256*j*conductorSqrtMoment / (ε*L) := by
    rw [le_div_iff₀ (mul_pos he lp)]
    apply le_of_mul_le_mul_right (a:=(j:ℝ)) _ jp
    have full := counted.trans (model.trans (mul_le_mul_of_nonneg_left ww
      (div_nonneg (mul_nonneg (by norm_num) mass) lp.le)))
    change (B.card:ℝ)*(ε*j/4) ≤ (32*conductorSqrtMoment/L)*(j*(2*j)) at full
    have scaled := mul_le_mul_of_nonneg_right full lp.le
    calc
      _ = ((B.card:ℝ)*(ε*j/4)*L)*4 := by ring
      _ ≤ (((32*conductorSqrtMoment/L)*(j*(2*j)))*L)*4 :=
        mul_le_mul_of_nonneg_right scaled (by norm_num)
      _ = _ := by field_simp [show L ≠ 0 from ne_of_gt lp]; ring
  change ((frozenFailures ε j).card:ℝ) ≤ (B.card:ℝ) + 128*(2*j:ℕ)/(ε^2*(Real.log (2*j:ℕ))^2) at split
  apply split.trans
  push_cast
  convert! add_le_add bound (le_refl (128*(2*j:ℝ)/(ε^2*(Real.log (2*j:ℝ))^2))) using 1
  dsimp only [L]
  ring

/-- A rate for the fraction in the exact even-index convention of the catalogue. -/
theorem even_frozen_exception_fraction_rate (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      (((Ico j (2*j)).filter (fun i =>
        (FrozenBulk.deskI (2*i) (FrozenBulk.deskHigh (2*i)) (FrozenBulk.deskHigh (2*i))).re <
        -(ε*(2*i:ℕ)))).card:ℝ)/j ≤
      512*conductorSqrtMoment / (ε*(Nat.log 2 (2*j+2))) +
        512 / (ε^2*(Real.log (4*j:ℕ))^2) := by
  have grow : Tendsto (fun j : ℕ => 2*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by decide)) tendsto_id
  filter_upwards [grow.eventually (frozen_failure_rate ε he), eventually_ge_atTop 1]
    with j count hj
  have inject (S : Finset ℕ) (hS : ∀ i ∈ S, 2*i ∈ frozenFailures ε (2*j)) :
      (S.card:ℝ) ≤ (frozenFailures ε (2*j)).card := by
    exact_mod_cast card_le_card_of_injOn (fun i : ℕ => 2*i) hS (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h)
  have le := inject ((Ico j (2*j)).filter (fun i =>
    (FrozenBulk.deskI (2*i) (FrozenBulk.deskHigh (2*i)) (FrozenBulk.deskHigh (2*i))).re <
      -(ε*(2*i:ℕ)))) (by
    intro i hi
    obtain ⟨win,bad⟩ := mem_filter.mp hi
    obtain ⟨lo,up⟩ := mem_Ico.mp win
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), ⟨i, by omega⟩, by omega⟩, bad⟩)
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  apply (div_le_div_of_nonneg_right (le.trans count) jp.le).trans_eq
  rw [show 2*(2*j) = 4*j by omega]
  push_cast
  rw [add_div]
  congr 1 <;> field_simp <;> ring

#print axioms even_frozen_exception_fraction_rate
#print axioms frozen_failure_rate
end GoldbachMinor
