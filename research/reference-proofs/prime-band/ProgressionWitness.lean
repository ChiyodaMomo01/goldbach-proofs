import ModelProgressionMean
import MajorModelGrowth

namespace GoldbachMinor
open Finset Filter
open scoped Topology

/-- In every sufficiently large dyadic interval of multiples of a fixed
modulus, one and the same target meets the minor-arc and count floors. -/
theorem exists_floor_target_on_multiples (d : ℕ) (hd : 0 < d) (ε : ℝ) (ep : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∃ i ∈ Ico j (2*j),
      -(ε*(d*i:ℕ)) ≤ (FrozenBulk.deskI (d*i) (FrozenBulk.deskHigh (d*i)) (FrozenBulk.deskHigh (d*i))).re ∧
      catalogueMajorModel (d*i) ≤ goldbachCount (d*i) + ε*(d*i:ℕ) := by
  let F (n : ℕ) := (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re
  have small := Metric.tendsto_nhds.mp (dyadic_minor_arc_mean d hd) (ε/2) (half_pos ep)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((bulk_pair_model_error certified_major_model_fit (ε/2) (half_pos ep)).and (diagonal_error ε ep))
  filter_upwards [small, eventually_ge_atTop N, eventually_ge_atTop 1] with j mean hj hj1
  let T := Ico j (2*j)
  let W := ∑ i ∈ T, (d:ℝ)*i
  have wp : 0 < W := sum_pos' (fun i _ => by positivity) ⟨j, mem_Ico.mpr ⟨le_rfl,by omega⟩,
    mul_pos (by exact_mod_cast hd) (by exact_mod_cast hj1)⟩
  have witness : ∃ i ∈ T, -(ε/2*((d*i:ℕ):ℝ)) ≤ F (d*i) := by
    by_contra! allBad
    have neg := sum_le_sum (s:=T) (fun i hi => (allBad i hi).le)
    have fail : (∑ i ∈ T, F (d*i)) ≤ -(ε/2)*W := by
      simpa only [W, Nat.cast_mul, neg_mul, mul_sum, sum_neg_distrib] using neg
    rw [Real.dist_eq, sub_zero, abs_lt] at mean
    exact (not_lt_of_ge fail) ((lt_div_iff₀ wp).mp mean.1)
  obtain ⟨i,hi,good⟩ := witness
  have large := hj.trans ((mem_Ico.mp hi).1.trans (Nat.le_mul_of_pos_left i hd))
  obtain ⟨approx,nonneg,_⟩ := hN (d*i) large
  have hpos := mul_nonneg ep.le (Nat.cast_nonneg (α:=ℝ) (d*i))
  change -(ε/2*((d*i:ℕ):ℝ)) ≤ _ at good
  dsimp [F] at good
  exact ⟨i,hi,by linarith only [good,hpos], by linarith only [good,(abs_le.mp approx).2,nonneg]⟩

/-- For every fixed level B one factorial modulus gives, in every sufficiently
large dyadic window, an even target with actual count at least B times the
target and with the requested signed minor-arc floor. -/
theorem abundant_count_witness (B : ℝ) :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      ∃ i ∈ Ico j (2*j), let n := k.factorial*i
        Even n ∧ B*n ≤ goldbachCount n ∧
          -(ε*n) ≤ (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re := by
  obtain ⟨k,N,hk,model⟩ := major_model_large_on_multiples (B+1)
  refine ⟨k,hk,fun ε ep => ?_⟩
  let d := k.factorial
  have dp : 0 < d := Nat.factorial_pos k
  filter_upwards [exists_floor_target_on_multiples d dp (min ε 1) (lt_min ep zero_lt_one),
    eventually_ge_atTop N, eventually_ge_atTop 1] with j witness hj hj1
  obtain ⟨i, hi, arc, count⟩ := witness
  let n := d*i
  have di : d ∣ n := dvd_mul_right ..
  have ji := (mem_Ico.mp hi).1
  have large : j ≤ n := ji.trans (Nat.le_mul_of_pos_left _ dp)
  have np : (0:ℝ) < n := by exact_mod_cast hj1.trans large
  have hm := (le_div_iff₀ np).mp (model n (hj.trans large) di)
  have he := even_iff_two_dvd.mpr ((Nat.dvd_factorial (by decide) hk).trans di)
  refine ⟨i,hi,he,?_,?_⟩
  · change catalogueMajorModel n ≤ goldbachCount n + min ε 1 * n at count
    nlinarith only [hm,count,mul_le_mul_of_nonneg_right (min_le_right ε 1) np.le]
  · exact (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left ε 1) np.le)).trans arc

#print axioms exists_floor_target_on_multiples
#print axioms abundant_count_witness
end GoldbachMinor
