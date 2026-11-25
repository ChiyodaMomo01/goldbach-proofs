import DeskPrimeInput
import Mathlib.NumberTheory.SumPrimeReciprocals

namespace GoldbachMinor
open Finset Filter

/-- Beyond a threshold, every multiple of one fixed factorial has a normalized
major model above the prescribed level. The factorial may depend on the level. -/
theorem major_model_large_on_multiples (B : ℝ) :
    ∃ k N : ℕ, 2 ≤ k ∧ ∀ n ≥ N, k.factorial ∣ n → B ≤ catalogueMajorModel n / n := by
  classical
  let c := archimedeanMass 1 / 2
  have hc : 0 < c := div_pos archimedean_one_pos (by norm_num)
  let f := Set.indicator {p : ℕ | p.Prime} (fun p => 1 / (p:ℝ))
  have hf (p : ℕ) : 0 ≤ f p := Set.indicator_nonneg (fun _ _ => by positivity) _
  have sums : Tendsto (fun m => ∑ p ∈ range m, f p) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp not_summable_one_div_on_primes
  obtain ⟨m, hm⟩ := eventually_atTop.mp (sums.eventually_ge_atTop (B/c))
  let k := max m 2
  let P := (range k).filter Nat.Prime
  have lower : B ≤ c * ∑ p ∈ P, 1 / (p:ℝ) := by
    have h := (div_le_iff₀ hc).mp (hm k (le_max_left ..))
    have partialSum : (∑ p ∈ range k, f p) = ∑ p ∈ P, 1 / (p:ℝ) := by
      rw [show P = (range k).filter Nat.Prime from rfl, sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases pr : p.Prime <;> simp [f, pr]
    rwa [partialSum, mul_comm] at h
  refine ⟨k, 2^k, le_max_right .., ?_⟩
  intro n hn hd
  have np : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (pow_pos (by decide : 0<2) k) hn)
  have bound : k ≤ catalogueCutoff n := by
    have h : k ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
    unfold catalogueCutoff
    simpa [pow_two] using h.trans (Nat.le_mul_self _)
  have even := even_iff_two_dvd.mpr ((Nat.dvd_factorial (by decide) (le_max_right m 2)).trans hd)
  have floor := prime_divisors_major_kernel_floor n (catalogueCutoff n) even P (by
    intro p hp
    obtain ⟨hin, pr⟩ := mem_filter.mp hp
    have pk := (mem_range.mp hin).le
    exact ⟨pr, pk.trans bound, (Nat.dvd_factorial pr.pos pk).trans hd⟩)
  simpa [catalogueMajorModel, mul_div_cancel_left₀, ne_of_gt np] using lower.trans floor

/-- The conclusion holds eventually along the whole factorial sequence. -/
theorem factorial_major_model_growth :
    Tendsto (fun j : ℕ => catalogueMajorModel j.factorial / j.factorial) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨k, N, _, h⟩ := major_model_large_on_multiples B
  filter_upwards [eventually_ge_atTop k, factorial_tendsto_atTop.eventually_ge_atTop N] with j hj hn
  exact h _ hn (Nat.factorial_dvd_factorial hj)

/-- The certified approximation transfers factorial growth to the real part of
the major-arc integral for the catalogue's high-prime spectrum. -/
theorem factorial_high_major_arc_growth :
    Tendsto (fun j : ℕ => let n := j.factorial
      (catalogueMajorValue (catalogueCutoff n) n (GoldbachWeight.high n)).re / n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [factorial_major_model_growth.eventually_ge_atTop (B+1),
    factorial_tendsto_atTop.eventually (certified_major_model_fit 1 zero_lt_one)] with j model err
  let n := j.factorial
  have pos : 0 < (n:ℝ) := by exact_mod_cast Nat.factorial_pos j
  have low := (abs_le.mp ((Complex.abs_re_le_norm _).trans err)).1
  simp only [Complex.sub_re, Complex.ofReal_re, one_mul] at low
  apply (le_div_iff₀ pos).mpr
  have hm := (le_div_iff₀ pos).mp model
  dsimp [n] at *
  linarith only [hm, low]

/-- The frozen signed floor would force the same divergence for actual
ordered log-weighted prime pairs along factorials. -/
theorem factorial_count_growth_of_bulk (bulk : FrozenBulk.BulkFloor) :
    Tendsto (fun j : ℕ => goldbachCount j.factorial / j.factorial) atTop atTop := by
  obtain ⟨N, hN⟩ := certified_bulk_iff_count_floor.mp bulk 1 zero_lt_one
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [factorial_major_model_growth.eventually_ge_atTop (B+1),
    factorial_tendsto_atTop.eventually_ge_atTop N, eventually_ge_atTop 2] with j model hn hj
  have jp : 0 < (j.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos j
  have even := even_iff_two_dvd.mpr (Nat.dvd_factorial (by decide) hj)
  have floor := hN _ hn even
  apply (le_div_iff₀ jp).mpr
  have h := (le_div_iff₀ jp).mp model
  linarith only [h, floor]

#print axioms major_model_large_on_multiples
#print axioms factorial_major_model_growth
#print axioms factorial_high_major_arc_growth
#print axioms factorial_count_growth_of_bulk
end GoldbachMinor
