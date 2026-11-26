import CommonModelMean
import WideExceptionalCount

namespace GoldbachMinor
open Finset Filter

/-- An individual failure needs a large common minor coefficient or a large
product over the distinct prime divisors of that very target. -/
theorem frozen_failure_needs_divisors (ε : ℝ) (he : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ n ≤ X, X ≤ 2*n →
      (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re < -(ε*n) →
      ε*(X:ℝ)/8 ≤ ‖commonMinor X n‖ ∨
        ε*(Nat.log 2 (n+2):ℝ) < 32*targetFactor n*conductorSqrtMoment := by
  filter_upwards [frozen_failure_alternatives ε he,wide_scale] with X split sep
  intro n hn half bad
  rcases split n hn half bad with minor | discrepancy
  · exact Or.inl minor
  right
  have np : 0<n := by omega
  let L := Nat.log 2 (n+2)
  have lp : 0<L := Nat.le_log_of_pow_le (by decide) (by omega : 2^1 ≤ n+2)
  have cap : 0<catalogueCutoff n := Nat.pow_pos lp
  have mono : L ≤ Nat.log 2 (X+2) := Nat.log_mono_right (by omega)
  have size : catalogueCutoff n ≤ wideCutoff X :=
    (Nat.pow_le_pow_left mono 2).trans (Nat.pow_le_pow_right (lp.trans_le mono) (by decide : 2 ≤ 20))
  have root : Real.sqrt (catalogueCutoff n) = L := by
    simp only [catalogueCutoff,Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg _),L]
  have lower := Real.sqrt_le_sqrt (show (catalogueCutoff n:ℝ) ≤ wideCutoff X by exact_mod_cast size)
  rw [root] at lower
  have c := catalogue_pointwise_rate n np cap
  rw [root] at c
  have w := common_model_pointwise_rate _ _ _ (cap.trans_le size) sep hn half
  have mpos : 0 ≤ targetFactor n * conductorSqrtMoment :=
    (tsum_nonneg (fun q => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).trans (target_moment_bound n np)
  have wp := w.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left
    (by nlinarith only [mpos]) (by exact_mod_cast lp : (0:ℝ)<L) lower) (Nat.cast_nonneg n))
  have abs1 := (abs_le.mp c).2
  have abs2 := (abs_le.mp wp).1
  have u : ε*n/4 < n*(2*targetFactor n*conductorSqrtMoment/(L:ℝ)) +
      n*(6*targetFactor n*conductorSqrtMoment/(L:ℝ)) := by linarith only [abs1,abs2,discrepancy]
  have lp' : (0:ℝ)<L := by exact_mod_cast lp
  have np' : (0:ℝ)<n := by exact_mod_cast np
  change ε*(L:ℝ) < _
  field_simp at u
  nlinarith only [u]

/-- For targets with a bounded number of distinct prime factors the model
discrepancy cannot cause a failure at sufficiently large window sizes. -/
theorem bounded_support_failure (k : ℕ) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ n ≤ X, X ≤ 2*n → n.primeFactors.card ≤ k →
      (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re < -(ε*n) →
      ε*(X:ℝ)/8 ≤ ‖commonMinor X n‖ := by
  obtain ⟨K,hK⟩ := exists_nat_gt (32*(3:ℝ)^k*conductorSqrtMoment/ε)
  have kp := (div_lt_iff₀ he).mp hK
  have mass : 0 ≤ conductorSqrtMoment := tsum_nonneg (fun q => by unfold conductorMass; positivity)
  filter_upwards [frozen_failure_needs_divisors ε he,eventually_ge_atTop (2*2^K)] with X split hx
  intro n hn half small bad
  refine (split n hn half bad).resolve_right ?_
  have L := Nat.le_log_of_pow_le (by decide : 1<2) (by omega : 2^K ≤ n+2)
  have large := mul_le_mul_of_nonneg_left (show (K:ℝ) ≤ Nat.log 2 (n+2) by exact_mod_cast L) he.le
  have factor := (targetFactor_le_three_pow n).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) small)
  have bound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left factor (by norm_num : (0:ℝ)≤32)) mass
  linarith only [large,kp,bound]

#print axioms frozen_failure_needs_divisors
#print axioms bounded_support_failure
end GoldbachMinor
