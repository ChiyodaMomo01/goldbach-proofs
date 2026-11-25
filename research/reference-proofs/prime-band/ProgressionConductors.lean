import MajorPositivity
import ResonantMean

namespace GoldbachMinor
open Finset ArithmeticFunction

/-- Sum of the complete-period coefficients that survive on the multiples of d. -/
theorem progression_resonance (d : ℕ) (hd : 0 < d) :
    (∑ q ∈ d.divisors, ram q 0 * ((moebius q:ℝ)/q.totient)^2) = (d:ℝ)/d.totient := by
  classical
  let S := d.primeFactors
  let f (p : ℕ) := 1 / ((p:ℝ)-1)
  have good (A : Finset ℕ) (h : A ∈ S.powerset) (p : ℕ) (hp : p ∈ A) :=
    Nat.prime_of_mem_primeFactors (mem_powerset.mp h hp : p ∈ d.primeFactors)
  calc
    _ = ∑ q ∈ d.divisors.filter Squarefree, ∏ p ∈ q.primeFactors, f p := by
      rw [sum_filter]
      apply sum_congr rfl
      intro q _
      by_cases sq : Squarefree q
      · simp only [sq, ite_true, coefficient_factorization 0 q sq, localSign, dvd_zero, f]
      · simp [sq, moebius_eq_zero_of_not_squarefree sq]
    _ = ∑ A ∈ S.powerset, ∏ p ∈ A, f p := by
      apply sum_bij (fun q _ => q.primeFactors)
      · intro q h
        exact mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors (mem_filter.mp h).1) hd.ne')
      · intro q h r h' eq
        rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp h).2,
          ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp h').2, eq]
      · intro A h
        let q := ∏ p ∈ A, p
        have eq : q.primeFactors = A := Nat.primeFactors_prod (good A h)
        have dvd : q ∣ d := (prod_dvd_prod_of_subset A S id (mem_powerset.mp h)).trans d.prod_primeFactors_dvd
        have sq := Nat.squarefree_prod_primeFactors q
        rw [eq] at sq
        exact ⟨q, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd, hd.ne'⟩, sq⟩, eq⟩
      · intro q _; rfl
    _ = ∏ p ∈ S, (1 + f p) := (prod_one_add S).symm
    _ = ∏ p ∈ S, (p:ℝ)/(p-1:ℕ) := by
      apply prod_congr rfl
      intro p hp
      have pr := Nat.prime_of_mem_primeFactors (show p ∈ d.primeFactors from hp)
      have pos : 1 < (p:ℝ) := by exact_mod_cast pr.one_lt
      rw [Nat.cast_sub pr.pos, Nat.cast_one]
      dsimp [f]
      field_simp
      ring
    _ = _ := by
      rw [prod_div_distrib]
      have tot : (0:ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
      have pos : 0 < ∏ p ∈ S, ((p-1:ℕ):ℝ) := prod_pos fun p hp => by
        exact_mod_cast Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors (show p ∈ d.primeFactors from hp)).one_lt
      rw [div_eq_div_iff pos.ne' tot.ne', mul_comm _ (d.totient:ℝ)]
      have h := congrArg (fun n : ℕ => (n:ℝ)) (Nat.totient_mul_prod_primeFactors d)
      simpa only [Nat.cast_mul, Nat.cast_prod] using h

/-- An unfinished period for a nonresonant conductor costs at most q squared,
independently of the starting point and the number of complete periods. -/
theorem nonresonant_prefix (q d s K : ℕ) (hq : 0 < q) (hd : ¬q ∣ d) :
    |∑ i ∈ range K, ram q (s+i*d)| ≤ (q:ℝ)^2 := by
  let L := K/q*q
  have div : q ∣ L*d := (dvd_mul_left q (K/q)).trans (dvd_mul_right L d)
  have full := ram_closed_progression q d L s hq div
  rw [ite_eq_right hd] at full
  conv_lhs => rw [show K = L+K%q from (Nat.div_add_mod' K q).symm, sum_range_add, full, zero_add]
  calc
    _ ≤ _ := abs_sum_le_sum_abs ..
    _ ≤ ∑ _i ∈ range (K%q), (q:ℝ) := sum_le_sum (fun _ _ => abs_ram_le q _ hq)
    _ ≤ _ := by
      simp only [sum_const, card_range, nsmul_eq_mul, pow_two]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt K hq).le) (Nat.cast_nonneg q)

/-- Summation by parts retains cancellation under a nonnegative increasing weight. -/
theorem increasing_weight_prefix_bound (f w : ℕ → ℝ) (K : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ k, |∑ i ∈ range k, f i| ≤ B) (pos : ∀ i, 0 ≤ w i) (mono : Monotone w) :
    |∑ i ∈ range K, w i * f i| ≤ 2 * w K * B := by
  simp_rw [← smul_eq_mul, sum_range_by_parts w f, smul_eq_mul]
  apply (abs_sub _ _).trans
  have rest : |∑ i ∈ range (K-1), (w (i+1)-w i)*(∑ j ∈ range (i+1), f j)| ≤
      (w (K-1)-w 0)*B := by
    apply (abs_sum_le_sum_abs ..).trans
    rw [← sum_range_sub w (K-1), sum_mul]
    apply sum_le_sum
    intro i _
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (mono (Nat.le_succ i)))]
    exact mul_le_mul_of_nonneg_left (h _) (sub_nonneg.mpr (mono (Nat.le_succ i)))
  rw [abs_mul, abs_of_nonneg (pos _)]
  have main := mul_le_mul_of_nonneg_left (h K) (pos (K-1))
  have last := mul_le_mul_of_nonneg_right (mono (Nat.sub_le K 1)) hB
  nlinarith only [rest, main, last, mul_nonneg (pos 0) hB]

#print axioms progression_resonance
end GoldbachMinor
