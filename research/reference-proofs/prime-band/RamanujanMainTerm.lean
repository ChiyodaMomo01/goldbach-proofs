import ConductorTail
import VaughanAlignment

namespace GoldbachMinor
open Finset Filter
open scoped Topology

/-- Holding the positive target fixed gives an absolutely convergent
Ramanujan expansion as a consequence of the positive-prefix estimate. -/
theorem ramWeight_point_bound (n q : ℕ) (hn : 0 < n) :
    |ramWeight q n| ≤ n*conductorMass q := by
  have one : |ram q n| ≤ ∑ m ∈ Ioc 0 n, |ram q m| :=
    single_le_sum (fun i _ => abs_nonneg (ram q i)) (mem_Ioc.mpr ⟨hn,le_rfl⟩)
  rw [ramWeight, abs_mul, abs_of_nonneg (sq_nonneg ((ArithmeticFunction.moebius q:ℝ)/q.totient)), conductorMass, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (one.trans (ram_absolute_prefix q n)) (sq_nonneg _)

theorem ramWeight_abs_summable (n : ℕ) (hn : 0 < n) :
    Summable (fun q => |ramWeight q n|) :=
  (conductorMass_summable.mul_left (n:ℝ)).of_nonneg_of_le (fun _ => abs_nonneg _)
    (ramWeight_point_bound n · hn)

private def primorial (Y : ℕ) := ∏ p ∈ Nat.primesLE Y, p

private theorem primorial_factors (Y : ℕ) : (primorial Y).primeFactors = Nat.primesLE Y :=
  Nat.primeFactors_prod fun _ hp => Nat.prime_of_mem_primesLE hp

private theorem primorial_squarefree (Y : ℕ) : Squarefree (primorial Y) := by
  have h := Nat.squarefree_prod_primeFactors (primorial Y)
  rw [primorial_factors] at h
  exact h

private theorem unit_plus_local (n p : ℕ) (hp : p.Prime) : 1+localSign n p = vaughanFactor p n := by
  have h : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have nz : (p:ℝ)-1 ≠ 0 := by linarith
  by_cases dvd : p ∣ n <;> simp only [vaughanFactor, localSign, dvd, ite_true, ite_false] <;> field_simp <;> ring

/-- Expand the finite singular-series product over squarefree divisors of the primorial. -/
private theorem finite_euler (Y n : ℕ) :
    (∑ q ∈ (primorial Y).divisors, ramWeight q n) =
    ∏ p ∈ Nat.primesLE Y, vaughanFactor p n := by
  let P := Nat.primesLE Y
  have good (A : Finset ℕ) (h : A ∈ P.powerset) : ∀ p∈A, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp h hp)
  calc
    _ = ∑ A ∈ P.powerset, ∏ p ∈ A, localSign n p := by
      apply sum_bij (fun q _ => q.primeFactors)
      · intro q h
        apply mem_powerset.mpr
        rw [show P = (primorial Y).primeFactors from (primorial_factors Y).symm]
        exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors h) (primorial_squarefree Y).ne_zero
      · intro a ha b hb eq
        rw [← Nat.prod_primeFactors_of_squarefree ((primorial_squarefree Y).squarefree_of_dvd (Nat.dvd_of_mem_divisors ha)),
            ← Nat.prod_primeFactors_of_squarefree ((primorial_squarefree Y).squarefree_of_dvd (Nat.dvd_of_mem_divisors hb)), eq]
      · intro A hA
        exact ⟨∏ p ∈ A, p, Nat.mem_divisors.mpr ⟨prod_dvd_prod_of_subset A P id (mem_powerset.mp hA),
          (primorial_squarefree Y).ne_zero⟩, Nat.primeFactors_prod (good A hA)⟩
      · intro q h
        exact coefficient_factorization n q ((primorial_squarefree Y).squarefree_of_dvd (Nat.dvd_of_mem_divisors h))
    _ = ∏ p ∈ P, (1+localSign n p) := (prod_one_add P).symm
    _ = _ := prod_congr rfl fun p hp => unit_plus_local n p (Nat.prime_of_mem_primesLE hp)

/-- The absolutely convergent arithmetic expansion has the exact classical
normalization, with the prime 2 included in the finite products. -/
theorem ramWeight_tsum_eq_classical (n : ℕ) (hn : 0 < n) :
    (∑' q, ramWeight q n) = 2*twinPrimeConstant*binaryShape n n := by
  let f (Y q : ℕ) := if q ∈ (primorial Y).divisors then ramWeight q n else 0
  have single (q : ℕ) : Tendsto (fun Y => f Y q) atTop (𝓝 (ramWeight q n)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop q] with Y hY
    by_cases sq : Squarefree q
    · have sub : q.primeFactors ⊆ Nat.primesLE Y := fun p hp =>
        Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hY, Nat.prime_of_mem_primeFactors hp⟩
      have dvd : q ∣ primorial Y := by
        conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree sq]
        exact prod_dvd_prod_of_subset _ _ id sub
      exact (ite_eq_left (Nat.mem_divisors.mpr ⟨dvd,(primorial_squarefree Y).ne_zero⟩)).symm
    · simp [f,ramWeight,ArithmeticFunction.moebius_eq_zero_of_not_squarefree sq]
  have lim := tendsto_tsum_of_dominated_convergence (ramWeight_abs_summable n hn) single
    (Eventually.of_forall (fun Y q => (by
      dsimp only [f]; split
      · exact (Real.norm_eq_abs _).le
      · rw [norm_zero]; exact abs_nonneg _ : ‖f Y q‖ ≤ |ramWeight q n|)))
  have eq (Y : ℕ) : (∑' q, f Y q) = ∏ p ∈ Nat.primesLE Y, vaughanFactor p n := by
    rw [← finite_euler]
    rw [tsum_eq_sum (s:=(primorial Y).divisors) (fun q h => by simp only [f, h, ite_false])]
    exact sum_congr rfl fun q h => by simp only [f, h, ite_true]
  exact tendsto_nhds_unique (lim.congr fun Y => eq Y) (vaughan_series_alignment n hn)

#print axioms ramWeight_tsum_eq_classical
end GoldbachMinor
