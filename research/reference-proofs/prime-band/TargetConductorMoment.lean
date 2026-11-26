import RamanujanMainTerm

namespace GoldbachMinor
open Finset ArithmeticFunction

private noncomputable def increment (n p : ℕ) : ℝ := Real.sqrt p * |localSign n p|
private noncomputable def weight (n q : ℕ) : ℝ := Real.sqrt q * |ramWeight q n|

private theorem increment_nonneg (n p : ℕ) : 0 ≤ increment n p :=
  mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)

private theorem weight_nonneg (n q : ℕ) : 0 ≤ weight n q :=
  mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)

private theorem factor_weight (n q : ℕ) (sq : Squarefree q) :
    weight n q = ∏ p ∈ q.primeFactors, increment n p := by
  have prodId : (q:ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) := by
    rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree sq]
  dsimp only [weight,increment,ramWeight]
  rw [coefficient_factorization n q sq,Finset.abs_prod,prodId,
      Real.sqrt_prod _ (fun _ _ => Nat.cast_nonneg _),prod_mul_distrib]

/-- Only primes dividing the target can increase its conductor moment
relative to the product at target one. Multiplicities do not enter. -/
noncomputable def targetFactor (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, (1+Real.sqrt p / ((p:ℝ)-1))

theorem targetFactor_le_three_pow (n : ℕ) : targetFactor n ≤ (3:ℝ)^n.primeFactors.card := by
  have row (p : ℕ) (hp : p∈n.primeFactors) : 1 + Real.sqrt p / ((p:ℝ)-1) ≤ 3 := by
    have two : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have r := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p)
    have l : Real.sqrt p ≤ p := le_of_sq_le_sq (by nlinarith) (Nat.cast_nonneg _)
    have t : Real.sqrt p / ((p:ℝ)-1) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith
  simpa only [targetFactor,prod_const] using (prod_le_prod₀ (fun p hp => by
    have : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    positivity) row)

private theorem prime_product_one (P : Finset ℕ) (prime : ∀ p∈P, p.Prime) :
    (∏ p ∈ P, (1+increment 1 p)) ≤ conductorSqrtMoment := by
  classical
  let prodN := fun S : Finset ℕ => ∏ p ∈ S, p
  have factors (S : Finset ℕ) (hS : S∈P.powerset) : (prodN S).primeFactors = S :=
    Nat.primeFactors_prod fun p hp => prime p (mem_powerset.mp hS hp)
  have sq (S : Finset ℕ) (hS : S∈P.powerset) : Squarefree (prodN S) := by
    have h := Nat.squarefree_prod_primeFactors (prodN S)
    rwa [factors S hS] at h
  rw [prod_one_add]
  apply le_trans _ (conductorMass_sqrt_summable.sum_le_tsum (P.powerset.image prodN)
    (fun q _ => by unfold conductorMass; positivity))
  apply sum_le_sum_of_injOn prodN _ (Subset.rfl) _ (fun q _ _ => by unfold conductorMass; positivity)
  · intro s hs t ht eq
    rw [← factors s hs,eq,factors t ht]
  · intro s hs
    rw [← factors s hs,← factor_weight 1 _ (sq s hs),factors s hs]
    dsimp only [weight]
    exact mul_le_mul_of_nonneg_left (by simpa using ramWeight_point_bound 1 (prodN s) (by decide))
      (Real.sqrt_nonneg _)

private theorem local_product (n : ℕ) (hn : 0<n) (P : Finset ℕ) (prime : ∀ p∈P, p.Prime) :
    (∏ p ∈ P, (1+increment n p)) ≤ targetFactor n * conductorSqrtMoment := by
  classical
  let a (p : ℕ) : ℝ := 1+Real.sqrt p/((p:ℝ)-1)
  let D := P.filter (· ∣ n)
  have sub : D ⊆ n.primeFactors := fun p hp => Nat.mem_primeFactors.mpr
    ⟨prime p (mem_filter.mp hp).1,(mem_filter.mp hp).2,hn.ne'⟩
  have age (p : ℕ) (hp : p.Prime) : 1 ≤ a p := by
    have : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    dsimp only [a]; linarith only [div_nonneg (Real.sqrt_nonneg (p:ℝ)) (by linarith : 0≤(p:ℝ)-1)]
  have pos (p : ℕ) : 0 ≤ 1+increment 1 p := by linarith only [increment_nonneg 1 p]
  have points (p : ℕ) (hp : p∈P) : 1+increment n p ≤
      (if p∣n then a p else 1)*(1+increment 1 p) := by
    have pr := prime p hp
    by_cases h : p∣n
    · have pp : (0:ℝ)<(p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast pr.one_lt)
      rw [ite_eq_left h]
      have eq : 1+increment n p = a p := by
        simp only [increment,localSign,h,ite_true,abs_of_nonneg (inv_nonneg.mpr pp.le),a,
          div_eq_mul_inv,one_mul]
      rw [eq]
      exact le_mul_of_one_le_right ((age p pr).trans' zero_le_one) (by linarith only [increment_nonneg 1 p])
    · simp only [h,ite_false,one_mul]
      simp [increment,localSign,h,pr.not_dvd_one]
  have bound := prod_le_prod₀ (fun p _ => by linarith only [increment_nonneg n p]) points
  rw [prod_mul_distrib, ← Finset.prod_filter] at bound
  apply bound.trans
  exact mul_le_mul (prod_le_prod_of_subset_of_one_le₀ sub
    (fun p hp => zero_le_one.trans (age p (Nat.prime_of_mem_primeFactors (sub hp))))
    (fun p hp _ => age p (Nat.prime_of_mem_primeFactors hp))) (prime_product_one P prime)
    (prod_nonneg (fun p _ => pos p)) (prod_nonneg (fun p hp => zero_le_one.trans (age p (Nat.prime_of_mem_primeFactors hp))))

private theorem prefix_moment (n : ℕ) (hn : 0<n) (N : ℕ) :
    (∑ q ∈ range N, weight n q) ≤ targetFactor n * conductorSqrtMoment := by
  classical
  let D := (range N).filter Squarefree
  let P := Nat.primesLE N
  have restrict : (∑ q ∈ range N, weight n q) = ∑ q ∈ D, weight n q := by
    rw [sum_filter]; apply sum_congr rfl; intro q _
    by_cases h : Squarefree q <;> simp [h,weight,ramWeight,moebius_eq_zero_of_not_squarefree]
  rw [restrict]
  apply le_trans _ (local_product n hn P (fun _ hp => Nat.prime_of_mem_primesLE hp))
  rw [prod_one_add]
  apply sum_le_sum_of_injOn Nat.primeFactors _ _ _ (fun s _ _ => prod_nonneg fun p _ => increment_nonneg n p)
  · intro a ha b hb eq
    rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2,
      ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2,eq]
  · intro s hs
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hs
    exact mem_powerset.mpr fun p hp => Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_mem_primeFactors hp).trans (mem_range.mp (mem_filter.mp hq).1).le,Nat.prime_of_mem_primeFactors hp⟩
  · intro q hq
    exact (factor_weight n q (mem_filter.mp hq).2).le

theorem target_moment_summable (n : ℕ) (hn : 0<n) :
    Summable (fun q : ℕ => Real.sqrt q * |ramWeight q n|) :=
  summable_of_sum_range_le (weight_nonneg n) (prefix_moment n hn)

theorem target_moment_bound (n : ℕ) (hn : 0<n) :
    (∑' q : ℕ, Real.sqrt q * |ramWeight q n|) ≤ targetFactor n * conductorSqrtMoment :=
  le_of_tendsto ((target_moment_summable n hn).hasSum.tendsto_sum_nat)
    (Filter.Eventually.of_forall (prefix_moment n hn))

/-- Apply a cutoff error to a single target's absolute Ramanujan coefficients. -/
theorem target_cutoff_rate (n Q : ℕ) (hn : 0<n) (hQ : 0<Q) (A : ℝ) (hA : 0≤A)
    (f : ℕ → ℝ) (hf : ∀ q, 0≤f q) (cap : ∀ q, 0<q → f q≤A)
    (slope : ∀ q, 0<q → f q*Q ≤ A*q) :
    (∑' q, |ramWeight q n| *f q) ≤ A*targetFactor n*conductorSqrtMoment / Real.sqrt Q := by
  have root : 0 < Real.sqrt Q := Real.sqrt_pos.mpr (by exact_mod_cast hQ)
  let g := fun q : ℕ => (A/Real.sqrt Q)*(Real.sqrt q*|ramWeight q n|)
  have sg : Summable g := (target_moment_summable n hn).mul_left _
  have row (q : ℕ) : |ramWeight q n| * f q ≤ g q := by
    rcases Nat.eq_zero_or_pos q with rfl | hp
    · simp [ramWeight,ram,g]
    have b := (le_div_iff₀ root).mpr (cutoff_factor_sqrt_le Q q hQ A hA _ (cap q hp) (slope q hp))
    exact (mul_le_mul_of_nonneg_left b (abs_nonneg _)).trans_eq (by dsimp [g]; ring)
  apply ((sg.of_nonneg_of_le (fun q => mul_nonneg (abs_nonneg _) (hf q)) row).tsum_le_tsum row sg).trans
  simp only [g,tsum_mul_left]
  convert! mul_le_mul_of_nonneg_left (target_moment_bound n hn) (div_nonneg hA root.le) using 1; ring

#print axioms target_moment_bound
end GoldbachMinor
