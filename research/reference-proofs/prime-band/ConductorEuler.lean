import AveragedBand

namespace GoldbachMinor
open Finset GoldbachWeight

/-- Expand the product while forcing every prime of T to appear in the chosen support. -/
private theorem forced_support (S T : Finset ℕ) (hT : T⊆S) (w : ℕ→ℝ) :
    (∑ A ∈ S.powerset, if T⊆A then ∏ p ∈ A, w p else 0) =
    ∏ p ∈ S, (w p + if p∈T then 0 else 1) := by
  rw [prod_add]
  apply sum_congr rfl
  intro A _
  by_cases h : T⊆A
  · have ones : (∏ p ∈ S \ A, (if p∈T then 0 else 1:ℝ))=1 := by
      apply prod_eq_one
      intro p hp
      exact ite_eq_right fun ht => (mem_sdiff.mp hp).2 (h ht)
    simp [h,ones]
  · obtain ⟨p,ht,ha⟩ := not_subset.mp h
    have zero : (∏ p ∈ S \ A, (if p∈T then 0 else 1:ℝ))=0 :=
      prod_eq_zero (mem_sdiff.mpr ⟨hT ht,ha⟩) (ite_eq_left ht)
    simp [h,zero]

/-- For a squarefree conductor the only forced odd primes are its own odd prime factors. -/
private theorem conductor_support (y q : ℕ) (sq : Squarefree q) (A : Finset ℕ) (ha : A⊆shapePrimes y) :
    q∣evenSupport A ↔ q.primeFactors.erase 2 ⊆ A := by
  have primes (p) (hp : p∈insert 2 A) : Nat.Prime p := by
    rcases mem_insert.mp hp with rfl|hp
    · exact Nat.prime_two
    · exact (Nat.mem_primesLE.mp (mem_filter.mp (ha hp)).1).2
  have ne : evenSupport A ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (primes p hp).ne_zero
  have factors : (evenSupport A).primeFactors = insert 2 A := Nat.primeFactors_prod primes
  have eq := Nat.prod_primeFactors_dvd_iff (n:=q) ne
  rw [Nat.prod_primeFactors_of_squarefree sq,factors] at eq
  refine eq.trans ⟨?_,?_⟩
  · intro h p hp
    exact (mem_insert.mp (h (mem_erase.mp hp).2)).resolve_left (mem_erase.mp hp).1
  · intro h p hp
    by_cases ht : p=2
    · exact mem_insert.mpr (Or.inl ht)
    · exact mem_insert_of_mem (h (mem_erase.mpr ⟨ht,hp⟩))

/-- Exact Euler factorization, including the denominator one and even conductors. -/
theorem conductorWeight_totient (y q : ℕ) (hd : q∣y.factorial) (sq : Squarefree q) :
    conductorWeight y q * (q.totient:ℝ)^2 = ∏ p ∈ shapePrimes y, factorMean p := by
  let S := shapePrimes y
  let T := q.primeFactors.erase 2
  let w (p : ℕ) := goldbachFactor p/p
  let v (p : ℕ) := ((p:ℝ)-1)^2
  have sub : T⊆S := by
    intro p hp
    obtain ⟨hn,hf⟩ := mem_erase.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hf
    have hle := hprime.dvd_factorial.mp ((Nat.dvd_of_mem_primeFactors hf).trans hd)
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle,hprime⟩,by have := hprime.two_le; omega⟩
  have weight : conductorWeight y q = ∏ p ∈ S, (w p+if p∈T then 0 else 1) := by
    rw [← forced_support S T sub,conductorWeight]
    apply sum_congr rfl
    intro A ha
    simp only [conductor_support y q sq A (mem_powerset.mp ha),T,w]
  have phi : q.totient = ∏ p ∈ q.primeFactors, (p-1) := by
    have h := Nat.totient_mul_prod_primeFactors q
    rw [Nat.prod_primeFactors_of_squarefree sq,Nat.mul_comm q.totient] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero sq.ne_zero) h
  have tot : (q.totient:ℝ)^2 = ∏ p ∈ T, v p := by
    have all : (q.totient:ℝ)^2 = ∏ p ∈ q.primeFactors, v p := by
      rw [phi,Nat.cast_prod,← prod_pow]
      exact prod_congr rfl fun p hp => by
        rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).pos,Nat.cast_one]
    rw [all]
    by_cases ht : 2∈q.primeFactors
    · have e := prod_erase_mul q.primeFactors v ht
      have v2 : v 2=1 := by norm_num [v]
      simpa only [v2,mul_one] using e.symm
    · simp [T,erase_eq_of_notMem ht]
  have lift : (∏ p ∈ T, v p) = ∏ p ∈ S, (if p∈T then v p else 1) := by
    rw [← prod_filter]
    have eq : S.filter (·∈T) = T := by ext p; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
    rw [eq]
  rw [weight,tot,lift,← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  by_cases ht : p∈T
  · simp only [ht,ite_true,add_zero]
    have hr : (3:ℝ)≤p := by exact_mod_cast (mem_filter.mp hp).2
    have h0 : (p:ℝ)≠0 := by linarith
    have h2 : (p:ℝ)-2≠0 := by linarith
    unfold w v factorMean goldbachFactor
    field_simp
    ring
  · simp [ht,factorMean,w,add_comm]

/-- Classical-looking closed form with no inner prime-support or offset sums. -/
noncomputable def eulerBandLoss (c : ℝ) (n : ℕ) : ℝ :=
  c*n*(∏ p ∈ shapePrimes (factorialIndex n), factorMean p)*
    ∑ q ∈ (Icc 1 (catalogueCutoff n)).filter (fun q => q∣factorialPeriod n ∧ Squarefree q),
      ram q n/(q.totient:ℝ)^2*sineIntegralWeight q

theorem arithmetic_band_euler (c : ℝ) (n : ℕ) : arithmeticBandLoss c n=eulerBandLoss c n := by
  unfold arithmeticBandLoss eulerBandLoss
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  obtain ⟨hi,hd,sq⟩ := mem_filter.mp hq
  have phi : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hi).1
  rw [← conductorWeight_totient (factorialIndex n) q hd sq]
  field_simp

theorem outer_euler_iff (c : ℝ) (hc : ClassicalMeanSquare c) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      firstBandSum n (firstBandEnd n) n (majorCoefficient (catalogueCutoff n) n) +
        eulerBandLoss c n ≤ pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  simpa only [arithmetic_band_euler] using outer_arithmetic_iff c hc

#print axioms conductorWeight_totient
#print axioms outer_euler_iff
end GoldbachMinor
