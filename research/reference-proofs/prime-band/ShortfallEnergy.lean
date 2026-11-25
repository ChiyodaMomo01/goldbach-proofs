import ModelProgressionMean
import SingularSeriesTransfer

namespace GoldbachMinor
open Finset Filter
open scoped Topology

/-- The full normalized binary singular-series shape at 2n dominates the
absolute value of the catalogue model, including targets n of odd parity. -/
theorem model_shape_majorant (n : ℕ) (hn : 0 < n) :
    |catalogueMajorModel n| ≤ (n:ℝ)*(3*binaryShape (2*n) (2*n)) := by
  classical
  let Q := catalogueCutoff n
  let P := Nat.primesLE Q
  let S := P.erase 2
  let G := S.filter (· ∣ n)
  have odd (p) (hp : p ∈ S) : p.Prime ∧ 3 ≤ p := by
    obtain ⟨ne,mem⟩ := mem_erase.mp hp
    have pr := Nat.prime_of_mem_primesLE mem
    exact ⟨pr,by have := pr.two_le; omega⟩
  have gpos (p) (hp : p ∈ S) : 0 ≤ goldbachFactor p := by
    have h : (3:ℝ) ≤ p := by exact_mod_cast (odd p hp).2
    unfold goldbachFactor; exact div_nonneg zero_le_one (by linarith)
  let good (p : ℕ) := if p ∣ n then 1+goldbachFactor p else 1
  have factor (p) (hp : p ∈ S) : 1+|localSign n p| ≤ lossFactor p * good p := by
    have h : (3:ℝ) ≤ p := by exact_mod_cast (odd p hp).2
    have b : 1 ≤ lossFactor p := le_add_of_nonneg_right (by positivity)
    by_cases dvd : p ∣ n
    · simp only [localSign, good, dvd, ite_true, abs_of_nonneg (div_nonneg zero_le_one (by linarith) : 0 ≤ 1/((p:ℝ)-1))]
      have a : 1 / ((p:ℝ)-1) ≤ goldbachFactor p :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      exact (add_le_add_right a 1).trans (le_mul_of_one_le_left (by linarith [gpos p hp]) b)
    · simp [localSign, good, dvd, lossFactor]
  have sub : G ⊆ (shapePrimes (2*n)).filter (· ∣ 2*n) := by
    intro p hp
    obtain ⟨hs,dvd⟩ := mem_filter.mp hp
    have h := odd p hs
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd hn dvd).trans (by omega), h.1⟩,h.2⟩, dvd.trans (dvd_mul_left n 2)⟩
  have shape : (∏ p ∈ S, good p) ≤ binaryShape (2*n) (2*n) := by
    rw [binaryShape, ite_eq_left (dvd_mul_right 2 n), oddFactorProduct]
    change (∏ p ∈ S, if p ∣ n then 1+goldbachFactor p else 1) ≤ _
    rw [← prod_filter]
    apply prod_le_prod_of_subset_of_one_le₀ sub
    · intro p hp
      have := gpos p (mem_filter.mp hp).1
      positivity
    · intro p hp _
      have h : (3:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp (mem_filter.mp hp).1).2
      unfold goldbachFactor; exact le_add_of_nonneg_right (div_nonneg zero_le_one (by linarith))
  have two : (1+|localSign n 2|) = 2 := by
    by_cases h : 2 ∣ n <;> norm_num [localSign,h]
  have all : (∏ p ∈ P, (1+|localSign n p|)) ≤ 2*∏ p ∈ S, (1+|localSign n p|) := by
    by_cases h : 2 ∈ P
    · rw [← prod_erase_mul _ _ h, two]; exact le_of_eq (mul_comm ..)
    · simp only [S, erase_eq_of_notMem h]
      have z : 0 ≤ ∏ p ∈ P, (1+|localSign n p|) := prod_nonneg fun _ _ => by positivity
      linarith
  have loss := bad_prime_product_bound S (fun p hp => ⟨(odd p hp).1,by have := (odd p hp).2; omega⟩)
  have gp : 0 ≤ ∏ p ∈ S, good p := prod_nonneg fun p hp => by
    dsimp [good]; split <;> linarith [gpos p hp]
  have product := prod_le_prod₀ (fun p (_ : p ∈ S) => (by positivity : 0 ≤ 1+|localSign n p|)) factor
  rw [prod_mul_distrib] at product
  have bound : (∏ p ∈ P, (1+|localSign n p|)) ≤ 3*binaryShape (2*n) (2*n) := by
    nlinarith only [all,product,mul_le_mul_of_nonneg_right loss gp,shape]
  rw [catalogueMajorModel, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), model_support_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (abs_sum_le_sum_abs ..).trans (le_trans _ bound)
  rw [prod_one_add]
  apply sum_le_sum
  intro A _
  have ker (q : ℕ) : |windowKernel Q q| ≤ 1 := by
    by_cases h : q ≤ Q
    · rw [windowKernel, ite_eq_left h, abs_of_nonneg (archimedean_nonneg _ (by positivity))]
      exact archimedean_mass_le_one _ (by positivity)
    · simp [windowKernel,h]
  rw [abs_mul, abs_prod]
  exact mul_le_of_le_one_right (prod_nonneg fun _ _ => abs_nonneg _) (ker _)

noncomputable def countShortfall (n : ℕ) : ℝ := max (catalogueMajorModel n-goldbachCount n) 0

private theorem shortfall_le_shape (n : ℕ) (hn : 0 < n) :
    countShortfall n ≤ n*(3*binaryShape (2*n) (2*n)) := by
  have count : 0 ≤ goldbachCount n := sum_nonneg fun x _ =>
    mul_nonneg (primeLog_nonneg x.1) (primeLog_nonneg x.2)
  apply le_trans _ (model_shape_majorant n hn)
  exact max_le ((sub_le_self _ count).trans (le_abs_self _)) (abs_nonneg _)

/-- A uniform second moment for the *downward* error, without a prime-pair
mean-square hypothesis. The modulus stays fixed as the dyadic window grows. -/
theorem dyadic_shortfall_energy (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
      (∑ i ∈ Ico j (2*j), (countShortfall (d*i)/(d*i:ℕ))^2) ≤ C*j := by
  let A := shapeConstant/2+2
  have ap : 0 < A := by dsimp [A,shapeConstant]; positivity
  let C := 9*(4*(d:ℝ)*A+16*d)
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  have grows : Tendsto (fun j : ℕ => 2*d*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by omega : 0 < 2*d)) tendsto_id
  filter_upwards [grows.eventually (harmonic_edge_budget 1 zero_lt_one), eventually_ge_atTop 1] with j edge hj
  let X := 2*d*j
  have hQ : 1 ≤ catalogueCutoff X := Nat.one_le_pow _ _
    (Nat.le_log_of_pow_le (by decide) (show 2^1 ≤ X+2 by omega))
  have z : 0 ≤ diagonalEnergy (catalogueCutoff X) (logWidth X) := by
    unfold diagonalEnergy; exact sum_nonneg fun _ _ => by positivity
  have fac : (1:ℝ) ≤ (catalogueCutoff X:ℝ)*(1+diagonalEnergy (catalogueCutoff X) (logWidth X)) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hQ) (by linarith)
  have harm : (harmonicCutoff (2*X))^4 ≤ X := by
    have e := le_mul_of_one_le_left (by positivity : 0 ≤ (harmonicCutoff (2*X))^4) fac
    exact e.trans (by simpa only [one_mul] using edge)
  let f (n : ℕ) := (binaryShape n n)^2
  have inject : (∑ i ∈ Ico j (2*j), f (2*(d*i))) ≤ ∑ n ∈ Ioc 0 (2*X), f n := by
    apply sum_le_sum_of_injOn (fun i => 2*(d*i))
    · intro a ha b hb he
      exact Nat.eq_of_mul_eq_mul_left hd (Nat.eq_of_mul_eq_mul_left (by decide : 0<2) he)
    · intro m hm
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hm
      have h := mem_Ico.mp hi
      have low : 0 < d*i := Nat.mul_pos hd (hj.trans h.1)
      have top := Nat.mul_le_mul_left d h.2.le
      apply mem_Ioc.mpr
      refine ⟨by omega,?_⟩
      dsimp [X]; calc
        _ ≤ 2*(d*(2*j)) := Nat.mul_le_mul_left _ top
        _ = _ := by ring
    · intro _ _; rfl
    · intro _ _ _; exact sq_nonneg _
  have shape := full_shape_energy 0 (2*X) (Nat.zero_le _)
  simp only [Nat.cast_zero,sub_zero] at shape
  calc
    _ ≤ ∑ i ∈ Ico j (2*j), 9*f (2*(d*i)) := by
      apply sum_le_sum
      intro i hi
      have np : 0 < d*i := Nat.mul_pos hd (hj.trans (mem_Ico.mp hi).1)
      have nonneg : 0 ≤ countShortfall (d*i)/(d*i:ℕ) := div_nonneg (le_max_right ..) (Nat.cast_nonneg _)
      have h := (div_le_iff₀ (by exact_mod_cast np : 0 < ((d*i:ℕ):ℝ))).mpr
        ((shortfall_le_shape _ np).trans_eq (mul_comm ..))
      have sq := mul_self_le_mul_self nonneg h
      dsimp [f]; nlinarith only [sq]
    _ = 9*∑ i ∈ Ico j (2*j), f (2*(d*i)) := (mul_sum ..).symm
    _ ≤ _ := by
      change (∑ n ∈ Ioc 0 (2*X), f n) ≤ ((2*X:ℕ):ℝ)*A+8*(harmonicCutoff (2*X))^4 at shape
      dsimp [X] at inject harm shape
      push_cast at harm shape
      dsimp [C]
      nlinarith only [inject,harm,shape]

#print axioms dyadic_shortfall_energy
end GoldbachMinor
