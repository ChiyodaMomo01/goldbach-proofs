import SingularSeriesDivisors
import BandArithmetic

namespace GoldbachMinor
open Finset

/-- A finite window has at most one unit of discrepancy for every positive divisor. -/
theorem multiples_window_discrepancy (K H q : ℕ) (h : K≤H) (hq : 0<q) :
    |(((Ioc K H).filter (q ∣ ·)).card : ℝ) - ((H:ℝ)-K)/q| ≤ 1 := by
  have count := sum_Ioc_consecutive (fun k : ℕ => if q ∣ k then (1 : ℕ) else 0) (Nat.zero_le K) h
  simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one, Nat.Ioc_filter_dvd_card_eq_div] at count
  have eq : (↑((Ioc K H).filter (q ∣ ·)).card : ℝ) * q - ((H:ℝ)-K) =
      ((K%q : ℕ):ℝ) - ((H%q : ℕ):ℝ) := by
    have h1 : (K/q:ℕ)*q+(K%q)=K := Nat.div_add_mod' ..
    have h2 : (H/q:ℕ)*q+(H%q)=H := Nat.div_add_mod' ..
    have hc : ((K/q:ℕ):ℝ) + (((Ioc K H).filter (q ∣ ·)).card : ℝ) = ((H/q:ℕ):ℝ) := by exact_mod_cast count
    have ha : ((K/q:ℕ):ℝ)*q+(K%q:ℕ)=K := by exact_mod_cast h1
    have hb : ((H/q:ℕ):ℝ)*q+(H%q:ℕ)=H := by exact_mod_cast h2
    nlinarith only [ha,hb,congrArg (·*(q:ℝ)) hc]
  have hqr : 0<(q:ℝ) := by exact_mod_cast hq
  rw [sub_div' hqr.ne', abs_div, abs_of_pos hqr, div_le_iff₀ hqr, one_mul, eq, abs_le]
  have hk : ((K%q:ℕ):ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt K hq).le
  have hh : ((H%q:ℕ):ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt H hq).le
  constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (H%q), Nat.cast_nonneg (α:=ℝ) (K%q)]

/-- Window mean square of a divisor sum, with a boundary error uniform in the location. -/
theorem divisor_window_second_moment (K H : ℕ) (h : K≤H) (D : Finset ℕ)
    (hd : ∀ d∈D, 0<d) (a : ℕ → ℝ) :
    |(∑ k ∈ Ioc K H, (∑ d ∈ D, if d ∣ k then a d else 0)^2) -
      ((H:ℝ)-K)*(∑ d ∈ D, ∑ e ∈ D, a d * a e / (d.lcm e))| ≤ (∑ d ∈ D, |a d|)^2 := by
  let W := Ioc K H
  let T := (H:ℝ)-K
  let N (q : ℕ) := (((Ioc K H).filter (q ∣ ·)).card:ℝ)
  have expand : (∑ k ∈ W, (∑ d ∈ D, if d ∣ k then a d else 0)^2) =
      ∑ d ∈ D, ∑ e ∈ D, a d * a e * N (d.lcm e) := by
    simp_rw [sq, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    have pt (k : ℕ) : (if d ∣ k then a d else 0)*(if e ∣ k then a e else 0) =
        if (d.lcm e) ∣ k then a d * a e else 0 := by
      by_cases x : d ∣ k <;> by_cases y : e ∣ k <;> simp [x,y,Nat.lcm_dvd_iff]
    simp_rw [pt]
    simp [W,N,← sum_filter,mul_comm]
  have err (d e : ℕ) (hx : d∈D) (hy : e∈D) :
      |a d*a e*N (d.lcm e)-T*(a d*a e/(d.lcm e))| ≤ |a d| * |a e| := by
    have eq : a d*a e*N (d.lcm e)-T*(a d*a e/(d.lcm e)) =
        (a d*a e)*(N (d.lcm e)-T/(d.lcm e)) := by ring
    rw [eq,abs_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_left
      (multiples_window_discrepancy K H _ h (Nat.lcm_pos (hd _ hx) (hd _ hy))) (by positivity)).trans_eq (mul_one _)
  change |(∑ k ∈ W, _) - T * _| ≤ _
  rw [expand]
  simp_rw [mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D, |a d| * |a e| := by
      refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun d hd' => ?_)
      exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun e he => err d e hd' he)
    _ = _ := by simp_rw [sq,sum_mul,mul_sum]


/-- Transfer an ordinary global mean-square error to both translated sides of the
positive-offset window. Each classical target is used at most once. -/
theorem paired_window_global_error (n K H : ℕ) (hH : H≤n) (e : ℕ→ℝ) :
    (∑ k ∈ Ioc K H, (e (n-k)+e (n+k))^2) ≤ 2*∑ m ∈ range (2*n+1), (e m)^2 := by
  let W := Ioc K H
  let f (k : ℕ) := (e k)^2
  have down : (∑ k ∈ W, f (n-k)) ≤ ∑ m ∈ range n, f m := by
    apply sum_le_sum_of_injOn (fun k => n-k)
    · intro x hx y hy he
      have ha := mem_Ioc.mp hx
      have hb := mem_Ioc.mp hy
      dsimp at he
      omega
    · intro p hp
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
      have ha := mem_Ioc.mp hx
      exact mem_range.mpr (by omega)
    · intro _ _; rfl
    · intro _ _ _; exact sq_nonneg _
  have up : (∑ k ∈ W, f (n+k)) ≤ ∑ m ∈ Ioc n (2*n), f m := by
    apply sum_le_sum_of_injOn (fun k => n+k)
    · intro x _ y _ he
      exact Nat.add_left_cancel he
    · intro p hp
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
      have ha := mem_Ioc.mp hx
      exact mem_Ioc.mpr ⟨by omega,by omega⟩
    · intro _ _; rfl
    · intro _ _ _; exact sq_nonneg _
  have dis : Disjoint (range n) (Ioc n (2*n)) := by
    apply disjoint_left.mpr
    intro m hm ht
    have ha := mem_range.mp hm
    have hb := mem_Ioc.mp ht
    omega
  have total : (∑ m ∈ range n, f m) + (∑ m ∈ Ioc n (2*n), f m) ≤ ∑ m ∈ range (2*n+1), f m := by
    rw [← sum_union dis]
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ha|hb := mem_union.mp hm
      · exact mem_range.mpr (by have := mem_range.mp ha; omega)
      · exact mem_range.mpr (by have := mem_Ioc.mp hb; omega)
    · intro _ _ _; exact sq_nonneg _
  calc
    _ ≤ ∑ k ∈ W, 2*(f (n-k)+f (n+k)) := by
      apply sum_le_sum
      intro k _
      unfold f
      nlinarith only [sq_nonneg (e (n-k)-e (n+k))]
    _ ≤ _ := by
      rw [← mul_sum,sum_add_distrib]
      exact mul_le_mul_of_nonneg_left ((add_le_add down up).trans total) (by norm_num)

private theorem divisor_restore (S : Finset ℕ) (hp : ∀ p∈S, Nat.Prime p) :
    (factorDivisor S).primeFactors = S := Nat.primeFactors_prod hp

private theorem divisor_inj (S : Finset ℕ) (hp : ∀ p∈S, Nat.Prime p) :
    Set.InjOn factorDivisor (S.powerset : Set (Finset ℕ)) := by
  intro A ha B hb h
  rw [← divisor_restore A (fun p hx => hp p (mem_powerset.mp ha hx)),
      ← divisor_restore B (fun p hx => hp p (mem_powerset.mp hb hx)),h]

private theorem divisor_pos (A : Finset ℕ) (hp : ∀ p∈A, Nat.Prime p) : 0 < factorDivisor A :=
  prod_pos fun p h => (hp p h).pos

private theorem weight_le_divisors (A : Finset ℕ) (hp : ∀ p∈A, Nat.Prime p ∧ 3≤p) (y : ℕ) :
    factorTailWeight y A ≤ 2*((factorDivisor A).divisors.card:ℝ)/(factorDivisor A) := by
  have h0 (p) (h : p∈A) : 0≤goldbachFactor p := by
    have hr : (3:ℝ)≤p := by exact_mod_cast (hp p h).2
    exact one_div_nonneg.mpr (by linarith)
  have hpos := divisor_pos A fun p h => (hp p h).1
  have card : A.powerset.card ≤ (factorDivisor A).divisors.card := by
    apply card_le_card_of_injOn factorDivisor _ (divisor_inj A fun p h => (hp p h).1)
    intro B hb
    exact Nat.mem_divisors.mpr ⟨prod_dvd_prod_of_subset _ _ id (mem_powerset.mp hb), hpos.ne'⟩
  have localBound (p) (h : p∈A) :
      goldbachFactor p * p ≤ (if p=3 then (3/2:ℝ) else 1) * 2 := by
    by_cases he : p=3
    · subst p; norm_num [goldbachFactor]
    have hr : (4:ℝ)≤p := by exact_mod_cast (show 4≤p by have := (hp p h).2; omega)
    simp only [he,ite_false,one_mul,goldbachFactor,one_div_mul_eq_div]
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have bd : (∏ p ∈ A, goldbachFactor p * p) ≤ 2*(A.powerset.card:ℝ) := by
    refine (prod_le_prod₀ (fun p h => mul_nonneg (h0 p h) (Nat.cast_nonneg p)) localBound).trans ?_
    rw [prod_mul_distrib]
    simp only [prod_ite_eq',prod_const,card_powerset,Nat.cast_pow,Nat.cast_ofNat]
    split_ifs <;> nlinarith [show 0≤(2:ℝ)^A.card by positivity]
  apply (le_div_iff₀ (by exact_mod_cast hpos : (0:ℝ)<factorDivisor A)).mpr
  calc
    _ ≤ (∏ p ∈ A, goldbachFactor p) * (factorDivisor A:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact sub_le_self _ (prod_nonneg fun p h => by split_ifs <;> first | exact h0 p h | exact le_rfl)
    _ = ∏ p ∈ A, goldbachFactor p * p := by simp [factorDivisor,prod_mul_distrib]
    _ ≤ _ := bd.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast card) (by norm_num))

/-- The unnormalized odd-prime part of the binary Goldbach singular series. -/
noncomputable def oddFactorProduct (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∏ p ∈ S.filter (· ∣ m), (1+goldbachFactor p)

theorem support_expansion (S : Finset ℕ) (hp : ∀ p∈S, Nat.Prime p) (m : ℕ) (f : ℕ→ℝ) :
    (∏ p ∈ S.filter (· ∣ m), (1+f p)) =
      ∑ A ∈ S.powerset, if factorDivisor A ∣ m then ∏ p ∈ A, f p else 0 := by
  have eq : (S.filter (· ∣ m)).powerset = S.powerset.filter (fun A => factorDivisor A ∣ m) := by
    ext A
    simp only [mem_powerset,mem_filter]
    constructor
    · intro h
      exact ⟨h.trans (filter_subset ..), prod_primes_dvd m
        (fun p ha => (hp p (mem_filter.mp (h ha)).1).prime) (fun p ha => (mem_filter.mp (h ha)).2)⟩
    · rintro ⟨hA,hd⟩ p ha
      exact mem_filter.mpr ⟨hA ha,(dvd_prod_of_mem id ha).trans hd⟩
  rw [prod_one_add,eq,sum_filter]

private theorem tail_expansion (S : Finset ℕ) (hp : ∀ p∈S, Nat.Prime p)
    (y m : ℕ) : oddFactorProduct S m - oddFactorProduct (S.filter (·≤y)) m =
      ∑ A ∈ S.powerset, if factorDivisor A ∣ m then factorTailWeight y A else 0 := by
  let b (p : ℕ) := if p≤y then goldbachFactor p else 0
  have eq : oddFactorProduct (S.filter (·≤y)) m = ∏ p ∈ S.filter (· ∣ m), (1+b p) := by
    unfold oddFactorProduct
    rw [prod_filter, prod_filter, prod_filter]
    apply prod_congr rfl
    intro p _
    by_cases h : p≤y <;> by_cases hd : p∣m <;> simp [b,h,hd]
  rw [eq,oddFactorProduct,support_expansion S hp m goldbachFactor,support_expansion S hp m b,← sum_sub_distrib]
  apply sum_congr rfl
  intro A _
  by_cases h : factorDivisor A ∣ m <;> simp [h,b,factorTailWeight]

/-- Actual mean-square error of the cutoff odd-prime product on every positive
integer window (K,H]. The harmonic fourth power pays for its two endpoints. -/
theorem odd_factor_window (S : Finset ℕ) (hp : ∀ p∈S, Nat.Prime p ∧ 3≤p)
    (K H y : ℕ) (hKH : K≤H) (hy : 2≤y) :
    (∑ m ∈ Ioc K H, (oddFactorProduct S m - oddFactorProduct (S.filter (·≤y)) m)^2) ≤
      ((H:ℝ)-K)*(Real.exp 9*(9*Real.exp 9+(3*Real.exp 9)^2)/(y:ℝ)^2) + 4*(harmonicCutoff H)^4 := by
  let D := S.powerset.filter (fun A => factorDivisor A≤H)
  let I := D.image factorDivisor
  let a (d : ℕ) := factorTailWeight y d.primeFactors
  have sub : D⊆S.powerset := filter_subset ..
  have hA {A} (ha : A∈D) (p) (h : p∈A) := hp p (mem_powerset.mp (sub ha) h)
  have inj : Set.InjOn factorDivisor (D : Set (Finset ℕ)) := (divisor_inj S (fun p h => (hp p h).1)).mono sub
  have restore {A} (ha : A∈D) : a (factorDivisor A) = factorTailWeight y A := by
    unfold a
    rw [divisor_restore _ (fun p h => (hA ha p h).1)]
  have inc : I ⊆ Icc 1 H := by
    intro d hd
    obtain ⟨A,ha,rfl⟩ := mem_image.mp hd
    exact mem_Icc.mpr ⟨divisor_pos A (fun p h => (hA ha p h).1), (mem_filter.mp ha).2⟩
  have on_window (m) (hm : m ∈ Ioc K H) :
      oddFactorProduct S m - oddFactorProduct (S.filter (·≤y)) m =
      ∑ d ∈ I, if d ∣ m then a d else 0 := by
    rw [tail_expansion S (fun p h => (hp p h).1),show I = D.image factorDivisor from rfl,sum_image inj]
    refine (sum_subset sub (fun A ha hnot => ?_)).symm.trans ?_
    · have hg : H<factorDivisor A := by
        by_contra! hc
        exact hnot (mem_filter.mpr ⟨ha,hc⟩)
      have hm' := mem_Ioc.mp hm
      have hnd : ¬factorDivisor A ∣ m := fun hd => by have := Nat.le_of_dvd (by omega : 0 < m) hd; omega
      simp [hnd]
    · exact sum_congr rfl fun A ha => by rw [restore ha]
  have main := factorTail_divisor_bound S hp y hy D sub
  have gram : (∑ d ∈ I, ∑ e ∈ I, a d*a e/(d.lcm e)) =
      ∑ A ∈ D, ∑ B ∈ D, factorTailWeight y A*factorTailWeight y B/((factorDivisor A).lcm (factorDivisor B):ℕ) := by
    simp_rw [I,sum_image inj]
    apply sum_congr rfl
    intro A ha
    apply sum_congr rfl
    intro B hb
    rw [restore ha,restore hb]
  have mass : (∑ d ∈ I, |a d|) ≤ 2*(harmonicCutoff H)^2 := by
    calc
      _ ≤ ∑ d ∈ I, 2*((d.divisors.card:ℝ)/d) := by
        apply sum_le_sum
        intro d hd
        obtain ⟨A,ha,rfl⟩ := mem_image.mp hd
        rw [restore ha,abs_of_nonneg (factorTailWeight_nonneg y _ fun p h => (hA ha p h).2),← mul_div_assoc]
        exact weight_le_divisors A (hA ha) y
      _ ≤ ∑ d ∈ Icc 1 H, 2*((d.divisors.card:ℝ)/d) :=
        sum_le_sum_of_subset_of_nonneg inc fun _ _ _ => by positivity
      _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (harmonic_divisors H) (by norm_num)
  have bound := (abs_le.mp (divisor_window_second_moment K H hKH I (fun d h => (mem_Icc.mp (inc h)).1) a)).2
  rw [gram] at bound
  have hT : 0≤(H:ℝ)-K := sub_nonneg.mpr (by exact_mod_cast hKH)
  have hs := (sq_le_sq₀ (sum_nonneg fun d _ => abs_nonneg (a d)) (by positivity)).mpr mass
  calc
    _ = ∑ m ∈ Ioc K H, (∑ d ∈ I, if d ∣ m then a d else 0)^2 :=
      sum_congr rfl fun m hm => by rw [on_window m hm]
    _ ≤ _ := by nlinarith only [bound, mul_le_mul_of_nonneg_left main hT, hs]


def shapePrimes (X : ℕ) := (Nat.primesLE X).filter (3≤·)

/-- Binary Goldbach singular series truncated at y, with the common factor 2 C₂
removed. Parity is retained even when the set of odd primes is empty. -/
noncomputable def binaryShape (y m : ℕ) : ℝ :=
  if 2 ∣ m then oddFactorProduct (shapePrimes y) m else 0

/-- Each retained local factor is at most its prime. This crude uniform bound
also covers residue zero, where every local factor is present. -/
theorem abs_binaryShape_le_factorial (y m : ℕ) : |binaryShape y m| ≤ y.factorial := by
  unfold binaryShape oddFactorProduct
  split_ifs
  · let S := (shapePrimes y).filter (· ∣ m)
    have prime (p) (hp : p∈S) : 3≤p ∧ p≤y := by
      obtain ⟨hs,_⟩ := mem_filter.mp hp
      obtain ⟨hy,hl⟩ := mem_filter.mp hs
      exact ⟨hl,(Nat.mem_primesLE.mp hy).1⟩
    have facts (p) (hp : p∈S) : 0≤1+goldbachFactor p ∧ 1+goldbachFactor p≤p := by
      have hr : (3:ℝ)≤p := by exact_mod_cast (prime p hp).1
      have hd : 0<(p:ℝ)-2 := by linarith
      have hu : 1/((p:ℝ)-2)≤1 := (div_le_iff₀ hd).mpr (by linarith)
      unfold goldbachFactor
      exact ⟨by positivity,by linarith⟩
    change |∏ p ∈ S, (1+goldbachFactor p)| ≤ _
    rw [abs_of_nonneg (prod_nonneg fun p hp => (facts p hp).1)]
    calc
      _ ≤ ∏ p ∈ S, (p:ℝ) := prod_le_prod₀ (fun p hp => (facts p hp).1) (fun p hp => (facts p hp).2)
      _ ≤ ∏ p ∈ Ico 1 (y+1), (p:ℝ) := by
        apply prod_le_prod_of_subset_of_one_le₀
        · intro p hp
          obtain ⟨hl,hu⟩ := prime p hp
          exact mem_Ico.mpr ⟨by omega,by omega⟩
        · intro p _; positivity
        · intro p hp _; exact_mod_cast (mem_Ico.mp hp).1
      _ = _ := by rw [← Nat.cast_prod,prod_Ico_id_eq_factorial]
  · simp

/-- Every factor in the cutoff profile only depends on the residue modulo y!. -/
theorem binaryShape_residue (y m : ℕ) (hy : 2≤y) :
    binaryShape y (m % y.factorial) = binaryShape y m := by
  have two : 2 ∣ y.factorial := Nat.dvd_factorial (by decide) hy
  have filters : (shapePrimes y).filter (· ∣ m % y.factorial) =
      (shapePrimes y).filter (· ∣ m) := by
    ext p
    by_cases h : p ∈ shapePrimes y
    · have hpy := Nat.mem_primesLE.mp (mem_filter.mp h).1
      simpa only [mem_filter,h,true_and] using
        (Nat.dvd_mod_iff (Nat.dvd_factorial hpy.2.pos hpy.1) : p ∣ m % y.factorial ↔ p ∣ m)
    · simp [h]
  simp only [binaryShape,oddFactorProduct,Nat.dvd_mod_iff two,filters]

/-- Uniform bound for the normalized classical singular series and its actual periodic
approximation on every window of positive integers. -/
theorem binary_shape_window (K H y : ℕ) (hKH : K≤H) (hy : 2≤y) :
    (∑ m ∈ Ioc K H, (binaryShape m m - binaryShape y m)^2) ≤
      ((H:ℝ)-K)*(Real.exp 9*(9*Real.exp 9+(3*Real.exp 9)^2)/(y:ℝ)^2) + 4*(harmonicCutoff H)^4 := by
  let S := shapePrimes (max H y)
  have hp (p) (h : p∈S) : Nat.Prime p ∧ 3≤p :=
    ⟨Nat.prime_of_mem_primesLE (mem_filter.mp h).1,(mem_filter.mp h).2⟩
  have low : S.filter (·≤y) = shapePrimes y := by
    ext p
    simp only [S,shapePrimes,mem_filter,Nat.mem_primesLE]
    exact ⟨fun ⟨⟨⟨_,pr⟩,h3⟩,h⟩ => ⟨⟨h,pr⟩,h3⟩,
      fun ⟨⟨h,pr⟩,h3⟩ => ⟨⟨⟨h.trans (le_max_right ..),pr⟩,h3⟩,h⟩⟩
  apply le_trans _ (odd_factor_window S hp K H y hKH hy)
  apply sum_le_sum
  intro m hm
  have hm' := mem_Ioc.mp hm
  have full : (shapePrimes m).filter (· ∣ m) = S.filter (· ∣ m) := by
    ext p
    simp only [S,shapePrimes,mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨h,pr⟩,h3⟩,hd⟩
      exact ⟨⟨⟨by omega,pr⟩,h3⟩,hd⟩
    · rintro ⟨⟨⟨_,pr⟩,h3⟩,hd⟩
      exact ⟨⟨⟨Nat.le_of_dvd (by omega) hd,pr⟩,h3⟩,hd⟩
  by_cases he : 2 ∣ m
  · simp [he,binaryShape,oddFactorProduct,full,low]
  · simpa only [binaryShape,he,ite_false,sub_self,zero_pow (by decide : 2≠0)] using
      sq_nonneg (oddFactorProduct S m - oddFactorProduct (S.filter (·≤y)) m)

#print axioms binary_shape_window
#print axioms binaryShape_residue
#print axioms paired_window_global_error
end GoldbachMinor
