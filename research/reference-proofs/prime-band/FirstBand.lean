import TailPrefixes

namespace GoldbachMinor

open Finset GoldbachWeight Filter
open scoped Topology

/-- Keep the small denominators exact and replace the sine by its argument at larger denominators. -/
noncomputable def firstBandCoefficient (Q n B k : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, ram q k *
    (if q ≤ B then Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*k)
     else 2*(Q:ℝ)/((q:ℝ)*n))

private theorem pair_mass_bound (n k : ℕ) (hn : 0<n) :
    |pairMass n k (high n)| ≤ (Real.log 4*n) * (2*Real.log n) := by
  let S (p : ℕ) := (range (n+1)).filter (fun r => (offset n p r).natAbs = k)
  have card (p : ℕ) : (S p).card ≤ 2 := by
    have sub : S p ⊆ {n+k-p, n-k-p} := by
      intro r hr
      have hm := (mem_filter.mp hr).2
      have hp := Int.natAbs_eq_natAbs_iff.mp (show (offset n p r).natAbs = (k:ℤ).natAbs by simpa using hm)
      simp only [mem_insert,mem_singleton]
      unfold offset at hp
      omega
    exact (card_le_card sub).trans (card_le_two)
  have row (p : ℕ) : (∑ r ∈ S p, |high n r|) ≤ 2*Real.log n := by
    calc
      _ ≤ ∑ _r ∈ S p, Real.log n := sum_le_sum (fun r hr =>
        high_le_log n r hn (by have := mem_range.mp (mem_filter.mp hr).1; omega))
      _ = ((S p).card:ℝ)*Real.log n := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card p)
        (Real.log_nonneg (by exact_mod_cast hn))
  unfold pairMass
  simp_rw [← sum_filter]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ p ∈ range (n+1), |high n p| *(2*Real.log n) := by
      apply sum_le_sum
      intro p _
      change |∑ r ∈ S p, high n p * high n r| ≤ _
      rw [← mul_sum, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (Finset.abs_sum_le_sum_abs ..).trans (row p)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (high_mass n) (by
        have := Real.log_nonneg (by exact_mod_cast hn : (1:ℝ)≤n); positivity)

private theorem wave_error {Q n B k q : ℕ} (hn : 0<n) (hB : 0<B) (hk : 0<k)
    (hq : B<q) (hkn : k*Q≤n) :
    |Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*k) - 2*(Q:ℝ)/((q:ℝ)*n)| ≤
      ((2*(Q:ℝ)/n)*((2*Real.pi/(B:ℝ))^2/6))/(q:ℝ) := by
  let x := 2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))
  have hp : 0<Real.pi*(k:ℝ) := mul_pos Real.pi_pos (by exact_mod_cast hk)
  have hb : (0:ℝ)<B := by exact_mod_cast hB
  have hqr : (0:ℝ)<q := by exact_mod_cast (lt_trans hB hq)
  have hnr : (0:ℝ)<n := by exact_mod_cast hn
  have hx : 0≤x := by dsimp [x]; positivity
  have hxle : x ≤ 2*Real.pi/(B:ℝ) := by
    have hmul : (k:ℝ)*Q ≤ n := by exact_mod_cast hkn
    have hden : (B:ℝ) ≤ q := by exact_mod_cast hq.le
    dsimp [x]
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_right hmul hb.le,
      mul_le_mul_of_nonneg_left hden hnr.le]
  have he : x / (Real.pi*k) = 2*(Q:ℝ)/((q:ℝ)*n) := by dsimp [x]; field_simp
  change |Real.sin x / _ - _| ≤ _
  rw [← he, ← sub_div, abs_div, abs_of_pos hp, abs_sub_comm]
  have hs := Real.abs_sub_sin_le x
  rw [abs_of_nonneg hx] at hs
  calc
    _ ≤ (x^3/6)/(Real.pi*k) := div_le_div_of_nonneg_right hs hp.le
    _ ≤ (x*((2*Real.pi/(B:ℝ))^2)/6)/(Real.pi*k) := by
      apply div_le_div_of_nonneg_right _ hp.le
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [show x^3=x*x^2 by ring]
      gcongr
    _ = _ := by dsimp [x]; field_simp

private theorem coefficient_error (Q n B k : ℕ) (hn : 0<n) (hB : 0<B) (hk : 0<k)
    (hkn : k*Q ≤ n) :
    |majorCoefficient Q n k - firstBandCoefficient Q n B k| ≤
    ∑ q ∈ Icc 1 Q, (((2*(Q:ℝ)/n)*((2*Real.pi/(B:ℝ))^2/6))/(q:ℝ)) * |ram q k| := by
  unfold majorCoefficient firstBandCoefficient
  rw [← sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun q _ => ?_)
  rw [← mul_sub,abs_mul,mul_comm]
  by_cases hq : q ≤ B
  · simp only [hq, ite_true,sub_self,abs_zero,zero_mul]
    positivity
  · simp only [hq, ite_false]
    exact mul_le_mul_of_nonneg_right (wave_error hn hB hk (by omega) hkn) (abs_nonneg _)

noncomputable def firstBandSum (n K H : ℕ) (coefficient : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Ioc K H, pairMass n k (high n) * coefficient k

/-- The estimate holds on every subinterval (K,H] with H*Q ≤ n. -/
theorem first_band_error (Q n B K H : ℕ) (hn : 0<n) (hB : 0<B) (hH : H*Q≤n) :
    |firstBandSum n K H (majorCoefficient Q n) -
      firstBandSum n K H (firstBandCoefficient Q n B)| ≤
      (Real.log 4*n)*(2*Real.log n)*
        (((2*(Q:ℝ)/n)*((2*Real.pi/(B:ℝ))^2/6))*H*(harmonicCutoff Q)^2) := by
  let A := (2*(Q:ℝ)/n)*((2*Real.pi/(B:ℝ))^2/6)
  let M := (Real.log 4*n)*(2*Real.log n)
  have ha : 0≤A := by dsimp [A]; positivity
  have hm : 0≤M := by dsimp [M]; have := Real.log_nonneg (by exact_mod_cast hn : (1:ℝ)≤n); positivity
  have sub : Ioc K H ⊆ Icc 1 H := by intro k h; obtain ⟨_,_⟩ := mem_Ioc.mp h; apply mem_Icc.mpr; omega
  have err : (∑ k ∈ Ioc K H, |majorCoefficient Q n k - firstBandCoefficient Q n B k|) ≤
      A*H*(harmonicCutoff Q)^2 := by
    calc
      _ ≤ ∑ k ∈ Icc 1 H, |majorCoefficient Q n k - firstBandCoefficient Q n B k| :=
        sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => abs_nonneg _)
      _ ≤ ∑ k ∈ Icc 1 H, ∑ q ∈ Icc 1 Q, (A/q)*|ram q k| := by
        apply sum_le_sum
        intro k hk
        exact coefficient_error Q n B k hn hB (mem_Icc.mp hk).1 ((Nat.mul_le_mul_right Q (mem_Icc.mp hk).2).trans hH)
      _ = ∑ q ∈ Icc 1 Q, (A/q)*(∑ k ∈ Icc 1 H, |ram q k|) := by rw [sum_comm]; simp_rw [mul_sum]
      _ ≤ ∑ q ∈ Icc 1 Q, (A/q)*((H:ℝ)*q.divisors.card) := by
        exact sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (ram_frequency_sum q H) (by positivity))
      _ = (A*H)*(∑ q ∈ Icc 1 Q, (q.divisors.card:ℝ)/q) := by
        rw [mul_sum]; apply sum_congr rfl; intro q _; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_divisors Q) (by positivity)
  unfold firstBandSum
  rw [← sum_sub_distrib]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ k ∈ Ioc K H, M*|majorCoefficient Q n k - firstBandCoefficient Q n B k| := by
      apply sum_le_sum
      intro k _
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_right (pair_mass_bound n k hn) (abs_nonneg _)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left err hm

/-- The first block of offsets goes up to n/Q. -/
def firstBandEnd (n : ℕ) := n / catalogueCutoff n

theorem catalogue_first_band_error (n K : ℕ) (hn : 0<n) :
    let Q := catalogueCutoff n
    let L := logWidth n
    let H := firstBandEnd n
    |firstBandSum n K H (majorCoefficient Q n) -
      firstBandSum n K H (firstBandCoefficient Q n L)| ≤
      (4*Real.log 4*(2*Real.pi)^2/6)*n*((1+2*Real.log (L:ℝ))^2/L) := by
  let Q := catalogueCutoff n
  let L := (logWidth n:ℝ)
  let H := firstBandEnd n
  have hl : 0<logWidth n := Nat.succ_pos _
  have hL : 0<L := by dsimp only [L]; exact_mod_cast hl
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hH : H*Q ≤ n := Nat.div_mul_le_self n _
  have hb : (H:ℝ)*Q ≤ n := by exact_mod_cast hH
  have hhar : 0 ≤ harmonicCutoff Q := by unfold harmonicCutoff; positivity
  calc
    _ ≤ _ := first_band_error Q n (logWidth n) K H hn hl hH
    _ ≤ (Real.log 4*n)*(2*L)*(((2*(Q:ℝ)/n)*((2*Real.pi/L)^2/6))*H*
          (1+2*Real.log L)^2) := by
      gcongr
      · exact log_n_le_width n hn
      · exact cutoff_harmonic n
    _ = (4*Real.log 4*(2*Real.pi)^2/6)*((H:ℝ)*Q)*((1+2*Real.log L)^2/L) := by
      field_simp
      ring
    _ ≤ _ := by gcongr

/-- The error is sublinear uniformly over where the surviving frequencies begin. -/
theorem first_band_negligible (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, ∀ n≥N, ∀ K : ℕ,
    |firstBandSum n K (firstBandEnd n) (majorCoefficient (catalogueCutoff n) n) -
      firstBandSum n K (firstBandEnd n) (firstBandCoefficient (catalogueCutoff n) n (logWidth n))|
      ≤ ε*n := by
  have hl : Tendsto (fun n : ℕ => (logWidth n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp logWidth_tends
  have lim := (log_bound_ratio.comp hl).const_mul (4*Real.log 4*(2*Real.pi)^2/6)
  rw [mul_zero] at lim
  obtain ⟨N,hN⟩ := eventually_atTop.mp (lim.eventually_lt_const hε)
  refine ⟨max 1 N,fun n hn K => (catalogue_first_band_error n K (by omega)).trans ?_⟩
  have h := mul_le_mul_of_nonneg_right (hN n (by omega)).le (show 0≤(n:ℝ) by positivity)
  dsimp only [Function.comp_apply] at h
  convert h using 1; ring

/-- Total prime-pair weight with absolute offset in (K,H] divisible by d. -/
noncomputable def divisibleMass (n K H d : ℕ) : ℝ :=
  ∑ k ∈ (Ioc K H).filter (d ∣ ·), pairMass n k (high n)

private theorem ram_against_mass (n K H q : ℕ) :
    (∑ k ∈ Ioc K H, pairMass n k (high n) * ram q k) =
    ∑ d ∈ q.divisors, ((d:ℝ) * (ArithmeticFunction.moebius (q/d):ℝ)) * divisibleMass n K H d := by
  unfold ram divisibleMass
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases h : d ∣ k <;> simp [h]
  ring

/-- On large denominators only divisibility of the offset remains in the linearized model. -/
theorem first_band_residue_formula (Q n B K H : ℕ) (hB : 1≤B) (hBQ : B≤Q) :
    firstBandSum n K H (firstBandCoefficient Q n B) =
      firstBandSum n K H (fun k =>
        ∑ q ∈ Icc 1 B, ram q k * (Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*k))) +
      ∑ q ∈ Ioc B Q, (2*(Q:ℝ)/((q:ℝ)*n)) *
        ∑ d ∈ q.divisors, ((d:ℝ)*(ArithmeticFunction.moebius (q/d):ℝ)) * divisibleMass n K H d := by
  have partition : Icc 1 Q = Icc 1 B ∪ Ioc B Q := by
    ext q
    simp only [mem_Icc,mem_union,mem_Ioc]
    omega
  have disj : Disjoint (Icc 1 B) (Ioc B Q) := by
    apply Finset.disjoint_left.mpr
    intro q h₁ h₂
    exact (not_lt_of_ge (mem_Icc.mp h₁).2) (mem_Ioc.mp h₂).1
  have split (k : ℕ) : firstBandCoefficient Q n B k =
      (∑ q ∈ Icc 1 B, ram q k * (Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*k))) +
      ∑ q ∈ Ioc B Q, ram q k * (2*(Q:ℝ)/((q:ℝ)*n)) := by
    unfold firstBandCoefficient
    rw [partition,sum_union disj]
    congr 1
    · exact sum_congr rfl (fun q h => by simp [(mem_Icc.mp h).2])
    · exact sum_congr rfl (fun q h => by simp [not_le.mpr (mem_Ioc.mp h).1])
  unfold firstBandSum
  simp_rw [split,mul_add,sum_add_distrib]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← mul_sum, ← ram_against_mass, mul_sum]
  apply sum_congr rfl
  intro k _
  ring

/-- On the first block use the mixed coefficient; on every higher offset keep the exact kernel. -/
noncomputable def modelLoss (n : ℕ) : ℝ :=
  firstBandSum n (primeBandWidth n) n (fun k =>
    if k ≤ firstBandEnd n then firstBandCoefficient (catalogueCutoff n) n (logWidth n) k
    else majorCoefficient (catalogueCutoff n) n k)

private theorem loss_difference (n : ℕ) :
    firstBandSum n (primeBandWidth n) n (majorCoefficient (catalogueCutoff n) n) - modelLoss n =
    firstBandSum n (primeBandWidth n) (firstBandEnd n) (majorCoefficient (catalogueCutoff n) n) -
    firstBandSum n (primeBandWidth n) (firstBandEnd n) (firstBandCoefficient (catalogueCutoff n) n (logWidth n)) := by
  have hle : firstBandEnd n ≤ n := Nat.div_le_self ..
  have sub : Ioc (primeBandWidth n) (firstBandEnd n) =
      (Ioc (primeBandWidth n) n).filter (fun k => k≤firstBandEnd n) := by ext k; simp; omega
  unfold modelLoss firstBandSum
  rw [sub, sum_filter, sum_filter, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  by_cases h : k≤firstBandEnd n <;> simp [h]

private theorem trimmed_as_loss (n : ℕ) :
    trimmedBulk (catalogueCutoff n) n (primeBandWidth n) (high n) =
    pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) -
      firstBandSum n (primeBandWidth n) n (majorCoefficient (catalogueCutoff n) n) := by
  rw [trimmed_frequency_sum]
  congr 1
  apply sum_congr rfl
  intro k _
  unfold tailWave majorCoefficient
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [← sum_mul]
  ring

/-- The exact frozen floor is equivalent to bounding the signed loss with the first block linearized. -/
theorem catalogue_first_band_iff : FrozenBulk.BulkFloor ↔
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      modelLoss n ≤ pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  rw [catalogue_prime_band_iff]
  simp_rw [trimmed_as_loss]
  constructor <;> intro h ε he <;>
    obtain ⟨N,hN⟩ := h (ε/2) (half_pos he) <;>
    obtain ⟨M,hM⟩ := first_band_negligible (ε/2) (half_pos he) <;>
    refine ⟨max N M,fun n hn hev => ?_⟩ <;>
    have herr := hM n (by omega) (primeBandWidth n) <;>
    rw [← loss_difference] at herr <;>
    obtain ⟨hl,hu⟩ := abs_le.mp herr <;> linarith only [hl,hu,hN n (by omega) hev]

#print axioms catalogue_first_band_error
#print axioms catalogue_first_band_iff

end GoldbachMinor
