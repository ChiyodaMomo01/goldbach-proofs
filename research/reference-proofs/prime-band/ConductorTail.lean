import ShortfallDensity

namespace GoldbachMinor
open Finset Filter ArithmeticFunction
open scoped Topology

/-- Sum over positive targets only. Each divisor contributes its size times
at most the number of its positive multiples up to the endpoint. -/
theorem ram_absolute_prefix (q X : ℕ) :
    (∑ n ∈ Ioc 0 X, |ram q n|) ≤ (X:ℝ)*q.divisors.card := by
  let cell (a n : ℕ) : ℝ := if a ∣ n then a else 0
  have row (n : ℕ) : |ram q n| ≤ ∑ a ∈ q.divisors, cell a n := by
    unfold ram
    apply (abs_sum_le_sum_abs ..).trans
    apply sum_le_sum
    intro a _
    have mu : |(moebius (q/a):ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    rw [abs_mul]
    by_cases h : a ∣ n
    · simp only [h, ite_true, cell, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) a)]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) mu
    · simp [cell,h]
  have col (a : ℕ) : (∑ n ∈ Ioc 0 X, cell a n) ≤ X := by
    simp only [cell, ← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    exact_mod_cast Nat.div_mul_le_self X a
  calc
    _ ≤ ∑ n ∈ Ioc 0 X, ∑ a ∈ q.divisors, cell a n := sum_le_sum fun n _ => row n
    _ = _ := sum_comm
    _ ≤ ∑ _a ∈ q.divisors, (X:ℝ) := sum_le_sum fun a _ => col a
    _ = _ := by simp [mul_comm]

/-- Summable majorant for the target average of absolute Ramanujan coefficients. -/
noncomputable def conductorMass (q : ℕ) : ℝ :=
  q.divisors.card * ((moebius q:ℝ)/q.totient)^2

private theorem mass_nonneg (q : ℕ) : 0 ≤ conductorMass q := by
  unfold conductorMass; positivity

private noncomputable def primeMass (p : ℕ) : ℝ := 2/((p-1:ℕ):ℝ)^2

private theorem mass_factorization (q : ℕ) (sq : Squarefree q) :
    conductorMass q = ∏ p ∈ q.primeFactors, primeMass p := by
  have card : q.divisors.card = ∏ _p ∈ q.primeFactors, 2 := by
    rw [Nat.card_divisors sq.ne_zero]
    apply prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree sq (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
  have phi : q.totient = ∏ p ∈ q.primeFactors, (p-1) := by
    have h := Nat.totient_mul_prod_primeFactors q
    rw [Nat.prod_primeFactors_of_squarefree sq, Nat.mul_comm q.totient] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero sq.ne_zero) h
  have mu : (moebius q:ℝ)^2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree sq
  simp only [conductorMass, div_pow, mu, card, phi, Nat.cast_prod, Nat.cast_ofNat,
    mul_one_div, primeMass, prod_div_distrib, prod_pow]

private theorem summable_squarefree_product (f g : ℕ → ℝ)
    (hf : ∀ q, 0 ≤ f q) (hg : ∀ p, 0 ≤ g p) (hs : Summable g)
    (outside : ∀ q, ¬ Squarefree q → f q = 0)
    (factors : ∀ q, Squarefree q → f q = ∏ p ∈ q.primeFactors, g p) : Summable f := by
  classical
  let term (A : Finset ℕ) := ∏ p ∈ A, g p
  have pos (A) : 0 ≤ term A := prod_nonneg fun p _ => hg p
  have total : Summable term := summable_finsetProd_of_summable_nonneg hg hs
  apply summable_of_sum_range_le (c := ∑' A, term A) hf
  intro N
  let D := (range N).filter Squarefree
  have restrict : (∑ q ∈ range N, f q) = ∑ q ∈ D, f q := by
    rw [sum_filter]
    apply sum_congr rfl
    intro q _
    by_cases h : Squarefree q <;> simp [h, outside]
  rw [restrict]
  apply le_trans _ (total.sum_le_tsum (D.image Nat.primeFactors) (fun A _ => pos A))
  apply sum_le_sum_of_injOn Nat.primeFactors _ (Subset.rfl) _ (fun A _ _ => pos A)
  · intro a ha b hb eq
    rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2,
        ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2, eq]
  · intro q hq
    exact (factors q (mem_filter.mp hq).2).le

theorem conductorMass_summable : Summable conductorMass := by
  apply summable_squarefree_product conductorMass primeMass mass_nonneg
    (fun p => by unfold primeMass; positivity) _ _ mass_factorization
  · apply (summable_nat_add_iff 1).mp
    simpa [primeMass, div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left 2
  · intro q h
    simp [conductorMass, moebius_eq_zero_of_not_squarefree h]

/-- The square-root moment of the absolute conductor majorant is finite. -/
theorem conductorMass_sqrt_summable :
    Summable (fun q : ℕ => Real.sqrt q * conductorMass q) := by
  let g := fun p : ℕ => Real.sqrt p * primeMass p
  apply summable_squarefree_product _ g (fun q => mul_nonneg (Real.sqrt_nonneg _) (mass_nonneg _))
    (fun p => by dsimp [g, primeMass]; positivity)
  · apply ((Real.summable_nat_rpow.mpr (show (-3/2:ℝ) < -1 by norm_num)).mul_left 8).of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop 2] with p hp
    have rp : (0:ℝ) < p := by exact_mod_cast (show 0<p by omega)
    have pred : ((p-1:ℕ):ℝ) = (p:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤p)]; norm_num
    have two : (2:ℝ) ≤ p := by exact_mod_cast hp
    have fac : (p:ℝ)^2 ≤ 4*((p:ℝ)-1)^2 := by
      have h := sq_le_sq' (by linarith : -(2*((p:ℝ)-1)) ≤ p) (by linarith : (p:ℝ) ≤ 2*(p-1))
      nlinarith only [h]
    have powid : (p:ℝ)^(-3/2:ℝ) = Real.sqrt p / (p:ℝ)^2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (p:ℝ) 2, ← Real.rpow_sub rp]
      norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g,primeMass]; positivity : 0 ≤ g p)]
    dsimp only [g,primeMass]
    rw [pred,powid, ← mul_div_assoc, ← mul_div_assoc]
    rw [div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < (p:ℝ)-1)) (sq_pos_of_pos rp)]
    nlinarith only [mul_le_mul_of_nonneg_left fac (Real.sqrt_nonneg (p:ℝ))]
  · intro q h
    simp [conductorMass, moebius_eq_zero_of_not_squarefree h]
  · intro q hq
    have prodId : (q:ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]
    rw [mass_factorization q hq, prodId, Real.sqrt_prod _ (fun _ _ => Nat.cast_nonneg _), ← prod_mul_distrib]

/-- A fixed finite constant for the absolute denominator tail on every window. -/
noncomputable def conductorSqrtMoment : ℝ := ∑' q : ℕ, Real.sqrt q * conductorMass q

/-- Sum a bounded cutoff error that also grows at most linearly with q/Q. -/
theorem conductor_cutoff_rate (Q : ℕ) (hQ : 0 < Q) (A : ℝ) (hA : 0 ≤ A)
    (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) (cap : ∀ q, 0 < q → f q ≤ A)
    (slope : ∀ q, 0 < q → f q * Q ≤ A * q) :
    (∑' q, conductorMass q * f q) ≤ A * conductorSqrtMoment / Real.sqrt Q := by
  have Qp : (0:ℝ) < Q := by exact_mod_cast hQ
  have root := Real.sqrt_pos.mpr Qp
  let g := fun q : ℕ => (A/Real.sqrt Q) * (Real.sqrt q * conductorMass q)
  have sg : Summable g := conductorMass_sqrt_summable.mul_left _
  have le (q : ℕ) : conductorMass q * f q ≤ g q := by
    rcases Nat.eq_zero_or_pos q with rfl|hq
    · simp [g,conductorMass]
    have mono : f q * Real.sqrt Q ≤ A * Real.sqrt q := by
      by_cases h : q ≤ Q
      · have order := Real.sqrt_le_sqrt (show (q:ℝ) ≤ Q by exact_mod_cast h)
        apply le_of_mul_le_mul_right (a:=Real.sqrt Q) _ root
        calc
          _ = f q * Q := by rw [mul_assoc,Real.mul_self_sqrt Qp.le]
          _ ≤ A * q := slope q hq
          _ = A * Real.sqrt q * Real.sqrt q := by rw [mul_assoc,Real.mul_self_sqrt (Nat.cast_nonneg _)]
          _ ≤ _ := mul_le_mul_of_nonneg_left order (mul_nonneg hA (Real.sqrt_nonneg _))
      · exact (mul_le_mul_of_nonneg_right (cap q hq) root.le).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_of_not_ge h))) hA)
    have row := mul_le_mul_of_nonneg_left ((le_div_iff₀ root).mpr mono) (mass_nonneg q)
    exact row.trans_eq (by dsimp [g]; ring)
  apply ((sg.of_nonneg_of_le (fun q => mul_nonneg (mass_nonneg q) (hf q)) le).tsum_le_tsum le sg).trans_eq
  dsimp only [g,conductorSqrtMoment]
  rw [tsum_mul_left]
  ring

theorem conductor_tail_rate (K : ℕ) :
    (∑' r : ℕ, conductorMass (r+(K+1))) ≤ conductorSqrtMoment / Real.sqrt (K+1:ℕ) := by
  let w := fun q : ℕ => Real.sqrt q * conductorMass q
  let shift := fun r : ℕ => r+(K+1)
  have hs : Summable (w ∘ shift) := (summable_nat_add_iff (K+1)).mpr conductorMass_sqrt_summable
  have tail := (summable_nat_add_iff (K+1)).mpr conductorMass_summable
  rw [le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos K)), ← tsum_mul_right]
  apply (tail.mul_right _).tsum_le_tsum _ hs |>.trans
    (tsum_comp_le_tsum_of_inj conductorMass_sqrt_summable
      (fun q => mul_nonneg (Real.sqrt_nonneg _) (mass_nonneg q))
      (show Function.Injective shift from fun a b eq => Nat.add_right_cancel eq))
  intro r
  change conductorMass (shift r)*_ ≤ Real.sqrt (shift r)*conductorMass (shift r)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_add_left (K+1) r)))
    (mass_nonneg _)

#print axioms conductorMass_summable

/-- Absolute coefficient of the normalized model before the arc weight. -/
noncomputable def ramWeight (q n : ℕ) : ℝ :=
  ram q n * ((moebius q:ℝ)/q.totient)^2

/-- Weighted average on any positive dyadic window; the constant depends on
the fixed modulus alone, even when the denominator is larger than the window. -/
theorem dyadic_ramWeight_bound (d j q : ℕ) (hd : 0 < d) (hj : 0 < j) :
    dyadicRatio d (fun n => n*|ramWeight q n|) j ≤ 4*d*conductorMass q := by
  let X := 2*d*j
  let T := Ico j (2*j)
  let W := ∑ i ∈ T, (d:ℝ)*i
  have dp : 0 < (d:ℝ) := by exact_mod_cast hd
  have jp : 0 < (j:ℝ) := by exact_mod_cast hj
  have card : T.card = j := by simp [T]; omega
  have scale : (d:ℝ)*j*j ≤ W := by
    have h := sum_le_sum (s:=T) fun i hi =>
      mul_le_mul_of_nonneg_left (show (j:ℝ) ≤ i by exact_mod_cast (mem_Ico.mp hi).1) dp.le
    simpa [W,card,mul_comm,mul_left_comm] using h
  have wp := (mul_pos (mul_pos dp jp) jp).trans_le scale
  have incl (i) (hi : i ∈ T) : d*i ∈ Ioc 0 X := by
    obtain ⟨lo,hi⟩ := mem_Ico.mp hi
    exact mem_Ioc.mpr ⟨Nat.mul_pos hd (hj.trans_le lo),
      (Nat.mul_le_mul_left d hi.le).trans_eq (by dsimp [X]; ring)⟩
  have bound : (∑ i ∈ T, (↑(d*i):ℝ)*|ramWeight q (d*i)|) ≤
      (X:ℝ)*((X:ℝ)*conductorMass q) := by
    calc
      _ ≤ ∑ n ∈ Ioc 0 X, (X:ℝ)*|ramWeight q n| := by
        apply sum_le_sum_of_injOn (fun i => d*i)
        · intro a _ b _ e; exact Nat.eq_of_mul_eq_mul_left hd e
        · intro n h; obtain ⟨i,hi,rfl⟩ := mem_image.mp h; exact incl i hi
        · intro i hi
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Ioc.mp (incl i hi)).2) (abs_nonneg _)
        · intro n _ _; positivity
      _ = (X:ℝ)*((∑ n ∈ Ioc 0 X, |ram q n|)*((moebius q:ℝ)/q.totient)^2) := by
        simp only [ramWeight, abs_mul, abs_of_nonneg (sq_nonneg ((moebius q:ℝ)/q.totient)), ← mul_sum, ← sum_mul]
      _ ≤ _ := by
        dsimp only [conductorMass]
        rw [← mul_assoc (X:ℝ) (q.divisors.card:ℝ)]
        gcongr
        exact ram_absolute_prefix q X
  change _ / W ≤ _
  rw [div_le_iff₀ wp]
  apply bound.trans
  calc
    (X:ℝ)*((X:ℝ)*conductorMass q) = (4*d*conductorMass q)*((d:ℝ)*j*j) := by
      simp only [X, Nat.cast_mul, Nat.cast_ofNat]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left scale (by have := mass_nonneg q; positivity)

/-- Part of the catalogue main term with denominators strictly above K. -/
noncomputable def catalogueConductorTail (K n : ℕ) : ℝ :=
  n * ∑ q ∈ Ioc K (catalogueCutoff n),
    ramWeight q n * archimedeanMass ((catalogueCutoff n:ℝ)/q)

private theorem tail_row (K n Q : ℕ) (hQ : catalogueCutoff n ≤ Q) :
    |catalogueConductorTail K n| ≤ ∑ q ∈ Ioc K Q, (n:ℝ)*|ramWeight q n| := by
  rw [catalogueConductorTail, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _), ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (abs_sum_le_sum_abs ..).trans
  apply le_trans _ (sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hQ) (fun i _ _ => abs_nonneg (ramWeight i n)))
  apply sum_le_sum
  intro q _
  rw [abs_mul, abs_of_nonneg (archimedean_nonneg _ (by positivity))]
  exact mul_le_of_le_one_right (abs_nonneg _) (archimedean_mass_le_one _ (by positivity))

/-- A single summable tail controls every positive window, with the actual
moving denominator cutoff and the actual integration weight of the catalogue. -/
theorem dyadic_conductor_tail (d j K : ℕ) (hd : 0 < d) (hj : 0 < j) :
    dyadicRatio d (fun n => |catalogueConductorTail K n|) j ≤
      4*d*(∑' r : ℕ, conductorMass (r+(K+1))) := by
  let T := Ico j (2*j)
  let W := ∑ i ∈ T, (d:ℝ)*i
  let Q := catalogueCutoff (2*d*j)
  have wp : 0 ≤ W := sum_nonneg fun i _ => by positivity
  have rows (i) (hi : i ∈ T) := tail_row K (d*i) Q (by
    apply Nat.pow_le_pow_left
    apply Nat.log_mono_right
    have le := Nat.mul_le_mul_left d (mem_Ico.mp hi).2.le
    have eq : d*(2*j) = 2*d*j := by ring
    omega)
  change (∑ i ∈ T, |catalogueConductorTail K (d*i)|)/W ≤ _
  calc
    _ ≤ (∑ i ∈ T, ∑ q ∈ Ioc K Q, (↑(d*i):ℝ)*|ramWeight q (d*i)|)/W :=
      div_le_div_of_nonneg_right (sum_le_sum rows) wp
    _ = ∑ q ∈ Ioc K Q, dyadicRatio d (fun n => n*|ramWeight q n|) j := by
      rw [sum_comm, sum_div]; rfl
    _ ≤ ∑ q ∈ Ioc K Q, 4*d*conductorMass q := sum_le_sum fun q _ => dyadic_ramWeight_bound d j q hd hj
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      let S := (Ioc K Q).image (fun q => q-(K+1))
      apply le_trans _ (((summable_nat_add_iff (K+1)).mpr conductorMass_summable).sum_le_tsum S
        (fun r _ => mass_nonneg _))
      apply sum_le_sum_of_injOn (fun q => q-(K+1)) _ (Subset.rfl) _ (fun r _ _ => mass_nonneg _)
      · intro a ha b hb eq
        change a-(K+1) = b-(K+1) at eq
        have := (mem_Ioc.mp ha).1; have := (mem_Ioc.mp hb).1; omega
      · intro q hq
        rw [Nat.sub_add_cancel (mem_Ioc.mp hq).1]

theorem uniform_catalogue_conductor_tail (d : ℕ) (hd : 0 < d) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, ∀ j : ℕ, 0 < j →
      dyadicRatio d (fun n => |catalogueConductorTail K n|) j < ε := by
  have tail := (tendsto_sum_nat_add conductorMass).comp (tendsto_add_atTop_nat 1)
  have lim := tail.const_mul (4*(d:ℝ))
  rw [mul_zero] at lim
  filter_upwards [lim.eventually_lt_const he] with K hK
  intro j hj
  exact (dyadic_conductor_tail d j K hd hj).trans_lt hK

/-- Quantitative tail for the catalogue model, uniform in the window index. -/
theorem dyadic_conductor_tail_rate (d j K : ℕ) (hd : 0 < d) (hj : 0 < j) :
    dyadicRatio d (fun n => |catalogueConductorTail K n|) j ≤
      4*d*conductorSqrtMoment / Real.sqrt (K+1:ℕ) := by
  exact (dyadic_conductor_tail d j K hd hj).trans
    ((mul_le_mul_of_nonneg_left (conductor_tail_rate K) (by positivity : (0:ℝ) ≤ 4*d)).trans_eq
      (by ring))

#print axioms dyadic_conductor_tail_rate
#print axioms uniform_catalogue_conductor_tail
end GoldbachMinor
