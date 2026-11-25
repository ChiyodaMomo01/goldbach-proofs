import DeskPrimeInput

namespace GoldbachMinor
open Finset Filter
open GoldbachMajorArc (classMass classError)
open scoped Topology

/-- Total ordered log-weighted pair count for multiples of q strictly below X. -/
noncomputable def progressionTotal (X q : ℕ) : ℝ :=
  ∑ n ∈ (range X).filter (q ∣ ·), goldbachCount n

/-- Least residue of the negative of p modulo q. -/
def oppositeResidue (q p : ℕ) := (-(p : ZMod q)).val

private theorem opposite_iff (q p r : ℕ) (hq : 0 < q) :
    r % q = oppositeResidue q p ↔ q ∣ p+r := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [← ZMod.val_natCast q r, oppositeResidue, (ZMod.val_injective q).eq_iff,
    eq_comm, neg_eq_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]

private theorem opposite_coprime (q p : ℕ) (hq : 0 < q) :
    (oppositeResidue q p).Coprime q ↔ p.Coprime q := by
  have : NeZero q := ⟨hq.ne'⟩
  simp only [oppositeResidue, ← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
  exact ⟨fun h => by simpa using h.neg, IsUnit.neg⟩

theorem progression_total_by_prefix (X q : ℕ) (hq : 0 < q) :
    progressionTotal X q =
      ∑ p ∈ range X, primeLog p * classMass (X-p) q (oppositeResidue q p) := by
  let box := range X ×ˢ range X
  let targets := (range X).filter (q ∣ ·)
  let weight (x : ℕ × ℕ) := primeLog x.1 * primeLog x.2
  have diag (n : ℕ) (hn : n ∈ targets) :
      Finset.HasAntidiagonal.antidiagonal n = box.filter (fun x => x.1+x.2=n) := by
    have bound := mem_range.mp (mem_filter.mp hn).1
    ext x
    simp only [Finset.HasAntidiagonal.mem_antidiagonal, box, mem_filter, mem_product, mem_range]
    omega
  calc
    _ = ∑ n ∈ targets, ∑ x ∈ box.filter (fun x => x.1+x.2=n), weight x :=
      sum_congr rfl fun n hn => by rw [goldbachCount, diag n hn]
    _ = _ := sum_fiberwise_eq_sum_filter box targets (fun x => x.1+x.2) weight
    _ = _ := by
      rw [sum_filter, sum_product]
      apply sum_congr rfl
      intro p _
      rw [GoldbachMajorArc.classMass, mul_sum, ← sum_filter]
      have sets : ((range X).filter (fun r => p+r ∈ targets)) =
          ((range (X-p)).filter (fun r => r % q = oppositeResidue q p)) := by
        ext r
        simp only [targets, mem_filter, mem_range, opposite_iff q p r hq]
        omega
      rw [sets]
      rfl

private noncomputable def unitPrefix (m q : ℕ) :=
  ∑ p ∈ (range m).filter (·.Coprime q), primeLog p

private theorem unit_prefix_error (m q : ℕ) (hq : 0 < q) {E : ℝ}
    (h : ∀ b < q, |classError m q b| ≤ E) :
    |unitPrefix m q - m| ≤ q.totient * E := by
  let units := (range q).filter (·.Coprime q)
  have hc : units.card = q.totient := by
    simp only [units, Nat.totient_eq_card_coprime, Nat.coprime_comm]
  have hφ : (q.totient:ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have total : ∑ b ∈ units, classMass m q b = unitPrefix m q := by
    unfold GoldbachMajorArc.classMass
    rw [sum_fiberwise_eq_sum_filter]
    unfold unitPrefix
    congr 1
    ext p
    simp [units, Nat.mod_lt p hq]
  have error : ∑ b ∈ units, classError m q b = unitPrefix m q - m := by
    unfold GoldbachMajorArc.classError
    rw [sum_sub_distrib, total]
    congr 1
    calc
      _ = ∑ _b ∈ units, (m:ℝ) / q.totient := sum_congr rfl fun b hb =>
        ite_eq_left (mem_filter.mp hb).2
      _ = _ := by simp [hc]; field_simp
  rw [← error]
  apply (abs_sum_le_sum_abs ..).trans
  simpa [hc] using sum_le_sum (s:=units) (fun b hb => h b (mem_range.mp (mem_filter.mp hb).1))

private theorem unit_triangle (X q : ℕ) :
    (∑ p ∈ range X, primeLog p * (if p.Coprime q then ((X-p:ℕ):ℝ) else 0)) =
      ∑ j ∈ range X, unitPrefix (j+1) q := by
  let w (p : ℕ) := if p.Coprime q then primeLog p else 0
  calc
    _ = ∑ p ∈ range X, ∑ _j ∈ Ico p X, w p := by
      apply sum_congr rfl
      intro p _
      by_cases hp : p.Coprime q <;> simp [w, hp, mul_comm]
    _ = ∑ j ∈ range X, ∑ p ∈ range (j+1), w p := by
      apply sum_comm'
      intro p j
      simp only [mem_range, mem_Ico]
      omega
    _ = _ := by simp only [unitPrefix, sum_filter, w]

private theorem triangular (X : ℕ) : (∑ j ∈ range X, ((j+1:ℕ):ℝ)) = (X:ℝ)*(X+1)/2 := by
  induction X with
  | zero => simp
  | succ X ih => rw [sum_range_succ, ih]; push_cast; ring

/-- A uniform one-prime discrepancy up to X controls the entire triangular
sum. This includes nonunit residue classes and counts ordered prime pairs. -/
theorem progression_total_error (X q : ℕ) (hq : 0 < q) (E : ℝ) (hE : 0 ≤ E)
    (bound : ∀ m ≤ X, ∀ b < q, |classError m q b| ≤ E) :
    |progressionTotal X q - (X:ℝ)*(X+1)/(2*q.totient)| ≤
      (Real.log 4 + 1)*X*E := by
  have : NeZero q := ⟨hq.ne'⟩
  let φ : ℝ := q.totient
  have hp : 0 < φ := by dsimp [φ]; exact_mod_cast Nat.totient_pos.mpr hq
  let main := (∑ j ∈ range X, unitPrefix (j+1) q) / φ
  have first : |progressionTotal X q - main| ≤ Real.log 4 * X * E := by
    rw [progression_total_by_prefix X q hq]
    dsimp only [main]
    rw [← unit_triangle, sum_div, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ p ∈ range X, primeLog p * E := by
        apply sum_le_sum
        intro p _
        have e := bound (X-p) (Nat.sub_le ..) (oppositeResidue q p) (ZMod.val_lt _)
        simp only [GoldbachMajorArc.classError, opposite_coprime q p hq] at e
        by_cases h : p.Coprime q
        · rw [ite_eq_left h] at e ⊢
          rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_nonneg (primeLog_nonneg p)]
          exact mul_le_mul_of_nonneg_left e (primeLog_nonneg p)
        · rw [ite_eq_right h] at e ⊢
          simpa [abs_mul, abs_of_nonneg (primeLog_nonneg p)] using
            mul_le_mul_of_nonneg_left e (primeLog_nonneg p)
      _ ≤ _ := by
        rw [← sum_mul]
        apply mul_le_mul_of_nonneg_right _ hE
        apply le_trans _ (primeLog_sum X)
        exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ X)) (fun p _ _ => primeLog_nonneg p)
  have second : |main - (X:ℝ)*(X+1)/(2*q.totient)| ≤ X*E := by
    change |(∑ j ∈ range X, unitPrefix (j+1) q) / φ - (X:ℝ)*(X+1)/(2*φ)| ≤ _
    rw [← div_div, ← triangular X, ← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    have h := sum_le_sum (s:=range X) (fun j hj => unit_prefix_error (j+1) q hq
      (bound _ (mem_range.mp hj)))
    simpa [φ, mul_assoc, mul_comm, mul_left_comm] using h
  exact (abs_sub_le _ main _).trans ((add_le_add first second).trans_eq (by ring))

/-- For a fixed modulus the discrepancy in every residue class is sublinear,
uniformly in prefix lengths through X. -/
theorem fixed_modulus_prefix_bound (q : ℕ) (hq : 0 < q) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ m ≤ X, ∀ b < q, |classError m q b| ≤ δ * X := by
  obtain ⟨M, _, x₀, _, raw⟩ := GoldbachMajorArc.all_class_error 1 1 zero_lt_one zero_lt_one
  have casts : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have logs := Real.tendsto_log_atTop.comp casts
  have small₁ : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp casts
  have small₂ : Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero.comp casts
  let C := Real.log q / Real.log 2
  have main : Tendsto (fun n : ℕ => M / Real.log n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop logs
  have invN : Tendsto (fun n : ℕ => 1 / (n:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop casts
  have budget : ∀ᶠ n : ℕ in atTop,
      M / Real.log n + Real.log n / n * C + 2 * (Real.log n / Real.sqrt n) + 1/n < δ := by
    have lim := (((main.add (small₁.mul_const C)).add (small₂.const_mul 2)).add invN)
    apply lim.eventually_lt_const
    simpa using hδ
  have large : ∀ᶠ n : ℕ in atTop, ∀ b < q, |classError (n+1) q b| ≤ δ*n := by
    filter_upwards [budget, casts.eventually_ge_atTop x₀, logs.eventually_ge_atTop (q:ℝ),
      eventually_ge_atTop 2] with n hb hx hqlog hn
    have np : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have lp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have root := Real.sqrt_pos.mpr np
    have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have lq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    have herr := mul_le_mul_of_nonneg_right (Real.natLog_le_logb n 2) lq
    simp only [Real.logb, Nat.cast_ofNat] at herr
    intro b hbound
    have h := raw n q b hx hq (by simpa using hqlog) hbound
    rw [Real.rpow_neg lp.le, Real.rpow_one] at h
    apply h.trans
    calc
      _ ≤ M * n * (Real.log n)⁻¹ + (Real.log n / Real.log 2)*Real.log q +
          2 * Real.sqrt n * Real.log n + 1 := by linarith only [herr]
      _ = (M / Real.log n + Real.log n / n * C + 2 * (Real.log n / Real.sqrt n) + 1/n)*n := by
        dsimp [C]
        field_simp
        nlinarith only [Real.sq_sqrt np.le, mul_nonneg l2.le lp.le,
          congrArg (fun z : ℝ => 2 * z * Real.log n ^ 2 * Real.log 2) (Real.sq_sqrt np.le)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb.le np.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp large
  let S := ∑ m ∈ range (N+1), ∑ b ∈ range q, |classError m q b|
  filter_upwards [casts.eventually_ge_atTop (S/δ)] with X hX
  intro m hm b hb
  by_cases hlarge : N < m
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact (hN u (by omega) b hb).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (show u ≤ X by omega)) hδ.le)
  · have inner := single_le_sum (fun i (_ : i ∈ range q) => abs_nonneg (classError m q i)) (mem_range.mpr hb)
    have outer := single_le_sum (fun i (_ : i ∈ range (N+1)) =>
      sum_nonneg (fun b (_ : b ∈ range q) => abs_nonneg (classError i q b))) (mem_range.mpr (by omega : m<N+1))
    exact (inner.trans outer).trans (by simpa [mul_comm] using (div_le_iff₀ hδ).mp hX)


/-- For every fixed modulus, the normalized sum of actual ordered Goldbach
counts over its multiples converges to one half of the inverse totient. -/
theorem progression_total_asymptotic (q : ℕ) (hq : 0 < q) :
    Tendsto (fun X : ℕ => progressionTotal X q / (X:ℝ)^2)
      atTop (𝓝 (1 / (2*(q.totient:ℝ)))) := by
  let K := Real.log 4 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have residual : Tendsto (fun X : ℕ =>
      (progressionTotal X q - (X:ℝ)*(X+1)/(2*q.totient)) / (X:ℝ)^2) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := ε / (2*K)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    filter_upwards [fixed_modulus_prefix_bound q hq hδ, eventually_ge_atTop 1] with X bound hX
    have xp : 0 < (X:ℝ) := by exact_mod_cast hX
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (sq_pos_of_pos xp), div_lt_iff₀ (sq_pos_of_pos xp)]
    have err := progression_total_error X q hq (δ*X) (by positivity) bound
    apply err.trans_lt
    change K * X * (δ*X) < ε * (X:ℝ)^2
    have coeff : K*δ < ε := by dsimp [δ]; field_simp; nlinarith [mul_pos hε hK]
    nlinarith only [mul_lt_mul_of_pos_right coeff (sq_pos_of_pos xp)]
  have invX : Tendsto (fun X : ℕ => 1 / (X:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have main : Tendsto (fun X : ℕ => (1+1/(X:ℝ)) / (2*q.totient)) atTop
      (𝓝 (1 / (2*(q.totient:ℝ)))) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).add invX |>.div_const (2*(q.totient:ℝ))
  apply (show Tendsto _ _ _ from (by simpa only [zero_add] using residual.add main)).congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have xp : 0 < (X:ℝ) := by exact_mod_cast hX
  have hp : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  field_simp
  ring

/-- On the window qj ≤ n < 2qj, divide the sum of pair counts by the sum of
the targets in the same progression. Its limit is the modulus-to-totient ratio. -/
theorem dyadic_progression_mean (q : ℕ) (hq : 0 < q) :
    Tendsto (fun j : ℕ =>
      (progressionTotal (2*q*j) q - progressionTotal (q*j) q) /
        (∑ i ∈ Ico j (2*j), (q:ℝ)*i)) atTop (𝓝 ((q:ℝ)/q.totient)) := by
  have tq : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have qp : 0 < (q:ℝ) := by exact_mod_cast hq
  have dilate (d : ℕ) (hd : 0 < d) :
      Tendsto (fun j : ℕ => progressionTotal (d*j) q / (j:ℝ)^2)
        atTop (𝓝 ((d:ℝ)^2 / (2*q.totient))) := by
    have grows : Tendsto (fun j : ℕ => d*j) atTop atTop := by
      apply tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j hd) tendsto_id
    have h := ((progression_total_asymptotic q hq).comp grows).const_mul ((d:ℝ)^2)
    convert h using 1
    · funext j
      simp only [Function.comp_apply, Nat.cast_mul, mul_pow, div_eq_mul_inv, mul_inv_rev]
      have dp : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
    · ring
  have numerator := (dilate (2*q) (by omega)).sub (dilate q hq)
  have identity (j : ℕ) :
      (∑ i ∈ Ico j (2*j), (q:ℝ)*i) = (q:ℝ)*j*(3*j-1)/2 := by
    rw [← mul_sum, sum_Ico_eq_sub _ (by omega)]
    have natSum (k : ℕ) : (∑ i ∈ range k, (i:ℝ)) = (k:ℝ)*(k-1)/2 := by
      induction k with
      | zero => simp
      | succ k ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring
    rw [natSum, natSum, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have inv : Tendsto (fun j : ℕ => 1/(j:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have denominator : Tendsto (fun j : ℕ => (∑ i ∈ Ico j (2*j), (q:ℝ)*i)/(j:ℝ)^2)
      atTop (𝓝 ((q:ℝ)*3/2)) := by
    have lim := (((tendsto_const_nhds (x:=(3:ℝ))).sub inv).const_mul (q:ℝ)).div_const 2
    apply (show Tendsto _ _ _ from (by simpa only [sub_zero] using lim)).congr'
    filter_upwards [eventually_ge_atTop 1] with j hj
    have jp : (j:ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    rw [identity]
    field_simp
  have lim := numerator.div denominator (by positivity)
  convert lim.congr' ?_ using 1
  · push_cast
    field_simp
    ring
  filter_upwards [eventually_ge_atTop 1] with j hj
  have jp : (j:ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  simp only [Pi.div_apply]
  rw [← sub_div, div_div_div_cancel_right₀ (pow_ne_zero _ jp)]

#print axioms progression_total_by_prefix
#print axioms progression_total_error
#print axioms progression_total_asymptotic
#print axioms dyadic_progression_mean
end GoldbachMinor
