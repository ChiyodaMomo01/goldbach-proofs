import Mathlib

namespace GoldbachMinor
open Finset

/-- A product of factors at least one is Lipschitz in the sum of their changes,
with the product of the larger factors as coefficient. -/
private theorem product_increments {ι : Type*} [DecidableEq ι] (S : Finset ι) (u v : ι → ℝ)
    (hu : ∀ i∈S, 1≤u i) (huv : ∀ i∈S, u i≤v i) :
    (∏ i ∈ S, v i) - (∏ i ∈ S, u i) ≤
      (∏ i ∈ S, v i) * ∑ i ∈ S, (v i - u i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hsubset := Finset.subset_insert i S
    have h1 (j) (hj : j ∈ S) := hu j (hsubset hj)
    have h2 (j) (hj : j ∈ S) := huv j (hsubset hj)
    have hi1 := hu i (mem_insert_self ..)
    have hi2 := huv i (mem_insert_self ..)
    have hi3 : 1≤v i := hi1.trans hi2
    let p := ∏ j ∈ S, v j
    let q := ∏ j ∈ S, u j
    have pp : 0≤p := prod_nonneg fun j hj => zero_le_one.trans ((h1 _ hj).trans (h2 _ hj))
    have qp : q≤p := prod_le_prod₀ (fun j hj => zero_le_one.trans (h1 j hj)) h2
    have bound := ih h1 h2
    simp only [prod_insert hi,sum_insert hi]
    change v i*p - u i*q ≤ v i*p*((v i-u i)+_)
    calc
      _ = v i*(p-q) + (v i-u i)*q := by ring
      _ ≤ v i*(p*∑ j ∈ S, (v j-u j)) + (v i-u i)*(v i*p) := by
        apply add_le_add (mul_le_mul_of_nonneg_left bound (zero_le_one.trans hi3))
        exact mul_le_mul_of_nonneg_left (qp.trans (le_mul_of_one_le_left pp hi3)) (sub_nonneg.mpr hi2)
      _ = _ := by ring

/-- Finite Euler-factor second moment around one. The two terms pay for the
variance of the product and the square of its mean shift. -/
theorem euler_product_second_moment {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (m v : ι → ℝ) (hm : ∀ i∈S, 1 ≤ m i) (hv : ∀ i∈S, (m i)^2≤v i) :
    let M := ∏ i ∈ S, m i
    let V := ∏ i ∈ S, v i
    V-2*M+1 ≤ V*(∑ i ∈ S, (v i-(m i)^2)) + (M*∑ i ∈ S, (m i-1))^2 := by
  let M := ∏ i ∈ S, m i
  let V := ∏ i ∈ S, v i
  have h1 (i) (hi : i∈S) : 1≤(m i)^2 := by nlinarith [hm i hi,sq_nonneg (m i-1)]
  have hvar := product_increments S (fun i => (m i)^2) v h1 hv
  rw [prod_pow] at hvar
  have hshift := product_increments S (fun _ => 1) m (fun _ _ => le_rfl) hm
  simp only [prod_const_one] at hshift
  have hM : 1≤M := Finset.one_le_prod₀ hm
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hM) hshift 2
  change V-2*M+1 ≤ _
  change V-M^2 ≤ _ at hvar
  nlinarith only [hvar,hs]

/-- Local multiplier above the parity factor in the binary Goldbach singular series. -/
noncomputable def goldbachFactor (p : ℕ) : ℝ := 1 / ((p:ℝ)-2)

/-- Mean and second moment when divisibility by p has density 1/p. -/
noncomputable def factorMean (p : ℕ) : ℝ := 1 + goldbachFactor p / p

noncomputable def factorSecond (p : ℕ) : ℝ :=
  1 + (2*goldbachFactor p + (goldbachFactor p)^2) / p

private theorem factor_bounds (p : ℕ) (hp : 3≤p) :
    1≤factorMean p ∧ (factorMean p)^2≤factorSecond p ∧
    factorMean p-1 ≤ 3/(p:ℝ)^2 ∧ factorSecond p-(factorMean p)^2 ≤ 9/(p:ℝ)^3 ∧
    factorSecond p ≤ 1+9/(p:ℝ)^2 := by
  have hr : (3:ℝ)≤p := by exact_mod_cast hp
  have hpos : 0<(p:ℝ) := by linarith
  let g := goldbachFactor p
  have g0 : 0≤g := by change 0≤1/((p:ℝ)-2); exact one_div_nonneg.mpr (by linarith)
  have g1 : g≤1 := by change 1/((p:ℝ)-2) ≤ 1; apply (div_le_iff₀ (by linarith)).mpr; linarith
  have gp : g*(p:ℝ) ≤ 3 := by
    change (1/((p:ℝ)-2))*p ≤ 3
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have gp0 : 0≤g*(p:ℝ) := mul_nonneg g0 hpos.le
  have gp2 := (sq_le_sq₀ gp0 (by norm_num : (0:ℝ)≤3)).mpr gp
  change 1≤1+g/p ∧ (1+g/p)^2 ≤ 1+(2*g+g^2)/p ∧
    (1+g/p)-1 ≤ 3/(p:ℝ)^2 ∧ 1+(2*g+g^2)/p-(1+g/p)^2 ≤ 9/(p:ℝ)^3 ∧ _
  refine ⟨by linarith [div_nonneg g0 hpos.le], ?_, ?_, ?_, ?_⟩
  · field_simp
    nlinarith only [mul_nonneg (sq_nonneg g) (show 0≤(p:ℝ)-1 by linarith)]
  · field_simp
    nlinarith only [gp]
  · field_simp
    nlinarith only [gp2,mul_nonneg (sq_nonneg g) hpos.le]
  · change 1+(2*g+g^2)/p ≤ 1+9/(p:ℝ)^2
    field_simp
    nlinarith only [gp, mul_nonneg gp0 (sub_nonneg.mpr g1)]

private theorem reciprocal_square_tail (y : ℕ) (hy : 0<y) (S : Finset ℕ)
    (hS : ∀ p∈S, y<p) : (∑ p ∈ S, 1/(p:ℝ)^2) ≤ 1/(y:ℝ) := by
  have tel (H : ℕ) (hle : y≤H) :
      (∑ p ∈ Ioc y H, 1/(p:ℝ)^2) ≤ 1/(y:ℝ) - 1/(H:ℝ) := by
    induction H, hle using Nat.le_induction with
    | base => simp
    | succ H hH ih =>
      rw [sum_Ioc_succ_top hH]
      have hr : 0<(H:ℝ) := by exact_mod_cast (hy.trans_le hH)
      have diff : 1/((H:ℝ)+1)^2 ≤ 1/(H:ℝ) - 1/((H:ℝ)+1) := by
        field_simp
        linarith
      push_cast
      linarith
  let H := max y (S.sup id)
  have inc : S ⊆ Ioc y H := by
    intro p hp
    exact mem_Ioc.mpr ⟨hS p hp,(le_sup (f:=id) hp).trans (le_max_right ..)⟩
  exact (sum_le_sum_of_subset_of_nonneg inc (fun p _ _ => by positivity)).trans
    ((tel H (le_max_left ..)).trans (sub_le_self _ (by positivity)))

/-- The product of local second moments is bounded independently of the prime set. -/
theorem factor_second_uniform (S : Finset ℕ) (hS : ∀ p∈S, 3≤p) :
    (∏ p ∈ S, factorSecond p) ≤ Real.exp 9 := by
  have point (p) (hp : p∈S) : factorSecond p ≤ Real.exp (9/(p:ℝ)^2) :=
    (factor_bounds p (hS p hp)).2.2.2.2.trans (by simpa only [add_comm] using Real.add_one_le_exp (9/(p:ℝ)^2))
  have tail := reciprocal_square_tail 1 (by decide) S (fun p hp => by have := hS p hp; omega)
  have mass : (∑ p ∈ S, 9/(p:ℝ)^2) ≤ 9 := by
    simp_rw [show ∀ p:ℕ, 9/(p:ℝ)^2 = 9*(1/(p:ℝ)^2) by intro; ring, ← mul_sum]
    simp only [Nat.cast_one,div_one] at tail
    linarith
  calc
    _ ≤ ∏ p ∈ S, Real.exp (9/(p:ℝ)^2) := prod_le_prod₀
      (fun p hp => (sq_nonneg (factorMean p)).trans (factor_bounds p (hS p hp)).2.1) point
    _ = _ := (Real.exp_sum ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr mass

/-- Uniform inverse-square tail for the two Goldbach Euler moments, for every finite
set above the cutoff. Neither the set's size nor its largest prime enters the bound. -/
theorem goldbach_factor_tail (y : ℕ) (hy : 2≤y) (S : Finset ℕ) (hS : ∀ p∈S, y<p) :
    let M := ∏ p ∈ S, factorMean p
    let V := ∏ p ∈ S, factorSecond p
    V-2*M+1 ≤ (9*Real.exp 9+(3*Real.exp 9)^2)/(y:ℝ)^2 := by
  let C := Real.exp 9
  let M := ∏ p ∈ S, factorMean p
  let V := ∏ p ∈ S, factorSecond p
  have h3 (p) (hp : p∈S) : 3≤p := by have := hS p hp; omega
  have hm p hp := (factor_bounds p (h3 p hp)).1
  have hv p hp := (factor_bounds p (h3 p hp)).2.1
  have hM0 : 0≤M := prod_nonneg fun p hp => zero_le_one.trans (hm p hp)
  have hV : V≤C := factor_second_uniform S h3
  have hM : M≤C := by
    refine le_trans (prod_le_prod₀ (fun p hp => zero_le_one.trans (hm p hp)) (fun p hp => ?_)) hV
    exact le_trans (by nlinarith [hm p hp,sq_nonneg (factorMean p-1)]) (hv p hp)
  have hyr : 0<(y:ℝ) := by exact_mod_cast (show 0<y by omega)
  have tail := reciprocal_square_tail y (by omega) S hS
  have shift : (∑ p ∈ S, (factorMean p-1)) ≤ 3/(y:ℝ) := by
    calc
      _ ≤ ∑ p ∈ S, 3*(1/(p:ℝ)^2) := sum_le_sum (fun p hp => by
        simpa only [mul_one_div] using (factor_bounds p (h3 p hp)).2.2.1)
      _ ≤ _ := by rw [← mul_sum, ← mul_one_div (3:ℝ)]; gcongr
  have var : (∑ p ∈ S, (factorSecond p-(factorMean p)^2)) ≤ 9/(y:ℝ)^2 := by
    calc
      _ ≤ ∑ p ∈ S, (9/(y:ℝ))*(1/(p:ℝ)^2) := by
        apply sum_le_sum
        intro p hp
        refine (factor_bounds p (h3 p hp)).2.2.2.1.trans ?_
        have hpr : (y:ℝ)<p := by exact_mod_cast hS p hp
        have hpos : 0<(p:ℝ) := hyr.trans hpr
        field_simp
        linarith
      _ = (9/(y:ℝ))*(∑ p ∈ S, 1/(p:ℝ)^2) := (mul_sum ..).symm
      _ ≤ (9/(y:ℝ))*(1/(y:ℝ)) := mul_le_mul_of_nonneg_left tail (by positivity)
      _ = _ := by ring
  have sh0 : 0≤∑ p ∈ S, (factorMean p-1) := sum_nonneg (fun p hp => sub_nonneg.mpr (hm p hp))
  have va0 : 0≤∑ p ∈ S, (factorSecond p-(factorMean p)^2) :=
    sum_nonneg (fun p hp => sub_nonneg.mpr (hv p hp))
  refine (euler_product_second_moment S factorMean factorSecond hm hv).trans ?_
  change V*_+(M*_)^2 ≤ _
  calc
    _ ≤ C*(9/(y:ℝ)^2)+(C*(3/(y:ℝ)))^2 := add_le_add
      (mul_le_mul hV var va0 (Real.exp_nonneg _))
      ((sq_le_sq₀ (mul_nonneg hM0 sh0) (by dsimp [C]; positivity)).mpr
        (mul_le_mul hM shift sh0 (Real.exp_nonneg _)))
    _ = _ := by unfold C; ring

#print axioms goldbach_factor_tail
end GoldbachMinor
