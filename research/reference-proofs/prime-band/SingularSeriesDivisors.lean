import SingularSeriesFactors

namespace GoldbachMinor
open Finset

/-- Squarefree divisor represented by a finite set of primes. -/
def factorDivisor (A : Finset ℕ) := ∏ p ∈ A, p

private theorem factorDivisor_lcm (A B : Finset ℕ) (hp : ∀ p∈A∪B, Nat.Prime p) :
    (factorDivisor A).lcm (factorDivisor B) = factorDivisor (A∪B) := by
  apply Nat.dvd_antisymm
  · exact Nat.lcm_dvd (prod_dvd_prod_of_subset A (A∪B) id subset_union_left)
      (prod_dvd_prod_of_subset B (A∪B) id subset_union_right)
  · apply prod_primes_dvd _ (fun p h => (hp p h).prime)
    intro p h
    obtain h|h := mem_union.mp h
    · exact (dvd_prod_of_mem id h).trans (Nat.dvd_lcm_left ..)
    · exact (dvd_prod_of_mem id h).trans (Nat.dvd_lcm_right ..)

private noncomputable def subsetCell (u v w : ℕ → ℝ) (A B : Finset ℕ) : ℝ :=
  (∏ p ∈ A, u p)*(∏ p ∈ B, v p)*(∏ p ∈ A∪B, w p)

/-- Each prime may belong to neither, either, or both divisor supports. -/
private theorem subset_product (S : Finset ℕ) (u v w : ℕ → ℝ) :
    (∑ A ∈ S.powerset, ∑ B ∈ S.powerset, subsetCell u v w A B) =
      ∏ p ∈ S, (1+(u p+v p+u p*v p)*w p) := by
  induction S using Finset.induction_on with
  | empty => simp [subsetCell]
  | @insert p S hp ih =>
    let F := subsetCell u v w
    let c := 1+(u p+v p+u p*v p)*w p
    calc
      _ = ∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
          ((F A B + F A (insert p B)) + (F (insert p A) B + F (insert p A) (insert p B))) := by
        simp_rw [sum_powerset_insert hp,sum_add_distrib]
        rfl
      _ = ∑ A ∈ S.powerset, ∑ B ∈ S.powerset, c * F A B := by
        apply sum_congr rfl
        intro A hA
        apply sum_congr rfl
        intro B hB
        have ha : p∉A := fun h => hp (mem_powerset.mp hA h)
        have hb : p∉B := fun h => hp (mem_powerset.mp hB h)
        simp [F,c,subsetCell,ha,hb,insert_union,union_insert,prod_insert]
        ring
      _ = _ := by simp_rw [← mul_sum]; rw [prod_insert hp,← ih]

/-- Full coefficient of the odd-prime expansion minus its cutoff at y. -/
noncomputable def factorTailWeight (y : ℕ) (A : Finset ℕ) : ℝ :=
  (∏ p ∈ A, goldbachFactor p) - ∏ p ∈ A, (if p≤y then goldbachFactor p else 0)

theorem factorTailWeight_nonneg (y : ℕ) (A : Finset ℕ) (hp : ∀ p∈A, 3≤p) :
    0 ≤ factorTailWeight y A := by
  unfold factorTailWeight
  apply sub_nonneg.mpr
  have h0 (p) (h : p∈A) : 0≤goldbachFactor p := by
    change 0≤1/((p:ℝ)-2)
    have hr : (3:ℝ)≤p := by exact_mod_cast hp p h
    exact one_div_nonneg.mpr (by linarith)
  exact prod_le_prod₀ (fun p h => by split_ifs <;> first | exact h0 p h | exact le_rfl)
    (fun p h => by split_ifs <;> first | exact le_rfl | exact h0 p h)

/-- Exact Euler factorization of the two-divisor mean-square sum. -/
theorem factorTail_gram (S : Finset ℕ) (hp : ∀ p∈S, Nat.Prime p) (y : ℕ) :
    let L := S.filter (·≤y)
    let R := S.filter (fun p => ¬p≤y)
    (∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
       factorTailWeight y A * factorTailWeight y B / ((factorDivisor A).lcm (factorDivisor B):ℕ)) =
      (∏ p ∈ L, factorSecond p) *
      ((∏ p ∈ R, factorSecond p) - 2*(∏ p ∈ R, factorMean p) + 1) := by
  let L := S.filter (·≤y)
  let R := S.filter (fun p => ¬p≤y)
  let g := goldbachFactor
  let b (p : ℕ) := if p≤y then g p else 0
  let w (p : ℕ) := (p:ℝ)⁻¹
  let form (u v : ℕ → ℝ) := ∑ A ∈ S.powerset, ∑ B ∈ S.powerset, subsetCell u v w A B
  let U := ∏ p ∈ L, factorSecond p
  let V := ∏ p ∈ R, factorSecond p
  let M := ∏ p ∈ R, factorMean p
  have cell (A B : Finset ℕ) (ha : A ∈ S.powerset) (hb : B ∈ S.powerset) :
      factorTailWeight y A * factorTailWeight y B / ((factorDivisor A).lcm (factorDivisor B):ℕ) =
      (subsetCell g g w A B - subsetCell g b w A B) -
      (subsetCell b g w A B - subsetCell b b w A B) := by
    rw [factorDivisor_lcm A B (fun p h => hp p ((union_subset (mem_powerset.mp ha) (mem_powerset.mp hb)) h))]
    simp only [subsetCell,factorTailWeight,b,g,w,factorDivisor, Nat.cast_prod,prod_inv_distrib,div_eq_mul_inv]
    ring
  have expand : (∑ A ∈ S.powerset, ∑ B ∈ S.powerset,
      factorTailWeight y A * factorTailWeight y B / ((factorDivisor A).lcm (factorDivisor B):ℕ)) =
      (form g g - form g b) - (form b g - form b b) := by
    simp only [form,← sum_sub_distrib]
    exact sum_congr rfl fun A ha => sum_congr rfl fun B hb => cell A B ha hb
  have form_split (u v l r : ℕ → ℝ)
      (hl : ∀ p∈L, 1+(u p+v p+u p*v p)*w p = l p)
      (hr : ∀ p∈R, 1+(u p+v p+u p*v p)*w p = r p) :
      form u v = (∏ p ∈ L, l p)*(∏ p ∈ R, r p) := by
    rw [show form u v = _ from subset_product S u v w,
      ← prod_filter_mul_prod_filter_not S (·≤y)]
    exact congrArg₂ _ (prod_congr rfl hl) (prod_congr rfl hr)
  have same (p : ℕ) : 1+(g p+g p+g p*g p)*w p = factorSecond p := by
    unfold factorSecond g w
    ring
  have left (p) (h : p∈L) : b p=g p := ite_eq_left (mem_filter.mp h).2
  have right (p) (h : p∈R) : b p=0 := ite_eq_right (mem_filter.mp h).2
  have mean (p : ℕ) : 1+g p*w p = factorMean p := by rfl
  have gg : form g g = U*V := form_split _ _ _ _ (fun p _ => same p) (fun p _ => same p)
  have gb : form g b = U*M := form_split _ _ _ _ (fun p h => by rw [left p h,same])
    (fun p h => by simp [right p h,mean])
  have bg : form b g = U*M := form_split _ _ _ _ (fun p h => by rw [left p h,same])
    (fun p h => by simp [right p h,mean])
  have bb : form b b = U := by
    have hh := form_split b b factorSecond (fun _ => 1)
      (fun p h => by rw [left p h,same]) (fun p h => by simp [right p h])
    simpa [U] using hh
  change _ = U*(V-2*M+1)
  rw [expand,gg,gb,bg,bb]
  ring

/-- Uniform bound for any subfamily, including divisors truncated by the target X. -/
theorem factorTail_divisor_bound (S : Finset ℕ) (hp : ∀ p∈S, Nat.Prime p ∧ 3≤p)
    (y : ℕ) (hy : 2≤y) (D : Finset (Finset ℕ)) (hD : D⊆S.powerset) :
    (∑ A ∈ D, ∑ B ∈ D,
      factorTailWeight y A * factorTailWeight y B / ((factorDivisor A).lcm (factorDivisor B):ℕ)) ≤
      Real.exp 9*(9*Real.exp 9+(3*Real.exp 9)^2)/(y:ℝ)^2 := by
  let L := S.filter (·≤y)
  let R := S.filter (fun p => ¬p≤y)
  have hL (p) (h : p∈L) := (hp p (mem_filter.mp h).1).2
  have U0 : 0 ≤ ∏ p ∈ L, factorSecond p := prod_nonneg fun p h => by
    have hpos : (3:ℝ)≤p := by exact_mod_cast hL p h
    dsimp [factorSecond,goldbachFactor]
    have : 0≤(p:ℝ)-2 := by linarith
    positivity
  have positive (A B) (ha : A∈S.powerset) (hb : B∈S.powerset) :
      0 ≤ factorTailWeight y A * factorTailWeight y B / ((factorDivisor A).lcm (factorDivisor B):ℕ) :=
    div_nonneg (mul_nonneg (factorTailWeight_nonneg y _ fun p h => (hp p (mem_powerset.mp ha h)).2)
      (factorTailWeight_nonneg y _ fun p h => (hp p (mem_powerset.mp hb h)).2)) (by positivity)
  calc
    _ ≤ ∑ A ∈ S.powerset, ∑ B ∈ S.powerset, _ := by
      refine (sum_le_sum (fun A ha => sum_le_sum_of_subset_of_nonneg hD (fun B hb _ => positive A B (hD ha) hb))).trans ?_
      exact sum_le_sum_of_subset_of_nonneg hD fun A ha _ => sum_nonneg fun B hb => positive A B ha hb
    _ = _ := factorTail_gram S (fun p h => (hp p h).1) y
    _ ≤ _ := by
      have t := goldbach_factor_tail y hy R (fun p h => lt_of_not_ge (mem_filter.mp h).2)
      have h := (mul_le_mul_of_nonneg_left t U0).trans
        (mul_le_mul_of_nonneg_right (factor_second_uniform L hL) (by positivity))
      convert h using 1
      ring

#print axioms factorTail_divisor_bound
end GoldbachMinor
