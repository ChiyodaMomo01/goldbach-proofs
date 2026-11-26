import TargetExceptions

namespace GoldbachMinor
open Finset Finset.HasAntidiagonal Filter
open scoped Topology

/-- The primes p in the half-open window j < p ≤ 2j. -/
def windowPrimes (j : ℕ) := Nat.primesLE (2*j) \ Nat.primesLE j

private theorem prime_window_size :
    ∀ᶠ j : ℕ in atTop, (j:ℝ)/2 ≤ (windowPrimes j).card * Real.log (2*j:ℕ) := by
  have grow : Tendsto (fun j : ℕ => 2*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by decide)) tendsto_id
  have theta := Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [(theta.comp grow).eventually_const_lt (show (7/8:ℝ)<1 by norm_num),
    theta.eventually_lt_const (show (1:ℝ)<9/8 by norm_num), eventually_ge_atTop 1] with j lo hi hj
  have jp : (0:ℝ)<j := by exact_mod_cast hj
  have up : (0:ℝ)<(2*j:ℕ) := by positivity
  have a := (lt_div_iff₀ up).mp lo
  have b := (div_lt_iff₀ jp).mp hi
  have eq := sum_sdiff (Nat.primesLE_mono (by omega : j≤2*j)) (f:=fun (p : ℕ) => Real.log (p:ℝ))
  rw [← Chebyshev.theta_eq_sum_primesLE_log,← Chebyshev.theta_eq_sum_primesLE_log] at eq
  have ub := sum_le_sum (s:=windowPrimes j) (g:=fun _ => Real.log (2*j:ℕ)) (fun p hp =>
    Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1).pos)
      (show (p:ℝ) ≤ (2*j:ℕ) by exact_mod_cast (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).1))
  simp only [sum_const,nsmul_eq_mul] at ub
  change (∑ p ∈ windowPrimes j, Real.log p) + _ = _ at eq
  push_cast at a ub eq ⊢
  linarith only [a,b,eq,ub]

/-- Primes in the window for which the frozen lower floor fails at twice the prime. -/
noncomputable def twicePrimeFailures (ε : ℝ) (j : ℕ) :=
  (windowPrimes j).filter (fun (p : ℕ) =>
    (FrozenBulk.deskI (2*p) (FrozenBulk.deskHigh (2*p)) (FrozenBulk.deskHigh (2*p))).re <
      -(ε*(2*p:ℕ)))

private theorem twice_prime_support (p : ℕ) (hp : p.Prime) : (2*p).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by decide) hp.ne_zero, Nat.prime_two.primeFactors, hp.primeFactors]
  exact (card_union_le _ _).trans_eq (by simp)

/-- Relative exceptional fraction among primes, with p itself in (j,2j].
The denominator counts just those primes. -/
theorem twice_prime_fraction_rate (ε : ℝ) (he : 0<ε) :
    ∀ᶠ j : ℕ in atTop,
      ((twicePrimeFailures ε j).card:ℝ) / (windowPrimes j).card ≤
        1280 / (ε^2 * Real.log (2*j:ℕ)) := by
  have grow : Tendsto (fun j : ℕ => 4*j+1) atTop atTop :=
    tendsto_atTop_mono (fun j => by change j ≤ 4*j+1; omega) tendsto_id
  filter_upwards [grow.eventually (bounded_support_failure 2 ε he),
    grow.eventually (wide_exceptional_count (ε/4) (by positivity)),prime_window_size,
    eventually_ge_atTop 1] with j force energy denom hj
  let X := 4*j+1
  let P := windowPrimes j
  let B := twicePrimeFailures ε j
  let H := (range X).filter (fun (n : ℕ) => (ε/4)*(X:ℝ)/2 ≤ ‖commonMinor X n‖)
  have inj : (B.card:ℝ) ≤ H.card := by
    apply Nat.cast_le.mpr
    apply card_le_card_of_injOn (fun (p : ℕ) => 2*p) _ (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (by decide : 0<2) h)
    intro p hp
    obtain ⟨win,bad⟩ := mem_filter.mp hp
    obtain ⟨hi,pr⟩ := Nat.mem_primesLE.mp (mem_sdiff.mp win).1
    have lo : j<p := by
      by_contra! le
      exact (mem_sdiff.mp win).2 (Nat.mem_primesLE.mpr ⟨le,pr⟩)
    have u : 2*p < X := by dsimp [X]; omega
    have h := force (2*p) u.le (by dsimp [X] at *; omega) (twice_prime_support p pr) bad
    exact mem_filter.mpr ⟨mem_range.mpr u,by dsimp only [X] at *; linarith only [h]⟩
  let L := Real.log (2*j:ℕ)
  have lp : 0<L := Real.log_pos (by exact_mod_cast (show 1<2*j by omega))
  have lx : L ≤ Real.log X := Real.log_le_log (by positivity) (by exact_mod_cast (show 2*j≤X by dsimp [X]; omega))
  have norm : (B.card:ℝ)*ε^2*L^2 ≤ 128*(X:ℝ) := by
    change (H.card:ℝ)*(ε/4)^2*(Real.log X)^2 ≤ 8*X at energy
    have sq := pow_le_pow_left₀ lp.le lx 2
    have mult := mul_le_mul inj sq (sq_nonneg _) (Nat.cast_nonneg (α:=ℝ) H.card)
    nlinarith only [energy,mul_le_mul_of_nonneg_right mult (sq_nonneg ε)]
  have pj : 0<(j:ℝ) := by exact_mod_cast hj
  change (j:ℝ)/2 ≤ (P.card:ℝ)*L at denom
  have pp : 0<(P.card:ℝ) := by
    by_contra! no
    linarith only [denom,pj,mul_nonpos_of_nonpos_of_nonneg no lp.le]
  change (B.card:ℝ)/(P.card:ℝ) ≤ 1280/(ε^2*L)
  rw [div_le_div_iff₀ pp (mul_pos (sq_pos_of_pos he) lp)]
  apply le_of_mul_le_mul_right (a:=L) _ lp
  have size : (X:ℝ) ≤ 5*j := by exact_mod_cast (show X≤5*j by dsimp [X]; omega)
  nlinarith only [norm,denom,size]

theorem twice_prime_exception_density (ε : ℝ) (he : 0<ε) :
    Tendsto (fun j => ((twicePrimeFailures ε j).card:ℝ) / (windowPrimes j).card) atTop (𝓝 0) := by
  have grow : Tendsto (fun j : ℕ => 2*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by decide)) tendsto_id
  have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)
  exact squeeze_zero' (Eventually.of_forall fun j => by positivity) (twice_prime_fraction_rate ε he)
    (tendsto_const_nhds.div_atTop (logs.const_mul_atTop (sq_pos_of_pos he)))

/-- Ordered distinct pairs of primes with arithmetic mean p. -/
def midpointPairs (p : ℕ) :=
  (antidiagonal (2*p)).filter (fun x => x.1.Prime ∧ x.2.Prime ∧ x.1 ≠ x.2)

private theorem count_by_midpoint_pairs (p : ℕ) :
    goldbachCount (2*p) ≤ ((midpointPairs p).card+1:ℝ)*(Real.log (2*p:ℕ))^2 := by
  let A := (antidiagonal (2*p)).filter (fun x => x.1.Prime ∧ x.2.Prime)
  have support : A ⊆ insert (p,p) (midpointPairs p) := by
    intro x hx
    obtain ⟨pair,pr⟩ := mem_filter.mp hx
    by_cases eq : x.1=x.2
    · have h := HasAntidiagonal.mem_antidiagonal.mp pair
      have e : x=(p,p) := Prod.ext (by omega) (by omega)
      exact mem_insert.mpr (Or.inl e)
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨pair,pr.1,pr.2,eq⟩))
  have size : A.card ≤ (midpointPairs p).card+1 :=
    (card_le_card support).trans (card_insert_le ..)
  have terms : goldbachCount (2*p) = ∑ x ∈ A, primeLog x.1 * primeLog x.2 := by
    rw [goldbachCount,show A = _ from rfl,sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases a : x.1.Prime <;> by_cases b : x.2.Prime <;> simp [primeLog,a,b]
  have row (x) (hx : x∈A) : primeLog x.1*primeLog x.2 ≤ (Real.log (2*p:ℕ))^2 := by
    obtain ⟨pair,ha,hb⟩ := mem_filter.mp hx
    have sum := HasAntidiagonal.mem_antidiagonal.mp pair
    have first := Real.log_le_log (show (0:ℝ)<x.1 by exact_mod_cast ha.pos)
      (show (x.1:ℝ)≤(2*p:ℕ) by exact_mod_cast (show x.1≤2*p by omega))
    have second := Real.log_le_log (show (0:ℝ)<x.2 by exact_mod_cast hb.pos)
      (show (x.2:ℝ)≤(2*p:ℕ) by exact_mod_cast (show x.2≤2*p by omega))
    simp only [primeLog,ha,hb,ite_true,pow_two]
    exact mul_le_mul first second (Real.log_nonneg (by exact_mod_cast hb.one_le))
      ((Real.log_nonneg (by exact_mod_cast ha.one_le)).trans first)
  rw [terms]
  apply (sum_le_sum row).trans
  simp only [sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast size) (sq_nonneg _)

/-- Positive coefficient for the non-diagonal representation bound. -/
noncomputable def midpointConstant : ℝ := archimedeanMass 1/8

theorem midpointConstant_pos : 0 < midpointConstant := div_pos archimedean_one_pos (by norm_num)

private theorem few_pairs_implies_failure :
    ∀ᶠ p : ℕ in atTop,
      ((midpointPairs p).card:ℝ)*(Real.log (2*p:ℕ))^2 < midpointConstant*(2*p:ℕ) →
      (FrozenBulk.deskI (2*p) (FrozenBulk.deskHigh (2*p)) (FrozenBulk.deskHigh (2*p))).re <
        -(midpointConstant*(2*p:ℕ)) := by
  have grow : Tendsto (fun p : ℕ => 2*p) atTop atTop :=
    tendsto_atTop_mono (fun p => Nat.le_mul_of_pos_left p (by decide)) tendsto_id
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
  have lim : Tendsto (fun x : ℝ => (Real.log x)^2/x) atTop (𝓝 0) := by simpa using h
  have small := ((lim.comp tendsto_natCast_atTop_atTop).comp grow).eventually_lt_const midpointConstant_pos
  filter_upwards [small,grow.eventually (frozen_count_error_sublinear midpointConstant midpointConstant_pos),
    eventually_ge_atTop 1] with p logbound transfer hp
  intro few
  have floor := even_major_model_floor (2*p) ⟨p,by omega⟩
  have count := count_by_midpoint_pairs p
  have up := (abs_le.mp transfer).2
  have pos : (0:ℝ)<(2*p:ℕ) := by positivity
  have logsmall := (div_lt_iff₀ pos).mp logbound
  dsimp only [midpointConstant] at *
  linarith only [few,floor,up,count,logsmall]

/-- Among primes in (j,2j], only this fraction can have fewer than a
constant times 2p/log(2p)^2 ordered non-diagonal prime representations. -/
theorem midpoint_shortfall_fraction_rate :
    ∀ᶠ j : ℕ in atTop,
      (((windowPrimes j).filter (fun p => ((midpointPairs p).card:ℝ)*(Real.log (2*p:ℕ))^2 <
        midpointConstant*(2*p:ℕ))).card:ℝ)/(windowPrimes j).card ≤
          1280/(midpointConstant^2*Real.log (2*j:ℕ)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp few_pairs_implies_failure
  filter_upwards [twice_prime_fraction_rate midpointConstant midpointConstant_pos,
    eventually_ge_atTop N] with j rate hj
  apply le_trans _ rate
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨win,few⟩ := mem_filter.mp hp
  have pr := Nat.prime_of_mem_primesLE (mem_sdiff.mp win).1
  have lo : j<p := by
    by_contra! le
    exact (mem_sdiff.mp win).2 (Nat.mem_primesLE.mpr ⟨le,pr⟩)
  exact mem_filter.mpr ⟨win,hN p (hj.trans lo.le) few⟩

#print axioms midpoint_shortfall_fraction_rate
#print axioms twice_prime_fraction_rate
#print axioms twice_prime_exception_density
end GoldbachMinor
