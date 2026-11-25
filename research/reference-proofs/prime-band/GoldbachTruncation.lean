import RamanujanEnergy

namespace GoldbachMinor
open Finset Finset.HasAntidiagonal GoldbachWeight Filter
open scoped Topology

/-- The classical ordered Goldbach count with a logarithm on each prime. -/
noncomputable def primeLog (p : ℕ) : ℝ := if p.Prime then Real.log p else 0

noncomputable def goldbachCount (m : ℕ) : ℝ :=
  ∑ x ∈ antidiagonal m, primeLog x.1 * primeLog x.2

def cubeCutoff (n : ℕ) := Nat.findGreatest (fun p => p^3 ≤ n) n

private def boxCount (n m : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ x ∈ (antidiagonal m).filter (fun x => x.1 ≤ n ∧ x.2 ≤ n), w x.1 * w x.2

private theorem box_rectangle (n m : ℕ) (w : ℕ → ℝ) :
    boxCount n m w = ∑ p ∈ range (n+1), ∑ r ∈ range (n+1),
      if p+r=m then w p * w r else 0 := by
  have eq : (antidiagonal m).filter (fun x => x.1 ≤ n ∧ x.2 ≤ n) =
      ((range (n+1)) ×ˢ (range (n+1))).filter (fun x => x.1+x.2=m) := by
    ext x
    simp only [mem_filter, mem_product, mem_range, HasAntidiagonal.mem_antidiagonal]
    omega
  rw [boxCount, eq, sum_filter, sum_product]

private theorem mass_split (n k : ℕ) (hk : 0<k) (hkn : k≤n) (w : ℕ → ℝ) :
    pairMass n k w = boxCount n (n-k) w + boxCount n (n+k) w := by
  simp only [pairMass, box_rectangle, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  have eq : (offset n p r).natAbs=k ↔ p+r=n-k ∨ p+r=n+k := by
    change _ = (k:ℤ).natAbs ↔ _
    rw [Int.natAbs_eq_natAbs_iff]
    unfold offset
    omega
  have dis : p+r=n-k → p+r≠n+k := by omega
  by_cases hl : p+r=n-k <;> by_cases hu : p+r=n+k <;> simp_all

private theorem primeLog_nonneg (p : ℕ) : 0≤primeLog p := by
  unfold primeLog
  split_ifs <;> positivity

private theorem primeLog_sum (t : ℕ) :
    (∑ p ∈ range (t+1), primeLog p) ≤ Real.log 4 * t := by
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x (show 0≤(t:ℝ) by positivity))
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, sum_filter]
  have eq : Finset.Icc 0 t = range (t+1) := by ext k; simp
  rw [eq]
  exact le_rfl

private theorem primeLog_le (p M : ℕ) (hM : 0<M) (hp : p≤M) : primeLog p ≤ Real.log M := by
  unfold primeLog
  split_ifs with h
  · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hp)
  · exact Real.log_nonneg (by exact_mod_cast hM)

private theorem small_coordinate (m t M : ℕ) (hm : m≤M) (hM : 0<M) :
    (∑ x ∈ antidiagonal m, if x.1≤t then primeLog x.1*primeLog x.2 else 0)
      ≤ Real.log 4 * t * Real.log M := by
  rw [← sum_filter]
  let S := (antidiagonal m).filter (fun x => x.1≤t)
  have inj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
    rintro ⟨p,r⟩ hx ⟨q,s⟩ hy e
    have h := HasAntidiagonal.mem_antidiagonal.mp (mem_filter.mp hx).1
    have h' := HasAntidiagonal.mem_antidiagonal.mp (mem_filter.mp hy).1
    simp only at e h h'
    congr 1
    omega
  calc
    _ ≤ ∑ p ∈ range (t+1), primeLog p * Real.log M := by
      apply sum_le_sum_of_injOn Prod.fst inj
      · intro p hp
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
        exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hx).2)
      · intro x hx
        have he := HasAntidiagonal.mem_antidiagonal.mp (mem_filter.mp hx).1
        exact mul_le_mul_of_nonneg_left (primeLog_le _ _ hM (by omega)) (primeLog_nonneg _)
      · intro p _ _
        exact mul_nonneg (primeLog_nonneg p) (Real.log_nonneg (by exact_mod_cast hM))
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (primeLog_sum t) (Real.log_nonneg (by exact_mod_cast hM))

private theorem box_error (n m M t : ℕ) (hm : m≤M) (hM : 0<M)
    (hc : cubeCutoff n ≤ t) (he : m-n ≤ t) :
    0 ≤ goldbachCount m - boxCount n m (high n) ∧
    goldbachCount m - boxCount n m (high n) ≤ 2 * (Real.log 4 * t * Real.log M) := by
  let f (x : ℕ × ℕ) := primeLog x.1 * primeLog x.2
  let keep (x : ℕ × ℕ) := x.1≤n ∧ x.2≤n ∧ n<x.1^3 ∧ n<x.2^3
  let cut (x : ℕ × ℕ) := if x.1≤t then f x else 0
  have diff : goldbachCount m - boxCount n m (high n) =
      ∑ x ∈ antidiagonal m, if keep x then 0 else f x := by
    rw [goldbachCount, boxCount, sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    change _ - (if _ then (if x.1^3≤n then 0 else primeLog x.1) *
      (if x.2^3≤n then 0 else primeLog x.2) else 0) = _
    by_cases a : x.1≤n ∧ x.2≤n <;> by_cases b : x.1^3≤n <;> by_cases c : x.2^3≤n <;>
      simp [a,b,c,keep,f,show (n<x.1^3) ↔ ¬x.1^3≤n by omega,show (n<x.2^3) ↔ ¬x.2^3≤n by omega]
  have pos (x) : 0≤f x := mul_nonneg (primeLog_nonneg _) (primeLog_nonneg _)
  have cover (x : ℕ × ℕ) (hx : x ∈ antidiagonal m) (h : ¬keep x) : x.1≤t ∨ x.2≤t := by
    have ha := HasAntidiagonal.mem_antidiagonal.mp hx
    have low (a : ℕ) (h : a^3≤n) : a≤t :=
      (Nat.le_findGreatest (P:=fun p => p^3≤n) ((Nat.le_self_pow (by decide : 3≠0) a).trans h) h).trans hc
    by_contra! hbad
    apply h
    exact ⟨by omega, by omega, lt_of_not_ge (fun h => (not_le.mpr hbad.1) (low _ h)),
      lt_of_not_ge (fun h => (not_le.mpr hbad.2) (low _ h))⟩
  rw [diff]
  constructor
  · exact sum_nonneg (fun x _ => by split_ifs <;> first | exact le_rfl | exact pos _)
  calc
    _ ≤ ∑ x ∈ antidiagonal m, (cut x + cut x.swap) := by
      apply sum_le_sum
      intro x hx
      have e : f x.swap = f x := mul_comm _ _
      by_cases h : keep x
      · simp only [h, ite_true, cut, e]
        split_ifs <;> linarith [pos x]
      · obtain ha|hb := cover x hx h <;> simp only [h, ite_false, cut, Prod.fst_swap, e] <;>
          split_ifs <;> linarith [pos x]
    _ ≤ _ := by
      rw [sum_add_distrib, Finset.Nat.sum_antidiagonal_swap]
      have bound := small_coordinate m t M hm hM
      change (∑ x ∈ antidiagonal m, if x.1≤t then primeLog x.1*primeLog x.2 else 0) + _ ≤ _
      linarith only [show (∑ x ∈ antidiagonal m, cut x) ≤ _ from bound]

/-- For positive offsets the classical count has two disjoint target sums. Removing either
endpoint discards only pairs with one coordinate below an explicit threshold. -/
theorem goldbach_truncation (n k : ℕ) (hk : 0<k) (hkn : k≤n) :
    let E := goldbachCount (n-k) + goldbachCount (n+k) - pairMass n k (high n)
    0 ≤ E ∧ E ≤ 2 * Real.log 4 * (cubeCutoff n + (max (cubeCutoff n) k : ℕ) : ℝ) *
      Real.log (2*n : ℕ) := by
  dsimp only
  rw [mass_split n k hk hkn]
  have hM : 0<2*n := by omega
  obtain ⟨la,ua⟩ := box_error n (n-k) (2*n) (cubeCutoff n) (by omega) hM le_rfl (by omega)
  obtain ⟨lb,ub⟩ := box_error n (n+k) (2*n) (max (cubeCutoff n) k) (by omega) hM (le_max_left _ _) (by omega)
  constructor <;> nlinarith only [la,lb,ua,ub]


/-- Difference between classical and catalogue weights at a positive offset. -/
noncomputable def truncationError (n k : ℕ) : ℝ :=
  goldbachCount (n-k) + goldbachCount (n+k) - pairMass n k (high n)

private theorem cutoff_in_window (n : ℕ) (hscale : 2*(catalogueCutoff n)^2<n) :
    cubeCutoff n ≤ firstBandEnd n := by
  have root : (cubeCutoff n)^3≤n :=
    Nat.findGreatest_spec (P:=fun p=>p^3≤n) (Nat.zero_le _) (by simp)
  have sqr : (cubeCutoff n)^2 ≤ n := by
    by_cases h : cubeCutoff n=0
    · simp [h]
    · exact (Nat.pow_le_pow_right (Nat.pos_of_ne_zero h) (by decide : 2≤3)).trans root
  have hq : 0<catalogueCutoff n := by
    unfold catalogueCutoff
    exact pow_pos (Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1≤n+2 by omega)) _
  apply (Nat.le_div_iff_mul_le hq).mpr
  have h1 : (cubeCutoff n:ℝ)^2 ≤ n := by exact_mod_cast sqr
  have h2 : (catalogueCutoff n:ℝ)^2 ≤ n := by exact_mod_cast (show (catalogueCutoff n)^2≤n by omega)
  exact_mod_cast (show (cubeCutoff n:ℝ)*(catalogueCutoff n)≤n by
    nlinarith only [h1,h2,sq_nonneg ((cubeCutoff n:ℝ)-catalogueCutoff n)])

/-- The pointwise cost on the first band saves a full binary logarithm. -/
theorem first_band_truncation (n k : ℕ) (hscale : 2*(catalogueCutoff n)^2<n)
    (hk : 0<k) (hH : k≤firstBandEnd n) :
    |truncationError n k| * (Nat.log 2 (n+2) : ℝ) ≤ 12 * Real.log 4 * n := by
  let d := Nat.log 2 (n+2)
  have hd : 1≤d := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1≤n+2 by omega)
  have hdr : (1:ℝ)≤d := by exact_mod_cast hd
  have hn : 0<n := by omega
  have hlog : Real.log (2*n:ℕ) ≤ 3*(d:ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
    have h := log_n_le_width n hn
    change Real.log n ≤ ((d+1:ℕ):ℝ) at h
    push_cast at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hr := cutoff_in_window n hscale
  have hmax := max_le hr hH
  have hsum : (cubeCutoff n : ℝ)+(max (cubeCutoff n) k : ℕ) ≤ 2*(firstBandEnd n:ℝ) := by
    exact_mod_cast (show cubeCutoff n + max (cubeCutoff n) k ≤ 2*firstBandEnd n by omega)
  have hq : (firstBandEnd n:ℝ)*(d:ℝ)^2 ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n (catalogueCutoff n)
  obtain ⟨hpos,herr⟩ := goldbach_truncation n k hk (hH.trans (Nat.div_le_self ..))
  rw [abs_of_nonneg (show 0≤truncationError n k from hpos)]
  calc
    _ ≤ (2*Real.log 4 * (2*(firstBandEnd n:ℝ)) * (3*(d:ℝ))) * d := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact herr.trans (by gcongr)
    _ = (12*Real.log 4)*((firstBandEnd n:ℝ)*d^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)

/-- On the catalogue window the full squared truncation error consumes a vanishing
fraction of the variance budget, before any residue-class centering. -/
theorem truncation_variance_negligible (ε : ℝ) (hε : 0<ε) : ∃ N : ℕ, ∀ n≥N,
    let Q := catalogueCutoff n
    let B := logWidth n
    (Q:ℝ) * (∑ k ∈ Ioc (primeBandWidth n) (firstBandEnd n), (truncationError n k)^2) *
      (1+diagonalEnergy Q B) ≤ ε*(n:ℝ)^3 := by
  let C := 12*Real.log 4
  have hC : 0≤C := by dsimp [C]; positivity
  obtain ⟨A,hA⟩ : ∃ A:ℕ, ∀ n≥A, 2*(catalogueCutoff n)^2<n :=
    PEqualNP.Outside.L_goldbach_arc_cutoff_scale
  have ht : Tendsto (fun n : ℕ => (logWidth n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp logWidth_tends
  obtain ⟨M,hM⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (4*C^2/ε+1))
  refine ⟨max A M,fun n hn => ?_⟩
  let Q := catalogueCutoff n
  let d := Nat.log 2 (n+2)
  let W := Ioc (primeBandWidth n) (firstBandEnd n)
  let S := ∑ k ∈ W, (truncationError n k)^2
  have scale := hA n (by omega)
  have hd : 1≤d := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1≤n+2 by omega)
  have hdr : (1:ℝ)≤d := by exact_mod_cast hd
  have hdpos : 0<(d:ℝ) := by linarith
  have hlen : (Q:ℝ)*W.card ≤ n := by
    dsimp [W]
    rw [Nat.card_Ioc]
    exact_mod_cast ((Nat.mul_le_mul_left Q (Nat.sub_le _ _)).trans
      (show Q * firstBandEnd n≤n by rw [mul_comm]; exact Nat.div_mul_le_self ..))
  have hS : S*(d:ℝ)^2 ≤ (W.card:ℝ)*(C*n)^2 := by
    unfold S
    rw [sum_mul]
    calc
      _ ≤ ∑ _k ∈ W, (C*n)^2 := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hk
        have h := first_band_truncation n k scale (by omega) hhi
        rw [← mul_pow]
        simpa only [mul_pow,sq_abs] using
          (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hdpos.le) (mul_nonneg hC (Nat.cast_nonneg _))).mpr h
      _ = _ := by simp
  have hJ : 1+diagonalEnergy Q (logWidth n) ≤ 4*(d:ℝ) := by
    have h := (diagonalEnergy_le_harmonic Q (logWidth n)).trans (cutoff_harmonic n)
    have hw : (logWidth n:ℝ) = (d:ℝ)+1 := by simp [logWidth,d]
    rw [hw] at h
    linarith [Real.log_le_sub_one_of_pos (show 0<(d:ℝ)+1 by positivity)]
  have budget : 4*C^2 ≤ ε*(d:ℝ) := by
    have h := hM n (by omega)
    change 4*C^2/ε+1 ≤ ((d+1:ℕ):ℝ) at h
    push_cast at h
    have hh := (div_le_iff₀ hε).mp (show 4*C^2/ε≤d by linarith)
    linarith
  have hSn : 0≤S := by dsimp [S]; positivity
  change (Q:ℝ)*S*(1+diagonalEnergy Q (logWidth n)) ≤ _
  apply (mul_le_mul_iff_left₀ hdpos).mp
  calc
    _ ≤ ((Q:ℝ)*S*(4*d))*d := by gcongr
    _ = 4*Q*(S*(d:ℝ)^2) := by ring
    _ ≤ 4*Q*((W.card:ℝ)*(C*n)^2) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (4*(C*n)^2)*((Q:ℝ)*W.card) := by ring
    _ ≤ (4*(C*n)^2)*n := mul_le_mul_of_nonneg_left hlen (by positivity)
    _ = (4*C^2)*(n:ℝ)^3 := by ring
    _ ≤ (ε*(d:ℝ))*(n:ℝ)^3 := mul_le_mul_of_nonneg_right budget (by positivity)
    _ = _ := by ring

/-- Class deviations are orthogonal to every function of the residue. -/
theorem classDeviation_orthogonal (n P : ℕ) (hP : 0 < P) (f : ℕ → ℝ) :
    ∑ k ∈ Ioc (primeBandWidth n) (firstBandEnd n),
      classDeviation n P k * f (k % P) = 0 := by
  let W := Ioc (primeBandWidth n) (firstBandEnd n)
  have maps : ∀ k ∈ W, k % P ∈ range P := fun k _ => mem_range.mpr (Nat.mod_lt k hP)
  rw [← sum_fiberwise_of_maps_to maps]
  apply sum_eq_zero
  intro r _
  change ∑ k ∈ residueWindow _ _ P r, _ = 0
  calc
    _ = ∑ k ∈ residueWindow (primeBandWidth n) (firstBandEnd n) P r,
        (pairMass n k (high n) - residueMean n P r) * f r := by
      apply sum_congr rfl
      intro k hk
      rw [classDeviation, (mem_filter.mp hk).2]
    _ = 0 := by rw [← sum_mul, centered_class_sum, zero_mul]


/-- Taking class means minimizes squared error among all residue-dependent profiles. -/
theorem classEnergy_le_profile (n P : ℕ) (hP : 0<P) (b : ℕ → ℝ) : classEnergy n P ≤
    ∑ k ∈ Ioc (primeBandWidth n) (firstBandEnd n), (pairMass n k (high n)-b (k%P))^2 := by
  let f (r : ℕ) := residueMean n P r - b r
  have zero := classDeviation_orthogonal n P hP f
  have split (k : ℕ) : (pairMass n k (high n)-b (k%P))^2 =
      (classDeviation n P k)^2 + (f (k%P))^2 + 2*(classDeviation n P k*f (k%P)) := by
    unfold classDeviation f
    ring
  simp_rw [split,sum_add_distrib,← mul_sum,zero,mul_zero,add_zero]
  unfold classEnergy
  exact le_add_of_nonneg_right (sum_nonneg fun _ _ => sq_nonneg _)

/-- The prime-pair input may be proved for the classical untruncated count and any
admissible periodic profile. -/
theorem outer_iff_of_goldbach_profile (period : ℕ → ℕ) (b : ℕ → ℕ → ℝ)
    (hp : ∀ n≥2, 0<period n ∧ period n ≤ logWidth n)
    (hv : ∀ δ:ℝ, 0<δ → ∃ N:ℕ, ∀ n≥N, Even n →
      let Q := catalogueCutoff n
      (Q:ℝ)*(∑ k ∈ Ioc (primeBandWidth n) (firstBandEnd n),
        (goldbachCount (n-k)+goldbachCount (n+k)-b n (k % period n))^2)*
        (1+diagonalEnergy Q (logWidth n)) ≤ δ*(n:ℝ)^3) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      outerAndSmall n ≤ pairMass n 0 (high n)*(1-arcLength (catalogueCutoff n) n) + ε*n := by
  apply outer_iff_of_variance period hp
  intro δ hδ
  obtain ⟨A,hA⟩ := hv (δ/4) (by positivity)
  obtain ⟨M,hM⟩ := truncation_variance_negligible (δ/4) (by positivity)
  refine ⟨max 2 (max A M), fun n hn hev => ?_⟩
  let W := Ioc (primeBandWidth n) (firstBandEnd n)
  let J := 1 + diagonalEnergy (catalogueCutoff n) (logWidth n)
  let Q := (catalogueCutoff n : ℝ)
  let e (k : ℕ) := goldbachCount (n-k)+goldbachCount (n+k)-b n (k % period n)
  let E := ∑ k ∈ W, (e k)^2
  let T := ∑ k ∈ W, (truncationError n k)^2
  have hJ : 0≤J := by dsimp [J,diagonalEnergy]; positivity
  have hQ : 0≤Q := by positivity
  have ec : classEnergy n (period n) ≤ 2*E+2*T := by
    refine (classEnergy_le_profile n (period n) (hp n (by omega)).1 (b n)).trans ?_
    unfold E T
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro k _
    have eq : pairMass n k (high n)-b n (k % period n) = e k - truncationError n k := by
      unfold e truncationError
      ring
    rw [eq]
    nlinarith only [sq_nonneg (e k + truncationError n k)]
  have he : Q*E*J ≤ (δ/4)*(n:ℝ)^3 := hA n (by omega) hev
  have ht : Q*T*J ≤ (δ/4)*(n:ℝ)^3 := hM n (by omega)
  change Q*classEnergy n (period n)*J ≤ _
  nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ec hQ) hJ,he,ht]

#print axioms goldbach_truncation
#print axioms truncation_variance_negligible
#print axioms outer_iff_of_goldbach_profile
end GoldbachMinor
