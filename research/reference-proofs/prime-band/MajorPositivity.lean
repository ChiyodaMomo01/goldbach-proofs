import MajorPairFloor

namespace GoldbachMinor
open Finset ArithmeticFunction

/-- Upper bound for every finite product over the potential odd-prime losses. -/
private theorem odd_loss_product (k : ℕ) :
    (∏ j ∈ range k, (1+1/(2*((j:ℝ)+1))^2)) ≤ (3*(k:ℝ)+2)/(2*((k:ℝ)+1)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [prod_range_succ,Nat.cast_succ]
    apply (mul_le_mul_of_nonneg_right ih (by positivity)).trans
    have a : (0:ℝ)<2*((k:ℝ)+1) := by positivity
    have b : (0:ℝ)<2*((k:ℝ)+1+1) := by positivity
    rw [le_div_iff₀ b]
    field_simp
    nlinarith [sq_nonneg (k:ℝ),Nat.cast_nonneg (α:=ℝ) k]

noncomputable def lossFactor (p : ℕ) : ℝ := 1+1/((p:ℝ)-1)^2

theorem bad_prime_product_bound (S : Finset ℕ)
    (oddPrimes : ∀ p∈S, Nat.Prime p ∧ p≠2) :
    (∏ p ∈ S, lossFactor p)≤3/2 := by
  let k := S.sup id
  let f (j : ℕ) := 2*(j+1)+1
  have sub : S⊆(range k).image f := by
    intro p hp
    have h := oddPrimes p hp
    obtain ⟨r,hr⟩ := h.1.odd_of_ne_two h.2
    have hp2 := h.1.two_le
    have hpk : p≤k := Finset.le_sup (f:=id) hp
    exact mem_image.mpr ⟨r-1,mem_range.mpr (by omega),by dsimp [f]; omega⟩
  have one (p : ℕ) : 1≤lossFactor p := le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ ∏ p ∈ (range k).image f, lossFactor p := by
      exact prod_le_prod_of_subset_of_one_le₀ sub (fun p _ => zero_le_one.trans (one p)) (fun p _ _ => one p)
    _ = ∏ j ∈ range k, (1+1/(2*((j:ℝ)+1))^2) := by
      rw [prod_image (fun a _ b _ (h:f a=f b) => by dsimp [f] at h; omega)]
      apply prod_congr rfl
      intro j _
      simp [lossFactor,f]
    _ ≤ _ := (odd_loss_product k).trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)

private def divisorWeight (n : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun d => if d∣n then (d:ℤ) else 0, by simp⟩

private theorem divisorWeight_mult (n : ℕ) : (divisorWeight n).IsMultiplicative := by
  refine ⟨by simp [divisorWeight],?_⟩
  intro a b hab
  have h : a*b∣n ↔ a∣n ∧ b∣n :=
    ⟨fun e => ⟨(dvd_mul_right a b).trans e,(dvd_mul_left b a).trans e⟩,
     fun e => hab.mul_dvd_of_dvd_of_dvd e.1 e.2⟩
  change (if a*b∣n then ((a*b:ℕ):ℤ) else 0) =
    (if a∣n then (a:ℤ) else 0)*(if b∣n then (b:ℤ) else 0)
  by_cases ha : a∣n <;> by_cases hb : b∣n <;> simp [h,ha,hb]

theorem ram_squarefree_product (q n : ℕ) (sq : Squarefree q) :
    ram q n=∏ p ∈ q.primeFactors, (if p∣n then (p:ℝ)-1 else -1) := by
  have mult : (ArithmeticFunction.moebius : ArithmeticFunction ℤ).IsMultiplicative := by arith_mult
  have h := (divisorWeight_mult n).prodPrimeFactors_add_of_squarefree mult sq
  rw [prodPrimeFactors_apply sq.ne_zero,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun d e => divisorWeight n d*ArithmeticFunction.moebius e)] at h
  have lifted := congrArg (fun x : ℤ => (x:ℝ)) h.symm
  push_cast at lifted
  unfold ram
  convert lifted using 1
  · apply sum_congr rfl
    intro d _
    by_cases hd : d∣n <;> simp [divisorWeight,hd]
  · apply prod_congr rfl
    intro p hp
    have pr := Nat.prime_of_mem_primeFactors hp
    by_cases hd : p∣n <;> simp [divisorWeight,hd,moebius_apply_prime pr]
    ring

/-- Monotone truncation may vary with the support. Any nonempty negative
support costs at most the empty-support mass times its absolute Euler weight. -/
theorem signed_bad_support_floor (S : Finset ℕ) (hS : ∀ p∈S, Nat.Prime p ∧ p≠2)
    (K : Finset ℕ→ℝ) (hK : ∀ B∈S.powerset, 0≤K B ∧ K B≤K ∅) :
    K ∅/2 ≤ ∑ B ∈ S.powerset, (∏ p ∈ B, -(1/((p:ℝ)-1)^2)) * K B := by
  let b (p : ℕ) := 1/((p:ℝ)-1)^2
  have b0 (p) : 0≤b p := by dsimp [b]; positivity
  have k0 := (hK ∅ (mem_powerset.mpr (empty_subset _))).1
  have total : (∑ B ∈ S.powerset, ∏ p ∈ B, b p)≤3/2 := by
    rw [← prod_one_add]
    exact bad_prime_product_bound S hS
  have each (B) (hB : B∈S.powerset) :
      (if B=∅ then 2*K ∅ else 0) ≤ (∏ p ∈ B, -b p)*K B+(∏ p ∈ B, b p)*K ∅ := by
    by_cases e : B=∅
    · simp [e]; ring_nf; rfl
    rw [ite_eq_right e]
    have absprod : |∏ p ∈ B, -b p|=∏ p ∈ B, b p := by
      rw [Finset.abs_prod]
      exact prod_congr rfl fun p _ => by simp [abs_of_nonneg (b0 p)]
    have lo := neg_abs_le (∏ p ∈ B, -b p)
    rw [absprod] at lo
    have pn := prod_nonneg (fun p (_ : p∈B) => b0 p)
    nlinarith only [mul_le_mul_of_nonneg_right lo (hK B hB).1,
      mul_le_mul_of_nonneg_left (hK B hB).2 pn]
  have sum := sum_le_sum each
  rw [sum_add_distrib,← sum_mul] at sum
  have zz : (∑ B ∈ S.powerset, if B=∅ then 2*K ∅ else 0)=2*K ∅ := by simp
  rw [zz] at sum
  change K ∅/2 ≤ ∑ B ∈ S.powerset, (∏ p ∈ B, -b p)*K B
  linarith only [sum,mul_le_mul_of_nonneg_right total k0]

noncomputable def localSign (n p : ℕ) : ℝ :=
  if p∣n then 1/((p:ℝ)-1) else -(1/((p:ℝ)-1)^2)

private theorem coefficient_factorization (n q : ℕ) (sq : Squarefree q) :
    ram q n*((ArithmeticFunction.moebius q:ℝ)/q.totient)^2 = ∏ p ∈ q.primeFactors, localSign n p := by
  have phi : q.totient=∏ p ∈ q.primeFactors, (p-1) := by
    have h := Nat.totient_mul_prod_primeFactors q
    rw [Nat.prod_primeFactors_of_squarefree sq,Nat.mul_comm q.totient] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero sq.ne_zero) h
  have phi' : (q.totient:ℝ)=∏ p ∈ q.primeFactors, ((p:ℝ)-1) := by
    rw [phi,Nat.cast_prod]; apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).pos,Nat.cast_one]
  have mu : (ArithmeticFunction.moebius q:ℝ)^2=1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree sq
  rw [ram_squarefree_product q n sq,div_pow,mu,phi',← prod_pow,mul_one_div,← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  have h : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have nz : (p:ℝ)-1≠0 := by linarith
  by_cases hd : p∣n <;> simp only [localSign,hd,ite_true,ite_false] <;> field_simp

private def supportProduct (A : Finset ℕ) := ∏ p ∈ A, p

private theorem support_sq (A : Finset ℕ) (pr : ∀ p∈A, Nat.Prime p) :
    Squarefree (supportProduct A) := by
  have h := Nat.squarefree_prod_primeFactors (supportProduct A)
  simpa only [supportProduct,Nat.primeFactors_prod pr] using h

private noncomputable def windowKernel (Q q : ℕ) : ℝ :=
  if q≤Q then archimedeanMass ((Q:ℝ)/q) else 0

private theorem model_support_sum (n Q : ℕ) :
    (∑ q ∈ Icc 1 Q, ram q n*((ArithmeticFunction.moebius q:ℝ)/q.totient)^2*archimedeanMass ((Q:ℝ)/q)) =
    ∑ A ∈ (Nat.primesLE Q).powerset, (∏ p ∈ A, localSign n p)*windowKernel Q (supportProduct A) := by
  let D := (Icc 1 Q).filter Squarefree
  let T := (Nat.primesLE Q).powerset
  have pr (A) (hA : A∈T) : ∀ p∈A, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp hA hp)
  calc
    _ = ∑ q ∈ D, (∏ p ∈ q.primeFactors, localSign n p)*archimedeanMass ((Q:ℝ)/q) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro q _
      by_cases h : Squarefree q
      · rw [ite_eq_left h,coefficient_factorization n q h]
      · simp [h,moebius_eq_zero_of_not_squarefree h]
    _ = ∑ A ∈ T.filter (fun A => supportProduct A≤Q),
        (∏ p ∈ A, localSign n p)*archimedeanMass ((Q:ℝ)/(supportProduct A)) := by
      apply sum_bij (fun q _ => q.primeFactors)
      · intro q hq
        obtain ⟨hq,sq⟩ := mem_filter.mp hq
        refine mem_filter.mpr ⟨mem_powerset.mpr (fun p hp => Nat.mem_primesLE.mpr
          ⟨(Nat.le_of_mem_primeFactors hp).trans (mem_Icc.mp hq).2,Nat.prime_of_mem_primeFactors hp⟩),?_⟩
        simpa [supportProduct,Nat.prod_primeFactors_of_squarefree sq] using (mem_Icc.mp hq).2
      · intro a ha b hb he
        rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2,
          ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2,he]
      · intro A hA
        obtain ⟨ha,hle⟩ := mem_filter.mp hA
        have sq := support_sq A (pr A ha)
        exact ⟨supportProduct A,mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero sq.ne_zero,hle⟩,sq⟩,
          Nat.primeFactors_prod (pr A ha)⟩
      · intro q hq
        rw [supportProduct,Nat.prod_primeFactors_of_squarefree (mem_filter.mp hq).2]
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro A _
      by_cases h : supportProduct A≤Q <;> simp [windowKernel,h]

private theorem split_support (G B : Finset ℕ) (dis : Disjoint G B) (f : Finset ℕ→ℝ) :
    (∑ A ∈ (G∪B).powerset, f A) = ∑ R ∈ G.powerset, ∑ C ∈ B.powerset, f (R∪C) := by
  rw [← sum_product (f:=fun x : Finset ℕ × Finset ℕ => f (x.1∪x.2))]
  symm
  apply sum_bij (fun x _ => x.1∪x.2)
  · intro x hx
    obtain ⟨r,c⟩ := mem_product.mp hx
    exact mem_powerset.mpr (union_subset_union (mem_powerset.mp r) (mem_powerset.mp c))
  · rintro ⟨r,c⟩ hx ⟨r',c'⟩ hy e
    obtain ⟨xr,xc⟩ := mem_product.mp hx
    obtain ⟨yr,yc⟩ := mem_product.mp hy
    have hG (r c : Finset ℕ) (hr : r⊆G) (hc : c⊆B) : (r∪c)∩G=r := by
      ext p; simp only [mem_inter,mem_union]
      have neg (hp : p∈c) (hg : p∈G) := Finset.disjoint_left.mp dis hg (hc hp)
      tauto
    have hB (r c : Finset ℕ) (hr : r⊆G) (hc : c⊆B) : (r∪c)∩B=c := by
      ext p; simp only [mem_inter,mem_union]
      have neg (hp : p∈r) (hb : p∈B) := Finset.disjoint_left.mp dis (hr hp) hb
      tauto
    apply Prod.ext
    · simpa only [hG r c (mem_powerset.mp xr) (mem_powerset.mp xc),
        hG r' c' (mem_powerset.mp yr) (mem_powerset.mp yc)] using congrArg (fun t => t∩G) e
    · simpa only [hB r c (mem_powerset.mp xr) (mem_powerset.mp xc),
        hB r' c' (mem_powerset.mp yr) (mem_powerset.mp yc)] using congrArg (fun t => t∩B) e
  · intro A ha
    refine ⟨(A∩G,A∩B),mem_product.mpr ⟨mem_powerset.mpr inter_subset_right,mem_powerset.mpr inter_subset_right⟩,?_⟩
    ext p
    have h : A⊆G∪B := mem_powerset.mp ha
    simp only [mem_union,mem_inter]
    have h' (hp : p∈A) := mem_union.mp (h hp)
    tauto
  · intro _ _; rfl

private theorem archimedean_nonneg (z : ℝ) (hz : 0≤z) : 0≤archimedeanMass z :=
  intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)

private theorem archimedean_mono (x y : ℝ) (hx : 0≤x) (h : x≤y) : archimedeanMass x≤archimedeanMass y := by
  apply intervalIntegral.integral_mono_interval (neg_le_neg h) (by linarith) h
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) ((by fun_prop : Continuous _).intervalIntegrable ..)

theorem archimedean_one_pos : 0<archimedeanMass 1 := by
  apply intervalIntegral.integral_pos (by norm_num) (by fun_prop) (fun _ _ => sq_nonneg _)
  exact ⟨0,by norm_num,by simp⟩

private theorem kernel_nonneg (Q q : ℕ) : 0≤windowKernel Q q := by
  unfold windowKernel
  split_ifs <;> first | exact archimedean_nonneg _ (by positivity) | rfl

private theorem kernel_decreases (Q a b : ℕ) (ha : 0<a) (h : a≤b) :
    windowKernel Q b ≤ windowKernel Q a := by
  by_cases hb : b≤Q
  · simp only [windowKernel,hb,h.trans hb,ite_true]
    exact archimedean_mono _ _ (by positivity) (div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast ha) (by exact_mod_cast h))
  · rw [windowKernel,ite_eq_right hb]
    exact kernel_nonneg Q a

/-- Every even target retains at least half the denominator-one mass, for
every integer cutoff, before sending the target or cutoff to infinity. -/
theorem even_major_kernel_floor (n Q : ℕ) (even : Even n) (hq : 1≤Q) :
    archimedeanMass 1/2 ≤ ∑ q ∈ Icc 1 Q, ram q n*((ArithmeticFunction.moebius q:ℝ)/q.totient)^2*
      archimedeanMass ((Q:ℝ)/q) := by
  let S := Nat.primesLE Q
  let G := S.filter (· ∣ n)
  let B := S.filter (fun p => ¬p∣n)
  have un : G∪B=S := by ext p; simp [G,B]; tauto
  have dis : Disjoint G B := by
    apply Finset.disjoint_left.mpr
    intro p hg hb
    exact (mem_filter.mp hb).2 (mem_filter.mp hg).2
  have oddB (p) (hb : p∈B) : Nat.Prime p ∧ p≠2 :=
    ⟨Nat.prime_of_mem_primesLE (mem_filter.mp hb).1, fun e =>
      (mem_filter.mp hb).2 (e ▸ even_iff_two_dvd.mp even)⟩
  let g (R : Finset ℕ) := ∏ p ∈ R, localSign n p
  let K (R C : Finset ℕ) := windowKernel Q (supportProduct (R∪C))
  have grouped (R : Finset ℕ) (hr : R∈G.powerset) :
      g R * windowKernel Q (supportProduct R)/2 ≤
        ∑ C ∈ B.powerset, (∏ p ∈ R∪C,localSign n p)*K R C := by
    have g0 : 0≤g R := prod_nonneg fun p hp => by
      rw [localSign,ite_eq_left ((mem_filter.mp (mem_powerset.mp hr hp)).2)]
      have pr := Nat.prime_of_mem_primesLE (mem_filter.mp (mem_powerset.mp hr hp)).1
      have h : 1≤(p:ℝ) := by exact_mod_cast pr.pos
      positivity
    have posR : 0<supportProduct R := prod_pos (fun p hp => (Nat.prime_of_mem_primesLE
      (mem_filter.mp (mem_powerset.mp hr hp)).1).pos)
    have kk (C) (hc : C∈B.powerset) : 0≤K R C ∧ K R C≤K R ∅ := by
      refine ⟨kernel_nonneg ..,?_⟩
      dsimp [K]; rw [union_empty]
      apply kernel_decreases Q _ _ posR
      apply Nat.le_of_dvd _ (prod_dvd_prod_of_subset _ _ id subset_union_left)
      apply prod_pos
      intro p hp
      rcases mem_union.mp hp with hp|hp
      · exact (Nat.prime_of_mem_primesLE (mem_filter.mp (mem_powerset.mp hr hp)).1).pos
      · exact (oddB p (mem_powerset.mp hc hp)).1.pos
    have low := mul_le_mul_of_nonneg_left (signed_bad_support_floor B oddB (K R) kk) g0
    dsimp only [K] at low
    rw [union_empty,mul_div_assoc',mul_sum] at low
    apply low.trans_eq
    apply sum_congr rfl
    intro C hc
    rw [prod_union (dis.mono (mem_powerset.mp hr) (mem_powerset.mp hc)),← mul_assoc]
    congr 2
    apply prod_congr rfl
    intro p hp
    exact (ite_eq_right ((mem_filter.mp (mem_powerset.mp hc hp)).2)).symm
  rw [model_support_sum]
  change _ ≤ ∑ A ∈ S.powerset, (∏ p ∈ A,localSign n p)*windowKernel Q (supportProduct A)
  rw [← un,split_support G B dis]
  apply le_trans _ (sum_le_sum grouped)
  have emp : ∅∈G.powerset := mem_powerset.mpr (empty_subset _)
  have one : archimedeanMass 1≤windowKernel Q (supportProduct ∅) := by
    simp only [supportProduct,prod_empty,windowKernel,hq,ite_true,Nat.cast_one,div_one]
    exact archimedean_mono _ _ zero_le_one (by exact_mod_cast hq)
  calc
    _ ≤ g ∅*windowKernel Q (supportProduct ∅)/2 := by simpa [g] using (div_le_div_of_nonneg_right one (by norm_num : (0:ℝ)≤2))
    _ ≤ _ := by
      apply single_le_sum (f:=fun R => g R*windowKernel Q (supportProduct R)/2) _ emp
      intro R hr
      have hg : 0≤g R := prod_nonneg fun p hp => by
        have pg := mem_filter.mp (mem_powerset.mp hr hp : p∈G)
        have pr := Nat.prime_of_mem_primesLE pg.1
        have h : (1:ℝ)≤p := by exact_mod_cast pr.pos
        rw [localSign,ite_eq_left pg.2]; positivity
      exact div_nonneg (mul_nonneg hg (kernel_nonneg ..)) (by norm_num)

theorem even_major_model_floor (n : ℕ) (he : Even n) :
    (archimedeanMass 1/2)*n ≤ catalogueMajorModel n := by
  have h : 1≤Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (show 2^1≤n+2 by omega)
  have hQ : 1≤catalogueCutoff n := Nat.one_le_pow _ _ h
  rw [catalogueMajorModel,mul_comm (archimedeanMass 1/2)]
  exact mul_le_mul_of_nonneg_left (even_major_kernel_floor n _ he hQ) (Nat.cast_nonneg _)

/-- The full log-weighted prime integral has a positive linear major-arc floor
on the catalogue's arcs under the sole external input, Vaughan's Theorem 5. -/
theorem full_prime_major_floor (v : VaughanMajorArcEstimate) : ∃ c : ℝ, ∃ N : ℕ,
    0<c ∧ ∀ n≥N, Even n → c*n≤(catalogueMajorValue (catalogueCutoff n) n primeLog).re := by
  let c := archimedeanMass 1/4
  have cp : 0<c := div_pos archimedean_one_pos (by norm_num)
  have logs : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp ((full_major_model_projection v).and
    (logs.eventually_ge_atTop (18/c)))
  refine ⟨c,N,cp,fun n hn he => ?_⟩
  obtain ⟨h,hlog⟩ := hN n hn
  have zp : 0<Real.log n := lt_of_lt_of_le (by positivity : 0<18/c) hlog
  have error : 18*(n:ℝ)/Real.log n ≤ c*n := by
    apply (div_le_iff₀ zp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right ((div_le_iff₀ cp).mp hlog) (Nat.cast_nonneg (α:=ℝ) n)]
  have est := (Complex.abs_re_le_norm (catalogueMajorValue (catalogueCutoff n) n primeLog-(catalogueMajorModel n:ℂ))).trans (h.trans error)
  simp only [Complex.sub_re,Complex.ofReal_re] at est
  have low := (abs_le.mp est).1
  dsimp [c] at low ⊢
  linarith only [low,even_major_model_floor n he]

/-- With the analytic major-arc estimate as input, the frozen bulk floor would
give ordinary two-prime representations for all sufficiently large even targets. -/
theorem bulk_implies_eventual_goldbach_of_fit (fit : MajorModelFits) (bulk : FrozenBulk.BulkFloor) :
    ∃ N:ℕ, ∀ n≥N, Even n → ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p+r=n := by
  have cp : 0<archimedeanMass 1/4 := div_pos archimedean_one_pos (by norm_num)
  obtain ⟨N,hN⟩ := (bulk_iff_count_of_fit fit).mp bulk _ cp
  refine ⟨max N 1,fun n hn he => ?_⟩
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have pos : 0<goldbachCount n := by
    nlinarith only [hN n (by omega) he,even_major_model_floor n he,mul_pos cp np]
  by_contra none
  have zero : goldbachCount n=0 := by
    apply sum_eq_zero
    intro x hx
    have eq := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    by_cases p : x.1.Prime
    · have r : ¬x.2.Prime := fun r => none ⟨_,_,p,r,eq⟩
      simp [primeLog,r]
    · simp [primeLog,p]
  linarith

theorem bulk_implies_eventual_goldbach (v : VaughanMajorArcEstimate) (bulk : FrozenBulk.BulkFloor) :
    ∃ N:ℕ, ∀ n≥N, Even n → ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p+r=n :=
  bulk_implies_eventual_goldbach_of_fit (major_model_negligible v) bulk

#print axioms full_prime_major_floor
#print axioms bulk_implies_eventual_goldbach
#print axioms even_major_kernel_floor
#print axioms split_support
#print axioms model_support_sum
#print axioms signed_bad_support_floor
#print axioms bad_prime_product_bound
#print axioms ram_squarefree_product
end GoldbachMinor
