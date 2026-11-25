import WideMinorMean
import WideGeometry
import WidePolylog
import WideKernel

namespace GoldbachMinor
open Finset MeasureTheory Filter GoldbachWeight
open scoped Topology

private theorem additive_phase (u v : ℝ) : phase (u+v)=phase u*phase v := by
  unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem full_integer_mode (k : ℤ) :
    (∫ t in (0:ℝ)..1, phase ((k:ℝ)*t)) = if k=0 then 1 else 0 := by
  have empty : catalogueArcs 0 1 = ∅ := by
    apply Set.eq_empty_of_forall_notMem; rintro t ⟨q,a,h,hh,_⟩; omega
  have h := minor_mode 0 1 (by decide) k
  rw [empty,Set.compl_empty,Set.indicator_univ] at h
  have eq (t : ℝ) : phase ((k:ℝ)*t) = mode k t := by unfold phase mode; congr 3; ring
  simp_rw [eq]
  rw [h]
  by_cases z : k=0 <;> simp [z,minorCoefficient,majorCoefficient,arcLength]

noncomputable def commonIntegrand (X n : ℕ) (t : ℝ) :=
  (GoldbachWeight.spectrum X primeLog t)^2*phase (-(n:ℝ)*t)

private theorem common_cont (X n : ℕ) : Continuous (commonIntegrand X n) := by
  unfold commonIntegrand GoldbachWeight.spectrum phase; fun_prop

/-- Extending the prime spectrum up to X leaves its full-circle coefficient
at every frequency n≤X equal to the ordered log-weighted count. -/
theorem common_full_count (X n : ℕ) (hn : n ≤ X) :
    (∫ t in (0:ℝ)..1, commonIntegrand X n t) = (goldbachCount n:ℂ) := by
  let I := range (X+1)
  let w := primeLog
  let term (k j : ℕ) (t : ℝ) := ((w k:ℂ)*(w j:ℂ))*phase ((((k:ℤ)+j-n:ℤ):ℝ)*t)
  have ct (k j) : Continuous (term k j) := by dsimp [term,phase]; fun_prop
  have expand (t : ℝ) : commonIntegrand X n t = ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [commonIntegrand, GoldbachWeight.spectrum,sq,sum_mul,mul_sum]
    apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro j _
    dsimp only [term,w]; push_cast
    rw [show ((k:ℝ)+j-n)*t = ((k:ℝ)*t+j*t)+ -(n:ℝ)*t by ring,additive_phase,additive_phase]
    ring
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (continuous_finsetSum I (fun j _ => ct k j)).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => (ct _ j).intervalIntegrable _ _)]
  let F (z : ℕ × ℕ) : ℂ := (w z.1:ℂ)*(w z.2:ℂ)
  have pairs : ((I ×ˢ I)).filter (fun z => z.1+z.2=n) = antidiagonal n := by
    ext ⟨a,b⟩
    simp only [mem_filter,mem_product,I,mem_range,HasAntidiagonal.mem_antidiagonal]
    omega
  calc
    _ = ∑ z ∈ (I ×ˢ I), if z.1+z.2=n then F z else 0 := by
      rw [sum_product]
      apply sum_congr rfl; intro k _
      apply sum_congr rfl; intro j _
      simp only [term,intervalIntegral.integral_const_mul,full_integer_mode]
      by_cases eq : k+j=n
      · simp only [show (k:ℤ)+j-n=0 by omega,eq,ite_true,mul_one,F]
      · simp only [show (k:ℤ)+j-n≠0 by omega,eq,ite_false,mul_zero]
    _ = _ := by rw [← sum_filter,pairs]; simp [goldbachCount,F,w]

noncomputable def commonArcModel (Q X n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 Q, (ramWeight q n:ℂ)*
    ∫ t in -(GoldbachBlockGeometry.width Q X q)..GoldbachBlockGeometry.width Q X q,
      GoldbachEstermannKernel.twisted X n t

private theorem major_error_bound (X n Q : ℕ) (sep : 2*Q^2<X) :
    ‖GoldbachBlockGeometry.majorContribution Q X (commonIntegrand X n)-commonArcModel Q X n‖ ≤
      GoldbachMajorArc.Polylog.totalArcError Q X n := by
  let C (q a : ℕ) := (GoldbachMajorArc.unitMean q a)^2*phase (-(n:ℝ)*((a:ℝ)/q))
  let K := GoldbachEstermannKernel.twisted X n
  have kc : Continuous K := by
    change Continuous (GoldbachEstermannKernel.twisted X n)
    unfold GoldbachEstermannKernel.twisted GoldbachEstermannKernel.kernel GoldbachEstermannKernel.phase
    fun_prop
  have integralPhase : phase (-(n:ℝ)) = 1 := by
    unfold phase
    convert Complex.exp_int_mul_two_pi_mul_I (-(n:ℤ)) using 2
    push_cast; ring
  have ends : C 1 0=C 1 1 := by
    dsimp only [C]
    rw [desk_unit_mean 1 0 (by decide) (by decide),desk_unit_mean 1 1 (by decide) (by decide)]
    simp only [Nat.cast_zero,mul_zero,Nat.cast_one,div_one,mul_one,integralPhase]
    simp [phase]
  have geom := GoldbachBlockGeometry.major_error (commonIntegrand X n) K (common_cont ..) kc C ends sep
  have coeff (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (∑ a ∈ (range q).filter (·.Coprime q), C q a) = (ramWeight q n:ℂ) := by
    have qp := (mem_Icc.mp hq).1
    let b : ℂ := (((ArithmeticFunction.moebius q:ℝ)/q.totient:ℝ):ℂ)
    calc
      _ = ∑ a ∈ (range q).filter (·.Coprime q), b^2*phase (-(n:ℝ)*((a:ℝ)/q)) :=
        sum_congr rfl fun a ha => by dsimp only [C]; rw [desk_unit_mean q a qp (mem_filter.mp ha).2]
      _ = _ := by rw [← mul_sum, center_trace q n qp]; simp only [b,ramWeight,Complex.ofReal_mul,Complex.ofReal_pow]; ring
  have term (q a : ℕ) (t : ℝ) :
      C q a*K t = (GoldbachMajorArc.unitMean q a*GoldbachMajorArc.kernel X t)^2*
        GoldbachMajorArc.phase (-(n:ℝ)*(GoldbachBlockGeometry.center q a+t)) := by
    change _ = _*phase _
    rw [mul_add,additive_phase]
    change (_^2*phase (-(n:ℝ)*((a:ℝ)/q)))*(GoldbachMajorArc.kernel X t^2*phase (-(n:ℝ)*t)) =
      (_*GoldbachMajorArc.kernel X t)^2*(phase (-(n:ℝ)*((a:ℝ)/q))*phase (-(n:ℝ)*t))
    ring
  have eq : (∑ q ∈ Icc 1 Q, (∑ a ∈ (range q).filter (·.Coprime q), C q a)*
      ∫ t in -(GoldbachBlockGeometry.width Q X q)..GoldbachBlockGeometry.width Q X q, K t) = commonArcModel Q X n :=
    sum_congr rfl fun q hq => by rw [coeff q hq]
  rw [eq] at geom
  simp_rw [term] at geom
  exact geom

theorem wide_scale : ∀ᶠ X : ℕ in atTop, 2*(wideCutoff X)^2 < X := by
  have h := (isLittleO_log_rpow_rpow_atTop (40:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
  have lim : Tendsto (fun x : ℝ => (Real.log x)^40/x) atTop (𝓝 0) := by simpa using h
  filter_upwards [(lim.comp tendsto_natCast_atTop_atTop).eventually_lt_const
    (show (0:ℝ)<1/(2*4^40) by positivity),eventually_ge_atTop 2] with X hs hx
  have b := GoldbachMajorArc.Polylog.cutoff_le_log 20 hx
  change (wideCutoff X:ℝ) ≤ _ at b
  change (Real.log X)^40/X < _ at hs
  have xp : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have p := pow_le_pow_left₀ (Nat.cast_nonneg (wideCutoff X): (0:ℝ)≤_) b 2
  have h1 := (div_lt_div_iff₀ xp (by norm_num : (0:ℝ)<2*4^40)).mp hs
  exact_mod_cast (show 2*(wideCutoff X:ℝ)^2 < X by nlinarith only [p,h1])

set_option maxHeartbeats 900000 in
/-- One threshold in the anchor X works for every mode below that anchor. -/
theorem common_count_projection (ε : ℝ) (he : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ n ≤ X, ‖(goldbachCount n:ℂ)-commonArcModel (wideCutoff X) X n‖ ≤
      ‖commonMinor X n‖ + ε*X := by
  have e := GoldbachMajorArc.Polylog.eventually_totalArcError_lt 20 0 (by decide) he
  filter_upwards [wide_scale,e] with X sep small
  intro n hn
  have split := integral_complement (catalogueArcs (wideCutoff X) X) (measurable_catalogue ..)
    (commonIntegrand X n) (common_cont ..)
  rw [common_full_count X n hn] at split
  let major := GoldbachBlockGeometry.majorContribution (wideCutoff X) X (commonIntegrand X n)
  have id : (goldbachCount n:ℂ) - major = commonMinor X n := split.symm
  have estimate := major_error_bound X n (wideCutoff X) sep
  have saving : GoldbachMajorArc.Polylog.totalArcError (wideCutoff X) X n ≤ ε*X := by
    simpa only [wideCutoff,GoldbachMajorArc.Polylog.cutoff,pow_zero,one_mul] using (small (n:ℝ)).le
  calc
    _ ≤ ‖(goldbachCount n:ℂ)-major‖+‖major-commonArcModel (wideCutoff X) X n‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ _ := add_le_add (congrArg norm id).le (estimate.trans saving)

#print axioms common_count_projection
end GoldbachMinor
