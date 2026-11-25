import CommonArcProjection
import CommonKernelTail

namespace GoldbachMinor
open Finset Filter MeasureTheory
open scoped Topology

private noncomputable def arcFactor (Q X n q : ℕ) : ℝ :=
  if q ∈ Icc 1 Q then (∫ t in -(GoldbachBlockGeometry.width Q X q)..GoldbachBlockGeometry.width Q X q,
    GoldbachEstermannKernel.twisted X n t).re else 0

private noncomputable def errorFactor (Q q : ℕ) : ℝ := min 4 ((4*q+2:ℝ)/Q)

private theorem error_bounds (Q q : ℕ) : 0 ≤ errorFactor Q q ∧ errorFactor Q q ≤ 4 :=
  ⟨le_min (by norm_num) (by positivity),min_le_left ..⟩

/-- The target may be anywhere in the upper half of the common spectrum.
The bound is summably dominated and tends to zero for every fixed denominator. -/
private theorem factor_error (Q X n q : ℕ) (hq : 0<q) (hQ : 0<Q) (sep : 2*Q^2<X)
    (hn : n≤X) (half : X≤2*n) :
    |arcFactor Q X n q - n| ≤ (n:ℝ)*errorFactor Q q := by
  have xp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have qp : 0<(q:ℝ) := by exact_mod_cast hq
  have cap : 0<(Q:ℝ) := by exact_mod_cast hQ
  have half' : (X:ℝ)≤2*n := by exact_mod_cast half
  have small : 2*Q < X := (Nat.mul_le_mul_left 2 (Nat.le_self_pow (by decide : 2≠0) Q)).trans_lt sep
  have qr : (Q:ℝ) ≤ X := by exact_mod_cast (show Q≤X by omega)
  rw [errorFactor,mul_min_of_nonneg _ _ np.le]
  apply le_min
  all_goals by_cases mem : q ∈ Icc 1 Q
  · let b := GoldbachBlockGeometry.width Q X q
    have bh : b ≤ 1/2 := by
      apply (div_le_iff₀ (mul_pos qp xp)).mpr
      have qr1 : (1:ℝ) ≤ q := by exact_mod_cast hq
      have hs : 2*(Q:ℝ) ≤ X := by exact_mod_cast small.le
      nlinarith only [hs,mul_le_mul_of_nonneg_right qr1 xp.le]
    have z := truncated_kernel_norm X n (b:=b) (by dsimp [b,GoldbachBlockGeometry.width]; positivity) bh
    rw [arcFactor,ite_eq_left mem]
    have abs := (abs_sub _ _).trans (add_le_add (Complex.abs_re_le_norm _ |>.trans z) (abs_of_pos np).le)
    have one : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
    linarith only [abs,half',one]
  · simp only [arcFactor,mem,ite_false,zero_sub,abs_neg,abs_of_pos np]; linarith
  · let b := GoldbachBlockGeometry.width Q X q
    have bp : 0 < b := div_pos cap (mul_pos qp xp)
    have bh : b ≤ 1/2 := by
      apply (div_le_iff₀ (mul_pos qp xp)).mpr
      have qr1 : (1:ℝ) ≤ q := by exact_mod_cast hq
      have hs : 2*(Q:ℝ) ≤ X := by exact_mod_cast small.le
      nlinarith only [hs,mul_le_mul_of_nonneg_right qr1 xp.le]
    have z := (Complex.abs_re_le_norm _).trans (truncated_kernel_error X n hn bp bh)
    simp only [Complex.sub_re,Complex.add_re,Complex.natCast_re,Complex.one_re] at z
    rw [arcFactor,ite_eq_left mem]
    have add := abs_sub_le (∫ t in -b..b, GoldbachEstermannKernel.twisted X n t).re (n+1:ℝ) (n:ℝ)
    rw [add_sub_cancel_left,abs_one] at add
    apply (add.trans (add_le_add_left z 1)).trans
    dsimp [b,GoldbachBlockGeometry.width]
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_left half' qp.le, qr.trans half']
  · simp only [arcFactor,mem,ite_false,zero_sub,abs_neg,abs_of_pos np]
    apply le_mul_of_one_le_right np.le
    apply (le_div_iff₀ cap).mpr
    have lt : Q<q := by by_contra! h; exact mem (mem_Icc.mpr ⟨hq,h⟩)
    have le : (Q:ℝ)≤q := by exact_mod_cast lt.le
    linarith

private theorem model_series (Q X n : ℕ) :
    (commonArcModel Q X n).re = ∑' q, ramWeight q n*arcFactor Q X n q := by
  rw [tsum_eq_sum (s:=Icc 1 Q) (fun q h => by simp only [arcFactor,h,ite_false,mul_zero])]
  simp only [commonArcModel,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact sum_congr rfl fun q h => by simp only [arcFactor,h,ite_true]

private noncomputable def localError (Q n q : ℕ) : ℝ := (n*|ramWeight q n|)*errorFactor Q q

private theorem local_summable (Q n : ℕ) (hn : 0<n) : Summable (localError Q n) :=
  (((ramWeight_abs_summable n hn).mul_left (n:ℝ)).mul_right 4).of_nonneg_of_le
    (fun _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (error_bounds ..).1)
    (fun q => mul_le_mul_of_nonneg_left (error_bounds Q q).2 (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))

private theorem anchored_error (Q X n : ℕ) (hQ : 0<Q) (sep : 2*Q^2<X) (hn : n≤X) (half : X≤2*n) :
    |(commonArcModel Q X n).re - 2*twinPrimeConstant*n*binaryShape n n| ≤ ∑' q, localError Q n q := by
  have np : 0<n := by omega
  let a (q : ℕ) := ramWeight q n*arcFactor Q X n q
  let c (q : ℕ) := (n:ℝ)*ramWeight q n
  have sa : Summable a := summable_of_ne_finset_zero (s:=Icc 1 Q) fun q h => by simp only [a,arcFactor,h,ite_false,mul_zero]
  have sc : Summable c := (summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using ramWeight_abs_summable n np) :
    Summable (fun q => ramWeight q n)).mul_left (n:ℝ)
  have eq : (commonArcModel Q X n).re-2*twinPrimeConstant*n*binaryShape n n = ∑' q, (a q-c q) := by
    rw [sa.tsum_sub sc,model_series]
    dsimp only [a,c]
    rw [tsum_mul_left,ramWeight_tsum_eq_classical n np]; ring
  have term (q : ℕ) : ‖a q-c q‖ ≤ localError Q n q := by
    rcases Nat.eq_zero_or_pos q with rfl|qp
    · simp [a,c,localError,ramWeight,ram]
    rw [show a q-c q = ramWeight q n*(arcFactor Q X n q-n) by dsimp [a,c]; ring,
      Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left (factor_error Q X n q qp hQ sep hn half) (abs_nonneg _)).trans_eq (by dsimp [localError]; ring)
  have norms := (local_summable Q n np).of_nonneg_of_le (fun _ => norm_nonneg _) term
  rw [eq,← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm norms).trans (norms.tsum_le_tsum term (local_summable Q n np))

private theorem wide_grows : Tendsto wideCutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (2^k)] with n hn
  exact (Nat.le_log_of_pow_le (by decide : 1<2) (by omega : 2^k ≤ n+2)).trans
    (Nat.le_self_pow (by decide : 20≠0) _)

theorem dyadic_common_model_mean (d : ℕ) (hd : 0<d) :
    Tendsto (fun j => dyadicRatio d (fun n => |(commonArcModel (wideCutoff (2*d*j)) (2*d*j) n).re -
      2*twinPrimeConstant*n*binaryShape n n|) j) atTop (𝓝 0) := by
  let X (j : ℕ) := 2*d*j
  let Q (j : ℕ) := wideCutoff (X j)
  have grow : Tendsto X atTop atTop := tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by omega : 0<2*d)) tendsto_id
  have cap := wide_grows.comp grow
  have limQ : Tendsto (fun j => (Q j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp cap
  let col (j q : ℕ) := (4*d*conductorMass q)*errorFactor (Q j) q
  have mass (q : ℕ) : 0≤conductorMass q := by unfold conductorMass; positivity
  have c0 (j q) : 0≤col j q := mul_nonneg (by have := mass q; positivity) (error_bounds ..).1
  have cb (j q) : col j q ≤ (4*d*conductorMass q)*4 :=
    mul_le_mul_of_nonneg_left (error_bounds ..).2 (by have := mass q; positivity)
  have envelope := (conductorMass_summable.mul_left (4*(d:ℝ))).mul_right 4
  have cols (j) := envelope.of_nonneg_of_le (c0 j) (cb j)
  have single (q) : Tendsto (fun j => col j q) atTop (𝓝 0) := by
    have f : Tendsto (fun j => errorFactor (Q j) q) atTop (𝓝 0) := squeeze_zero
      (fun _ => (error_bounds ..).1) (fun _ => min_le_right ..) (tendsto_const_nhds.div_atTop limQ)
    simpa only [mul_zero] using f.const_mul (4*d*conductorMass q)
  have total := tendsto_tsum_of_dominated_convergence envelope single (Eventually.of_forall fun j q => by
    rw [Real.norm_eq_abs,abs_of_nonneg (c0 j q)]; exact cb j q)
  apply squeeze_zero' (Eventually.of_forall fun j => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
    (sum_nonneg fun _ _ => by positivity)) _ (by simpa only [tsum_zero] using total)
  filter_upwards [grow.eventually wide_scale,cap.eventually_ge_atTop 1,eventually_ge_atTop 1] with j sep qpos jp
  let T := Ico j (2*j)
  let W := ∑ i ∈ T, (d:ℝ)*i
  let b (i q : ℕ) := localError (Q j) (d*i) q
  have low (i) (hi : i∈T) : 0<d*i := Nat.mul_pos hd (jp.trans (mem_Ico.mp hi).1)
  have sb (i) (hi : i∈T) : Summable (b i) := local_summable _ _ (low i hi)
  have sc := (summable_sum (s:=T) sb).div_const W
  have row (i) (hi : i∈T) := anchored_error (Q j) (X j) (d*i) qpos sep
    ((Nat.mul_le_mul_left d (mem_Ico.mp hi).2.le).trans_eq (by dsimp [X]; ring))
    ((show X j = 2*(d*j) by dsimp [X]; ring).le.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d (mem_Ico.mp hi).1)))
  calc
    _ ≤ (∑ i ∈ T, ∑' q, b i q)/W := div_le_div_of_nonneg_right (sum_le_sum row) (sum_nonneg fun _ _ => by positivity)
    _ = ∑' q, (∑ i ∈ T, b i q)/W := by rw [tsum_div_const,Summable.tsum_finsetSum sb]
    _ ≤ _ := by
      apply sc.tsum_le_tsum _ (cols j)
      intro q
      simp only [b,localError, ← sum_mul,mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right (dyadic_ramWeight_bound d j q hd jp) (error_bounds ..).1

#print axioms dyadic_common_model_mean
end GoldbachMinor
