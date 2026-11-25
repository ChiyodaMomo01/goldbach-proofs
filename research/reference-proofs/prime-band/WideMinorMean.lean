import WideVaughan
import WideBessel
import ModelAbsoluteMean

namespace GoldbachMinor
open Finset Filter MeasureTheory GoldbachWeight
open scoped Topology

/-- Taking A=2 in the uniform Vaughan bound gives exponent 20. -/
def wideCutoff (X : ℕ) := (Nat.log 2 (X+2))^20

/-- All Fourier modes in a window use the same truncation of the prime sum. -/
noncomputable def commonMinor (X n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, (catalogueArcs (wideCutoff X) X)ᶜ.indicator
    (fun u => (spectrum X primeLog u)^2 * phase (-(n:ℝ)*u)) t

theorem common_minor_energy : ∀ᶠ X : ℕ in atTop, ∀ H : ℕ,
    (∑ n ∈ range H, ‖commonMinor X n‖^2)*(Real.log X)^2 ≤ 2*(X:ℝ)^3 := by
  obtain ⟨N,hN⟩ := GoldbachEstermann.uniformMinorSum (2:ℝ) (by norm_num)
  filter_upwards [eventually_ge_atTop N,eventually_ge_atTop 2] with X hX h2
  have xp : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have lp := Real.log_pos (show 1 < (X:ℝ) by exact_mod_cast h2)
  let L := Real.log X
  let U := (X:ℝ)/L^2
  have sup (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hm : t ∉ catalogueArcs (wideCutoff X) X) :
      ‖spectrum X primeLog t‖ ≤ U := by
    have exp : 2*⌈(2:ℝ)⌉₊+16 = 20 := by norm_num
    have raw := hN X hX t ht
    rw [exp] at raw
    have h := (raw hm).2
    simpa only [GoldbachWeight.spectrum,primeLog,phase,U,L,Real.rpow_neg lp.le,Real.rpow_two,div_eq_mul_inv] using h
  have energy : (∑ k ∈ range (X+1), (primeLog k)^2) ≤ (X+1:ℝ)*L^2 := by
    apply le_trans (sum_le_sum (g:=fun _ => L^2) ?_)
    · simp
    intro k hk
    by_cases p : k.Prime
    · simp only [primeLog,p,ite_true]
      exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast p.one_le))
        (Real.log_le_log (by exact_mod_cast p.pos) (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hk))) 2
    · simp [primeLog,p,sq_nonneg]
  intro H
  have h := WindowBessel.minorFourthMoment X H primeLog (catalogueArcs (wideCutoff X) X)
    U (measurable_catalogue ..) (div_nonneg xp.le (sq_nonneg _)) sup
  change (∑ n ∈ range H, ‖commonMinor X n‖^2) ≤ U^2*_ at h
  calc
    _ ≤ (U^2*((X+1:ℝ)*L^2))*L^2 := mul_le_mul_of_nonneg_right
      (h.trans (mul_le_mul_of_nonneg_left energy (sq_nonneg _))) (sq_nonneg _)
    _ = (X:ℝ)^2*(X+1) := by dsimp [U,L]; field_simp
    _ ≤ _ := by have one : (1:ℝ) ≤ X := by exact_mod_cast (show 1≤X by omega)
                nlinarith only [mul_le_mul_of_nonneg_right one (sq_nonneg (X:ℝ))]

/-- In the dyadic window of multiples of d, the sum of absolute minor
coefficients divided by the sum of the targets tends to zero. -/
theorem dyadic_common_minor_mean (d : ℕ) (hd : 0<d) :
    Tendsto (fun j => dyadicRatio d (fun n => ‖commonMinor (2*d*j) n‖) j) atTop (𝓝 0) := by
  have grows : Tendsto (fun j : ℕ => 2*d*j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j (by omega)) tendsto_id
  have logs := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).comp grows
  have dp : 0<(d:ℝ) := by exact_mod_cast hd
  apply squeeze_zero' (Eventually.of_forall fun j =>
    div_nonneg (sum_nonneg fun _ _ => norm_nonneg _) (sum_nonneg fun _ _ => by positivity)) _
    (show Tendsto (fun j : ℕ => 4*(d:ℝ)/Real.log (2*d*j:ℕ)) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop logs)
  filter_upwards [grows.eventually common_minor_energy,logs.eventually_gt_atTop 0,
    eventually_ge_atTop 1] with j hE hL hj
  let X := 2*d*j
  let T := Ico j (2*j)
  let W := ∑ i ∈ T, (d:ℝ)*i
  let f (i : ℕ) := ‖commonMinor X (d*i)‖
  let S := ∑ i ∈ T, f i
  let L := Real.log X
  have lp : 0<L := hL
  have jp : 0<(j:ℝ) := by exact_mod_cast hj
  have card : T.card=j := by simp [T]; omega
  have scale : (d:ℝ)*j*j ≤ W := by
    have h := sum_le_sum (s:=T) fun i hi =>
      mul_le_mul_of_nonneg_left (show (j:ℝ) ≤ i by exact_mod_cast (mem_Ico.mp hi).1) dp.le
    simpa [W,card,mul_comm,mul_left_comm] using h
  have wp := (mul_pos (mul_pos dp jp) jp).trans_le scale
  have inj : (∑ i ∈ T, (f i)^2) ≤ ∑ n ∈ range X, ‖commonMinor X n‖^2 := by
    apply sum_le_sum_of_injOn (fun i => d*i)
    · intro a _ b _ e; exact Nat.eq_of_mul_eq_mul_left hd e
    · intro n hn
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
      exact mem_range.mpr ((Nat.mul_lt_mul_of_pos_left (mem_Ico.mp hi).2 hd).trans_eq (by dsimp [X]; ring))
    · intro _ _; rfl
    · intro _ _ _; exact sq_nonneg _
  have cs := sum_mul_sq_le_sq_mul_sq T (fun _ => (1:ℝ)) f
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,card] at cs
  have bound : S^2*L^2 ≤ (j:ℝ)*(2*(X:ℝ)^3) := by
    apply (mul_le_mul_of_nonneg_right cs (sq_nonneg L)).trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right inj (sq_nonneg L)).trans (hE X)) jp.le
  have one : (1:ℝ) ≤ d := by exact_mod_cast hd
  have sq : (S*L)^2 ≤ (4*d*((d:ℝ)*j*j))^2 := by
    rw [mul_pow]
    apply bound.trans
    simp only [X,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [mul_le_mul_of_nonneg_right one (by positivity : 0≤16*(d:ℝ)^3*(j:ℝ)^4)]
  change S/W ≤ 4*d/L
  rw [div_le_div_iff₀ wp lp]
  exact (le_of_sq_le_sq sq (by positivity)).trans (mul_le_mul_of_nonneg_left scale (by positivity))

#print axioms dyadic_common_minor_mean
end GoldbachMinor
