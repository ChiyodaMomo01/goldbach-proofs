import SingularSeriesWindow
import GoldbachTruncation

namespace GoldbachMinor
open Finset

noncomputable def shapeConstant : ℝ := Real.exp 9*(9*Real.exp 9+(3*Real.exp 9)^2)

private theorem shape_at_two (m : ℕ) : binaryShape 2 m = if 2∣m then 1 else 0 := by
  unfold binaryShape oddFactorProduct
  split_ifs <;> rfl
/-- A bound for the full normalized series including odd targets and both endpoints. -/
theorem full_shape_energy (K H : ℕ) (hKH : K≤H) :
    (∑ m ∈ Ioc K H, (binaryShape m m)^2) ≤
      ((H:ℝ)-K)*(shapeConstant/2+2)+8*(harmonicCutoff H)^4 := by
  let T := (H:ℝ)-K
  have h := binary_shape_window K H 2 hKH (by decide)
  have h' : (∑ m ∈ Ioc K H, (binaryShape m m-binaryShape 2 m)^2) ≤
      T*(shapeConstant/4) + 4*(harmonicCutoff H)^4 := by
    dsimp [T,shapeConstant]
    norm_num at h ⊢
    exact h
  have count : ((Ioc K H).card:ℝ) = T := by simp [T,Nat.cast_sub hKH]
  calc
    _ ≤ ∑ m ∈ Ioc K H, (2*(binaryShape m m-binaryShape 2 m)^2+2) := by
      apply sum_le_sum
      intro m _
      rw [shape_at_two]
      split_ifs <;> nlinarith [sq_nonneg (binaryShape m m-2)]
    _ ≤ _ := by
      rw [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,count]
      change _ ≤ T*_+_
      linarith

private theorem shifted_square_sums (n K H : ℕ) (hKH : K≤H) (hH : H<n) (f : ℕ→ℝ)
    (a b : ℝ) (bound : ∀ l h : ℕ, l≤h → h≤2*n →
      (∑ m ∈ Ioc l h, (f m)^2) ≤ ((h:ℝ)-l)*a+b) :
    (∑ k ∈ Ioc K H, ((f (n-k))^2+(f (n+k))^2)) ≤ 2*(((H:ℝ)-K)*a+b) := by
  have down : (∑ k ∈ Ioc K H, (f (n-k))^2) ≤ ∑ m ∈ Ioc (n-H-1) (n-K-1), (f m)^2 := by
    apply sum_le_sum_of_injOn (fun k => n-k)
    · intro x hx y hy he
      have ha := mem_Ioc.mp hx
      have hb := mem_Ioc.mp hy
      dsimp at he
      omega
    · intro m hm
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hm
      have := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨by omega,by omega⟩
    · intro _ _; rfl
    · intro _ _ _; exact sq_nonneg _
  have up : (∑ k ∈ Ioc K H, (f (n+k))^2) ≤ ∑ m ∈ Ioc (n+K) (n+H), (f m)^2 := by
    apply sum_le_sum_of_injOn (fun k => n+k)
    · intro x _ y _ he; exact Nat.add_left_cancel he
    · intro m hm
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hm
      have := mem_Ioc.mp hk
      exact mem_Ioc.mpr ⟨by omega,by omega⟩
    · intro _ _; rfl
    · intro _ _ _; exact sq_nonneg _
  have neg := down.trans (bound _ _ (by omega) (by omega))
  have pos := up.trans (bound _ _ (by omega) (by omega))
  have neglen : ((n-K-1:ℕ):ℝ) - ((n-H-1:ℕ):ℝ) = (H:ℝ)-K := by
    rw [sub_eq_sub_iff_add_eq_add]
    exact_mod_cast (show n-K-1+K=H+(n-H-1) by omega)
  rw [neglen] at neg
  push_cast at pos
  rw [sum_add_distrib]
  linarith

/-- Use the residue of the offset as the argument of the two-sided periodic profile. -/
theorem shifted_shape_residue (n k y : ℕ) (hk : k≤n) (hy : 2≤y) :
    binaryShape y (n-k % y.factorial) = binaryShape y (n-k) ∧
    binaryShape y (n+k % y.factorial) = binaryShape y (n+k) := by
  let P := y.factorial
  have modk : k%P ≡ k [MOD P] := Nat.mod_modEq ..
  have le : k%P≤n := (Nat.mod_le ..).trans hk
  have a := modk.sub_left' (iff_of_true le hk) (a:=n)
  have b := modk.add_left n
  have congruent {u v : ℕ} (he : u ≡ v [MOD P]) : binaryShape y u = binaryShape y v :=
    (binaryShape_residue y u hy).symm.trans ((congrArg (binaryShape y) he).trans (binaryShape_residue y v hy))
  exact ⟨congruent a,congruent b⟩


/-- One finite transfer inequality for a normalization c, using both actual offset
windows. The only term involving the classical representation count is global. -/
theorem first_band_classical_transfer (c : ℝ) (n K H y : ℕ) (hKH : K≤H) (hH : H<n) (hy : 2≤y) :
    let b (r : ℕ) := c*n*(binaryShape y (n-r)+binaryShape y (n+r))
    let e (m : ℕ) := goldbachCount m-c*m*binaryShape m m
    let T := (H:ℝ)-K
    let B := (harmonicCutoff (2*n))^4
    (∑ k ∈ Ioc K H, (goldbachCount (n-k)+goldbachCount (n+k)-b (k%y.factorial))^2) ≤
      6*(∑ m ∈ range (2*n+1), (e m)^2)
      +12*(c*H)^2*(T*(shapeConstant/2+2)+8*B)
      +12*(c*n)^2*(T*(shapeConstant/(y:ℝ)^2)+4*B) := by
  let W := Ioc K H
  let b (r : ℕ) := c*n*(binaryShape y (n-r)+binaryShape y (n+r))
  let e (m : ℕ) := goldbachCount m-c*m*binaryShape m m
  let s (m : ℕ) := binaryShape m m
  let d (m : ℕ) := binaryShape m m-binaryShape y m
  let T := (H:ℝ)-K
  let B := (harmonicCutoff (2*n))^4
  have harmonic (h) (hh : h≤2*n) : (harmonicCutoff h)^4≤B := by
    unfold B
    apply pow_le_pow_left₀ (by unfold harmonicCutoff; positivity)
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
    exact Icc_subset_Icc (le_refl _) hh
  have hbS := shifted_square_sums n K H hKH hH s (shapeConstant/2+2) (8*B) (by
    intro l h hl hh
    exact (full_shape_energy l h hl).trans (by linarith only [harmonic h hh]))
  have hbD := shifted_square_sums n K H hKH hH d (shapeConstant/(y:ℝ)^2) (4*B) (by
    intro l h hl hh
    exact (binary_shape_window l h y hl hy).trans (by unfold shapeConstant; linarith only [harmonic h hh]))
  have hbE := paired_window_global_error n K H hH.le e
  let L (k : ℕ) := (s (n-k))^2+(s (n+k))^2
  let R (k : ℕ) := (d (n-k))^2+(d (n+k))^2
  have point (k : ℕ) (hk : k∈W) :
      (goldbachCount (n-k)+goldbachCount (n+k)-b (k%y.factorial))^2 ≤
        3*(e (n-k)+e (n+k))^2 + 6*(c*H)^2*L k + 6*(c*n)^2*R k := by
    obtain ⟨_,hkH⟩ := mem_Ioc.mp hk
    have hkn := hkH.trans hH.le
    obtain ⟨hm,hp⟩ := shifted_shape_residue n k y hkn hy
    have eq : goldbachCount (n-k)+goldbachCount (n+k)-b (k%y.factorial) =
        e (n-k)+e (n+k)+c*k*(s (n+k)-s (n-k))+c*n*(d (n-k)+d (n+k)) := by
      unfold b e s d
      rw [hm,hp,Nat.cast_sub hkn,Nat.cast_add]
      ring
    let x := e (n-k)+e (n+k)
    let z := c*k*(s (n+k)-s (n-k))
    let u := c*n*(d (n-k)+d (n+k))
    have zs : z^2 ≤ (c*H)^2*(2*L k) := by
      have coef : (c*k)^2≤(c*H)^2 := by
        simp only [mul_pow]; gcongr
      have sq : (s (n+k)-s (n-k))^2≤2*L k := by
        unfold L; nlinarith only [sq_nonneg (s (n+k)+s (n-k))]
      unfold z
      rw [mul_pow]
      exact mul_le_mul coef sq (sq_nonneg _) (sq_nonneg _)
    have us : u^2 ≤ (c*n)^2*(2*R k) := by
      unfold u R
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (d (n+k)-d (n-k))]) (sq_nonneg _)
    rw [eq]
    change (x+z+u)^2 ≤ 3*x^2+_+_
    nlinarith only [sq_nonneg (x-z),sq_nonneg (z-u),sq_nonneg (u-x),zs,us]
  change (∑ k ∈ W, _) ≤ _
  calc
    _ ≤ _ := sum_le_sum point
    _ ≤ _ := by
      simp only [sum_add_distrib,← mul_sum]
      have he := mul_le_mul_of_nonneg_left hbE (by norm_num : (0:ℝ)≤3)
      have hs := mul_le_mul_of_nonneg_left hbS (show 0≤6*(c*H)^2 by positivity)
      have hd := mul_le_mul_of_nonneg_left hbD (show 0≤6*(c*n)^2 by positivity)
      dsimp only [W,L,R,T,B] at *
      linarith only [he,hs,hd]

open Filter
open scoped Topology

/-- The growing factorial cutoff absorbs the slowly growing diagonal energy. -/
theorem factorial_profile_budget (ε : ℝ) (he : 0<ε) : ∀ᶠ n : ℕ in atTop,
    1+diagonalEnergy (catalogueCutoff n) (logWidth n) ≤ ε*(factorialIndex n:ℝ)^2 := by
  have h1 : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have h2 : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hr : Tendsto (fun x : ℝ => (1+Real.log x)/x) atTop (𝓝 0) := by
    simpa only [add_div,add_zero] using h1.add h2
  have ht : Tendsto (fun n : ℕ => ((factorialIndex n:ℝ)+1)) atTop atTop :=
    Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop.comp factorialIndex_tends) tendsto_const_nhds
  filter_upwards [(hr.comp ht).eventually_lt_const (show 0<ε/8 by positivity),
    factorialIndex_tends.eventually (eventually_ge_atTop 2)] with n hsmall hn
  let j := factorialIndex n
  let L := logWidth n
  have hj : (2:ℝ)≤j := by exact_mod_cast hn
  have hL : 0<L := Nat.succ_pos _
  have hfac : L < (j+1).factorial := by
    by_contra! h
    have bad := Nat.le_findGreatest (P:=fun i => i.factorial ≤ L)
      ((Nat.self_le_factorial _).trans h) h
    change j+1≤j at bad
    omega
  have hpow : L ≤ (j+1)^(j+1) := hfac.le.trans (Nat.factorial_le_pow _)
  have hlog := Real.log_le_log (by exact_mod_cast hL : 0<(L:ℝ))
    (show (L:ℝ) ≤ ((j:ℝ)+1)^(j+1) by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hdiag := (diagonalEnergy_le_harmonic (catalogueCutoff n) L).trans (cutoff_harmonic n)
  change (1+Real.log ((j:ℝ)+1))/((j:ℝ)+1) < ε/8 at hsmall
  have h := (div_lt_iff₀ (show 0<(j:ℝ)+1 by positivity)).mp hsmall
  have hx := mul_le_mul_of_nonneg_left h.le (show 0≤2*((j:ℝ)+1) by positivity)
  have sq : ((j:ℝ)+1)^2 ≤ 4*(j:ℝ)^2 := by
    nlinarith only [mul_nonneg (show 0≤(j:ℝ)-1 by linarith) (show 0≤3*(j:ℝ)+1 by positivity)]
  change 1+_ ≤ ε*(j:ℝ)^2
  nlinarith only [hx, hdiag, hlog, hj, mul_le_mul_of_nonneg_left sq he.le]

/-- Even after the variance normalization, the fourth harmonic power from the
two incomplete intervals is negligible. -/
theorem harmonic_edge_budget (ε : ℝ) (he : 0<ε) : ∀ᶠ n : ℕ in atTop,
    (catalogueCutoff n:ℝ)*(1+diagonalEnergy (catalogueCutoff n) (logWidth n))*
      (harmonicCutoff (2*n))^4 ≤ ε*n := by
  have lim := tendsto_pow_const_div_const_pow_of_one_lt 7 (by norm_num : (1:ℝ)<2)
  filter_upwards [logWidth_tends.eventually (lim.eventually_lt_const
    (show 0<ε/648 by positivity)), eventually_ge_atTop 2] with n hs hn
  let L := (logWidth n:ℝ)
  let Q := (catalogueCutoff n:ℝ)
  have hL : 1≤L := by dsimp only [L]; exact_mod_cast (show 1≤logWidth n from Nat.succ_pos _)
  have hQ : Q≤L^2 := by
    change ((Nat.log 2 (n+2)^2:ℕ):ℝ) ≤ ((Nat.log 2 (n+2)+1:ℕ):ℝ)^2
    push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2))]
  have hJ := (diagonalEnergy_le_harmonic (catalogueCutoff n) (logWidth n)).trans (cutoff_harmonic n)
  have hj : 1+diagonalEnergy (catalogueCutoff n) (logWidth n) ≤ 2*L := by
    have hlog := Real.log_le_sub_one_of_pos (show 0<L by linarith)
    dsimp only [L] at *; linarith
  have hh : harmonicCutoff (2*n) ≤ 3*L := by
    have hharm : harmonicCutoff (2*n) ≤ 1+Real.log (2*n:ℕ) := by
      simpa only [harmonicCutoff,one_div,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
        using harmonic_le_one_add_log (2*n)
    have hlog : Real.log (2*n:ℕ) ≤ 1+L := by
      rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (by positivity)]
      have h := log_n_le_width n (by omega)
      change Real.log n ≤ L at h
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hp := Nat.pow_log_le_self 2 (show n+2≠0 by omega)
  have hexp : (2:ℝ)^logWidth n ≤ 4*n := by
    exact_mod_cast (show 2^logWidth n≤4*n by unfold logWidth; rw [pow_succ]; omega)
  have hx := (div_lt_iff₀ (by positivity : 0<(2:ℝ)^logWidth n)).mp hs
  calc
    _ ≤ L^2*(2*L)*(3*L)^4 := by
      apply mul_le_mul (mul_le_mul hQ hj (by unfold diagonalEnergy; positivity) (sq_nonneg _))
        (pow_le_pow_left₀ (by unfold harmonicCutoff; positivity) hh _) (by positivity) (by positivity)
    _ = 162*L^7 := by ring
    _ ≤ _ := by dsimp only [L]; nlinarith only [hx,mul_le_mul_of_nonneg_left hexp he.le]

/-- The translation of the factor m to the fixed centre n has smaller order on the band. -/
theorem diagonal_over_cutoff (ε : ℝ) (he : 0<ε) : ∀ᶠ n : ℕ in atTop,
    1+diagonalEnergy (catalogueCutoff n) (logWidth n) ≤ ε*(catalogueCutoff n:ℝ) := by
  have lt := (tendsto_natCast_atTop_atTop.comp logWidth_tends).eventually_ge_atTop (4/ε+1)
  filter_upwards [lt] with n hn
  let d := Nat.log 2 (n+2)
  have hd : 1≤d := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1≤n+2 by omega)
  have hr : (1:ℝ)≤d := by exact_mod_cast hd
  have hL : (logWidth n:ℝ) = (d:ℝ)+1 := by simp [logWidth,d]
  have hJ := (diagonalEnergy_le_harmonic (catalogueCutoff n) (logWidth n)).trans (cutoff_harmonic n)
  rw [hL] at hJ
  have ha : 1+diagonalEnergy (catalogueCutoff n) (logWidth n) ≤ 4*(d:ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show 0<(d:ℝ)+1 by positivity)]
  change 4/ε+1 ≤ (logWidth n:ℝ) at hn
  rw [hL] at hn
  have h4 := (div_le_iff₀ he).mp (show 4/ε≤d by linarith)
  have hmul := mul_le_mul_of_nonneg_right h4 (show 0≤(d:ℝ) by positivity)
  have eq : (catalogueCutoff n:ℝ) = (d:ℝ)^2 := by simp [catalogueCutoff,d]
  rw [eq]
  exact ha.trans (by nlinarith only [hmul])

/-- The needed external input, in the fourth logarithmic saving form of the
classical binary Goldbach mean-square theorem. The normalization is c = 2 C₂. -/
def ClassicalMeanSquare (c : ℝ) : Prop := ∃ A : ℝ, 0≤A ∧ ∀ᶠ X : ℕ in atTop,
    (∑ m ∈ Icc 1 X, (goldbachCount m-c*m*binaryShape m m)^2)*(Real.log X)^4 ≤ A*(X:ℝ)^3

private theorem classical_budget (c : ℝ) (hc : ClassicalMeanSquare c) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ n : ℕ in atTop, (catalogueCutoff n:ℝ)*(1+diagonalEnergy (catalogueCutoff n) (logWidth n))*
      (∑ m ∈ range (2*n+1), (goldbachCount m-c*m*binaryShape m m)^2) ≤ ε*(n:ℝ)^3 := by
  obtain ⟨A,hA0,hA⟩ := hc
  let B := 8*A/(Real.log 2)^4
  have logpos := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hB : 0≤B := by dsimp [B]; positivity
  obtain ⟨M,hM⟩ := eventually_atTop.mp hA
  filter_upwards [eventually_ge_atTop (max 2 M),
    diagonal_over_cutoff (ε/(B+1)) (by positivity)] with n hn hJ
  let d := Nat.log 2 (n+2)
  let Q := (catalogueCutoff n:ℝ)
  let G := ∑ m ∈ range (2*n+1), (goldbachCount m-c*m*binaryShape m m)^2
  have hq : Q=(d:ℝ)^2 := by simp [Q,catalogueCutoff,d]
  have hg0 : 0≤G := by dsimp [G]; positivity
  have p : (2:ℝ)^d ≤ (2*n:ℕ) := by
    exact_mod_cast (Nat.pow_log_le_self 2 (show n+2≠0 by omega)).trans (show n+2≤2*n by omega)
  have hlog := Real.log_le_log (by positivity) p
  rw [Real.log_pow] at hlog
  have h4 := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) logpos.le) hlog 4
  push_cast only [Nat.cast_mul,Nat.cast_ofNat] at h4
  have ext := hM (2*n) (by omega)
  have gr : G = ∑ m ∈ Icc 1 (2*n), (goldbachCount m-c*m*binaryShape m m)^2 := by
    have eq : range (2*n+1) = insert 0 (Icc 1 (2*n)) := by ext m; simp; omega
    simp [G,eq,goldbachCount,primeLog]
  rw [← gr] at ext
  push_cast only [Nat.cast_mul,Nat.cast_ofNat] at ext
  have hG : G*Q^2 ≤ B*(n:ℝ)^3 := by
    unfold B
    rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos logpos 4),hq]
    nlinarith only [ext, mul_le_mul_of_nonneg_left h4 hg0]
  have hfrac : (ε/(B+1))*B ≤ ε := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    linarith
  calc
    _ ≤ Q*((ε/(B+1))*Q)*G := by gcongr
    _ = (ε/(B+1))*(G*Q^2) := by ring
    _ ≤ (ε/(B+1))*(B*(n:ℝ)^3) := mul_le_mul_of_nonneg_left hG (by positivity)
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hfrac (by positivity)

/-- A complete reduction of the first-band prime-pair variance to the classical global
mean-square theorem, without assuming a distribution estimate for individual residue classes. -/
theorem variance_of_classical_mean_square (c : ℝ) (hc : ClassicalMeanSquare c) :
    ∀ δ:ℝ, 0<δ → ∃ N:ℕ, ∀ n≥N, Even n →
      (catalogueCutoff n:ℝ)*classEnergy n (factorialPeriod n)*(1+diagonalEnergy (catalogueCutoff n) (logWidth n))
        ≤ δ*(n:ℝ)^3 := by
  let b (n r : ℕ) := c*n*(binaryShape (factorialIndex n) (n-r)+binaryShape (factorialIndex n) (n+r))
  apply class_variance_of_goldbach_profile factorialPeriod b (fun n _ => factorialPeriod_fits n)
  intro ε he
  let C := shapeConstant
  let A := C/2+2
  let F := 6+12*c^2*A+12*c^2*C+144*c^2
  have hC : 0≤C := by dsimp [C,shapeConstant]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hF : 0<F := by dsimp [F]; positivity
  let δ := ε/F
  have hδ : 0<δ := div_pos he hF
  apply eventually_atTop.mp
  filter_upwards [classical_budget c hc δ hδ, harmonic_edge_budget δ hδ,
    factorial_profile_budget δ hδ, diagonal_over_cutoff δ hδ,
    factorialIndex_tends.eventually (eventually_ge_atTop 2), eventually_ge_atTop 4]
    with n hg hedge hfact hj hy hn
  intro _
  let Q := (catalogueCutoff n:ℝ)
  let J := 1+diagonalEnergy (catalogueCutoff n) (logWidth n)
  let H := firstBandEnd n
  let K := primeBandWidth n
  let y := factorialIndex n
  let T := (H:ℝ)-K
  let B := (harmonicCutoff (2*n))^4
  let G := ∑ m ∈ range (2*n+1), (goldbachCount m-c*m*binaryShape m m)^2
  have hj0 : 0≤J := by dsimp [J,diagonalEnergy]; positivity
  have hB0 : 0≤B := by dsimp [B]; positivity
  have hy0 : 0<(y:ℝ) := by exact_mod_cast (show 0<y from (by omega : 0<factorialIndex n))
  have hd := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^2 ≤ n+2 by omega)
  have hq : 1<catalogueCutoff n := by unfold catalogueCutoff; nlinarith only [hd,sq_nonneg (Nat.log 2 (n+2)-1:ℤ)]
  have hq1 : 1≤Q := by dsimp [Q]; exact_mod_cast hq.le
  have hq0 : 0≤Q := by positivity
  have hn0 : 0≤(n:ℝ) := by positivity
  have kh : K≤H := by
    apply Nat.div_le_div_left _ (by omega : 0<catalogueCutoff n)
    change (Nat.log 2 (n+2))^2 ≤ (Nat.log 2 (n+2)+1)^4
    exact le_trans (Nat.pow_le_pow_left (Nat.le_succ _) 2)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by decide : 2≤4))
  have hH : H<n := Nat.div_lt_self (by omega) hq
  have hr : (H:ℝ)≤n := by exact_mod_cast hH.le
  have ht : 0≤T := sub_nonneg.mpr (by exact_mod_cast kh)
  have mult : Q*(H:ℝ)≤n := by
    dsimp only [Q,H,firstBandEnd]; exact_mod_cast (Nat.mul_comm _ _ ▸ Nat.div_mul_le_self n (catalogueCutoff n) :
      catalogueCutoff n*(n/catalogueCutoff n)≤n)
  have len : Q*T≤n :=
    (mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg K)) hq0).trans mult
  have mainShift : Q*J*((H:ℝ)^2*T) ≤ δ*(n:ℝ)^3 := by
    have hq2 : Q≤Q^2 := by nlinarith [sq_nonneg (Q-1)]
    have hJ : J ≤ δ*Q^2 := hj.trans (mul_le_mul_of_nonneg_left hq2 hδ.le)
    calc
      _ = J*(H:ℝ)^2*(Q*T) := by ring
      _ ≤ (δ*Q^2)*(H:ℝ)^2*n := mul_le_mul
        (mul_le_mul_of_nonneg_right hJ (sq_nonneg _)) len (mul_nonneg hq0 ht) (by positivity)
      _ = δ*(Q*H)^2*n := by ring
      _ ≤ δ*(n:ℝ)^2*n := by gcongr
      _ = _ := by ring
  have mainTail : Q*J*((n:ℝ)^2*(T/(y:ℝ)^2)) ≤ δ*n^3 := by
    have hv : J/(y:ℝ)^2 ≤ δ := (div_le_iff₀ (sq_pos_of_pos hy0)).mpr hfact
    calc
      _ = ((J/(y:ℝ)^2)*(Q*T))*(n:ℝ)^2 := by ring
      _ ≤ (δ*n)*(n:ℝ)^2 := mul_le_mul_of_nonneg_right (mul_le_mul hv len (mul_nonneg hq0 ht) hδ.le) (sq_nonneg _)
      _ = _ := by ring
  have edgeN : Q*J*((n:ℝ)^2*B) ≤ δ*n^3 := by
    calc
      _ = (Q*J*B)*(n:ℝ)^2 := by ring
      _ ≤ (δ*n)*(n:ℝ)^2 := mul_le_mul_of_nonneg_right hedge (sq_nonneg _)
      _ = _ := by ring
  have edgeH : Q*J*((H:ℝ)^2*B) ≤ δ*n^3 :=
    le_trans (by gcongr) edgeN
  let E := ∑ k ∈ Ioc K H, (goldbachCount (n-k)+goldbachCount (n+k)-b n (k%factorialPeriod n))^2
  have est : E ≤ 6*G + 12*(c*H)^2*(T*A+8*B)+12*(c*n)^2*(T*(C/(y:ℝ)^2)+4*B) :=
    first_band_classical_transfer c n K H y kh hH hy
  change Q*E*J ≤ ε*(n:ℝ)^3
  have cls : Q*J*G ≤ δ*(n:ℝ)^3 := hg
  have eq : δ*F=ε := by dsimp only [δ]; field_simp
  calc
    _ ≤ δ*F*(n:ℝ)^3 := by
      unfold F
      simp only [div_eq_mul_inv] at est mainTail
      have h := mul_le_mul_of_nonneg_left est (mul_nonneg hq0 hj0)
      nlinarith only [h,cls,
        mul_le_mul_of_nonneg_left mainShift (show 0≤12*c^2*A by positivity),
        mul_le_mul_of_nonneg_left mainTail (show 0≤12*c^2*C by positivity),
        mul_le_mul_of_nonneg_left edgeH (show 0≤96*c^2 by positivity),
        mul_le_mul_of_nonneg_left edgeN (show 0≤48*c^2 by positivity)]
    _ = _ := by rw [eq]

/-- The first-band centred large-denominator loss is sublinear under the single
classical mean-square input. -/
theorem first_band_large_of_classical_mean_square (c : ℝ) (hc : ClassicalMeanSquare c)
    (ε : ℝ) (hε : 0<ε) : ∃ N:ℕ, ∀ n≥N, Even n →
    |largeDenominatorSum (catalogueCutoff n) n (logWidth n) (primeBandWidth n) (firstBandEnd n)
        (classDeviation n (factorialPeriod n))| ≤ ε*n :=
  large_negligible_of_variance factorialPeriod (variance_of_classical_mean_square c hc) ε hε

/-- The remaining high-high floor only uses the small denominators and outer frequencies. -/
theorem outer_iff_of_classical_mean_square (c : ℝ) (hc : ClassicalMeanSquare c) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      outerAndSmall n ≤ pairMass n 0 (GoldbachWeight.high n)*(1-arcLength (catalogueCutoff n) n) + ε*n :=
  outer_iff_of_variance factorialPeriod (fun n _ => factorialPeriod_fits n) (variance_of_classical_mean_square c hc)

#print axioms first_band_large_of_classical_mean_square
#print axioms outer_iff_of_classical_mean_square
end GoldbachMinor
