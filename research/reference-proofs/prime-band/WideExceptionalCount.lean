import CommonArcProjection

namespace GoldbachMinor
open Finset Filter

/-- An explicit exceptional-set estimate for the common, wide-arc coefficient.
This auxiliary coefficient uses one spectrum throughout the dyadic window. -/
theorem wide_exceptional_count (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ((((range X).filter (fun n => ε * (X : ℝ) / 2 ≤ ‖commonMinor X n‖)).card : ℝ)
        * ε ^ 2 * (Real.log X) ^ 2) ≤ 8 * X := by
  filter_upwards [common_minor_energy, eventually_ge_atTop 1] with X energy hX
  let B := (range X).filter (fun n => ε * (X : ℝ) / 2 ≤ ‖commonMinor X n‖)
  have threshold : ∀ n ∈ B, (ε * (X : ℝ) / 2) ^ 2 ≤ ‖commonMinor X n‖ ^ 2 := by
    intro n hn
    exact pow_le_pow_left₀ (by positivity) (mem_filter.mp hn).2 2
  have lower : (B.card : ℝ) * (ε * (X : ℝ) / 2) ^ 2 ≤
      ∑ n ∈ range X, ‖commonMinor X n‖ ^ 2 := by
    calc
      _ = ∑ _n ∈ B, (ε * (X : ℝ) / 2) ^ 2 := by simp
      _ ≤ ∑ n ∈ B, ‖commonMinor X n‖ ^ 2 := sum_le_sum threshold
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => sq_nonneg _)
  have bound := (mul_le_mul_of_nonneg_right lower (sq_nonneg (Real.log X))).trans (energy X)
  change (B.card : ℝ) * ε ^ 2 * (Real.log X) ^ 2 ≤ 8 * X
  have xp : 0 < (X : ℝ) := by exact_mod_cast hX
  apply le_of_mul_le_mul_right (a := (X : ℝ) ^ 2) _ (sq_pos_of_pos xp)
  nlinarith only [bound]

#print axioms wide_exceptional_count

/-- Every failure of the frozen floor in the window belongs to one of two
explicit exceptional sets. Only the one-sided model discrepancy is needed. -/
theorem frozen_failure_alternatives (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ n ≤ X, X ≤ 2*n →
      (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re < -(ε*n) →
      ε*(X:ℝ)/8 ≤ ‖commonMinor X n‖ ∨
        ε*(n:ℝ)/4 < catalogueMajorModel n - (commonArcModel (wideCutoff X) X n).re := by
  obtain ⟨N, transfer⟩ := eventually_atTop.mp
    (frozen_count_error_sublinear (ε/4) (by positivity))
  filter_upwards [common_count_projection (ε/8) (by positivity),
    eventually_ge_atTop (2*N)] with X projection hX
  intro n hn half bad
  by_cases large : ε*(X:ℝ)/8 ≤ ‖commonMinor X n‖
  · exact Or.inl large
  right
  have p := (abs_le.mp ((Complex.abs_re_le_norm _).trans (projection n hn))).1
  simp only [Complex.sub_re, Complex.ofReal_re] at p
  have f := (abs_le.mp (transfer n (by omega))).1
  have scale := mul_le_mul_of_nonneg_left
    (show (X:ℝ) ≤ 2*n by exact_mod_cast half) he.le
  linarith only [p, f, scale, bad, lt_of_not_ge large]

#print axioms frozen_failure_alternatives

/-- A quantitative bound for failures of the original floor once the
one-sided discrepancy of the two major-arc models is counted. -/
theorem frozen_failure_count (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      let T := (range X).filter (fun n => Even n ∧ X ≤ 2*n)
      let F := T.filter (fun (n : ℕ) =>
        (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re < -(ε*n))
      let B := T.filter (fun (n : ℕ) =>
        ε*(n:ℝ)/4 < catalogueMajorModel n - (commonArcModel (wideCutoff X) X n).re)
      (F.card:ℝ) ≤ B.card + 128*(X:ℝ)/(ε^2*(Real.log X)^2) := by
  filter_upwards [wide_exceptional_count (ε/4) (by positivity),
    frozen_failure_alternatives ε he, eventually_ge_atTop 2] with X energy split hX
  dsimp only
  let T := (range X).filter (fun n => Even n ∧ X ≤ 2*n)
  let F := T.filter (fun (n : ℕ) =>
    (FrozenBulk.deskI n (FrozenBulk.deskHigh n) (FrozenBulk.deskHigh n)).re < -(ε*n))
  let B := T.filter (fun (n : ℕ) =>
    ε*(n:ℝ)/4 < catalogueMajorModel n - (commonArcModel (wideCutoff X) X n).re)
  let H := (range X).filter (fun n => (ε/4)*(X:ℝ)/2 ≤ ‖commonMinor X n‖)
  have sub : F ⊆ B ∪ H := by
    intro n hn
    obtain ⟨tn, bad⟩ := mem_filter.mp hn
    obtain ⟨rn, _, half⟩ := mem_filter.mp tn
    rcases split n (mem_range.mp rn).le half bad with large | discrep
    · exact mem_union_right _ (mem_filter.mpr ⟨rn, by linarith only [large]⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨tn, discrep⟩)
  have count : (F.card:ℝ) ≤ (B.card:ℝ) + H.card := by
    exact_mod_cast (card_le_card sub).trans (card_union_le B H)
  have lp : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have bound : (H.card:ℝ) ≤ 128*(X:ℝ)/(ε^2*(Real.log X)^2) := by
    rw [le_div_iff₀ (by positivity)]
    change (H.card:ℝ) * (ε/4)^2 * (Real.log X)^2 ≤ 8*X at energy
    nlinarith only [energy]
  exact count.trans (add_le_add (le_refl (B.card : ℝ)) bound)

#print axioms frozen_failure_count
end GoldbachMinor
