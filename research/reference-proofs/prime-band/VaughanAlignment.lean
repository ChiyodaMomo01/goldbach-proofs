import SingularSeriesTransfer

namespace GoldbachMinor
open Finset Filter
open scoped Topology

/-- The two local factors as printed in Vaughan's Theorem 8. -/
noncomputable def vaughanFactor (p m : ℕ) : ℝ :=
  if p ∣ m then (p:ℝ)/(p-1) else (p:ℝ)*(p-2)/(p-1)^2

private noncomputable def baseFactor (p : ℕ) : ℝ := 1-1/((p:ℝ)-1)^2
noncomputable def twinPartial (X : ℕ) : ℝ := ∏ p ∈ shapePrimes X, baseFactor p
noncomputable def twinPrimeConstant : ℝ := ⨅ X : ℕ, twinPartial X

private theorem base_range (p : ℕ) (h : 3≤p) : 0≤baseFactor p ∧ baseFactor p≤1 := by
  have h' : (3:ℝ)≤p := by exact_mod_cast h
  have sq : (1:ℝ)≤((p:ℝ)-1)^2 := by nlinarith [sq_nonneg ((p:ℝ)-2)]
  unfold baseFactor
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le zero_lt_one sq |>.trans_eq (by norm_num))
  · exact sub_le_self _ (by positivity)

theorem twinPartial_tends : Tendsto twinPartial atTop (𝓝 twinPrimeConstant) := by
  apply tendsto_atTop_ciInf
  · intro a b hab
    apply prod_le_prod_of_subset_of_le_one₀
    · intro p hp
      have h := mem_filter.mp hp
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE h.1).trans hab,
        Nat.prime_of_mem_primesLE h.1⟩,h.2⟩
    · intro p hp; exact (base_range p (mem_filter.mp hp).2).1
    · intro p hp _; exact (base_range p (mem_filter.mp hp).2).2
  · refine ⟨0, ?_⟩
    rintro z ⟨X,rfl⟩
    exact prod_nonneg fun p hp => (base_range p (mem_filter.mp hp).2).1

/-- The finite product already has the full shape at m once all its prime
divisors have been passed, including the p=2 factor for odd and even m. -/
theorem vaughan_finite_alignment (m X : ℕ) (hm : 0 < m) (hX : max 2 m≤X) :
    (∏ p ∈ Nat.primesLE X, vaughanFactor p m) = 2*twinPartial X*binaryShape m m := by
  have x2 : 2∉shapePrimes X := by simp [shapePrimes]
  have eqp : Nat.primesLE X = insert 2 (shapePrimes X) := by
    ext p
    simp only [mem_insert,shapePrimes,mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨h,pr⟩
      have := pr.two_le
      by_cases h2 : p=2
      · exact Or.inl h2
      · exact Or.inr ⟨⟨h,pr⟩,by omega⟩
    · rintro (rfl|⟨h,_⟩)
      · exact ⟨by omega,Nat.prime_two⟩
      · exact h
  have eqm : (shapePrimes X).filter (· ∣ m) = (shapePrimes m).filter (· ∣ m) := by
    ext p
    simp only [shapePrimes,mem_filter,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨_,pr⟩,h3⟩,hd⟩
      exact ⟨⟨⟨Nat.le_of_dvd hm hd,pr⟩,h3⟩,hd⟩
    · rintro ⟨⟨⟨hle,pr⟩,h3⟩,hd⟩
      exact ⟨⟨⟨by omega,pr⟩,h3⟩,hd⟩
  have factor (p) (h : p∈shapePrimes X) :
      vaughanFactor p m = baseFactor p * (if p∣m then 1+goldbachFactor p else 1) := by
    have h3 : (3:ℝ)≤p := by exact_mod_cast (mem_filter.mp h).2
    have h1 : (p:ℝ)-1≠0 := by linarith
    have h2 : (p:ℝ)-2≠0 := by linarith
    unfold vaughanFactor baseFactor goldbachFactor
    split_ifs <;> field_simp <;> ring
  rw [eqp,prod_insert x2,prod_congr rfl factor,prod_mul_distrib,← prod_filter,eqm]
  change vaughanFactor 2 m * (twinPartial X * oddFactorProduct (shapePrimes m) m) = _
  change _ = 2*twinPartial X*(if 2∣m then oddFactorProduct (shapePrimes m) m else 0)
  by_cases he : 2∣m <;> simp [vaughanFactor,he]
  ring

theorem vaughan_series_alignment (m : ℕ) (hm : 0 < m) :
    Tendsto (fun X => ∏ p ∈ Nat.primesLE X, vaughanFactor p m) atTop
      (𝓝 (2*twinPrimeConstant*binaryShape m m)) := by
  apply ((twinPartial_tends.const_mul 2).mul_const (binaryShape m m)).congr'
  filter_upwards [eventually_ge_atTop (max 2 m)] with X hX
  exact (vaughan_finite_alignment m X hm hX).symm

/-- The literal global bound, with the singular series specified by the printed
Euler product, implies the single external hypothesis used by the transfer. -/
theorem classical_of_vaughan (s : ℕ→ℝ)
    (series : ∀ m, 0 < m → Tendsto (fun X => ∏ p ∈ Nat.primesLE X, vaughanFactor p m) atTop (𝓝 (s m)))
    (estimate : ∃ A:ℝ, 0≤A ∧ ∀ᶠ X : ℕ in atTop,
      (∑ m ∈ Icc 1 X, (goldbachCount m-m*s m)^2)*(Real.log X)^4 ≤ A*(X:ℝ)^3) :
    ClassicalMeanSquare (2*twinPrimeConstant) := by
  obtain ⟨A,hA,h⟩ := estimate
  refine ⟨A,hA,?_⟩
  filter_upwards [h] with X hx
  have eq : (∑ m ∈ Icc 1 X, (goldbachCount m-(2*twinPrimeConstant)*m*binaryShape m m)^2) =
      ∑ m ∈ Icc 1 X, (goldbachCount m-m*s m)^2 := by
    apply sum_congr rfl
    intro m hm
    have pos : 0 < m := (mem_Icc.mp hm).1
    rw [tendsto_nhds_unique (series m pos) (vaughan_series_alignment m pos)]
    ring
  rw [eq]
  exact hx

theorem outer_iff_of_vaughan (s : ℕ→ℝ)
    (series : ∀ m, 0 < m → Tendsto (fun X => ∏ p ∈ Nat.primesLE X, vaughanFactor p m) atTop (𝓝 (s m)))
    (estimate : ∃ A:ℝ, 0≤A ∧ ∀ᶠ X : ℕ in atTop,
      (∑ m ∈ Icc 1 X, (goldbachCount m-m*s m)^2)*(Real.log X)^4 ≤ A*(X:ℝ)^3) :
    FrozenBulk.BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      outerAndSmall n ≤ pairMass n 0 (GoldbachWeight.high n)*(1-arcLength (catalogueCutoff n) n) + ε*n :=
  outer_iff_of_classical_mean_square _ (classical_of_vaughan s series estimate)

#print axioms outer_iff_of_vaughan
end GoldbachMinor
