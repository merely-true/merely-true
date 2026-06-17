/-
  Formalization of Section 5 of borsuk_ulam_tucker_lean_audit_final_v3.tex:
  Euclidean estimates and the maximal coordinate.
-/
import RequestProject.BorsukUlam.BasicTypes

open scoped BigOperators
open Finset

noncomputable section

/-! ## Coordinate threshold (Section 5) -/

/-- Definition 5.1 (Coordinate threshold).
`coordThreshold n = 1 / √n`, corresponding to `c(n)` in the source.
This is a total real-valued definition used only under `0 < n`. -/
def coordThreshold (n : ℕ) : ℝ := 1 / Real.sqrt n

/-
Lemma 5.2 (Threshold positivity).
If `0 < n`, then `0 < coordThreshold n`.
Corresponds to Lemma 5.2 in the source.
-/
theorem coordThreshold_pos (n : ℕ) (hpos : 0 < n) : 0 < coordThreshold n := by
  exact one_div_pos.mpr <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr hpos

/-! ## External theorems on Euclidean norms (Section 5) -/

/-
External theorem 5.3 (Euclidean norm square formula).
For every `x : Euc m`, `‖x‖² = ∑ i, (x i)²`.
Corresponds to External theorem 5.3 in the source.
-/
theorem euc_norm_sq (m : ℕ) (x : Euc m) :
    ‖x‖ ^ 2 = ∑ i : Fin m, (x i) ^ 2 := by
  rw [ EuclideanSpace.norm_eq ];
  rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ; aesop

/-
External theorem 5.4 (Coordinate difference bound).
For every `a, b : Euc m` and `i : Fin m`, `|a i - b i| ≤ ‖a - b‖`.
Corresponds to External theorem 5.4 in the source.
-/
theorem coord_diff_bound (m : ℕ) (a b : Euc m) (i : Fin m) :
    |a i - b i| ≤ ‖a - b‖ := by
  rw [ EuclideanSpace.norm_eq ];
  refine' Real.le_sqrt_of_sq_le _;
  simpa using Finset.single_le_sum ( fun i _ => sq_nonneg ( |a.ofLp i - b.ofLp i| ) ) ( Finset.mem_univ i )

/-! ## Large coordinate lemma (Section 5) -/

/-
Lemma 5.5 (A unit vector has a large coordinate).
If `0 < n` and `‖y‖ = 1`, then there exists `i : Fin n` with `coordThreshold n ≤ |y i|`.
Corresponds to Lemma 5.5 in the source.
-/
theorem exists_large_coord (n : ℕ) (hpos : 0 < n) (y : Euc n) (hy : ‖y‖ = 1) :
    ∃ i : Fin n, coordThreshold n ≤ |y i| := by
  -- By contradiction, assume that for all i, |y i| < 1/√n.
  by_contra h_contra
  push_neg at h_contra;
  -- Then for all i, � y� i ^ 2 < (1 / sqrt n) ^ 2 = 1 / n.
  have h_sq_lt : ∀ i : Fin n, y.ofLp i ^ 2 < 1 / n := by
    intro i; specialize h_contra i; rw [ coordThreshold ] at h_contra; simpa [ div_pow, Real.sq_sqrt ( Nat.cast_nonneg n ) ] using pow_lt_pow_left₀ h_contra ( abs_nonneg _ ) two_ne_zero;
  -- Summing gives y_i^2 < n * (1/n) = 1.
  have h_sum_lt : ∑ i : Fin n, y.ofLp i ^ 2 < 1 := by
    exact lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty ⟨ ⟨ 0, hpos ⟩, Finset.mem_univ _ ⟩ fun i _ => h_sq_lt i ) ( by norm_num [ hpos.ne' ] );
  have := euc_norm_sq n y; aesop;

/-! ## Least maximal coordinate operator (Section 5) -/

/-- External theorem 5.6 (Least maximal coordinate operator).
For `0 < n`, `MaxIdx hpos y` returns the least index in `Fin n` that maximizes `|y i|`.
Corresponds to `MaxIdx_{n, h₊}` in External theorem 5.6. -/
def MaxIdx (n : ℕ) (hpos : 0 < n) (y : Euc n) : Fin n :=
  let maxVal := univ.sup' ⟨⟨0, hpos⟩, mem_univ _⟩ (fun i => |y i|)
  (univ.filter (fun i : Fin n => |y i| = maxVal)).min' (by
    simp only [Finset.filter_nonempty_iff]
    obtain ⟨i, hi_mem, hi⟩ := Finset.exists_max_image univ (fun i => |y i|)
      ⟨⟨0, hpos⟩, mem_univ _⟩
    refine ⟨i, mem_univ i, ?_⟩
    apply le_antisymm
    · exact Finset.le_sup' (fun j => |y j|) (mem_univ i)
    · exact Finset.sup'_le _ _ (fun j hj => hi j hj))

/-
Property (M1) of `MaxIdx`: it is a global maximizer of `|y ·|`.
Corresponds to property (M1) in External theorem 5.6.
-/
theorem MaxIdx_is_max (n : ℕ) (hpos : 0 < n) (y : Euc n) (j : Fin n) :
    |y j| ≤ |y (MaxIdx n hpos y)| := by
  convert Finset.le_sup' ( fun k => |y.ofLp k| ) ( Finset.mem_univ j );
  refine' le_antisymm _ _;
  · exact Finset.le_sup' ( fun k => |y.ofLp k| ) ( Finset.mem_univ _ );
  · convert Finset.sup'_le _ _ _;
    intro i hi; exact (by
    convert Finset.le_sup' ( fun i => |y i| ) hi using 1;
    convert Finset.mem_filter.mp ( Finset.min'_mem ( Finset.filter ( fun i => |y i| = Finset.sup' Finset.univ ⟨ ⟨ 0, hpos ⟩, Finset.mem_univ _ ⟩ fun i => |y i| ) Finset.univ ) _ ) |>.2 using 1)

/-
Property (M2) of `MaxIdx`: it is the least index among all global maximizers.
Corresponds to property (M2) in External theorem 5.6.
-/
theorem MaxIdx_is_least (n : ℕ) (hpos : 0 < n) (y : Euc n) (k : Fin n)
    (hk : ∀ j : Fin n, |y j| ≤ |y k|) :
    MaxIdx n hpos y ≤ k := by
  refine' Finset.min'_le _ _ _;
  simp_all +decide;
  exact le_antisymm ( Finset.le_sup' ( fun x => |y.ofLp x| ) ( Finset.mem_univ k ) ) ( Finset.sup'_le _ _ fun x _ => hk x )

/-
Property (M3) of `MaxIdx`: negation invariance, `MaxIdx hpos (-y) = MaxIdx hpos y`.
Corresponds to property (M3) in External theorem 5.6.
-/
theorem MaxIdx_neg (n : ℕ) (hpos : 0 < n) (y : Euc n) :
    MaxIdx n hpos (-y) = MaxIdx n hpos y := by
  unfold MaxIdx;
  simp +decide [ Finset.min' ]

/-! ## Maximal coordinate on the unit sphere (Section 5) -/

/-
Lemma 5.7 (The maximal coordinate is large on the unit sphere).
If `0 < n` and `‖y‖ = 1`, then `coordThreshold n ≤ |y (MaxIdx hpos y)|`.
Corresponds to Lemma 5.7 in the source.
-/
theorem maxCoord_large (n : ℕ) (hpos : 0 < n) (y : Euc n) (hy : ‖y‖ = 1) :
    coordThreshold n ≤ |y (MaxIdx n hpos y)| := by
  -- By exists_large_coord, there � exists� i with c(n) ≤ |y i|.
  obtain ⟨i, hi⟩ : ∃ i : Fin n, coordThreshold n ≤ |y i| := exists_large_coord n hpos y hy;
  exact le_trans hi ( MaxIdx_is_max n hpos y i )

end