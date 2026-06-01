/-
  Formalization of Section 6 of borsuk_ulam_tucker_lean_audit_final_v3.tex:
  Total sign extraction and canonical Tucker labels.
-/
import RequestProject.BorsukUlam.Estimates

open Sign

noncomputable section

/-! ## Total sign extraction (Section 6) -/

/-- Definition 6.1 (Total sign extraction).
`signOf r` returns `plus` if `0 < r`, and `minus` otherwise.
Thus `signOf 0 = minus`. Corresponds to `signOf` in the source. -/
def signOf (r : ℝ) : Sign :=
  if 0 < r then plus else minus

/-- Lemma 6.2 (Positive branch of sign extraction).
If `0 < r`, then `signOf r = plus`.
Corresponds to Lemma 6.2 in the source. -/
theorem signOf_pos {r : ℝ} (hr : 0 < r) : signOf r = plus := by
  simp [signOf, hr]

/-- Lemma 6.3 (Negative branch of sign extraction).
If `r < 0`, then `signOf r = minus`.
Corresponds to Lemma 6.3 in the source. -/
theorem signOf_neg {r : ℝ} (hr : r < 0) : signOf r = minus := by
  simp [signOf, not_lt.mpr (le_of_lt hr)]

/-- Lemma 6.4 (Positive sign implies positive real).
If `signOf r = plus`, then `0 < r`.
Corresponds to Lemma 6.4 in the source. -/
theorem pos_of_signOf_plus {r : ℝ} (h : signOf r = plus) : 0 < r := by
  simp [signOf] at h; exact h

/-
Lemma 6.5 (Negative sign plus nonzero implies negative real).
If `r ≠ 0` and `signOf r = minus`, then `r < 0`.
Corresponds to Lemma 6.5 in the source.
-/
theorem neg_of_signOf_minus {r : ℝ} (hne : r ≠ 0) (h : signOf r = minus) : r < 0 := by
  exact lt_of_le_of_ne ( le_of_not_gt fun hr => by simp_all +decide [ signOf ] ) hne

/-
Lemma 6.6 (Sign extraction commutes with negation on nonzero reals).
If `r ≠ 0`, then `signOf (-r) = negSign (signOf r)`.
Corresponds to Lemma 6.6 in the source.
-/
theorem signOf_neg_comm {r : ℝ} (hne : r ≠ 0) :
    signOf (-r) = negSign (signOf r) := by
  cases lt_or_gt_of_ne hne <;> simp_all +decide [ signOf ];
  · rw [ if_neg ( by linarith ) ] ; rfl;
  · linarith

/-! ## Canonical Tucker label (Section 6) -/

/-- Definition 6.7 (Canonical Tucker label).
For `0 < n`, `canonLabel hpos y` assigns to `y : TSph n` the label
`(MaxIdx hpos (amb y), signOf ((amb y) (MaxIdx hpos (amb y))))`.
Corresponds to `λ_{n, h₊}` in the source. -/
def canonLabel (n : ℕ) (hpos : 0 < n) (y : TSph n) : Label n :=
  let i := MaxIdx n hpos y.val
  (i, signOf (y.val i))

/-
Lemma 6.8 (Selected coordinate is nonzero).
For `y : TSph n`, the coordinate at `MaxIdx hpos (amb y)` is nonzero.
Corresponds to Lemma 6.8 in the source.
-/
theorem selected_coord_ne_zero (n : ℕ) (hpos : 0 < n) (y : TSph n) :
    y.val (MaxIdx n hpos y.val) ≠ 0 := by
  -- Since `y : TSph n`, we have `‖y.val‖ = 1`. By `maxCoord_large`, `coordThreshold n ≤ |y.val (MaxIdx)|`.
  have h_max : coordThreshold n ≤ |(y.val) (MaxIdx n hpos y.val)| := by
    apply_rules [ maxCoord_large ];
    exact y.2 |> fun h => by simp;
  exact fun h => absurd h_max ( by rw [ h, abs_zero ] ; exact not_le_of_gt ( coordThreshold_pos n hpos ) )

/-
Lemma 6.9 (Positive label estimate).
If `canonLabel hpos y = (i, s)` and `s = plus`, then `coordThreshold n ≤ (amb y) i`.
Corresponds to Lemma 6.9 in the source.
-/
theorem positive_label_estimate (n : ℕ) (hpos : 0 < n) (y : TSph n)
    (i : Fin n) (s : Sign)
    (hlab : canonLabel n hpos y = (i, s)) (hs : s = plus) :
    coordThreshold n ≤ y.val i := by
  -- From `canonLabel` definition, `hlab` gives `i = MaxIdx n hpos y.val`.
  -- Also `hlab` gives `s = signOf (y.val i)`.
  -- Since `hs` gives `s = plus`, this means `signOf (y.val i) = plus`, so `0 < y.val i`.
  -- Hence `y.val i` is positive, and `|y.val i| = y.val i`.
  have hi_eq : i = MaxIdx n hpos y.val := by
    injection hlab.symm
  have hs_eq : signOf (y.val i) = plus := by
    unfold canonLabel at hlab; aesop;
  have hpos : 0 < y.val i := by
    exact pos_of_signOf_plus hs_eq
  have habs : |y.val i| = y.val i := by
    exact abs_of_pos hpos;
  grind +suggestions

/-
Lemma 6.10 (Negative label estimate).
If `canonLabel hpos y = (i, s)` and `s = minus`, then `(amb y) i ≤ -coordThreshold n`.
Corresponds to Lemma 6.10 in the source.
-/
theorem negative_label_estimate (n : ℕ) (hpos : 0 < n) (y : TSph n)
    (i : Fin n) (s : Sign)
    (hlab : canonLabel n hpos y = (i, s)) (hs : s = minus) :
    y.val i ≤ -coordThreshold n := by
  unfold canonLabel at hlab; simp_all +decide;
  have h_neg : y.val (MaxIdx n hpos y.val) < 0 := by
    exact neg_of_signOf_minus ( selected_coord_ne_zero n hpos y ) hlab.2;
  have := maxCoord_large n hpos y.val ?_ <;> simp_all +decide;
  cases abs_cases ( y.val i ) <;> linarith!

/-
Lemma 6.11 (Canonical label is antipodal).
For every `y : TSph n`, `canonLabel hpos (TAnt n y) = negLabel (canonLabel hpos y)`.
Corresponds to Lemma 6.11 in the source.
-/
theorem canonLabel_antipodal (n : ℕ) (hpos : 0 < n) (y : TSph n) :
    canonLabel n hpos (TAnt n y) = negLabel (canonLabel n hpos y) := by
  unfold canonLabel TAnt;
  simp +decide [ MaxIdx_neg, negLabel ];
  exact signOf_neg_comm ( selected_coord_ne_zero n hpos y )

/-
Lemma 6.12 (Complementary labels force target points far apart).
If `canonLabel hpos y = negLabel (canonLabel hpos z)`, then
`2 * coordThreshold n ≤ ‖(amb y) - (amb z)‖`.
Corresponds to Lemma 6.12 in the source.
-/
theorem complementary_labels_far (n : ℕ) (hpos : 0 < n) (y z : TSph n)
    (h : canonLabel n hpos y = negLabel (canonLabel n hpos z)) :
    2 * coordThreshold n ≤ ‖y.val - z.val‖ := by
  -- By definition of `canonLabel`, we know that � `�canonLabel n hpos y = (i, s)` where `i = MaxIdx n hpos y.val` and `s = signOf (y.val i)`.
  obtain ⟨i, s, hlab⟩ : ∃ i : Fin n, ∃ s : Sign, canonLabel n hpos z = (i, s) := by
    grind;
  cases s <;> simp_all +decide [ negLabel ];
  · -- By positive_label_estimate, we have $c(n) \leq z.val i$.
    have hz : coordThreshold n ≤ z.val i := by
      apply positive_label_estimate n hpos z i plus hlab rfl;
    -- By negative_label_estimate, we have $y.val i \leq -c(n)$.
    have hy : y.val i ≤ -coordThreshold n := by
      apply negative_label_estimate n hpos y i minus h rfl;
    have := coord_diff_bound n y.val z.val i;
    linarith [ abs_le.mp this ];
  · have := positive_label_estimate n hpos y i plus h rfl;
    have := negative_label_estimate n hpos z i minus hlab rfl;
    have := coord_diff_bound n y.val z.val i;
    linarith [ abs_le.mp this ]

end