/-
  Formalization of Sections 2–3 of borsuk_ulam_tucker_lean_audit_final_v3.tex:
  Basic types (Euc, Sph, TSph), antipodal maps, signs, and labels.
-/
import Mathlib

open scoped BigOperators
open Finset

set_option maxHeartbeats 800000

noncomputable section

/-! ## Basic types (Section 2) -/

/-- Definition 2.1 (Finite Euclidean spaces).
`Euc m` is the finite-dimensional Euclidean space `Fin m → ℝ` equipped with
the Euclidean (L²) norm, corresponding to `𝓔(m)` in the source. -/
abbrev Euc (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- Definition 2.2 (Domain sphere).
`Sph n` is the unit sphere in `Euc (n+1)`, corresponding to `𝕊(n)` in the source.
Elements satisfy `‖x‖ = 1`. -/
abbrev Sph (n : ℕ) := ↥(Metric.sphere (0 : Euc (n + 1)) 1)

/-- Definition 2.2 (Target sphere).
`TSph n` is the unit sphere in `Euc n`, corresponding to `𝕋(n)` in the source.
Elements satisfy `‖y‖ = 1`. -/
abbrev TSph (n : ℕ) := ↥(Metric.sphere (0 : Euc n) 1)

/-- `amb` extracts the ambient vector from a domain-sphere element.
Corresponds to the notation `amb(x)` in Definition 2.2. -/
abbrev Sph.amb {n : ℕ} (x : Sph n) : Euc (n + 1) := x.val

/-- `amb` extracts the ambient vector from a target-sphere element.
Corresponds to the notation `amb(y)` in Definition 2.2. -/
abbrev TSph.amb {n : ℕ} (y : TSph n) : Euc n := y.val

/-- Helper: a negated sphere vector still has norm 1. -/
theorem norm_neg_of_mem_sphere {m : ℕ} {x : Euc m}
    (hx : x ∈ Metric.sphere (0 : Euc m) 1) :
    -x ∈ Metric.sphere (0 : Euc m) 1 := by
  simp [norm_neg] at hx ⊢; exact hx

/-- Definition 2.3 (Antipodal map on the domain sphere).
`Ant n x` is the antipodal point of `x` on `Sph n`, satisfying `amb(Ant_n(x)) = -amb(x)`.
Corresponds to `Ant_n` in the source. -/
def Ant (n : ℕ) (x : Sph n) : Sph n :=
  ⟨-x.val, norm_neg_of_mem_sphere x.prop⟩

/-- Definition 2.3 (Antipodal map on the target sphere).
`TAnt n y` is the antipodal point of `y` on `TSph n`, satisfying `amb(TAnt_n(y)) = -amb(y)`.
Corresponds to `TAnt_n` in the source. -/
def TAnt (n : ℕ) (y : TSph n) : TSph n :=
  ⟨-y.val, norm_neg_of_mem_sphere y.prop⟩

@[simp] theorem Ant_val (n : ℕ) (x : Sph n) : (Ant n x).val = -x.val := rfl
@[simp] theorem TAnt_val (n : ℕ) (y : TSph n) : (TAnt n y).val = -y.val := rfl

/-- Lemma 2.4 (Antipodal involutivity, domain sphere).
For every `x : Sph n`, `Ant n (Ant n x) = x`.
Proof: by subtype extensionality and `neg_neg`. -/
theorem Ant_Ant (n : ℕ) (x : Sph n) : Ant n (Ant n x) = x := by
  ext i; simp [Ant]

/-- Lemma 2.4 (Antipodal involutivity, target sphere).
For every `y : TSph n`, `TAnt n (TAnt n y) = y`.
Proof: by subtype extensionality and `neg_neg`. -/
theorem TAnt_TAnt (n : ℕ) (y : TSph n) : TAnt n (TAnt n y) = y := by
  ext i; simp [TAnt]

/-- External theorem 2.5 (Continuity of the antipodal map on the domain sphere).
`Ant n` is continuous. -/
theorem continuous_Ant (n : ℕ) : Continuous (Ant n) := by
  apply Continuous.subtype_mk
  exact continuous_neg.comp continuous_subtype_val

/-- External theorem 2.5 (Continuity of the antipodal map on the target sphere).
`TAnt n` is continuous. -/
theorem continuous_TAnt (n : ℕ) : Continuous (TAnt n) := by
  apply Continuous.subtype_mk
  exact continuous_neg.comp continuous_subtype_val

/-! ## Signs and labels (Section 3) -/

/-- Definition 3.1 (The sign type).
`Sign` is the two-constructor type with constructors `plus` and `minus`,
corresponding to `Sign` in the source. -/
inductive Sign : Type where
  | plus : Sign
  | minus : Sign
  deriving DecidableEq, Inhabited

open Sign

/-- Definition 3.1 (Real value of a sign).
`sgnval plus = 1` and `sgnval minus = -1`.
Corresponds to `sgnval` in the source. -/
def sgnval : Sign → ℝ
  | plus => 1
  | minus => -1

/-- Definition 3.1 (Sign negation).
`negSign plus = minus` and `negSign minus = plus`.
Corresponds to `negSign` in the source. -/
def negSign : Sign → Sign
  | plus => minus
  | minus => plus

/-- Lemma 3.2 (Sign case split).
For every `s : Sign`, either `s = plus` or `s = minus`. -/
theorem Sign.cases (s : Sign) : s = plus ∨ s = minus := by
  cases s <;> simp

/-- Lemma 3.3 (Sign negation on constructors: plus).
`negSign plus = minus`. -/
@[simp] theorem negSign_plus : negSign plus = minus := rfl

/-- Lemma 3.3 (Sign negation on constructors: minus).
`negSign minus = plus`. -/
@[simp] theorem negSign_minus : negSign minus = plus := rfl

/-- Lemma 3.4 (Sign negation is involutive).
For every `s : Sign`, `negSign (negSign s) = s`. -/
@[simp] theorem negSign_negSign (s : Sign) : negSign (negSign s) = s := by
  cases s <;> rfl

/-- Lemma 3.5 (The two signs are distinct).
`plus ≠ minus`. -/
theorem plus_ne_minus : plus ≠ minus := by decide

/-- Definition 3.6 (Signed labels).
`Label n = Fin n × Sign`. The first component is the index `idx(a)`.
Corresponds to `Label(n)` in the source. -/
abbrev Label (n : ℕ) := Fin n × Sign

/-- `idx a` is the index (first component) of a label.
Corresponds to `idx(a)` in Definition 3.6. -/
abbrev Label.idx {n : ℕ} (a : Label n) : Fin n := a.1

/-- Definition 3.6 (Label negation).
`negLabel a = (idx a, negSign a.2)`.
Corresponds to `-a` in the source. -/
def negLabel {n : ℕ} (a : Label n) : Label n := (a.1, negSign a.2)

/-- Lemma 3.7 (Label negation is involutive).
For every `a : Label n`, `negLabel (negLabel a) = a`. -/
@[simp] theorem negLabel_negLabel {n : ℕ} (a : Label n) : negLabel (negLabel a) = a := by
  simp [negLabel]

/-- Lemma 3.8 (Complementary labels have the same index).
If `a = negLabel b`, then `a.idx = b.idx`.
Corresponds to Lemma 3.8 in the source. -/
theorem idx_of_negLabel {n : ℕ} (a b : Label n) (h : a = negLabel b) :
    a.idx = b.idx := by
  subst h; rfl

/-! ## Compactness and metric inheritance (External theorems from Sections 7) -/

/-- External theorem 7.1 (Compactness of the domain sphere).
`Sph n` is a compact space. -/
instance Sph.compactSpace (n : ℕ) : CompactSpace (Sph n) := by
  rw [← isCompact_iff_compactSpace]; exact isCompact_sphere 0 1

/-- External theorem 7.1 (Compactness of the target sphere).
`TSph n` is a compact space. -/
instance TSph.compactSpace (n : ℕ) : CompactSpace (TSph n) := by
  rw [← isCompact_iff_compactSpace]; exact isCompact_sphere 0 1

/-- External theorem 7.3 (Subtype metrics are inherited, domain sphere).
For `x, x' : Sph n`, `dist x x' = dist x.val x'.val`.
Corresponds to External theorem 7.3 in the source. -/
theorem Sph.dist_eq {n : ℕ} (x x' : Sph n) : dist x x' = dist x.val x'.val := rfl

/-- External theorem 7.3 (Subtype metrics are inherited, target sphere).
For `y, y' : TSph n`, `dist y y' = dist y.val y'.val`.
Corresponds to External theorem 7.3 in the source. -/
theorem TSph.dist_eq {n : ℕ} (y y' : TSph n) : dist y y' = dist y.val y'.val := rfl

end
