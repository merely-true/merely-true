/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

import Mathlib

open Real PMF BigOperators ENNReal NNReal Finset

/-- The sum of two independent binomial random variables with the same success
probability is binomial with the combined number of trials. -/
lemma PMF.binomial_add_binomial (p : NNReal) (hp : p ≤ 1) (m₁ m₂ : ℕ) :
    (do
      let k ← PMF.binomial p hp (m₁ + m₂)
      return (k : ℕ))
    =
    (do
      let k ← PMF.binomial p hp m₁
      let l ← PMF.binomial p hp m₂
      return (k + l : ℕ) ):= by
  ext n
  show ((PMF.binomial p hp (m₁ + m₂)).bind (fun k => PMF.pure (k : ℕ))) n =
       ((PMF.binomial p hp m₁).bind (fun k =>
         (PMF.binomial p hp m₂).bind (fun l => PMF.pure (k + l : ℕ)))) n
  simp only [PMF.bind_apply, PMF.pure_apply, tsum_fintype, mul_ite, mul_one, mul_zero]
  by_cases hn : n ≤ m₁ + m₂
  · have hn' : n < m₁ + m₂ + 1 := Nat.lt_succ_of_le hn
    have lhs_eq : (∑ x : Fin (m₁ + m₂ + 1), if n = ↑x then (binomial p hp (m₁ + m₂)) x else 0) =
        (binomial p hp (m₁ + m₂)) ⟨n, hn'⟩ := by
      rw [Finset.sum_eq_single ⟨n, hn'⟩]
      · simp only [↓reduceIte]
      · intro b _ hne
        have hne' : n ≠ (b : ℕ) := by
          intro heq
          apply hne
          ext
          exact heq.symm
        simp only [hne', ↓reduceIte]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [lhs_eq]
    simp only [PMF.binomial_apply, Fin.val_last]
    conv_rhs =>
      arg 2
      ext x
      rw [show (∑ x_1 : Fin (m₂ + 1), if n = ↑x + ↑x_1 then
            (p : ENNReal) ^ ↑x_1 * (1 - (p : ENNReal)) ^ (m₂ - ↑x_1) * ↑(m₂.choose ↑x_1) else 0) =
          if (x : ℕ) ≤ n ∧ n - (x : ℕ) ≤ m₂ then
            (p : ENNReal) ^ (n - (x : ℕ)) * (1 - (p : ENNReal)) ^ (m₂ - (n - (x : ℕ))) * ↑(m₂.choose (n - (x : ℕ)))
          else 0 by
        split_ifs with hcond
        · obtain ⟨hxn, hnxm⟩ := hcond
          rw [Finset.sum_eq_single ⟨n - (x : ℕ), Nat.lt_succ_of_le hnxm⟩]
          · simp only [add_tsub_cancel_of_le hxn, ↓reduceIte]
          · intro b _ hne
            have hne' : n ≠ ↑x + ↑b := by
              intro heq
              apply hne
              ext
              have : n - (x : ℕ) = (b : ℕ) := by omega
              simp only [this]
            simp only [hne', ↓reduceIte]
          · intro h
            exact (h (Finset.mem_univ _)).elim
        · push_neg at hcond
          apply Finset.sum_eq_zero
          intro y _
          simp only [ite_eq_right_iff]
          intro heq
          specialize hcond (by omega : (x : ℕ) ≤ n)
          have hy : (y : ℕ) ≤ m₂ := Fin.is_le y
          omega
      ]
    simp only [mul_ite, mul_zero]
    rw [Nat.add_choose_eq m₁ m₂ n, Nat.cast_sum]
    erw [Finset.mul_sum]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    have lhs_filter : ∑ i ∈ antidiagonal n, (p : ENNReal) ^ n * (1 - (p : ENNReal)) ^ (m₁ + m₂ - n) *
        ↑(m₁.choose i.1 * m₂.choose i.2) =
        ∑ i ∈ (antidiagonal n).filter (fun ij => ij.1 ≤ m₁ ∧ ij.2 ≤ m₂),
        (p : ENNReal) ^ n * (1 - (p : ENNReal)) ^ (m₁ + m₂ - n) *
        ↑(m₁.choose i.1 * m₂.choose i.2) := by
      symm
      apply Finset.sum_filter_of_ne
      intro ⟨i, j⟩ hij hne
      simp only at hne
      constructor
      · by_contra hi
        push_neg at hi
        simp only [Nat.choose_eq_zero_of_lt hi, zero_mul, Nat.cast_zero, mul_zero,
          ne_eq, not_true_eq_false] at hne
      · by_contra hj
        push_neg at hj
        simp only [Nat.choose_eq_zero_of_lt hj, mul_zero, Nat.cast_zero, mul_zero,
          ne_eq, not_true_eq_false] at hne
    rw [lhs_filter]
    symm
    refine Finset.sum_bij' (fun x _ => (↑x, n - ↑x))
        (fun ij hij => ⟨ij.1, Nat.lt_succ_of_le (Finset.mem_filter.mp hij).2.1⟩)
        ?hi ?hj ?left_inv ?right_inv ?h
    case hi =>
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      obtain ⟨_, hxn, hnxm₂⟩ := hx
      simp only
      constructor
      · rw [mem_antidiagonal]
        omega
      · exact ⟨Fin.is_le x, hnxm₂⟩
    case hj =>
      intro ⟨i, j⟩ hij
      rw [Finset.mem_filter] at hij ⊢
      obtain ⟨hij_mem, hi_le, hj_le⟩ := hij
      rw [mem_antidiagonal] at hij_mem
      constructor
      · exact Finset.mem_univ _
      · simp only
        constructor
        · omega
        · omega
    case left_inv =>
      intro x hx
      ext
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Binomial distribution as a convolution of Bernoulli distributions

This file develops an API for *additive convolution* of `PMF ℕ`s and uses it to
prove that the binomial distribution is the `n`-fold self-convolution of the
Bernoulli distribution.  The key structural result,

    `PMF.binomial_add_binomial`,

states that summing two independent binomials with the same bias `p` and trial
counts `m₁`, `m₂` yields a binomial with `m₁ + m₂` trials.  Rather than
proving this by a direct Vandermonde-style computation, we

1. define the additive convolution `PMF.addConv`,
2. establish its **commutativity** (`addConv_comm`) and **associativity**
   (`addConv_assoc`),
3. show that `binomial p hp n` equals the `n`-fold convolution of
   `bernoulliNat p hp` (`binomial_map_val_eq_iterAddConv`), and
4. deduce `binomial_add_binomial` purely from the algebraic structure.
-/

open PMF BigOperators ENNReal NNReal Finset

namespace PMF

/-! ## Additive convolution of `PMF ℕ` -/

/-- The additive convolution of two `PMF ℕ`s: the distribution of `X + Y`
when `X ~ f` and `Y ~ g` are drawn independently. -/
noncomputable def addConv (f g : PMF ℕ) : PMF ℕ :=
  f.bind fun x => g.bind fun y => PMF.pure (x + y)

/-- Additive convolution is commutative. -/
theorem addConv_comm (f g : PMF ℕ) : addConv f g = addConv g f := by
  simp only [addConv]
  rw [PMF.bind_comm f g]
  simp only [add_comm]

/-- Additive convolution is associative. -/
theorem addConv_assoc (f g h : PMF ℕ) :
    addConv (addConv f g) h = addConv f (addConv g h) := by
  simp only [addConv, PMF.bind_bind, PMF.pure_bind, add_assoc]

/-- Convolving with `pure 0` on the left is the identity. -/
@[simp]
theorem addConv_pure_zero_left (f : PMF ℕ) : addConv (PMF.pure 0) f = f := by
  simp [addConv, PMF.pure_bind]

/-- Convolving with `pure 0` on the right is the identity. -/
@[simp]
theorem addConv_pure_zero_right (f : PMF ℕ) : addConv f (PMF.pure 0) = f := by
  simp only [addConv, PMF.pure_bind, add_zero, PMF.bind_pure]

/-! ## Bernoulli distribution as a `PMF ℕ` -/

/-- The Bernoulli distribution with bias `p`, viewed as a `PMF ℕ` supported on
`{0, 1}` (where `1` represents "heads"). -/
noncomputable def bernoulliNat (p : ℝ≥0) (hp : p ≤ 1) : PMF ℕ :=
  (PMF.bernoulli p hp).map (cond · 1 0)

@[simp]
theorem bernoulliNat_apply_zero (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliNat p hp 0 = 1 - p := by
  simp [bernoulliNat, PMF.map_apply, tsum_bool, PMF.bernoulli_apply]

@[simp]
theorem bernoulliNat_apply_one (p : ℝ≥0) (hp : p ≤ 1) :
    bernoulliNat p hp 1 = p := by
  simp [bernoulliNat, PMF.map_apply, tsum_bool, PMF.bernoulli_apply]

@[simp]
theorem bernoulliNat_apply_of_gt_one (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (hn : 1 < n) :
    bernoulliNat p hp n = 0 := by
  simp only [bernoulliNat, PMF.map_apply, tsum_bool, PMF.bernoulli_apply,
             Bool.cond_true, Bool.cond_false,
             if_neg (show n ≠ 1 from by omega), if_neg (show n ≠ 0 from by omega),
             add_zero]

/-! ## Iterated convolution and its interaction with addition -/

/-- The `n`-fold additive convolution of a `PMF ℕ` with itself. -/
noncomputable def iterAddConv (f : PMF ℕ) : ℕ → PMF ℕ
  | 0     => PMF.pure 0
  | n + 1 => addConv (iterAddConv f n) f

@[simp]
theorem iterAddConv_zero (f : PMF ℕ) : iterAddConv f 0 = PMF.pure 0 := rfl

@[simp]
theorem iterAddConv_succ (f : PMF ℕ) (n : ℕ) :
    iterAddConv f (n + 1) = addConv (iterAddConv f n) f := rfl

/-- The `(m + n)`-fold convolution splits as the convolution of the `m`-fold
and `n`-fold convolutions.  This is the key algebraic fact used to prove
`binomial_add_binomial`, and its proof uses only commutativity and associativity
of `addConv`. -/
theorem iterAddConv_add (f : PMF ℕ) (m n : ℕ) :
    iterAddConv f (m + n) = addConv (iterAddConv f m) (iterAddConv f n) := by
  induction m with
  | zero => simp [addConv_pure_zero_left]
  | succ k ih =>
    -- Goal: iterAddConv f (k + 1 + n) = addConv (iterAddConv f (k + 1)) (iterAddConv f n)
    -- Rewrite LHS: (k+1+n) = (k+n+1), then unfold iterAddConv
    rw [show k + 1 + n = k + n + 1 from by ring, iterAddConv_succ, ih, iterAddConv_succ]
    -- Goal: addConv (addConv A B) f = addConv (addConv A f) B
    --   where A = iterAddConv f k, B = iterAddConv f n
    -- Proof: assoc + comm on B and f + assoc backward
    rw [addConv_assoc, addConv_comm (iterAddConv f n) f, ← addConv_assoc]

/-! ## Binomial as iterated Bernoulli convolution -/

/-- Adding one Bernoulli trial extends the binomial distribution by one step.
This follows from the Pascal recurrence `C(n+1, k) = C(n, k) + C(n, k-1)`. -/
theorem binomial_succ_map_val_eq_addConv_bernoulliNat
    (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    (PMF.binomial p hp (n + 1)).map Fin.val =
    addConv ((PMF.binomial p hp n).map Fin.val) (bernoulliNat p hp) := by
  ext k
  simp only [addConv, PMF.map_apply, PMF.bind_apply, PMF.pure_apply,
             bernoulliNat, PMF.map_apply, tsum_bool, PMF.bernoulli_apply,
             Bool.cond_true, Bool.cond_false]
  -- Simplify Fin tsums to Fin sums and expand binomial_apply
  simp only [tsum_fintype, PMF.binomial_apply, Fin.val_last, mul_ite, mul_one, mul_zero]
  -- Step 1: Simplify the inner ℕ-tsum (bernoulliNat part).
  -- ∑' a₁, if k = a + a₁ then X(a₁) else 0
  -- reduces to X(k-a) when k ≥ a, and 0 when k < a.
  -- X(0) = ↑(1-p), X(1) = ↑p, X(≥2) = 0.
  have hG : ∀ a : ℕ, ∑' (a_1 : ℕ),
      (if k = a + a_1 then
        (if a_1 = 0 then (↑(1 - p) : ℝ≥0∞) else 0) +
        if a_1 = 1 then (↑p : ℝ≥0∞) else 0
      else 0) =
      (if k = a then (↑(1 - p) : ℝ≥0∞) else 0) +
      (if k = a + 1 then (↑p : ℝ≥0∞) else 0) := by
    intro a
    rcases le_or_gt a k with h | h
    · rw [tsum_eq_single (k - a)
        (fun b hb => by rw [if_neg (show k ≠ a + b from by omega)])]
      rw [show a + (k - a) = k from by omega, if_pos rfl]
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · simp
      · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with h2 | h2
        · -- k = a + 1
          have hka0 : k - a ≠ 0 := by omega
          have hka1 : k - a = 1 := by omega
          have hne : k ≠ a := by omega
          have heq : k = a + 1 := by omega
          simp [heq]
        · -- k ≥ a + 2
          have hka0 : k - a ≠ 0 := by omega
          have hka1 : k - a ≠ 1 := by omega
          have hne : k ≠ a := by omega
          have hne2 : ¬(k = a + 1) := by omega
          simp [hka0, hka1, hne, hne2]
    · -- k < a: all terms are 0
      rw [tsum_eq_single 0
        (fun b hb => by rw [if_neg (show k ≠ a + b from by omega)])]
      simp [show k ≠ a from by omega, show ¬(k = a + 1) from by omega]
  simp_rw [hG, mul_add]
  rw [ENNReal.tsum_add]
  -- Step 2: Simplify each outer ℕ-tsum to a single term.
  simp_rw [mul_ite, mul_zero]
  -- First sum: ∑' a, if k = a then F(a)*↑(1-p) else 0
  -- Second sum: ∑' a, if k = a+1 then F(a)*↑p else 0
  rw [tsum_eq_single k (fun a ha => by rw [if_neg (Ne.symm ha)]),
      tsum_eq_single (k - 1) (fun a ha => by
        rw [if_neg (show ¬(k = a + 1) from by omega)])]
  -- Step 3: Helper to simplify Fin sums ∑ a : Fin m, if c = ↑a then g a else 0
  have hS : ∀ (m : ℕ) (c : ℕ) (g : Fin m → ℝ≥0∞),
      (∑ a : Fin m, if c = ↑a then g a else 0) =
      if h : c < m then g ⟨c, h⟩ else 0 := by
    intro m c g
    by_cases hc : c < m
    · rw [dif_pos hc]
      have key : (∑ a : Fin m, if c = ↑a then g a else 0) =
          if c = ↑(Fin.mk c hc : Fin m) then g (Fin.mk c hc) else 0 :=
        Finset.sum_eq_single_of_mem (Fin.mk c hc) (Finset.mem_univ _)
          (fun b _ hb => if_neg (fun h : c = ↑b => hb (Fin.ext h.symm)))
      simpa using key
    · rw [dif_neg hc]
      exact Finset.sum_eq_zero (fun b _ => if_neg (fun h : c = ↑b => by omega))
  simp only [if_true]
  simp_rw [hS]
  -- Step 4: Case split on k and apply Pascal's rule
  rcases k with _ | k
  · -- k = 0: second term vanishes, both sides reduce to (1-↑p)^(n+1)
    simp [show ¬(0 : ℕ) = 1 from by omega, ENNReal.coe_sub, pow_succ]
  · -- k = k+1
    simp only [Nat.succ_sub_one, if_true]
    by_cases hk1 : k + 1 < n + 1 + 1
    · rw [dif_pos hk1]
      by_cases hk2 : k + 1 < n + 1
      · -- Both terms present: apply Pascal's rule
        rw [dif_pos hk2, dif_pos (show k < n + 1 from by omega), ENNReal.coe_sub,
            show n + 1 - (k + 1) = n - k from by omega,
            show n - (k + 1) = n - k - 1 from by omega,
            Nat.choose_succ_succ]
        push_cast
        -- Combine (1-↑p)^(n-k-1) * ↑C * (1-↑p) → (1-↑p)^(n-k) * ↑C on the RHS
        conv_rhs => lhs; rw [mul_right_comm, mul_assoc _ ((1 - ↑p : ℝ≥0∞) ^ _) (1 - ↑p),
          ← pow_succ, show n - k - 1 + 1 = n - k from by omega]
        ring
      · -- k+1 ≥ n+1 with k+1 < n+2: k = n
        have hkn : k = n := by omega
        rw [hkn, dif_neg (show ¬(n + 1 < n + 1) from by omega),
            dif_pos (show n < n + 1 from by omega), ENNReal.coe_sub]
        simp [Nat.choose_self, pow_succ]
    · -- k+1 ≥ n+2
      rw [dif_neg hk1, dif_neg (show ¬(k + 1 < n + 1) from by omega),
          dif_neg (show ¬(k < n + 1) from by omega)]
      simp

/-- The binomial distribution `PMF.binomial p hp n`, viewed as a `PMF ℕ` via
`Fin.val`, equals the `n`-fold additive convolution of `bernoulliNat p hp`. -/
theorem binomial_map_val_eq_iterAddConv (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    (PMF.binomial p hp n).map Fin.val = iterAddConv (bernoulliNat p hp) n := by
  induction n with
  | zero =>
    ext k
    simp only [iterAddConv_zero, PMF.pure_apply, PMF.map_apply]
    rw [tsum_eq_single (⟨0, Nat.lt_succ_self 0⟩ : Fin 1)
        (fun i hi => absurd (Fin.fin_one_eq_zero i) hi)]
    simp [PMF.binomial_apply]
  | succ n ih =>
    rw [binomial_succ_map_val_eq_addConv_bernoulliNat, ih, iterAddConv_succ]

/-! ## Main theorem -/

/-- The sum of two independent binomially distributed random variables with the
same bias `p` and trial counts `m₁`, `m₂` is binomially distributed with
`m₁ + m₂` trials.

The proof proceeds by identifying each binomial with the iterated Bernoulli
convolution (`binomial_map_val_eq_iterAddConv`) and then applying the splitting
lemma `iterAddConv_add`, whose proof uses only commutativity and associativity
of `addConv`. -/
theorem binomial_add_binomial (p : NNReal) (hp : p ≤ 1) (m₁ m₂ : ℕ) :
    (PMF.binomial p hp (m₁ + m₂)).map Fin.val =
    addConv ((PMF.binomial p hp m₁).map Fin.val)
            ((PMF.binomial p hp m₂).map Fin.val) := by
  rw [binomial_map_val_eq_iterAddConv, binomial_map_val_eq_iterAddConv,
      binomial_map_val_eq_iterAddConv, iterAddConv_add]

end PMF
