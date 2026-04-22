import MerelyTrue.BinomialAdd

open PMF NNReal

lemma PMF.binomial_add_binomial_comm (p : NNReal) (hp : p ≤ 1) (m₁ m₂ : ℕ) :
    (do
      let k ← PMF.binomial p hp m₁
      let l ← PMF.binomial p hp m₂
      return (k + l : ℕ))
    =
    (do
      let l ← PMF.binomial p hp m₂
      let k ← PMF.binomial p hp m₁
      return (k + l : ℕ)) := by
  calc
    (do
      let k ← PMF.binomial p hp m₁
      let l ← PMF.binomial p hp m₂
      return (k + l : ℕ))
      =
        (do
          let n ← PMF.binomial p hp (m₁ + m₂)
          return (n : ℕ)) := by
            symm
            exact PMF.binomial_add_binomial p hp m₁ m₂
    _ =
        (do
          let n ← PMF.binomial p hp (m₂ + m₁)
          return (n : ℕ)) := by
            rw [Nat.add_comm m₁ m₂]
    _ =
        (do
          let l ← PMF.binomial p hp m₂
          let k ← PMF.binomial p hp m₁
          return (k + l : ℕ)) := by
            simpa [Nat.add_comm] using PMF.binomial_add_binomial p hp m₂ m₁

lemma PMF.binomial_add_binomial_assoc (p : NNReal) (hp : p ≤ 1) (m₁ m₂ m₃ : ℕ) :
    (do
      let x ← PMF.binomial p hp m₁
      let y ← PMF.binomial p hp m₂
      let z ← PMF.binomial p hp m₃
      return (x + y + z : ℕ))
    =
    (do
      let n ← PMF.binomial p hp (m₁ + m₂ + m₃)
      return (n : ℕ)) := by
  calc
    (do
      let x ← PMF.binomial p hp m₁
      let y ← PMF.binomial p hp m₂
      let z ← PMF.binomial p hp m₃
      return (x + y + z : ℕ))
      =
        (do
          let s ← (do
            let x ← PMF.binomial p hp m₁
            let y ← PMF.binomial p hp m₂
            return (x + y : ℕ))
          let z ← PMF.binomial p hp m₃
          return (s + z : ℕ)) := by
            simp [bind_assoc]
    _ =
        (do
          let s ← PMF.binomial p hp (m₁ + m₂)
          let z ← PMF.binomial p hp m₃
          return (s + z : ℕ)) := by
            rw [(PMF.binomial_add_binomial p hp m₁ m₂).symm]
            simp
    _ =
        (do
          let n ← PMF.binomial p hp (m₁ + m₂ + m₃)
          return (n : ℕ)) := by
            simpa [Nat.add_assoc] using
              (PMF.binomial_add_binomial p hp (m₁ + m₂) m₃).symm
