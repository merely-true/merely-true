import MerelyTrue.BinomialAdd

open PMF NNReal

theorem PMF.binomial_add_binomial_comm (p : NNReal) (hp : p ≤ 1) (m₁ m₂ : ℕ) :
    PMF.addConv ((PMF.binomial p hp m₁).map Fin.val)
      ((PMF.binomial p hp m₂).map Fin.val) =
    PMF.addConv ((PMF.binomial p hp m₂).map Fin.val)
      ((PMF.binomial p hp m₁).map Fin.val) := by
  simpa using PMF.addConv_comm
    ((PMF.binomial p hp m₁).map Fin.val)
    ((PMF.binomial p hp m₂).map Fin.val)

theorem PMF.binomial_add_binomial_assoc (p : NNReal) (hp : p ≤ 1) (m₁ m₂ m₃ : ℕ) :
    PMF.addConv
      (PMF.addConv ((PMF.binomial p hp m₁).map Fin.val)
        ((PMF.binomial p hp m₂).map Fin.val))
      ((PMF.binomial p hp m₃).map Fin.val) =
    (PMF.binomial p hp (m₁ + m₂ + m₃)).map Fin.val := by
  calc
    PMF.addConv
        (PMF.addConv ((PMF.binomial p hp m₁).map Fin.val)
          ((PMF.binomial p hp m₂).map Fin.val))
        ((PMF.binomial p hp m₃).map Fin.val)
      =
        PMF.addConv ((PMF.binomial p hp (m₁ + m₂)).map Fin.val)
          ((PMF.binomial p hp m₃).map Fin.val) := by
            rw [PMF.binomial_add_binomial p hp m₁ m₂]
    _ = (PMF.binomial p hp ((m₁ + m₂) + m₃)).map Fin.val := by
          symm
          exact PMF.binomial_add_binomial p hp (m₁ + m₂) m₃
    _ = (PMF.binomial p hp (m₁ + m₂ + m₃)).map Fin.val := by
          simp
