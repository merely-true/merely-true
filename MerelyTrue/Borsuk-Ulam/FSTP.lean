/-
  Formalization of Section 4 of borsuk_ulam_tucker_lean_audit_final_v3.tex:
  The Fine Spherical Tucker Package (FSTP).
-/
import RequestProject.BorsukUlam.BasicTypes

open Sign

noncomputable section

/-- Definition 4.1 (Fine Spherical Tucker Package).
`FSTP` is the proposition that for every `n : ℕ`, every proof `hpos : 0 < n`,
and every `δ > 0`, there exist a finite type `V`, a map `p : V → Sph n`,
an involution `A : V → V`, and a symmetric relation `E : V → V → Prop`,
satisfying the five properties (P1)–(P5) from the source.

Specifically:
(P1) `A` is an involution: `A (A v) = v` for all `v`.
(P2) `p (A v) = Ant n (p v)` for all `v`.
(P3) `E` is symmetric: `E u v → E v u`.
(P4) `E u v` implies `dist (amb(p u)) (amb(p v)) < δ`.
(P5) For every antipodal labelling `ℓ : V → Label n` (i.e., `ℓ(A w) = -ℓ(w)`),
     there exist `u, v` with `E u v` and `ℓ u = -ℓ v`.

Corresponds to Definition 4.1 in the source. -/
def FSTP : Prop :=
  ∀ (n : ℕ) (hpos : 0 < n) (δ : ℝ), 0 < δ →
    ∃ (V : Type) (_ : Fintype V) (p : V → Sph n) (A : V → V) (E : V → V → Prop),
      (∀ v, A (A v) = v) ∧
      (∀ v, p (A v) = Ant n (p v)) ∧
      (∀ u v, E u v → E v u) ∧
      (∀ u v, E u v → dist (Sph.amb (p u)) (Sph.amb (p v)) < δ) ∧
      (∀ ℓ : V → Label n, (∀ w, ℓ (A w) = negLabel (ℓ w)) →
        ∃ u v, E u v ∧ ℓ u = negLabel (ℓ v))

end
