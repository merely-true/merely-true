/-
  Formalization of Sections 7–12 of borsuk_ulam_tucker_lean_audit_final_v3.tex:
  Uniform continuity, no continuous odd map, normalization, and the Borsuk–Ulam theorem.
-/
import RequestProject.BorsukUlam.FSTP
import RequestProject.BorsukUlam.CanonicalLabel

open Sign

noncomputable section

/-! ## Uniform continuity on the domain sphere (Section 7) -/

/-
Lemma 7.4 (Ambient uniform-continuity delta).
If `g : Sph n → TSph n` is continuous and `ε > 0`, then there exists `δ > 0` such that
`dist (amb(x)) (amb(x')) < δ` implies `dist (amb(g x)) (amb(g x')) < ε`.
Corresponds to Lemma 7.4 in the source.
-/
theorem ambient_uniform_continuity (n : ℕ) (g : Sph n → TSph n)
    (hg : Continuous g) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x x' : Sph n,
      dist x.val x'.val < δ → dist (g x).val (g x').val < ε := by
  have := Metric.uniformContinuous_iff.mp ( CompactSpace.uniformContinuous_of_continuous hg ) ε hε;
  convert this using 6

/-! ## Nonexistence of continuous odd maps (Section 8) -/

/-- Definition 8.1 (Odd map into the target sphere).
A map `g : Sph n → TSph n` is odd if `g (Ant n x) = TAnt n (g x)` for all `x`.
Corresponds to Definition 8.1 in the source. -/
def IsOddMap (n : ℕ) (g : Sph n → TSph n) : Prop :=
  ∀ x : Sph n, g (Ant n x) = TAnt n (g x)

/-
Proposition 8.2 (No continuous odd map).
Assuming FSTP, for `0 < n`, there is no continuous odd map `Sph n → TSph n`.
Corresponds to Proposition 8.2 in the source.
-/
theorem no_continuous_odd_map (hFSTP : FSTP) (n : ℕ) (hpos : 0 < n) :
    ¬∃ g : Sph n → TSph n, Continuous g ∧ IsOddMap n g := by
  -- By contradiction, assume there exists a continuous odd map g : Sph n → TSph n.
  by_contra h_contra
  obtain ⟨g, hg_cont, hg_odd⟩ := h_contra

  -- Set $c := coordThreshold n$.
  set c := coordThreshold n

  -- By coordThreshold_pos, $0 < c$.
  have hc_pos : 0 < c := by
    exact one_div_pos.mpr <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr hpos

  -- By ambient_uniform_continuity with $\epsilon = c$, get $\delta > 0$ with the proximity property.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x x' : Sph n, dist x.val x'.val < δ → dist (g x).val (g x').val < c := by
    exact ambient_uniform_continuity n g hg_cont c hc_pos

  -- Apply hFSTP to n, hpos, δ.
  obtain ⟨V, hFintype, p, A, E, hP1, hP2, hP3, hP4, hP5⟩ := hFSTP n hpos δ hδ_pos

  -- Define ℓ(w) := canonLabel hpos (g(p(w)).
  set ℓ : V → Label n := fun w => canonLabel n hpos (g (p w));
  -- Show ℓ is antipodal: ℓ(A w) = negLabel(ℓ w).
  have hℓ_antipodal : ∀ w, ℓ (A w) = negLabel (ℓ w) := by
    intros w
    simp [ℓ, hP2];
    convert canonLabel_antipodal n hpos ( g ( p w ) ) using 1;
    rw [ hg_odd ];
  -- By P5, get u, v with E u v and ℓ u = negLabel(ℓ v).
  obtain ⟨u, v, hEuv, hℓuv⟩ := hP5 ℓ hℓ_antipodal;
  -- By P4, dist(amb(p u), amb(p v)) < δ.
  have h_dist : dist (p u).val (p v).val < δ := by
    exact hP4 u v hEuv;
  -- By complementary_labels_far, 2c ≤ ‖amb(g(p u)) - amb(g(p v))‖.
  have h_complementary : 2 * c ≤ ‖(g (p u)).val - (g (p v)).val‖ := by
    exact complementary_labels_far n hpos (g (p u)) (g (p v)) hℓuv;
  exact not_lt_of_ge h_complementary ( by simpa [ dist_eq_norm ] using lt_of_lt_of_le ( hδ _ _ h_dist ) ( by linarith ) )

/-! ## Difference map and normalization (Section 9) -/

/-- Definition 9.1 (Difference map).
For `f : Sph n → Euc n`, `diffMap f x = f x - f (Ant n x)`.
Corresponds to `h_f` in Definition 9.1 in the source. -/
def diffMap {n : ℕ} (f : Sph n → Euc n) (x : Sph n) : Euc n :=
  f x - f (Ant n x)

/-
External theorem 9.2 (Continuity of the difference map).
If `f` is continuous, then `diffMap f` is continuous.
Corresponds to External theorem 9.2 in the source.
-/
theorem continuous_diffMap {n : ℕ} {f : Sph n → Euc n} (hf : Continuous f) :
    Continuous (diffMap f) := by
  exact hf.sub ( hf.comp ( continuous_Ant n ) )

/-
Lemma 9.3 (Difference map is odd).
For every `x : Sph n`, `diffMap f (Ant n x) = -(diffMap f x)`.
Corresponds to Lemma 9.3 in the source.
-/
theorem diffMap_odd {n : ℕ} (f : Sph n → Euc n) (x : Sph n) :
    diffMap f (Ant n x) = -diffMap f x := by
  unfold diffMap; simp +decide [ Ant_Ant ] ;

/-
Lemma 9.4 (Difference map is nowhere zero under the contradiction hypothesis).
If `¬∃ x, f x = f (Ant n x)`, then `diffMap f x ≠ 0` for all `x`.
Corresponds to Lemma 9.4 in the source.
-/
theorem diffMap_ne_zero {n : ℕ} (f : Sph n → Euc n)
    (hne : ¬∃ x : Sph n, f x = f (Ant n x)) (x : Sph n) :
    diffMap f x ≠ 0 := by
  grind +locals

/-- Definition 9.5 (Ambient normalization).
`ambNorm h x = (1 / ‖h x‖) • h x`.
Corresponds to `𝓝^{amb}_h` in Definition 9.5 in the source. -/
def ambNorm {n : ℕ} (h : Sph n → Euc n) (x : Sph n) : Euc n :=
  (1 / ‖h x‖) • h x

/-
External theorem 9.6 (Ambient normalization lands in the unit sphere).
If `h x ≠ 0` for all `x`, then `‖ambNorm h x‖ = 1`.
Corresponds to External theorem 9.6 in the source.
-/
theorem ambNorm_mem_sphere {n : ℕ} (h : Sph n → Euc n)
    (h0 : ∀ x : Sph n, h x ≠ 0) (x : Sph n) :
    ‖ambNorm h x‖ = 1 := by
  unfold ambNorm; simp +decide [ norm_smul, h0 ] ;

/-- Definition 9.7 (Sphere-valued normalization).
`sphNorm h h0 x` is the normalized `h x` as an element of `TSph n`.
Corresponds to `N_{h, H_0}` in Definition 9.7 in the source. -/
def sphNorm {n : ℕ} (h : Sph n → Euc n)
    (h0 : ∀ x : Sph n, h x ≠ 0) (x : Sph n) : TSph n :=
  ⟨ambNorm h x, mem_sphere_zero_iff_norm.mpr (ambNorm_mem_sphere h h0 x)⟩

/-
External theorem 9.8 (Normalization is continuous).
If `h` is continuous and `h x ≠ 0` for all `x`, then `sphNorm h h0` is continuous.
Corresponds to External theorem 9.8 in the source.
-/
theorem continuous_sphNorm {n : ℕ} (h : Sph n → Euc n)
    (hcont : Continuous h) (h0 : ∀ x : Sph n, h x ≠ 0) :
    Continuous (sphNorm h h0) := by
  refine' Continuous.subtype_mk _ _;
  exact Continuous.smul ( continuous_const.div ( hcont.norm ) fun x => norm_ne_zero_iff.mpr ( h0 x ) ) hcont

/-
Lemma 9.9 (Normalization preserves oddness).
If `h (Ant n x) = -h x` for all `x` and `h x ≠ 0` for all `x`, then
`sphNorm h h0 (Ant n x) = TAnt n (sphNorm h h0 x)`.
Corresponds to Lemma 9.9 in the source.
-/
theorem sphNorm_odd {n : ℕ} (h : Sph n → Euc n)
    (h0 : ∀ x : Sph n, h x ≠ 0)
    (hodd : ∀ x : Sph n, h (Ant n x) = -h x)
    (x : Sph n) :
    sphNorm h h0 (Ant n x) = TAnt n (sphNorm h h0 x) := by
  simp +decide [ sphNorm ];
  unfold ambNorm; aesop;

/-! ## Borsuk–Ulam theorem (Sections 10–12) -/

/-
Theorem 10.1 (Borsuk–Ulam in positive dimension).
Assuming FSTP, for `0 < n` and continuous `f : Sph n → Euc n`,
there exists `x : Sph n` with `f x = f (Ant n x)`.
Corresponds to Theorem 10.1 in the source.
-/
theorem borsuk_ulam_pos (hFSTP : FSTP) (n : ℕ) (hpos : 0 < n)
    (f : Sph n → Euc n) (hf : Continuous f) :
    ∃ x : Sph n, f x = f (Ant n x) := by
  contrapose! hFSTP with hFSTP;
  intro hFSTP'
  obtain ⟨g, hg⟩ := no_continuous_odd_map hFSTP' n hpos (by
  exact ⟨ _, continuous_sphNorm _ ( continuous_diffMap hf ) ( diffMap_ne_zero _ ( by push_neg; tauto ) ), fun x => sphNorm_odd _ ( diffMap_ne_zero _ ( by push_neg; tauto ) ) ( diffMap_odd _ ) x ⟩)

/-
Lemma 11.1 (The space `Euc 0` is subsingleton).
For every `a, b : Euc 0`, `a = b`.
Corresponds to Lemma 11.1 in the source.
-/
theorem euc_zero_subsingleton (a b : Euc 0) : a = b := by
  exact Subsingleton.elim _ _

/-
External theorem 11.2 (The zero-dimensional sphere is inhabited).
There exists `x : Sph 0`.
Corresponds to External theorem 11.2 in the source.
-/
theorem sph_zero_inhabited : Nonempty (Sph 0) := by
  refine' ⟨ ⟨ EuclideanSpace.single 0 1, _ ⟩ ⟩ ; norm_num

/-
Theorem 11.3 (Borsuk–Ulam in zero dimension).
For any `f : Sph 0 → Euc 0`, there exists `x : Sph 0` with `f x = f (Ant 0 x)`.
Corresponds to Theorem 11.3 in the source.
-/
theorem borsuk_ulam_zero (f : Sph 0 → Euc 0) :
    ∃ x : Sph 0, f x = f (Ant 0 x) := by
  cases' sph_zero_inhabited with x;
  use x;
  exact euc_zero_subsingleton _ _

/-
Theorem 12.1 (Borsuk–Ulam conditional on the Fine Spherical Tucker Package).
Assuming FSTP, for every `n` and continuous `f : Sph n → Euc n`,
there exists `x : Sph n` with `f x = f (Ant n x)`.
Corresponds to Theorem 12.1 (the final theorem) in the source.
-/
theorem borsuk_ulam (hFSTP : FSTP) (n : ℕ)
    (f : Sph n → Euc n) (hf : Continuous f) :
    ∃ x : Sph n, f x = f (Ant n x) := by
  cases n <;> [ exact borsuk_ulam_zero f; exact borsuk_ulam_pos hFSTP _ ( Nat.succ_pos _ ) f hf ]

end