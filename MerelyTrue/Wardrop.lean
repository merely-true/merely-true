import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Wardrop Equilibrium

This file formalizes the *Wardrop equilibrium* of a network routing problem with
**both series and parallel structure**, and proves that the equilibrium **link
flows** are unique when the link cost functions are strictly increasing.

## Model

A `RoutingProblem` is built from a finite set of `links` `L` and a finite,
nonempty set of `routes` `R`:

* a total `demand : ℝ` of traffic that must be routed;
* `route : R → Finset L`, giving for each route the **set of links** that
  compose it (series structure: a route traverses several links; parallel
  structure: several routes may exist between the same endpoints);
* `linkCost : L → ℝ → ℝ`, where `linkCost ℓ x` is the cost of link `ℓ` as a
  function of its usage `x`.

Given a *route flow* `f : R → ℝ`:

* `linkFlow f ℓ` is the **usage** of link `ℓ`, i.e. the total flow on all routes
  that traverse `ℓ`;
* `routeCost f r` is the cost of route `r`, namely the **sum of the costs of its
  links** evaluated at the current link usages.

A flow is `Feasible` when it is nonnegative and routes the total demand, and
`IsWardrop` when, additionally, every used route carries minimal cost (Wardrop's
first principle).

## Main results

* `RoutingProblem.wardrop_variational`: a Wardrop equilibrium solves the
  variational inequality `0 ≤ ∑ r, routeCost f r * (g r - f r)` against every
  feasible competitor `g`.
* `RoutingProblem.routeCost_inner_eq`: the route-space pairing equals the
  link-space pairing — the bridge that moves the analysis onto link flows.
* `RoutingProblem.wardrop_link_unique`: if every link cost is *strictly*
  increasing, any two Wardrop equilibria induce the **same link flows**.
* `RoutingProblem.wardrop_linkCost_unique`: if every link cost is merely
  *monotone*, any two Wardrop equilibria induce the **same link costs** (the most
  that survives when strictness is dropped).

## A caveat on uniqueness

With shared links, equilibrium *route* flows need **not** be unique: distinct
route distributions can realize identical link usages and both be equilibria.
What is pinned down — and what `wardrop_link_unique` establishes — is the vector
of *link* flows.  This is the classical content of Beckmann's theorem.

Strictness of the cost functions cannot be dropped from `wardrop_link_unique`:
with merely monotone costs (e.g. two *constant*-cost parallel links), every split
of the demand is an equilibrium and the link flows genuinely differ.  In that
regime only the equilibrium link *costs* are determined, which is exactly
`wardrop_linkCost_unique`.

Existence of an equilibrium is a deeper fact requiring fixed-point /
convex-optimization machinery and is not addressed here.
-/

open Finset

namespace Wardrop

/-- For a monotone scalar function `φ`, the product `(φ x - φ y) * (x - y)` is
nonnegative: the two factors always share a sign. -/
private lemma mul_sub_nonneg_of_monotone {φ : ℝ → ℝ} (h : Monotone φ) (x y : ℝ) :
    0 ≤ (φ x - φ y) * (x - y) := by
  rcases le_total x y with hxy | hxy
  · nlinarith [h hxy]
  · nlinarith [h hxy]

/-- For a strictly monotone scalar function `φ`, the product `(φ x - φ y) * (x - y)`
is strictly positive whenever `x ≠ y`. -/
private lemma mul_sub_pos_of_strictMono {φ : ℝ → ℝ} (h : StrictMono φ) {x y : ℝ}
    (hxy : x ≠ y) : 0 < (φ x - φ y) * (x - y) := by
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · nlinarith [h hlt]
  · nlinarith [h hlt]

/-- If the product `(φ x - φ y) * (x - y)` vanishes then `φ x = φ y`: either the
arguments already agree, or the value difference is forced to be zero.  (No
monotonicity is needed here.) -/
private lemma eq_of_mul_sub_eq_zero {φ : ℝ → ℝ} {x y : ℝ}
    (hxy : (φ x - φ y) * (x - y) = 0) : φ x = φ y := by
  rcases mul_eq_zero.mp hxy with h | h
  · exact sub_eq_zero.mp h
  · rw [sub_eq_zero.mp h]

end Wardrop

/-- A network routing problem with series–parallel structure: a finite set of
`links` `L` and a finite set of `routes` `R`, where each route is composed of a
set of links and each link has a usage-dependent cost. -/
structure RoutingProblem (L R : Type*) where
  /-- Total amount of traffic that must be routed across the network. -/
  demand : ℝ
  /-- `route r` is the set of links that make up route `r` (traversed in series). -/
  route : R → Finset L
  /-- `linkCost ℓ x` is the cost incurred on link `ℓ` when its usage equals `x`. -/
  linkCost : L → ℝ → ℝ

namespace RoutingProblem

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [Nonempty R]
  (P : RoutingProblem L R)

/-- The **usage** of link `ℓ` under route flow `f`: the total flow carried by all
routes that traverse `ℓ`. -/
def linkFlow (f : R → ℝ) (ℓ : L) : ℝ := ∑ r, if ℓ ∈ P.route r then f r else 0

/-- The **cost of route `r`** under route flow `f`: the sum, over the links of
the route, of each link's cost evaluated at the current link usage. -/
def routeCost (f : R → ℝ) (r : R) : ℝ := ∑ ℓ ∈ P.route r, P.linkCost ℓ (P.linkFlow f ℓ)

/-- A route flow `f` is **feasible** when it is nonnegative on every route and
routes exactly the total demand. -/
def Feasible (f : R → ℝ) : Prop :=
  (∀ r, 0 ≤ f r) ∧ ∑ r, f r = P.demand

/-- A route flow `f` is a **Wardrop equilibrium** when it is feasible and every
*used* route (one carrying positive flow) has minimal cost: no route offers a
cheaper alternative.  This is Wardrop's first principle. -/
def IsWardrop (f : R → ℝ) : Prop :=
  P.Feasible f ∧ ∀ r s, 0 < f r → P.routeCost f r ≤ P.routeCost f s

/-- The link costs are **increasing**: each link's cost is a strictly increasing
function of that link's usage.  This is the congestion assumption under which the
equilibrium link flows are unique. -/
def Increasing : Prop := ∀ ℓ, StrictMono (P.linkCost ℓ)

omit [Fintype L] in
/-- **Variational characterization.**  A Wardrop equilibrium `f` solves the
variational inequality: for every feasible competitor `g`,
`0 ≤ ∑ r, routeCost f r * (g r - f r)`.

Intuitively, redistributing traffic away from the equilibrium can only increase
total experienced cost. -/
theorem wardrop_variational {f g : R → ℝ} (hf : P.IsWardrop f)
    (hg : P.Feasible g) : 0 ≤ ∑ r, P.routeCost f r * (g r - f r) := by
  obtain ⟨⟨hf_nonneg, hf_sum⟩, hf_min⟩ := hf
  obtain ⟨hg_nonneg, hg_sum⟩ := hg
  -- Choose a route `r₀` of minimal cost and let `m` be that minimal cost.
  obtain ⟨r₀, -, hr₀⟩ :=
    Finset.exists_min_image univ (fun r => P.routeCost f r) univ_nonempty
  set m := P.routeCost f r₀ with hm
  -- `m` lower-bounds every route's cost.
  have hmin : ∀ r, m ≤ P.routeCost f r := fun r => hr₀ r (mem_univ r)
  -- Every used route attains the minimal cost `m`.
  have hused : ∀ r, 0 < f r → P.routeCost f r = m := by
    intro r hr
    have h1 := hf_min r r₀ hr
    rw [← hm] at h1
    exact le_antisymm h1 (hmin r)
  -- The flows route equal demand, so the net redistribution sums to zero.
  have hgf : ∑ r, (g r - f r) = 0 := by
    rw [Finset.sum_sub_distrib, hg_sum, hf_sum, sub_self]
  -- Subtracting the constant `m` from each cost does not change the sum.
  have key : ∑ r, P.routeCost f r * (g r - f r)
      = ∑ r, (P.routeCost f r - m) * (g r - f r) := by
    have hsplit : ∑ r, P.routeCost f r * (g r - f r)
        = ∑ r, ((P.routeCost f r - m) * (g r - f r) + m * (g r - f r)) :=
      Finset.sum_congr rfl fun r _ => by ring
    rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hgf, mul_zero, add_zero]
  rw [key]
  -- Each remaining term is nonnegative: used routes contribute `0`, while on
  -- unused routes both factors are nonnegative.
  apply Finset.sum_nonneg
  intro r _
  rcases (hf_nonneg r).lt_or_eq with hpos | hzero
  · simp [hused r hpos]
  · have hfr : f r = 0 := hzero.symm
    have h1 : 0 ≤ P.routeCost f r - m := sub_nonneg.mpr (hmin r)
    have h2 : 0 ≤ g r - f r := by rw [hfr, sub_zero]; exact hg_nonneg r
    exact mul_nonneg h1 h2

omit [Fintype L] [Nonempty R] in
/-- The difference of link usages, expressed as a single sum over routes. -/
private lemma linkFlow_sub (f g : R → ℝ) (ℓ : L) :
    P.linkFlow g ℓ - P.linkFlow f ℓ = ∑ r, if ℓ ∈ P.route r then g r - f r else 0 := by
  rw [linkFlow, linkFlow, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ => by split_ifs <;> ring

omit [Nonempty R] in
/-- `routeCost f r`, written as a sum over *all* links via an indicator. -/
private lemma routeCost_eq_indicator (f : R → ℝ) (r : R) :
    P.routeCost f r
      = ∑ ℓ, if ℓ ∈ P.route r then P.linkCost ℓ (P.linkFlow f ℓ) else 0 := by
  simp only [routeCost, Finset.sum_ite_mem, Finset.univ_inter]

omit [Nonempty R] in
/-- **Route–link bridge.**  The pairing of route costs with a flow difference in
*route* space equals the pairing of link costs with the induced flow difference
in *link* space.  This is just Fubini together with the definition of link flow:
`∑ r, routeCost f r * (g r - f r) = ∑ ℓ, linkCost ℓ (linkFlow f ℓ) * (linkFlow g ℓ - linkFlow f ℓ)`. -/
theorem routeCost_inner_eq (f g : R → ℝ) :
    ∑ r, P.routeCost f r * (g r - f r)
      = ∑ ℓ, P.linkCost ℓ (P.linkFlow f ℓ) * (P.linkFlow g ℓ - P.linkFlow f ℓ) := by
  calc
    ∑ r, P.routeCost f r * (g r - f r)
        = ∑ r, ∑ ℓ, (if ℓ ∈ P.route r then P.linkCost ℓ (P.linkFlow f ℓ) else 0)
            * (g r - f r) := by
          simp_rw [routeCost_eq_indicator, Finset.sum_mul]
      _ = ∑ ℓ, ∑ r, (if ℓ ∈ P.route r then P.linkCost ℓ (P.linkFlow f ℓ) else 0)
            * (g r - f r) := Finset.sum_comm
      _ = ∑ ℓ, P.linkCost ℓ (P.linkFlow f ℓ) * (P.linkFlow g ℓ - P.linkFlow f ℓ) := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [P.linkFlow_sub f g ℓ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ => by split_ifs <;> ring

/-- **Core monotone estimate.**  Assuming only that each link cost is *monotone*
(non-decreasing), any two Wardrop equilibria make each link's
`(cost difference) · (flow difference)` vanish.

This is the shared heart of both uniqueness statements below: adding the two
variational inequalities (in link space) gives `∑ ℓ, termₗ ≤ 0`, while
monotonicity gives `termₗ ≥ 0`, so the sum is zero and every term vanishes. -/
private lemma wardrop_term_zero (hmono : ∀ ℓ, Monotone (P.linkCost ℓ)) {f g : R → ℝ}
    (hf : P.IsWardrop f) (hg : P.IsWardrop g) (ℓ : L) :
    (P.linkCost ℓ (P.linkFlow f ℓ) - P.linkCost ℓ (P.linkFlow g ℓ))
      * (P.linkFlow f ℓ - P.linkFlow g ℓ) = 0 := by
  -- Each equilibrium satisfies the variational inequality; move both to link space.
  have hVIf := P.wardrop_variational hf hg.1
  have hVIg := P.wardrop_variational hg hf.1
  rw [P.routeCost_inner_eq f g] at hVIf
  rw [P.routeCost_inner_eq g f] at hVIg
  -- Adding the two inequalities cancels everything except the monotonicity term.
  have key : (∑ ℓ, (P.linkCost ℓ (P.linkFlow f ℓ) - P.linkCost ℓ (P.linkFlow g ℓ))
        * (P.linkFlow f ℓ - P.linkFlow g ℓ))
      + ((∑ ℓ, P.linkCost ℓ (P.linkFlow f ℓ) * (P.linkFlow g ℓ - P.linkFlow f ℓ))
        + (∑ ℓ, P.linkCost ℓ (P.linkFlow g ℓ) * (P.linkFlow f ℓ - P.linkFlow g ℓ))) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun ℓ _ => by ring
  have hsum_le : (∑ ℓ, (P.linkCost ℓ (P.linkFlow f ℓ) - P.linkCost ℓ (P.linkFlow g ℓ))
      * (P.linkFlow f ℓ - P.linkFlow g ℓ)) ≤ 0 := by linarith
  -- Monotonicity makes every term nonnegative.
  have hterm_nonneg : ∀ ℓ ∈ univ,
      0 ≤ (P.linkCost ℓ (P.linkFlow f ℓ) - P.linkCost ℓ (P.linkFlow g ℓ))
        * (P.linkFlow f ℓ - P.linkFlow g ℓ) :=
    fun ℓ _ => Wardrop.mul_sub_nonneg_of_monotone (hmono ℓ) _ _
  -- Hence the sum is exactly zero, forcing every term to vanish.
  have hzero : (∑ ℓ, (P.linkCost ℓ (P.linkFlow f ℓ) - P.linkCost ℓ (P.linkFlow g ℓ))
      * (P.linkFlow f ℓ - P.linkFlow g ℓ)) = 0 :=
    le_antisymm hsum_le (Finset.sum_nonneg hterm_nonneg)
  exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hzero ℓ (mem_univ ℓ)

/-- **Uniqueness of equilibrium link flows.**  If every link cost is *strictly*
increasing, then any two Wardrop equilibria induce the same usage on every link. -/
theorem wardrop_link_unique (hinc : P.Increasing) {f g : R → ℝ}
    (hf : P.IsWardrop f) (hg : P.IsWardrop g) (ℓ : L) :
    P.linkFlow f ℓ = P.linkFlow g ℓ := by
  -- A vanishing term on a strictly increasing cost forces equal link usages.
  by_contra hne
  have hpos := Wardrop.mul_sub_pos_of_strictMono (hinc ℓ) hne
  rw [P.wardrop_term_zero (fun ℓ => (hinc ℓ).monotone) hf hg ℓ] at hpos
  exact lt_irrefl 0 hpos

/-- **Uniqueness of equilibrium link costs — without strictness.**  If every link
cost is merely *monotone* (non-decreasing), then any two Wardrop equilibria assign
the same cost to every link, even though the link *flows* may differ.

This is the most that survives when strictness is dropped: the constant-cost
parallel-links network shows that genuinely distinct equilibrium flows can occur,
so `wardrop_link_unique` really does require strict monotonicity. -/
theorem wardrop_linkCost_unique (hmono : ∀ ℓ, Monotone (P.linkCost ℓ)) {f g : R → ℝ}
    (hf : P.IsWardrop f) (hg : P.IsWardrop g) (ℓ : L) :
    P.linkCost ℓ (P.linkFlow f ℓ) = P.linkCost ℓ (P.linkFlow g ℓ) :=
  Wardrop.eq_of_mul_sub_eq_zero (P.wardrop_term_zero hmono hf hg ℓ)

end RoutingProblem
