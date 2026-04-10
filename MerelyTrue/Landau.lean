/-!
# Vlasov-Maxwell-Landau Steady-State Theorem

A complete formalization of smooth steady-state solutions to the
**Vlasov-Maxwell-Landau (VML) system** with Coulomb collisions on the 3-torus.

**Status: fully verified by the Lean 4 kernel. 0 sorry's across 34 files (~10,400 lines).**

## External Resources

- **arXiv paper:** <https://arxiv.org/abs/2603.15929>
- **Technical report:** <https://github.com/Vilin97/Clawristotle/blob/landau/TECHNICAL_REPORT.md>
- **Blueprint & dependency graph:** <https://vilin97.github.io/Clawristotle/>
- **Agent logs dataset:** <https://huggingface.co/datasets/Vilin97/clawristotle-landau-agent-logs>
- **Origin repo (Clawristotle):** <https://github.com/Vilin97/Clawristotle/tree/landau>

## The Physical System

The Vlasov-Maxwell-Landau system models charged plasma dynamics:

- `f(x, v)` — particle distribution function on `T³ × ℝ³`
- `E(x)` — electric field on `T³`
- `B(x)` — magnetic field on `T³`

The equations are:

```
  v · ∇ₓf + (E + v × B) · ∇ᵥf = ν · Q(f, f)     (Vlasov)
  curl B = J = ∫ v f dv                             (Ampere)
  div E = ∫ f dv - ρ_ion                            (Gauss)
  div B = 0                                          (Solenoidal)
```

The **Landau collision operator** is:

```
  Q(f, f)(v) = ∇ᵥ · ∫ A(v - w) [f(w)∇ᵥf(v) - f(v)∇ᵥf(w)] dw
```

where `A(z) = Ψ(|z|)(|z|²I - zz^T)` is the Landau collision matrix
with Coulomb kernel `Ψ(r) = r⁻³`.

## Main Theorem

**Theorem (`CoulombConcreteTheorem42`).** Let `f > 0` be a smooth steady-state solution
of the VML system with Coulomb collisions on `T³ = (ℝ/ℤ)³`, with Schwartz-class
velocity decay and stretched-exponential lower bound. Then:

1. **`f` is a spatially uniform Maxwellian:**
   `f(x, v) = ρ_ion / (2πT)^(3/2) · exp(-|v|² / 2T)` for some `T > 0`
2. **The electric field vanishes:** `E(x) = 0` everywhere
3. **The magnetic field is constant:** `B(x) = B₀` for some constant `B₀`

The theorem takes 13 physically meaningful hypotheses (see `CoulombConcreteTheorem42`
in `CoulombConcreteTheorem42.lean`). Non-vacuousness is proved separately: the equilibrium
Maxwellian with `E = 0`, `B = 0` witnesses all 13 conditions
(see `CoulombConcreteTheorem42_nonvacuous` in `CoulombNonvacuous.lean`).

## Proof Architecture

The proof decomposes into 7 mathematically distinct steps:

```
  Section 2: Landau matrix A(z) is positive semi-definite
       ↓
  Section 3: H-theorem → entropy dissipation D(f) ≤ 0
       ↓     D(f) = 0 ⟹ f is Maxwellian (nullspace characterization)
  Section 4: Vlasov transport → f is a LOCAL Maxwellian at each x
       ↓
  Section 5: Polynomial matching → temperature T is constant
       ↓
  Section 6: Killing's equation → bulk velocity u is constant
       ↓
  Section 7: Maximum principle → u = 0 and E = 0
       ↓
  Section 8: Harmonic analysis on T³ → B is constant
```

The abstract proof is formalized against a `FlatTorus3` typeclass (see `Defs.lean`),
which specifies integration by parts, curl/divergence identities, a maximum principle,
and constancy of harmonic functions — without fixing a particular manifold.
The concrete torus `T³ = Fin 3 → AddCircle 1` satisfies all 22 fields
(see `TorusInstance.lean`).

## File Guide

### Core Definitions & Infrastructure

- `Defs.lean` — Landau collision operator, `VelocityDecayConditions`, `FlatTorus3` typeclass,
  `@[simp]` unfolding lemmas
- `VMLStructures.lean` — `VMLSteadyState`, `VMLEquilibrium`, `VMLInput` data structures
- `SchwartzDecayDefs.lean` — `UniformSchwartzDecay` and basic integrability lemmas
- `FlatTorus3Lemmas.lean` — Derived lemmas from `FlatTorus3` axioms: spatial multiplication,
  gradient vanishing, chain rules, integration by parts, Laplacian sign at extrema

### Torus Geometry & Integration

- `TorusDefs.lean` — 3-torus `T³ = (ℝ/ℤ)³`, projection `torusMk`, periodic lift,
  differential operators (`torusGradX`, `torusDivX`, `torusCurlX`)
- `TorusInstance.lean` — Full `FlatTorus3` instance on `Fin 3 → AddCircle 1`
- `TorusIntegration.lean` — Box integrals, integration by parts on `T³`,
  curl integral vanishing, energy method for harmonic constancy

### Mathematical Helpers

- `GaussianHelpers.lean` — Gaussian normalization, gradient of exp-quadratic functions
- `IteratedDerivHelpers.lean` — Bounds on iterated derivatives of CLMs and quadratic forms
- `LogBoundHelpers.lean` — Logarithmic growth from polynomial score bounds
- `NewtonianPotential.lean` — `|A(z)_{ij}| ≤ ‖z‖⁻¹`, local integrability of `‖z‖⁻¹`
- `Section3Helpers.lean` — Gaussian normalization, Maxwellian characterization helpers
- `Section3Helpers2.lean` — Landau flux vanishes for log-quadratic distributions

### Abstract Theory (Sections 2–8)

- `Section2.lean` — Landau matrix evenness, PSD, symmetrized weak form, entropy dissipation `D(f)`
- `Section3.lean` — H-theorem (`D(f) ≤ 0`), nullspace characterization (`D(f) = 0 ⟹ Maxwellian`)
- `Section4.lean` — Steady states are local Maxwellians
- `Section5.lean` — Temperature is spatially constant (polynomial matching)
- `Section6.lean` — Drift velocity `u = 0` via Ampere's law and Stokes' theorem
- `Section7.lean` — Poisson-Boltzmann equation, `E = 0`, harmonic theory on torus
- `Section8.lean` — `B = const` via `curl B = 0`, `div B = 0`, and harmonic constancy

### Assembly

- `VMLInputDerive.lean` — Constructs `VMLInput` from `VMLSteadyState` + `VelocityDecayConditions`,
  applies Sections 2–8 to derive `ConcreteTheorem42`
- `Theorem42.lean` — Main abstract result: steady state + decay conditions → global Maxwellian,
  `E = 0`, `B = const`

### Coulomb Kernel Instantiation

- `CoulombKernel.lean` — `coulombKernel` (`Ψ(r) = r⁻³`), strict positivity, Schwartz bounds
- `CoulombFlux.lean` — Integrability of the Landau collision flux for Coulomb
- `CoulombFluxConv.lean` — Coulomb entry convolution: differentiability and bounds
- `CoulombFluxDiff.lean` — Flux derivative decay and IBP integrability
- `CoulombFluxBound.lean` — Flux component bounds, `flux × log` integrability
- `CoulombPSDHelpers.lean` — PSD integrand continuity and pointwise bounds
- `CoulombPSD.lean` — PSD integrability and Fubini symmetrization
- `CoulombForceTransport.lean` — Force transport and IBP integrability
- `CoulombSpatialTransport.lean` — Spatial transport measurability, joint integrability
- `VelocityDecayInstance.lean` — Lorentz force component bound (`|F_i| ≤ C(1 + ‖v‖)`)
- `CoulombConcreteTheorem42.lean` — Specializes abstract theorem to Coulomb;
  verifies all 19 fields of `VelocityDecayConditions`
- `CoulombNonvacuous.lean` — Equilibrium Maxwellian witnesses all 13 hypotheses

## Development

This formalization was developed in 10 days (Mar 1–10, 2026) by Vasily Ilin
working collaboratively with Claude Code (Anthropic) and Aristotle (Harmonic).
The natural-language proof blueprint was generated by Gemini DeepThink.
See the technical report linked above for the full development narrative.
-/

-- Core definitions and infrastructure
import MerelyTrue.Landau.Defs
import MerelyTrue.Landau.VMLStructures
import MerelyTrue.Landau.SchwartzDecayDefs
import MerelyTrue.Landau.FlatTorus3Lemmas

-- Torus geometry and integration
import MerelyTrue.Landau.TorusDefs
import MerelyTrue.Landau.TorusInstance
import MerelyTrue.Landau.TorusIntegration

-- Mathematical helpers
import MerelyTrue.Landau.GaussianHelpers
import MerelyTrue.Landau.IteratedDerivHelpers
import MerelyTrue.Landau.LogBoundHelpers
import MerelyTrue.Landau.NewtonianPotential
import MerelyTrue.Landau.Section3Helpers
import MerelyTrue.Landau.Section3Helpers2

-- Abstract theory (Sections 2-8)
import MerelyTrue.Landau.Section2
import MerelyTrue.Landau.Section3
import MerelyTrue.Landau.Section4
import MerelyTrue.Landau.Section5
import MerelyTrue.Landau.Section6
import MerelyTrue.Landau.Section7
import MerelyTrue.Landau.Section8

-- Assembly
import MerelyTrue.Landau.VMLInputDerive
import MerelyTrue.Landau.Theorem42

-- Coulomb kernel instantiation
import MerelyTrue.Landau.CoulombKernel
import MerelyTrue.Landau.CoulombFlux
import MerelyTrue.Landau.CoulombFluxConv
import MerelyTrue.Landau.CoulombFluxDiff
import MerelyTrue.Landau.CoulombFluxBound
import MerelyTrue.Landau.CoulombPSDHelpers
import MerelyTrue.Landau.CoulombPSD
import MerelyTrue.Landau.CoulombForceTransport
import MerelyTrue.Landau.CoulombSpatialTransport
import MerelyTrue.Landau.VelocityDecayInstance
import MerelyTrue.Landau.CoulombConcreteTheorem42
import MerelyTrue.Landau.CoulombNonvacuous
