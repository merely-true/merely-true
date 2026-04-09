import MerelyTrue.Landau.CoulombConcreteTheorem42
import MerelyTrue.Landau.CoulombFlux
import MerelyTrue.Landau.CoulombFluxBound
import MerelyTrue.Landau.CoulombFluxConv
import MerelyTrue.Landau.CoulombFluxDiff
import MerelyTrue.Landau.CoulombForceTransport
import MerelyTrue.Landau.CoulombKernel
import MerelyTrue.Landau.CoulombNonvacuous
import MerelyTrue.Landau.CoulombPSD
import MerelyTrue.Landau.CoulombPSDHelpers
import MerelyTrue.Landau.CoulombSpatialTransport
import MerelyTrue.Landau.Defs
import MerelyTrue.Landau.FlatTorus3Lemmas
import MerelyTrue.Landau.GaussianHelpers
import MerelyTrue.Landau.IteratedDerivHelpers
import MerelyTrue.Landau.LogBoundHelpers
import MerelyTrue.Landau.MaxwellMoleculesTheorem42
import MerelyTrue.Landau.NewtonianPotential
import MerelyTrue.Landau.SchwartzDecayDefs
import MerelyTrue.Landau.Section2
import MerelyTrue.Landau.Section3
import MerelyTrue.Landau.Section3Helpers
import MerelyTrue.Landau.Section3Helpers2
import MerelyTrue.Landau.Section4
import MerelyTrue.Landau.Section5
import MerelyTrue.Landau.Section6
import MerelyTrue.Landau.Section7
import MerelyTrue.Landau.Section8
import MerelyTrue.Landau.Theorem42
import MerelyTrue.Landau.TorusDefs
import MerelyTrue.Landau.TorusInstance
import MerelyTrue.Landau.TorusIntegration
import MerelyTrue.Landau.VMLInputDerive
import MerelyTrue.Landau.VMLStructures
import MerelyTrue.Landau.VelocityDecayInstance

/-!
# Vlasov-Maxwell-Landau Steady State Classification

A formalization of the steady-state classification for the Vlasov-Maxwell-Landau (VML) system,
working within the non-relativistic kinetic theory framework. The central result is **Theorem 4.2**:
any sufficiently smooth steady-state solution of the VML system on a periodic spatial domain,
subject to suitable velocity decay conditions, must be a **global Maxwellian equilibrium** with
electric field **E = 0** and magnetic field **B = const**.

The formalization covers the abstract form of Theorem 4.2 as well as its concrete specializations:
the **Coulomb kernel** (where the interaction potential satisfies Ψ(r) = r⁻³) and
**Maxwell molecules** (bounded interaction kernels). Non-vacuousness proofs verify that the
hypotheses of these theorems are satisfiable, ensuring the results are not vacuously true.
Supporting material includes definitions for the flat 3-torus domain, Schwartz-class velocity
decay, the Landau collision operator, and various analytic estimates (flux bounds, transport
identities, positive semi-definiteness of the collision kernel).

The development follows the section-by-section structure of the H-theorem analysis for the VML
system, covering entropy production (Sections 2-3), the Landau collision operator properties
(Sections 4-5), spatial and velocity transport identities (Sections 6-7), and the final
classification argument (Section 8).
-/
