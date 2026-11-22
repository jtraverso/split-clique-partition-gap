module

import all SplitGap
import all GapExtremal.Bridge
import all GapExtremal.Cap
import all GapExtremal.Completion
import all GapExtremal.Core
import all GapExtremal.Defs
import all GapExtremal.ExactOrder
import all GapExtremal.Exponent
import all GapExtremal.ExponentTwo
import all GapExtremal.Geometry
import all GapExtremal.Global
import all GapExtremal.Global2
import all GapExtremal.GlobalLemmas
import all GapExtremal.Hosts
import all GapExtremal.Layered
import all GapExtremal.LayeredExponent
import all GapExtremal.LocalEmbed
import all GapExtremal.LocalH12
import all GapExtremal.Main
import all GapExtremal.PCore
import all GapExtremal.PHosts
import all GapExtremal.PMain
import all GapExtremal.PSource
import all GapExtremal.Residual
import all GapExtremal.SCap
import all GapExtremal.Single
import all GapExtremal.Source
import all GapExtremal.Sphere
import all GapExtremal.WeightCap
import all GraphBase.Clique.CliqueSets
import all GraphBase.Clique.Partition
import all R417.LogErrorAbsorption
import all R417.OptimalCoefficient
import all R434.AffineH54
import all R434.CoreDefect
import all R434.CoreDirections
import all R434.CoreFractional
import all R434.DensityThreshold
import all R434.EHPSClasses
import all R434.EHPSCompactExterior
import all R434.EHPSDensity
import all R434.EHPSGrid
import all R434.EHPSHostTransfer
import all R434.EHPSPotential
import all R434.EHPSProduct
import all R434.EHPSRegion
import all R434.ExactGraphTransfer
import all R434.FiniteR434
import all R434.GroupedGap
import all R434.GroupedHosts
import all R434.LocalH54
import all R434.LocalPacking
import all R434.LocalTriangleLift
import all R434.MidpointHosts
import all R434.OddMidpoints
import all R434.PackingTriangles
import all R434.PartitionEnergy
import all R434.PolylogGap
import all R434.PolylogOrder
import all R434.ResidualArithmetic
import all R434.ResidualIsolates
import all R434.RobustHosts
import all R434.RoleMatchings
import all R434.TightPieces
import all R434.TightTriangles
import all R434.TripartiteSlack
import all R434.UniformOrder
import all R434.UniversalHosts
import all R434.UniversalR434
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut rows := #[]
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    unless [`GapExtremal, `GraphBase, `R417, `R434, `SplitGap].any (·.isPrefixOf modName) do continue
    for info in env.header.moduleData[idx]!.constants do
      unless info matches .thmInfo _ do continue
      let name := info.name
      let axioms ← collectAxioms name
      unless axioms.all ([`propext, `Classical.choice, `Quot.sound].contains ·) do
        throwError "Unexpected axioms for {name}: {axioms}"
      rows := rows.push s!"{modName}\t{name}\t{axioms}"
  unless rows.any (·.contains "GapExtremal.R434.universal_R434_linear_mixed\t") do throwError "Missing mixed endpoint"
  if rows.isEmpty then throwError "No project theorems found"
  for row in rows.qsort (· < ·) do IO.println row
  IO.println s!"PASS: {rows.size} project theorems"
