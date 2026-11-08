import EnvyFreeResearch.MixedApproximation
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut total : Nat := 0
  for (declName, declInfo) in env.constants.toList do
    if declName.toString.startsWith "EnvyFreeResearch.MixedApproximation." ||
        declName.toString.startsWith "EnvyFreeResearch.R6MixedMonteCarlo." then
      let axioms ← collectAxioms declName
      let unexpected := axioms.filter fun a =>
        !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
      unless unexpected.isEmpty do
        throwError m!"Unexpected axioms for {declName}: {unexpected.toList}"
      match declInfo with
      | .axiomInfo _ => throwError m!"Project axiom: {declName}"
      | .thmInfo _ =>
        total := total + 1
        logInfo m!"{declName}: {axioms.toList}"
      | _ => pure ()
  if total == 0 then
    throwError "No reviewed theorems found."
  logInfo m!"MIXED INDEPENDENT FINITE AXIOM AUDIT PASSED: {total} theorem declarations."
