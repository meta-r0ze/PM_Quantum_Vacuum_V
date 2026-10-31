import PMDecay
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in env.allImportedModuleNames do
    if (`PMCosmo).isPrefixOf name then
      throwError "Downstream dependency {name} in Paper V"
  logInfo "Dependency audit passed: no Paper VI imports in Paper V"
