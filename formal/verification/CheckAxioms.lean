import Resonance
import Lean.Util.FoldConsts

/-!
Audit the transitive type/value constant dependencies of every imported
Resonance theorem, including private and compiler-generated theorem roots.
No dependency is skipped on account of its name, namespace or library.
This is an environment audit, not a theorem asserting the paper's semantics.
-/
open Lean in
run_cmd do
  let env ← getEnv
  let mut todo : List Name := []
  let mut roots := 0
  for (name, ci) in env.constants.toList do
    if (privateToUserName name).toString.startsWith "Resonance." then
      match ci with
      | .thmInfo _ =>
        roots := roots + 1
        todo := name :: todo
        logInfo m!"CONE_ROOT {name}"
      | _ => pure ()
  unless roots > 0 do throwError "No Resonance theorem roots found"
  let mut seen : NameSet := {}
  let mut count := 0
  let mut unsafeCount := 0
  let mut partialCount := 0
  let mut forbiddenAxioms := 0
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      seen := seen.insert name
      count := count + 1
      let some ci := env.find? name | throwError m!"Missing dependency {name}"
      logInfo m!"CONE_CONSTANT {name}"
      if ci.isUnsafe then
        unsafeCount := unsafeCount + 1
        logInfo m!"CONE_UNSAFE {name}"
      if ci.isPartial then
        partialCount := partialCount + 1
        logInfo m!"CONE_PARTIAL {name}"
      match ci with
      | .axiomInfo _ =>
        logInfo m!"CONE_AXIOM {name}"
        unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
          forbiddenAxioms := forbiddenAxioms + 1
      | _ => pure ()
      for dep in ci.getUsedConstantsAsSet do
        if !seen.contains dep then todo := dep :: todo
  logInfo m!"CONE_COUNTS roots={roots} constants={count} unsafe={unsafeCount} partial={partialCount}"
  unless unsafeCount == 0 && partialCount == 0 && forbiddenAxioms == 0 do
    throwError "The proof cone contains an unsafe/partial constant or a nonstandard axiom"
