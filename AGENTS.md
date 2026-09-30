# Research repository constraints

- This repository contains only the 1D pinned collision-invariant classification proof and the current narrow-band experiments. Do not add other models or unrelated formal results.
- The classification is the authors' own unpublished result, not a previously established external result.
- Do not compile or execute Lean locally. Python --source-only checks are allowed. Lean execution is restricted to explicitly authorized cab17/cab75 Linux servers; compare load before choosing. Reuse recorded verification when formal source hashes are unchanged.
- Keep precise boundaries between Lean-checked classification, manuscript proofs and finite Galerkin numerics. Variational upper bounds and unvalidated quadrature are not matching gap asymptotics or certified lower bounds.
- Preserve numerics/results as the tracked baseline. Put recalculations in generated/ and compare them before updating baseline data.
- If changing formal source, regenerate the manifest and obtain new server evidence for exactly those hashes. Never carry over a success claim from different source bytes.
