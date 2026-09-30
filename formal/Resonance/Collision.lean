import Mathlib

/-!
# Pinned one-dimensional dispersion

Only the original dispersion definition needed by the collision-invariant
classification is retained from the upstream shared algebra module.
-/

namespace Resonance.Collision
noncomputable section

/-- The unmodified pinned dispersion on a real lift of the circle. -/
def pinnedDispersion (d x : ℝ) : ℝ := Real.sqrt (1 - 2 * d * Real.cos x)

end
end Resonance.Collision
