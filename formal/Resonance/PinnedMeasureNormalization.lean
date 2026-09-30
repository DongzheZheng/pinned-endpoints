import Resonance.PinnedPeriodicity
import Mathlib.Geometry.Euclidean.Volume.Measure

/-! Explicit normalization of the pinned regular coarea.  Mathlib's
`μH[2]` and Euclidean area `μHE[2]` are not silently identified: the
same positive finite Haar scalar multiplies the full restricted, weighted,
and periodic-pushforward measures.  This is an equivalence of null sets,
not a claim that this scalar is one.  Area is formed in the original
Euclidean ambient space before taking the half-open cell and quotient map;
no Hausdorff measure for the default product metric on `CircleMomenta` is
used or identified with flat Euclidean torus area. -/
open MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory
namespace Resonance.PinnedMeasureNormalization
noncomputable section
open Resonance.PinnedMeasure Resonance.PinnedPeriodicity

def areaFactor : ℝ≥0 :=
  Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) μH[(2 : ℕ)]

theorem areaFactor_ne_zero : areaFactor ≠ 0 :=
  Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2

theorem areaFactor_pos : 0 < areaFactor := pos_iff_ne_zero.mpr areaFactor_ne_zero

theorem areaFactor_finite : (areaFactor : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top

theorem euclideanArea_eq_smul :
    (μHE[2] : Measure Ambient) = (areaFactor : ℝ≥0∞) • (μH[2] : Measure Ambient) := by
  rw [Measure.euclideanHausdorffMeasure_def]
  rfl

def euclideanLiftedRegularCoarea (d : ℝ) : Measure Ambient :=
  ((μHE[2] : Measure Ambient).restrict (regularSurface d)).withDensity (coareaWeight d)

def euclideanCellCoarea (d : ℝ) : Measure Ambient :=
  (euclideanLiftedRegularCoarea d).restrict fundamentalCell

def euclideanCircleRegularCoarea (d : ℝ) : Measure CircleMomenta :=
  (euclideanCellCoarea d).map quotientCoordinates

def euclideanCircleInvariant (d : ℝ) (φ : PinnedPeriodicity.Circle → ℂ) : Prop :=
  ∀ᵐ k ∂euclideanCircleRegularCoarea d, circleInvariantRelation φ k

theorem euclideanLiftedRegularCoarea_eq_smul (d : ℝ) :
    euclideanLiftedRegularCoarea d = (areaFactor : ℝ≥0∞) • liftedRegularCoarea d := by
  unfold euclideanLiftedRegularCoarea liftedRegularCoarea
  rw [euclideanArea_eq_smul, Measure.restrict_smul, withDensity_smul_measure]

theorem euclideanCellCoarea_eq_smul (d : ℝ) :
    euclideanCellCoarea d = (areaFactor : ℝ≥0∞) • cellCoarea d := by
  unfold euclideanCellCoarea cellCoarea
  rw [euclideanLiftedRegularCoarea_eq_smul, Measure.restrict_smul]

theorem euclideanCircleRegularCoarea_eq_smul (d : ℝ) :
    euclideanCircleRegularCoarea d = (areaFactor : ℝ≥0∞) • circleRegularCoarea d := by
  unfold euclideanCircleRegularCoarea circleRegularCoarea
  rw [euclideanCellCoarea_eq_smul, Measure.map_smul]

theorem lifted_coarea_mutually_absolutelyContinuous (d : ℝ) :
    euclideanLiftedRegularCoarea d ≪ liftedRegularCoarea d ∧
    liftedRegularCoarea d ≪ euclideanLiftedRegularCoarea d := by
  rw [euclideanLiftedRegularCoarea_eq_smul]
  exact ⟨Measure.smul_absolutelyContinuous,
    Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.mpr areaFactor_ne_zero)⟩

theorem circle_coarea_mutually_absolutelyContinuous (d : ℝ) :
    euclideanCircleRegularCoarea d ≪ circleRegularCoarea d ∧
    circleRegularCoarea d ≪ euclideanCircleRegularCoarea d := by
  rw [euclideanCircleRegularCoarea_eq_smul]
  exact ⟨Measure.smul_absolutelyContinuous,
    Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.mpr areaFactor_ne_zero)⟩

theorem lifted_coarea_ae_iff (d : ℝ) (p : Ambient → Prop) :
    (∀ᵐ k ∂euclideanLiftedRegularCoarea d, p k) ↔
      ∀ᵐ k ∂liftedRegularCoarea d, p k := by
  rw [euclideanLiftedRegularCoarea_eq_smul]
  exact Measure.ae_ennreal_smul_measure_iff (ENNReal.coe_ne_zero.mpr areaFactor_ne_zero)

theorem circle_coarea_ae_iff (d : ℝ) (p : CircleMomenta → Prop) :
    (∀ᵐ k ∂euclideanCircleRegularCoarea d, p k) ↔
      ∀ᵐ k ∂circleRegularCoarea d, p k := by
  rw [euclideanCircleRegularCoarea_eq_smul]
  exact Measure.ae_ennreal_smul_measure_iff (ENNReal.coe_ne_zero.mpr areaFactor_ne_zero)

theorem euclideanCircleInvariant_iff (d : ℝ) (φ : PinnedPeriodicity.Circle → ℂ) :
    euclideanCircleInvariant d φ ↔ circleInvariant d φ :=
  circle_coarea_ae_iff d (circleInvariantRelation φ)

end
end Resonance.PinnedMeasureNormalization
