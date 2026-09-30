import Resonance.PinnedGlobalRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The completed-measure representative dictionary.  Borel measurability
and almost-everywhere measurability are not identified. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedCircleAE
noncomputable section
open Resonance.PinnedPeriodicity
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

/-- Circle Lebesgue measure, with total mass 2π. -/
abbrev circleVolume : Measure PinnedPeriodicity.Circle := volume

theorem circle_ae_lift {f g : PinnedPeriodicity.Circle → ℂ} (h : f =ᵐ[circleVolume] g) :
    periodicLift f =ᵐ[volume] periodicLift g := by
  change ∀ᵐ x ∂volume, periodicLift f x = periodicLift g x
  rw [ae_iff]
  let S := {x | periodicLift f x ≠ periodicLift g x}
  change volume S = 0
  apply measure_null_of_locally_null S
  intro x _hx
  let t := x-period/2
  let I := Ioc t (t+period)
  have he := (AddCircle.measurePreserving_mk period t).quasiMeasurePreserving.ae_eq h
  have hz : volume (S ∩ I) = 0 := by
    change ∀ᵐ y ∂volume.restrict I, periodicLift f y = periodicLift g y at he
    rw [ae_iff,Measure.restrict_apply' measurableSet_Ioc] at he
    exact he
  have hI : I ∈ 𝓝 x := by
    apply Ioc_mem_nhds
    · dsimp [t]
      linarith [period_pos]
    · dsimp [t]
      linarith [period_pos]
  exact ⟨S ∩ I,inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hI),hz⟩

theorem circle_aemeasurable_lift {φ : PinnedPeriodicity.Circle → ℂ} (hφ : AEMeasurable φ circleVolume) :
    AEMeasurable (periodicLift φ) (volume : Measure ℝ) := by
  have hm : Measurable (periodicLift (hφ.mk φ)) :=
    hφ.measurable_mk.comp (AddCircle.continuous_mk' period).measurable
  exact hm.aemeasurable.congr (circle_ae_lift hφ.ae_eq_mk).symm

theorem circle_ae_of_lift_ae {f g : PinnedPeriodicity.Circle → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (h : periodicLift f =ᵐ[volume] periodicLift g) : f =ᵐ[circleVolume] g := by
  have mp := AddCircle.measurePreserving_mk period 0
  have h' : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioc 0 (0+period)),
      f (x:PinnedPeriodicity.Circle) = g (x:PinnedPeriodicity.Circle) :=
    ae_restrict_of_ae h
  change ∀ᵐ k ∂(volume : Measure PinnedPeriodicity.Circle), f k = g k
  rw [← mp.map_eq]
  exact (ae_map_iff mp.measurable.aemeasurable (measurableSet_eq_fun hf hg)).mpr h'

end
end Resonance.PinnedCircleAE
