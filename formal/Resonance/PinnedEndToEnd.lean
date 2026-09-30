import Resonance.PinnedAERegularity

/-!
End-to-end classification for the original pinned dispersion, full periodic
regular coarea, and finite complex-valued almost-everywhere measurable
invariant.  No integrability, smooth representative, differential equation,
chart identity, or classification assertion is an input to the main theorem.

The coarea is the already defined regular Hausdorff coarea on the same
half-open periodic momentum cell, with the fourth momentum determined in
the quotient group. This module makes no assertion about a bare delta
distribution at energy-critical quartets, a nonlinear diffusion limit, or
the unrelated NLS-to-kinetic limit.
-/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedEndToEnd
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedGeometry
open Resonance.PinnedCircleAE Resonance.PinnedAERegularity

/-- The actual sqrt dispersion on the momentum circle, descended using its
proved 2π periodicity rather than a new dispersion relation. -/
def circleDispersion (d : ℝ) : PinnedPeriodicity.Circle → ℝ :=
  (PinnedPeriodicity.omega_periodic d).lift

@[simp] theorem circleDispersion_coe (d x : ℝ) :
    circleDispersion d (x : PinnedPeriodicity.Circle) =
      Real.sqrt (1-2*d*Real.cos x) := rfl

theorem circleDispersion_continuous {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) :
    Continuous (circleDispersion d) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (omega d)
  exact (PinnedCharts.signed_omega_contDiff (by linarith) hdU 0).continuous

/-- Classification in real periodic coordinates, still for the original
completed-measure circle input and the same full regular coarea. -/
theorem aemeasurable_circleInvariant_lift_classification {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : PinnedPeriodicity.Circle → ℂ) (hφ : AEMeasurable φ circleVolume)
    (hi : circleInvariant d φ) :
    ∃ A B : ℂ, periodicLift φ =ᵐ[volume]
      (fun x => A+B*(Real.sqrt (1-2*d*Real.cos x) : ℂ)) := by
  obtain ⟨g,hgs,hge,hgp⟩ := circleInvariant_AE_smooth_periodic_representative hd0 hdU φ hφ hi
  exact PinnedInvariantTransfer.circleInvariant_classification_of_smooth_representative
    hd0 hdU hi hge (hgs.of_le (WithTop.coe_le_coe.mpr (show (3:ℕ∞) ≤ ⊤ from le_top))) hgp

/-- The original circle classification. The initial function is only
almost-everywhere measurable for circle Lebesgue measure; its invariant
identity is the original coarea-a.e. identity with all four periodic legs. -/
theorem aemeasurable_circleInvariant_classification {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : PinnedPeriodicity.Circle → ℂ) (hφ : AEMeasurable φ circleVolume)
    (hi : circleInvariant d φ) :
    ∃ A B : ℂ, φ =ᵐ[circleVolume] (fun k => A+B*(circleDispersion d k : ℂ)) := by
  obtain ⟨A,B,hAB⟩ := aemeasurable_circleInvariant_lift_classification hd0 hdU φ hφ hi
  let φ₀ := hφ.mk φ
  let F : PinnedPeriodicity.Circle → ℂ := fun k => A+B*(circleDispersion d k : ℂ)
  have hmF : Measurable F :=
    (continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp (circleDispersion_continuous hd0 hdU)))).measurable
  have he : periodicLift φ₀ =ᵐ[volume] periodicLift F := by
    exact (circle_ae_lift hφ.ae_eq_mk).symm.trans hAB
  exact ⟨A,B,hφ.ae_eq_mk.trans (circle_ae_of_lift_ae hφ.measurable_mk hmF he)⟩

theorem measurable_circleInvariant_classification {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : PinnedPeriodicity.Circle → ℂ) (hφ : Measurable φ)
    (hi : circleInvariant d φ) :
    ∃ A B : ℂ, φ =ᵐ[circleVolume] (fun k => A+B*(circleDispersion d k : ℂ)) :=
  aemeasurable_circleInvariant_classification hd0 hdU φ hφ.aemeasurable hi

/-- The classified representative satisfies every original resonance
equation, including trivial and critical quartets. -/
theorem affine_dispersion_full_resonance (d : ℝ) (A B : ℂ) (x y z : ℝ)
    (he : energyDefect d x y z = 0) :
    (A+B*(circleDispersion d (x : PinnedPeriodicity.Circle) : ℂ)) +
      (A+B*(circleDispersion d (y : PinnedPeriodicity.Circle) : ℂ)) =
    (A+B*(circleDispersion d (z : PinnedPeriodicity.Circle) : ℂ)) +
      (A+B*(circleDispersion d ((x+y-z) : PinnedPeriodicity.Circle) : ℂ)) := by
  have hreal : omega d x+omega d y = omega d z+omega d (x+y-z) := by
    unfold energyDefect at he
    linarith
  have hc := congrArg (fun t : ℝ => (t : ℂ)) hreal
  simp only [Complex.ofReal_add] at hc
  change (A+B*(omega d x : ℂ))+(A+B*(omega d y : ℂ)) =
    (A+B*(omega d z : ℂ))+(A+B*(omega d (x+y-z) : ℂ))
  calc
    _ = 2*A+B*((omega d x : ℂ)+(omega d y : ℂ)) := by ring
    _ = 2*A+B*((omega d z : ℂ)+(omega d (x+y-z) : ℂ)) := by rw [hc]
    _ = _ := by ring

end
end Resonance.PinnedEndToEnd
