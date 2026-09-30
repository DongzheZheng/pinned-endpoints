import Resonance.PinnedRepresentatives

/-! Gluing the actual local representatives.  Compatibility follows from
equality to the same measurable source on every overlap. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedGlobalRegularity
noncomputable section
open Resonance.PinnedRepresentatives

theorem smooth_representative_of_local {f : ℝ → ℂ}
    (hloc : ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ F : ℝ → ℂ,
      ContDiffOn ℝ ∞ F (Metric.ball x r) ∧
      f =ᵐ[volume.restrict (Metric.ball x r)] F) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ f =ᵐ[volume] g := by
  choose r hr F hFs hFe using hloc
  have hcompat (x y p : ℝ) (hpx : p ∈ Metric.ball x (r x))
      (hpy : p ∈ Metric.ball y (r y)) : F x p = F y p := by
    let I := Metric.ball x (r x) ∩ Metric.ball y (r y)
    have hxe : f =ᵐ[volume.restrict I] F x :=
      (hFe x).filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
    have hye : f =ᵐ[volume.restrict I] F y :=
      (hFe y).filter_mono (ae_mono (Measure.restrict_mono inter_subset_right le_rfl))
    exact Measure.eqOn_open_of_ae_eq (hxe.symm.trans hye)
      (Metric.isOpen_ball.inter Metric.isOpen_ball)
      ((hFs x).continuousOn.mono inter_subset_left)
      ((hFs y).continuousOn.mono inter_subset_right) ⟨hpx,hpy⟩
  let g : ℝ → ℂ := fun x => F x x
  have heq (x : ℝ) : EqOn g (F x) (Metric.ball x (r x)) := by
    intro y hy
    exact hcompat y x y (Metric.mem_ball_self (hr y)) hy
  have hgs : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    apply ((hFs x).contDiffAt (Metric.ball_mem_nhds x (hr x))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds x (hr x)] with y hy
    exact heq x hy
  refine ⟨g,hgs,?_⟩
  change ∀ᵐ x ∂volume, f x = g x
  rw [ae_iff]
  let S := {x | f x ≠ g x}
  change volume S = 0
  apply measure_null_of_locally_null S
  intro x _hx
  have hae : f =ᵐ[volume.restrict (Metric.ball x (r x))] g := by
    filter_upwards [hFe x,ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hIy
    exact hy.trans (heq x hIy).symm
  have hz : volume (S ∩ Metric.ball x (r x)) = 0 := by
    change ∀ᵐ y ∂volume.restrict (Metric.ball x (r x)), f y = g y at hae
    rw [ae_iff,Measure.restrict_apply' Metric.isOpen_ball.measurableSet] at hae
    exact hae
  refine ⟨S ∩ Metric.ball x (r x),?_,hz⟩
  exact inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (hr x)))

theorem periodic_of_ae_periodic {f g : ℝ → ℂ} {T : ℝ}
    (hf : Function.Periodic f T) (hg : Continuous g) (he : f =ᵐ[volume] g) :
    Function.Periodic g T := by
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) T).quasiMeasurePreserving.ae_eq he
  have hae : (fun x => g (x+T)) =ᵐ[volume] g := by
    filter_upwards [he,hshift] with x hx hs
    exact hs.symm.trans ((hf x).trans hx)
  have hpoint := Measure.eq_of_ae_eq hae (hg.comp (continuous_id.add continuous_const)) hg
  intro x
  exact congrFun hpoint x

theorem liftedInvariant_smooth_representative {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (f : ℝ → ℂ) (hf : Measurable f) (hi : PinnedMeasure.liftedInvariant d f) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ f =ᵐ[volume] g :=
  smooth_representative_of_local (liftedInvariant_local_smooth_representative hd0 hdU f hf hi)

theorem circleInvariant_smooth_periodic_representative {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : PinnedPeriodicity.Circle → ℂ) (hφ : Measurable φ)
    (hi : PinnedPeriodicity.circleInvariant d φ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧
      PinnedPeriodicity.periodicLift φ =ᵐ[volume] g ∧
      Function.Periodic g (2*Real.pi) := by
  let f := PinnedPeriodicity.periodicLift φ
  have hf : Measurable f := hφ.comp
    (AddCircle.continuous_mk' PinnedPeriodicity.period).measurable
  obtain ⟨g,hgs,hge⟩ := liftedInvariant_smooth_representative hd0 hdU f hf
    (PinnedPeriodicity.circleInvariant_lifted hd0 hdU hi)
  refine ⟨g,hgs,hge,periodic_of_ae_periodic ?_ hgs.continuous hge⟩
  exact PinnedPeriodicity.periodicLift_periodic φ

end
end Resonance.PinnedGlobalRegularity
