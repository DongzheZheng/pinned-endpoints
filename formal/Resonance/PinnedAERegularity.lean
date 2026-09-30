import Resonance.PinnedCircleAE
import Resonance.PinnedInvariantTransfer

/-! Completed-measure invariants.  Only the Borel representative's relation
on each good chart is needed; invariance of that representative on the
whole regular coarea is not assumed or inferred. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedAERegularity
noncomputable section
open Resonance.PinnedMeasurable Resonance.PinnedRepresentatives
open Resonance.PinnedGlobalRegularity Resonance.PinnedInvariantTransfer

theorem measurable_chart_relation_joint {g : ℝ → ℂ} (hg : Measurable g)
    {H : ℝ × ℝ → ℝ} {x z r : ℝ}
    (hs : ContinuousOn H (Metric.ball x r ×ˢ Metric.ball z r))
    (hi : ∀ᵐ a ∂volume.restrict (Metric.ball x r),
      ∀ᵐ t ∂volume.restrict (Metric.ball z r),
        g a + g (H (a,t)) = g t + g (a+H (a,t)-t)) :
    ∀ᵐ p ∂volume.restrict (Metric.ball x r ×ˢ Metric.ball z r),
      g p.1 + g (H p) = g p.2 + g (p.1+H p-p.2) := by
  classical
  let O := Metric.ball x r ×ˢ Metric.ball z r
  have hO : MeasurableSet O := (Metric.isOpen_ball.prod Metric.isOpen_ball).measurableSet
  let H₀ : ℝ × ℝ → ℝ := O.piecewise H (fun _ => 0)
  have hH₀ : Measurable H₀ := hs.measurable_piecewise continuous_const.continuousOn hO
  have heq (p : ℝ × ℝ) (hp : p ∈ O) : H₀ p = H p := by simp [H₀,hp]
  have hrel : MeasurableSet {p : ℝ × ℝ |
      g p.1 + g (H₀ p) = g p.2 + g (p.1+H₀ p-p.2)} := by
    apply measurableSet_eq_fun
    · exact (hg.comp measurable_fst).add (hg.comp hH₀)
    · exact (hg.comp measurable_snd).add
        (hg.comp ((measurable_fst.add hH₀).sub measurable_snd))
  have hiter : ∀ᵐ a ∂volume.restrict (Metric.ball x r),
      ∀ᵐ t ∂volume.restrict (Metric.ball z r),
        g a + g (H₀ (a,t)) = g t + g (a+H₀ (a,t)-t) := by
    filter_upwards [hi,ae_restrict_mem Metric.isOpen_ball.measurableSet] with a hai ha
    filter_upwards [hai,ae_restrict_mem Metric.isOpen_ball.measurableSet] with t hit ht
    simpa only [heq (a,t) ⟨ha,ht⟩] using hit
  have hj : ∀ᵐ p ∂(volume.restrict (Metric.ball x r)).prod
      (volume.restrict (Metric.ball z r)),
      g p.1 + g (H₀ p) = g p.2 + g (p.1+H₀ p-p.2) :=
    (Measure.ae_prod_iff_ae_ae hrel).mpr hiter
  rw [Measure.prod_restrict,← Measure.volume_eq_prod] at hj
  filter_upwards [hj,ae_restrict_mem hO] with p hp hOp
  simpa only [heq p hOp] using hp

theorem liftedInvariant_AE_smooth_representative {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (f : ℝ → ℂ) (hf : AEMeasurable f (volume : Measure ℝ))
    (hi : PinnedMeasure.liftedInvariant d f) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ f =ᵐ[volume] g := by
  let f₀ := hf.mk f
  have hm : Measurable f₀ := hf.measurable_mk
  have he : f =ᵐ[volume] f₀ := hf.ae_eq_mk
  have hcharts (x : ℝ) : ∃ z : ℝ, ∃ H : ℝ × ℝ → ℝ, ∃ r κ : ℝ,
      0 < r ∧ 0 < κ ∧
      ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r) ∧
      (∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r,
        κ ≤ |PinnedCharts.zDifferential H p| ∧ κ ≤ |PinnedCharts.zDifferential H p-1|) ∧
      (∀ᵐ p ∂volume.restrict (Metric.ball x r ×ˢ Metric.ball z r),
        f₀ p.1 + f₀ (H p) = f₀ p.2 + f₀ (p.1+H p-p.2)) := by
    obtain ⟨_y,z,H,r,κ,hr,hκ,_hy,hs,hb,hrel⟩ :=
      PinnedMeasure.every_target_invariant_chart hd0 hdU hi x
    have hb' := fun p hp => (hb p hp).2.2
    exact ⟨z,H,r,κ,hr,hκ,hs,hb',measurable_chart_relation_joint hm hs.continuousOn
      (chart_relation_ae_congr he hκ hs hb' hrel)⟩
  have hfi : LocallyIntegrable f₀ (volume : Measure ℝ) := by
    apply locallyIntegrable_of_local_essential_bound f₀ hm
    intro x
    obtain ⟨z,H,r,κ,hr,hκ,hs,hb,hrel⟩ := hcharts x
    obtain ⟨M,hM,hbound⟩ := invariant_chart_essential_bound H x z r κ hr hκ hs hb f₀ hm hrel
    exact ⟨r/2,M,half_pos hr,hM,hbound⟩
  obtain ⟨g,hgs,hge⟩ := smooth_representative_of_local (f:=f₀) (fun x => by
    obtain ⟨z,H,r,κ,hr,hκ,hs,hb,hrel⟩ := hcharts x
    obtain ⟨F,hFs,hFe⟩ := chart_smooth_representative hr hκ hs hb hfi hrel
    exact ⟨r/4,by positivity,F,hFs,hFe⟩)
  exact ⟨g,hgs,he.trans hge⟩

theorem circleInvariant_AE_smooth_periodic_representative {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : PinnedPeriodicity.Circle → ℂ)
    (hφ : AEMeasurable φ PinnedCircleAE.circleVolume)
    (hi : PinnedPeriodicity.circleInvariant d φ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧
      PinnedPeriodicity.periodicLift φ =ᵐ[volume] g ∧
      Function.Periodic g (2*Real.pi) := by
  obtain ⟨g,hgs,hge⟩ := liftedInvariant_AE_smooth_representative hd0 hdU
    (PinnedPeriodicity.periodicLift φ) (PinnedCircleAE.circle_aemeasurable_lift hφ)
    (PinnedPeriodicity.circleInvariant_lifted hd0 hdU hi)
  exact ⟨g,hgs,hge,periodic_of_ae_periodic (PinnedPeriodicity.periodicLift_periodic φ)
    hgs.continuous hge⟩

end
end Resonance.PinnedAERegularity
