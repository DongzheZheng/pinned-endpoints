import Resonance.PinnedAveraging

/-! Actual local smoothing, using the original resonance source maps. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedLocalSmooth
noncomputable section
open Resonance.PinnedSmoothing Resonance.PinnedAveraging
open Resonance.PinnedMeasurable

theorem compact_chart_source_data {H : ℝ × ℝ → ℝ} {x z r κ : ℝ}
    (hr : 0 < r) (hκ : 0 < κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r, κ ≤ |partialZ H p|) :
    ∃ L : ℝ, 0 < L ∧ ∀ a ∈ Metric.ball x (r/4),
      AEMeasurable (fun t => H (a,t))
        (volume.restrict (Icc (z-r/4) (z+r/4))) ∧
      (volume.restrict (Icc (z-r/4) (z+r/4))).map (fun t => H (a,t)) ≤
        (ENNReal.ofReal κ)⁻¹ • volume.restrict (Icc (-L) L) := by
  let J := Metric.ball z (r/2)
  let D := Icc (z-r/4) (z+r/4)
  have hD : D ⊆ J := by
    dsimp [D,J]
    rw [← Real.closedBall_eq_Icc]
    exact Metric.closedBall_subset_ball (by linarith)
  have hJ : J ⊆ Metric.ball z r := Metric.ball_subset_ball (by linarith)
  let K := Metric.closedBall x (r/2) ×ˢ Metric.closedBall z (r/2)
  have hK : IsCompact K := (isCompact_closedBall x (r/2)).prod (isCompact_closedBall z (r/2))
  have hKs : K ⊆ Metric.ball x r ×ˢ Metric.ball z r :=
    Set.prod_mono (Metric.closedBall_subset_ball (by linarith))
      (Metric.closedBall_subset_ball (by linarith))
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (hs.continuousOn.mono hKs)
  let L := max B 1
  refine ⟨L,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro a ha
  have ha' : a ∈ Metric.ball x r :=
    Metric.ball_subset_ball (by linarith : r/4 ≤ r) ha
  have hds (t : ℝ) (ht : t ∈ J) :
      HasDerivAt (fun v => H (a,v)) (partialZ H (a,t)) t := by
    apply partialZ_hasDerivAt
    exact ((hs.differentiableOn (by simp)) (a,t) ⟨ha',hJ ht⟩).differentiableAt
      ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds ⟨ha',hJ ht⟩)
  have hd : DifferentiableOn ℝ (fun t => H (a,t)) J :=
    fun t ht => (hds t ht).differentiableAt.differentiableWithinAt
  have hm : AEMeasurable (fun t => H (a,t)) (volume.restrict D) :=
    (hd.continuousOn.mono hD).aemeasurable measurableSet_Icc
  refine ⟨hm,?_⟩
  refine map_domination_restrict_range (volume.restrict D) (fun t => H (a,t)) hm
    ((ENNReal.ofReal κ)⁻¹) ?_ (Icc (-L) L) measurableSet_Icc ?_
  · apply map_domination_of_lower_jacobian (volume.restrict D) (fun t => H (a,t)) hm κ hκ
    intro E hE
    have hj := PinnedJacobian.preimage_measure_lower_jacobian Metric.isOpen_ball
      (convex_ball z (r/2)) hd.continuousOn hd hκ
      (fun t ht => by rw [(hds t ht).deriv]; exact hb (a,t) ⟨ha',hJ ht⟩) hE
    apply le_trans _ hj
    exact mul_le_mul_right ((Measure.restrict_mono hD le_rfl) _) _
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply abs_le.mp
    have hak : a ∈ Metric.closedBall x (r/2) := Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by linarith : r/4 ≤ r/2) ha)
    have htk : t ∈ Metric.closedBall z (r/2) := Metric.ball_subset_closedBall (hD ht)
    exact (hB (a,t) ⟨hak,htk⟩).trans (le_max_left _ _)

/-- Every locally integrable source becomes smooth after averaging on one
of the genuine uniformly nondegenerate source legs. -/
theorem bump_average_contDiffOn {H : ℝ × ℝ → ℝ} {x z r κ : ℝ}
    (hr : 0 < r) (hκ : 0 < κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r, κ ≤ |partialZ H p|)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρsupp : tsupport ρ ⊆ Metric.ball z (r/8))
    {f : ℝ → ℂ} (hf : LocallyIntegrable f (volume : Measure ℝ)) :
    ContDiffOn ℝ ∞
      (fun a => ∫ t in Icc (z-r/4) (z+r/4), ρ t • f (H (a,t)))
      (Metric.ball x (r/4)) := by
  obtain ⟨L,hL,hdata⟩ := compact_chart_source_data hr hκ hs hb
  let ν : Measure ℝ := volume.restrict (Icc (-L) L)
  have hfi : Integrable f ν := hf.integrableOn_isCompact isCompact_Icc
  have hsub : Icc (z-r/4) (z+r/4) ⊆ Metric.ball z (r/2) := by
    rw [← Real.closedBall_eq_Icc]
    exact Metric.closedBall_subset_ball (by linarith)
  have ha : z-r/4 ∉ tsupport ρ := by
    intro h
    have hh := hρsupp h
    rw [Metric.mem_ball, Real.dist_eq,
      show z-r/4-z = -(r/4) by ring, abs_neg, abs_of_pos (by positivity)] at hh
    linarith
  have hb' : z+r/4 ∉ tsupport ρ := by
    intro h
    have hh := hρsupp h
    rw [Metric.mem_ball, Real.dist_eq,
      show z+r/4-z = r/4 by ring, abs_of_pos (by positivity)] at hh
    linarith
  have hhalf : Metric.ball x (r/2) ×ˢ Metric.ball z (r/2) ⊆
      Metric.ball x r ×ˢ Metric.ball z r :=
    Set.prod_mono (Metric.ball_subset_ball (by linarith))
      (Metric.ball_subset_ball (by linarith))
  apply actual_L1_average_contDiffOn Metric.isOpen_ball Metric.isOpen_ball Metric.isOpen_ball
    (isCompact_closedBall x (r/4)) Metric.ball_subset_closedBall
    (Metric.closedBall_subset_ball (by linarith))
    (by linarith : z-r/4 ≤ z+r/4) hsub
    (isClosed_tsupport ρ).isOpen_compl ha hb' (hs.mono hhalf)
    (hρ.comp contDiff_snd).contDiffOn
    (fun p hp => abs_pos.mp (lt_of_lt_of_le hκ (hb p (hhalf hp))))
    (fun p hp => by
      change ρ p.2 = 0
      exact image_eq_zero_of_notMem_tsupport hp.2)
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hκ)))
    (fun a ha => (hdata a ha).1) (fun a ha => (hdata a ha).2) hfi

/-- Integrability in the same source variable, before applying the
functional identity or splitting its four terms. -/
theorem chart_weighted_source_integrable {H : ℝ × ℝ → ℝ} {x z r κ : ℝ}
    (hr : 0 < r) (hκ : 0 < κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r, κ ≤ |partialZ H p|)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    {f : ℝ → ℂ} (hf : LocallyIntegrable f (volume : Measure ℝ))
    {a : ℝ} (ha : a ∈ Metric.ball x (r/4)) :
    IntegrableOn (fun t => ρ t • f (H (a,t))) (Icc (z-r/4) (z+r/4)) := by
  obtain ⟨L,_hL,hdata⟩ := compact_chart_source_data hr hκ hs hb
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hρ.continuousOn
  exact weighted_comp_integrable (hdata a ha).1 (hdata a ha).2
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hκ)))
    (hf.integrableOn_isCompact isCompact_Icc) hρ.aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hB t ht))

theorem exists_normalized_source_bump {z r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Metric.ball z (r/8) ∧
      (∫ t in Icc (z-r/4) (z+r/4), ρ t) = 1 := by
  let b : ContDiffBump z :=
    { rIn := r/32
      rOut := r/16
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let ρ := b.normed (volume : Measure ℝ)
  have hs : tsupport ρ ⊆ Metric.ball z (r/8) := by
    rw [b.tsupport_normed_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  refine ⟨ρ,b.contDiff_normed,b.hasCompactSupport_normed,hs,?_⟩
  have hD : tsupport ρ ⊆ Icc (z-r/4) (z+r/4) := by
    rw [← Real.closedBall_eq_Icc]
    exact hs.trans (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith)))
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
  · exact b.integral_normed
  · exact Eventually.of_forall (fun t ht => image_eq_zero_of_notMem_tsupport
      (fun ht' => ht (hD ht')))

end
end Resonance.PinnedLocalSmooth
