import Resonance.PinnedLocalSmooth

/-! Smooth representatives of the original measurable resonance invariant.
All local identities use the same function on its four momentum legs. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedRepresentatives
noncomputable section
open Resonance.PinnedSmoothing Resonance.PinnedLocalSmooth
open Resonance.PinnedMeasurable

theorem chart_smooth_representative
    {H : ℝ × ℝ → ℝ} {x z r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r,
      κ ≤ |partialZ H p| ∧ κ ≤ |partialZ H p - 1|)
    {f : ℝ → ℂ} (hf : LocallyIntegrable f (volume : Measure ℝ))
    (hi : ∀ᵐ p ∂volume.restrict (Metric.ball x r ×ˢ Metric.ball z r),
      f p.1 + f (H p) = f p.2 + f (p.1 + H p - p.2)) :
    ∃ F : ℝ → ℂ, ContDiffOn ℝ ∞ F (Metric.ball x (r/4)) ∧
      f =ᵐ[volume.restrict (Metric.ball x (r/4))] F := by
  let O := Metric.ball x r ×ˢ Metric.ball z r
  let W : ℝ × ℝ → ℝ := fun p => p.1 + H p - p.2
  have hWs : ContDiffOn ℝ ∞ W O := (contDiffOn_fst.add hs).sub contDiffOn_snd
  have hwz (p : ℝ × ℝ) (hp : p ∈ O) : partialZ W p = partialZ H p - 1 := by
    have hdH := ((hs.differentiableOn (by simp)) p hp).differentiableAt
      ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hp)
    have hdW := ((hWs.differentiableOn (by simp)) p hp).differentiableAt
      ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hp)
    have he := ((partialZ_hasDerivAt hdH).const_add p.1).sub (hasDerivAt_id p.2)
    exact (partialZ_hasDerivAt hdW).unique he
  have hWb : ∀ p ∈ O, κ ≤ |partialZ W p| := by
    intro p hp
    rw [hwz p hp]
    exact (hb p hp).2
  obtain ⟨ρ,hρ,hρcomp,hρsupp,hρmass⟩ := exists_normalized_source_bump (z:=z) hr
  let D := Icc (z-r/4) (z+r/4)
  let I := Metric.ball x (r/4)
  let A₀ : ℂ := ∫ t in D, ρ t • f t
  let A₁ : ℝ → ℂ := fun a => ∫ t in D, ρ t • f (W (a,t))
  let A₂ : ℝ → ℂ := fun a => ∫ t in D, ρ t • f (H (a,t))
  let F : ℝ → ℂ := fun a => A₀ + A₁ a - A₂ a
  have hA₁ : ContDiffOn ℝ ∞ A₁ I := bump_average_contDiffOn hr hκ hWs hWb hρ hρsupp hf
  have hA₂ : ContDiffOn ℝ ∞ A₂ I := bump_average_contDiffOn hr hκ hs
    (fun p hp => (hb p hp).1) hρ hρsupp hf
  refine ⟨F,(contDiffOn_const.add hA₁).sub hA₂,?_⟩
  have hIr : I ⊆ Metric.ball x r := Metric.ball_subset_ball (by linarith)
  have hDr : D ⊆ Metric.ball z r := by
    dsimp [D]
    rw [← Real.closedBall_eq_Icc]
    exact Metric.closedBall_subset_ball (by linarith)
  have hip : ∀ᵐ p ∂(volume.restrict I).prod (volume.restrict D),
      f p.1 + f (H p) = f p.2 + f (W p) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact hi.filter_mono (ae_mono (Measure.restrict_mono (Set.prod_mono hIr hDr) le_rfl))
  have his := Measure.ae_ae_of_ae_prod hip
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hρ.continuous.continuousOn
  have hi₀ : IntegrableOn (fun t => ρ t • f t) D :=
    (hf.integrableOn_isCompact isCompact_Icc).bdd_smul B hρ.continuous.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hB t ht))
  filter_upwards [his,ae_restrict_mem Metric.isOpen_ball.measurableSet] with a ha hIa
  have hi₁ : IntegrableOn (fun t => ρ t • f (W (a,t))) D :=
    chart_weighted_source_integrable hr hκ hWs hWb hρ.continuous hf hIa
  have hi₂ : IntegrableOn (fun t => ρ t • f (H (a,t))) D :=
    chart_weighted_source_integrable hr hκ hs (fun p hp => (hb p hp).1) hρ.continuous hf hIa
  have hae : (fun t => ρ t • f a) =ᵐ[volume.restrict D]
      (fun t => ρ t • f t + ρ t • f (W (a,t)) - ρ t • f (H (a,t))) := by
    filter_upwards [ha] with t ht
    have he : f a = f t + f (W (a,t)) - f (H (a,t)) := eq_sub_of_add_eq ht
    rw [he]
    simp only [Complex.real_smul]
    ring
  calc
    f a = ∫ t in D, ρ t • f a := by
      have he := integral_smul_const (𝕜:=ℝ) (μ:=volume.restrict D) ρ (f a)
      rw [hρmass] at he
      simpa only [one_smul] using he.symm
    _ = ∫ t in D, (ρ t • f t + ρ t • f (W (a,t)) - ρ t • f (H (a,t))) :=
      integral_congr_ae hae
    _ = (∫ t in D, ρ t • f t + ρ t • f (W (a,t))) - A₂ a :=
      integral_sub (hi₀.add hi₁) hi₂
    _ = F a := congrArg (fun q : ℂ => q-A₂ a) (integral_add hi₀ hi₁)

theorem liftedInvariant_local_smooth_representative {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (f : ℝ → ℂ) (hf : Measurable f) (hi : PinnedMeasure.liftedInvariant d f) (x : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℝ → ℂ, ContDiffOn ℝ ∞ F (Metric.ball x r) ∧
      f =ᵐ[volume.restrict (Metric.ball x r)] F := by
  obtain ⟨_y,z,H,r,κ,hr,hκ,_hy,hs,hb,hrel⟩ :=
    PinnedMeasure.every_target_invariant_chart hd0 hdU hi x
  obtain ⟨F,hFs,hF⟩ := chart_smooth_representative hr hκ hs
    (fun p hp => ⟨(hb p hp).2.2.1,(hb p hp).2.2.2⟩)
    (liftedInvariant_locallyIntegrable hd0 hdU f hf hi) hrel
  exact ⟨r/4,by positivity,F,hFs,hF⟩

end
end Resonance.PinnedRepresentatives
