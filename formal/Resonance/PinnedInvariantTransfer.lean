import Resonance.PinnedMeasurable
import Resonance.PinnedClassification
import Resonance.PinnedGlobalRegularity

/-! Transfer through a chart based at an arbitrary specified original
three-source nondegenerate quartet. No Borel assumption on the two a.e.-equal
representatives is needed for the slice transfer. -/
open Real MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
namespace Resonance.PinnedInvariantTransfer
open PinnedGeometry PinnedCharts PinnedMeasure PinnedMeasurable
noncomputable section

theorem specified_uniform_chart {d x y z : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (he : energyDefect d x y z=0)
    (hyz : velocity d y≠velocity d z) (hyw : velocity d y≠velocity d (x+y-z))
    (hzw : velocity d z≠velocity d (x+y-z)) :
    ∃H : ℝ×ℝ→ℝ, ∃r κ:ℝ, 0<r ∧ 0<κ ∧ H (x,z)=y ∧
      ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r) ∧
      ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
        energyDefect d p.1 (H p) p.2=0 ∧
        κ≤|velocity d (H p)-velocity d (p.1+H p-p.2)| ∧
        κ≤|zDifferential H p| ∧ κ≤|zDifferential H p-1| := by
  have hdL : -(1/2:ℝ)<d := by linarith
  obtain ⟨H,hbase,hH,hres⟩ := exists_analytic_resonance_branch hdL hdU he hyw
  have hz := branch_z_derivative hdL hdU hbase hH hres hyw
  have hdz := zDifferential_eq_deriv (hH.differentiableAt (by simp))
  have hz0 : zDifferential H (x,z)≠0 := by
    rw [hdz,hz]
    exact div_ne_zero (sub_ne_zero.mpr hzw) (sub_ne_zero.mpr hyw)
  have hw0 : zDifferential H (x,z)-1≠0 := by
    intro hh
    have hone : deriv (fun t=>H (x,t)) z=1 := by rw [←hdz]; linarith
    rw [hz] at hone
    have heq := (div_eq_one_iff_eq (sub_ne_zero.mpr hyw)).mp hone
    apply hyz
    linarith only [heq]
  let g : ℝ×ℝ→ℝ := fun p=>velocity d (H p)-velocity d (p.1+H p-p.2)
  have hgc : ContinuousAt g (x,z) := by
    exact ((velocity_continuous hdL hdU).continuousAt.comp hH.continuousAt).sub
      ((velocity_continuous hdL hdU).continuousAt.comp
        ((continuousAt_fst.add hH.continuousAt).sub continuousAt_snd))
  have hg0 : g (x,z)≠0 := by
    dsimp [g]
    rw [hbase]
    exact sub_ne_zero.mpr hyw
  have hzc := zDifferential_continuousAt hH
  have hwc : ContinuousAt (fun p=>zDifferential H p-1) (x,z) := hzc.sub continuousAt_const
  let κ := min (|g (x,z)|/2) (min (|zDifferential H (x,z)|/2) (|zDifferential H (x,z)-1|/2))
  have hk : 0<κ := lt_min (half_pos (abs_pos.mpr hg0))
    (lt_min (half_pos (abs_pos.mpr hz0)) (half_pos (abs_pos.mpr hw0)))
  have hev : ∀ᶠ p in 𝓝 (x,z), ContDiffAt ℝ ω H p ∧ energyDefect d p.1 (H p) p.2=0 ∧
      κ≤|g p| ∧ κ≤|zDifferential H p| ∧ κ≤|zDifferential H p-1| := by
    filter_upwards [hH.eventually (by simp),hres,eventually_abs_lower hgc hg0,
      eventually_abs_lower hzc hz0,eventually_abs_lower hwc hw0] with p hHp hr hg hz' hw'
    exact ⟨hHp,hr,(min_le_left _ _).trans hg.le,
      ((min_le_right _ _).trans (min_le_left _ _)).trans hz'.le,
      ((min_le_right _ _).trans (min_le_right _ _)).trans hw'.le⟩
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨H,r,κ,hr,hk,hbase,?_,?_⟩
  · intro p hp
    have hb : p∈Metric.ball (x,z) r := by simpa only [←ball_prod_same] using hp
    exact ((hsub hb).1.of_le (show (∞ : WithTop ℕ∞)≤ω by simp)).contDiffWithinAt
  · intro p hp
    have hb : p∈Metric.ball (x,z) r := by simpa only [←ball_prod_same] using hp
    exact (hsub hb).2

theorem ae_comp_of_map_domination {E : Type*} {f g : ℝ→E}
    (hfg : f =ᵐ[volume] g) {ζ : Measure ℝ} {T : ℝ→ℝ} (hT : AEMeasurable T ζ)
    {C : ℝ≥0∞} (hdom : ζ.map T≤C • (volume : Measure ℝ)) :
    (fun t=>f (T t)) =ᵐ[ζ] (fun t=>g (T t)) := by
  have hac : ζ.map T≪(volume : Measure ℝ) := by
    intro S hS
    exact le_antisymm ((hdom S).trans_eq (by simp [Measure.smul_apply,hS])) bot_le
  exact ae_eq_comp' hT hfg hac

/-- Simultaneous equality on all three source legs for every allowed target
section; the representatives themselves can be arbitrary functions. -/
theorem chart_source_ae_congr {E : Type*} {f g : ℝ→E}
    (hfg : f =ᵐ[volume] g) {H : ℝ×ℝ→ℝ} {x z r κ : ℝ} (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|zDifferential H p| ∧ κ≤|zDifferential H p-1|)
    (a : ℝ) (ha : a∈Metric.ball x r) (i : Fin 3) :
    (fun t=>f (sourceLeg H i a t)) =ᵐ[volume.restrict (Metric.ball z r)]
      (fun t=>g (sourceLeg H i a t)) := by
  have hm := chart_source_measurable H x z r hs a ha i
  apply ae_comp_of_map_domination hfg hm
  exact map_domination_of_lower_jacobian _ _ hm (min κ 1) (lt_min hκ zero_lt_one)
    (chart_source_jacobian H x z r κ hκ hs hb a ha i)

/-- Nested a.e. form of the complete chart relation. No converse of Fubini
for a nonmeasurable predicate is invoked. -/
theorem chart_relation_ae_congr {f g : ℝ→ℂ} (hfg : f =ᵐ[volume] g)
    {H : ℝ×ℝ→ℝ} {x z r κ : ℝ} (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|zDifferential H p| ∧ κ≤|zDifferential H p-1|)
    (hi : ∀ᵐ p ∂volume.restrict (Metric.ball x r ×ˢ Metric.ball z r),
      f p.1+f (H p)=f p.2+f (p.1+H p-p.2)) :
    ∀ᵐ a ∂volume.restrict (Metric.ball x r),
      ∀ᵐ t ∂volume.restrict (Metric.ball z r),
        g a+g (H (a,t))=g t+g (a+H (a,t)-t) := by
  have hip : ∀ᵐ p ∂(volume.restrict (Metric.ball x r)).prod (volume.restrict (Metric.ball z r)),
      f p.1+f (H p)=f p.2+f (p.1+H p-p.2) := by
    rwa [Measure.prod_restrict,←Measure.volume_eq_prod]
  have hi' := Measure.ae_ae_of_ae_prod hip
  filter_upwards [hi',ae_restrict_of_ae hfg,ae_restrict_mem Metric.isOpen_ball.measurableSet]
    with a hai hfa ha
  have h0 := chart_source_ae_congr hfg hκ hs hb a ha 0
  have h1 := chart_source_ae_congr hfg hκ hs hb a ha 1
  have h2 := chart_source_ae_congr hfg hκ hs hb a ha 2
  filter_upwards [hai,h0,h1,h2] with t hit ht0 ht1 ht2
  change f t=g t at ht0
  change f (a+H (a,t)-t)=g (a+H (a,t)-t) at ht1
  change f (H (a,t))=g (H (a,t)) at ht2
  simpa only [hfa,ht0,ht1,ht2] using hit

theorem continuous_chart_relation_of_ae {g : ℝ→ℂ} (hg : Continuous g)
    {H : ℝ×ℝ→ℝ} {x z r : ℝ}
    (hs : ContinuousOn H (Metric.ball x r ×ˢ Metric.ball z r))
    (hi : ∀ᵐ a ∂volume.restrict (Metric.ball x r),
      ∀ᵐ t ∂volume.restrict (Metric.ball z r),
        g a+g (H (a,t))=g t+g (a+H (a,t)-t)) :
    ∀a∈Metric.ball x r, ∀t∈Metric.ball z r,
      g a+g (H (a,t))=g t+g (a+H (a,t)-t) := by
  have hsections : ∀ᵐ a ∂volume.restrict (Metric.ball x r),
      ∀t∈Metric.ball z r, g a+g (H (a,t))=g t+g (a+H (a,t)-t) := by
    filter_upwards [hi,ae_restrict_mem Metric.isOpen_ball.measurableSet] with a hai ha
    have hH : ContinuousOn (fun t=>H (a,t)) (Metric.ball z r) :=
      hs.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht=>⟨ha,ht⟩)
    apply Measure.eqOn_open_of_ae_eq hai Metric.isOpen_ball
    · exact continuousOn_const.add (hg.comp_continuousOn hH)
    · exact hg.continuousOn.add (hg.comp_continuousOn
        ((continuousOn_const.add hH).sub continuousOn_id))
  intro a ha t ht
  have hsection : ∀ᵐ b ∂volume.restrict (Metric.ball x r),
      g b+g (H (b,t))=g t+g (b+H (b,t)-t) := hsections.mono (fun b hb=>hb t ht)
  have hH : ContinuousOn (fun b=>H (b,t)) (Metric.ball x r) :=
    hs.comp (continuous_id.prodMk continuous_const).continuousOn (fun b hb=>⟨hb,ht⟩)
  have heq := Measure.eqOn_open_of_ae_eq hsection Metric.isOpen_ball
    (hg.continuousOn.add (hg.comp_continuousOn hH))
    (continuousOn_const.add (hg.comp_continuousOn ((continuousOn_id.add hH).sub continuousOn_const)))
  exact heq ha

/-- A continuous representative inherits every original three-source
nondegenerate quartet relation. The quartet is specified, not selected after
the representative or the target point. -/
theorem liftedInvariant_continuous_representative {d : ℝ} {f g : ℝ→ℂ}
    (hd0 : 0<d) (hdU : d<1/2) (hi : liftedInvariant d f)
    (hfg : f =ᵐ[volume] g) (hg : Continuous g) :
    PinnedClassification.complexSmoothInvariant d g := by
  intro x y z he hyz hyw hzw
  obtain ⟨H,r,κ,hr,hκ,hbase,hs,hdata⟩ := specified_uniform_chart hd0 hdU he hyz hyw hzw
  have hif := graph_invariant_ae hd0 hdU hi H
    (Metric.isOpen_ball.prod Metric.isOpen_ball).measurableSet (fun p hp=>by
      obtain ⟨he,hgap,_⟩ := hdata p hp
      apply graph_regular he
      intro hz
      rw [hz,sub_self,abs_zero] at hgap
      linarith)
  have hig := chart_relation_ae_congr hfg hκ hs (fun p hp=>(hdata p hp).2.2) hif
  have hall := continuous_chart_relation_of_ae hg hs.continuousOn hig
  have h := hall x (Metric.mem_ball_self hr) z (Metric.mem_ball_self hr)
  simpa only [hbase] using h

theorem circleInvariant_continuous_representative {d : ℝ}
    {φ : PinnedPeriodicity.Circle→ℂ} {g : ℝ→ℂ}
    (hd0 : 0<d) (hdU : d<1/2) (hi : PinnedPeriodicity.circleInvariant d φ)
    (hfg : PinnedPeriodicity.periodicLift φ =ᵐ[volume] g) (hg : Continuous g) :
    PinnedClassification.complexSmoothInvariant d g := by
  exact liftedInvariant_continuous_representative hd0 hdU
    (PinnedPeriodicity.circleInvariant_lifted hd0 hdU hi) hfg hg

theorem circleInvariant_classification_of_smooth_representative {d : ℝ}
    {φ : PinnedPeriodicity.Circle→ℂ} {g : ℝ→ℂ}
    (hd0 : 0<d) (hdU : d<1/2) (hi : PinnedPeriodicity.circleInvariant d φ)
    (hfg : PinnedPeriodicity.periodicLift φ =ᵐ[volume] g)
    (hg : ContDiff ℝ 3 g) (hp : Function.Periodic g (2*Real.pi)) :
    ∃A B:ℂ, PinnedPeriodicity.periodicLift φ =ᵐ[volume]
      (fun x=>A+B*(omega d x:ℂ)) := by
  have hgi := circleInvariant_continuous_representative hd0 hdU hi hfg hg.continuous
  obtain ⟨A,B,hAB⟩ := PinnedClassification.complex_smooth_invariant_classification hd0 hdU hg hgi hp
  exact ⟨A,B,hfg.trans (Filter.Eventually.of_forall hAB)⟩

/-- The original Borel measurable circle invariant reaches the affine
dispersion classification without any assumed integrability, boundedness,
smooth representative, chart identity, or differential equation. -/
theorem measurable_circleInvariant_classification {d : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (φ : PinnedPeriodicity.Circle→ℂ)
    (hφ : Measurable φ) (hi : PinnedPeriodicity.circleInvariant d φ) :
    ∃A B:ℂ, PinnedPeriodicity.periodicLift φ =ᵐ[volume]
      (fun x=>A+B*(omega d x:ℂ)) := by
  obtain ⟨g,hg,hfg,hp⟩ := PinnedGlobalRegularity.circleInvariant_smooth_periodic_representative
    hd0 hdU φ hφ hi
  exact circleInvariant_classification_of_smooth_representative hd0 hdU hi hfg
    (hg.of_le (WithTop.coe_le_coe.mpr (show (3:ℕ∞)≤⊤ from le_top))) hp

end
end Resonance.PinnedInvariantTransfer
