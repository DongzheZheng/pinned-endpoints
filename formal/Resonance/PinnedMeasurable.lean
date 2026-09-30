import Resonance.PinnedJacobian
import Resonance.PinnedMeasure
import Resonance.PinnedPeriodicity

/-!
The finite-level-set step in measurable pinned regularity. No L¹ or local
essential bound is an input. Actual chart Jacobian estimates must provide
the displayed three pushforward measure dominations; the original invariant
identity must hold on their same source window. This module does not assume
or prove the missing periodic-lift/coarea identification.
-/
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Resonance.PinnedMeasurable

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem finite_value_levelsets_vanish {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (f : Y → E) (hf : Measurable f) :
    Tendsto (fun n : ℕ => ν {y | (n : ℝ) < ‖f y‖}) atTop (nhds 0) := by
  let s : ℕ → Set Y := fun n => {y | (n : ℝ) < ‖f y‖}
  have hs (n : ℕ) : MeasurableSet (s n) := measurableSet_lt measurable_const hf.norm
  have ha : Antitone s := by
    intro n m hnm y hy
    change (m : ℝ) < ‖f y‖ at hy
    change (n : ℝ) < ‖f y‖
    exact lt_of_le_of_lt (Nat.cast_le.mpr hnm) hy
  have he : (⋂ n, s n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨n, hn⟩ := exists_nat_gt ‖f y‖
    have hny := Set.mem_iInter.mp hy n
    exact (not_lt_of_ge hn.le) hny
  have ht := tendsto_measure_iInter_atTop (fun n => (hs n).nullMeasurableSet) ha
    ⟨0, (measure_lt_top ν (s 0)).ne⟩
  simpa only [he, measure_empty, Function.comp_def] using ht

theorem exists_common_level_bound {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (f : Y → E) (hf : Measurable f)
    (C a : ℝ≥0∞) (hC : C ≠ ⊤) (ha : 0 < a) :
    ∃ n : ℕ, (3 : ℝ≥0∞) * C * ν {y | (n : ℝ) < ‖f y‖} < a := by
  have ht := ENNReal.Tendsto.const_mul (finite_value_levelsets_vanish ν f hf)
    (a := (3 : ℝ≥0∞) * C) (Or.inr (ENNReal.mul_ne_top (by norm_num) hC))
  have he : ∀ᶠ n : ℕ in atTop,
      (3 : ℝ≥0∞) * C * ν {y | (n : ℝ) < ‖f y‖} < a := by
    apply ht.eventually
    simpa only [mul_zero] using (Iio_mem_nhds ha)
  exact he.exists

theorem three_pullbacks_point_bound {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y]
    (ζ : Measure Z) (ν : Measure Y) (f : Y → E) (hf : Measurable f)
    (T : Fin 3 → Z → Y) (hT : ∀ i, AEMeasurable (T i) ζ)
    (C : ℝ≥0∞) (hdom : ∀ i, Measure.map (T i) ζ ≤ C • ν)
    (n : ℕ) (hsmall : (3 : ℝ≥0∞) * C * ν {y | (n : ℝ) < ‖f y‖} < ζ univ)
    (a : E) (ha : ∀ᵐ z ∂ζ, a = f (T 0 z) + f (T 1 z) - f (T 2 z)) :
    ‖a‖ ≤ 3 * (n : ℝ) := by
  let S : Set Y := {y | (n : ℝ) < ‖f y‖}
  let B : Fin 3 → Set Z := fun i => T i ⁻¹' S
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf.norm
  have hb (i : Fin 3) : ζ (B i) ≤ C * ν S := by
    rw [show ζ (B i) = Measure.map (T i) ζ S from
      (Measure.map_apply_of_aemeasurable (hT i) hS).symm]
    exact hdom i S
  have hsum : ζ (B 0 ∪ B 1 ∪ B 2) ≤ (3 : ℝ≥0∞) * C * ν S := by
    calc
      ζ (B 0 ∪ B 1 ∪ B 2) ≤ ζ (B 0 ∪ B 1) + ζ (B 2) := measure_union_le _ _
      _ ≤ (ζ (B 0) + ζ (B 1)) + ζ (B 2) := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ (C * ν S + C * ν S) + C * ν S := add_le_add (add_le_add (hb 0) (hb 1)) (hb 2)
      _ = (3 : ℝ≥0∞) * C * ν S := by ring
  by_contra hn
  have hbad : ∀ᵐ z ∂ζ, z ∈ B 0 ∪ B 1 ∪ B 2 := by
    filter_upwards [ha] with z hz
    by_contra hzbad
    have h0 : ‖f (T 0 z)‖ ≤ (n : ℝ) := by
      by_contra h
      exact hzbad (Or.inl (Or.inl (lt_of_not_ge h)))
    have h1 : ‖f (T 1 z)‖ ≤ (n : ℝ) := by
      by_contra h
      exact hzbad (Or.inl (Or.inr (lt_of_not_ge h)))
    have h2 : ‖f (T 2 z)‖ ≤ (n : ℝ) := by
      by_contra h
      exact hzbad (Or.inr (lt_of_not_ge h))
    apply hn
    rw [hz]
    calc
      ‖f (T 0 z) + f (T 1 z) - f (T 2 z)‖ ≤
        ‖f (T 0 z) + f (T 1 z)‖ + ‖f (T 2 z)‖ := norm_sub_le _ _
      _ ≤ (‖f (T 0 z)‖ + ‖f (T 1 z)‖) + ‖f (T 2 z)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ 3 * (n : ℝ) := by linarith
  have he : (B 0 ∪ B 1 ∪ B 2 : Set Z) =ᵐ[ζ] (univ : Set Z) :=
    hbad.mono (fun z hz => propext ⟨fun _ => Set.mem_univ z, fun _ => hz⟩)
  have hfull := measure_congr he
  exact (not_lt_of_ge (hfull ▸ hsum)) hsmall

theorem uniform_three_pullbacks_essential_bound {X Z Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure X) (ζ : Measure Z) (ν : Measure Y) [IsFiniteMeasure ν]
    (hζ : 0 < ζ univ) (f : Y → E) (hf : Measurable f)
    (T : Fin 3 → X → Z → Y) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hdom : ∀ᵐ x ∂μ, ∀ i, AEMeasurable (T i x) ζ ∧ Measure.map (T i x) ζ ≤ C • ν)
    (F : X → E)
    (hidentity : ∀ᵐ x ∂μ, ∀ᵐ z ∂ζ,
      F x = f (T 0 x z) + f (T 1 x z) - f (T 2 x z)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, ‖F x‖ ≤ M := by
  obtain ⟨n, hn⟩ := exists_common_level_bound ν f hf C (ζ univ) hC hζ
  refine ⟨3 * (n : ℝ), by positivity, ?_⟩
  filter_upwards [hdom, hidentity] with x hx hi
  exact three_pullbacks_point_bound ζ ν f hf (fun i => T i x)
    (fun i => (hx i).1) C (fun i => (hx i).2) n hn (F x) hi

theorem product_three_pullbacks_essential_bound {X Z Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure X) (ζ : Measure Z) [SFinite ζ]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (hζ : 0 < ζ univ) (f : Y → E) (hf : Measurable f)
    (T : Fin 3 → X → Z → Y) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hdom : ∀ᵐ x ∂μ, ∀ i, AEMeasurable (T i x) ζ ∧ Measure.map (T i x) ζ ≤ C • ν)
    (F : X → E)
    (hidentity : ∀ᵐ p ∂μ.prod ζ,
      F p.1 = f (T 0 p.1 p.2) + f (T 1 p.1 p.2) - f (T 2 p.1 p.2)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, ‖F x‖ ≤ M :=
  uniform_three_pullbacks_essential_bound μ ζ ν hζ f hf T C hC hdom F
    (Measure.ae_ae_of_ae_prod hidentity)

theorem map_domination_of_lower_jacobian {Z : Type*} [MeasurableSpace Z]
    (ζ : Measure Z) (g : Z → ℝ) (hg : AEMeasurable g ζ)
    (κ : ℝ) (hκ : 0 < κ)
    (hb : ∀ S : Set ℝ, MeasurableSet S → ENNReal.ofReal κ * ζ (g ⁻¹' S) ≤ volume S) :
    Measure.map g ζ ≤ (ENNReal.ofReal κ)⁻¹ • (volume : Measure ℝ) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply_of_aemeasurable hg hS]
  change ζ (g ⁻¹' S) ≤ (ENNReal.ofReal κ)⁻¹ * volume S
  rw [mul_comm, ← div_eq_mul_inv]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hκ)))
    (Or.inl ENNReal.ofReal_ne_top)).mpr (by simpa [mul_comm] using hb S hS)

theorem map_domination_restrict_range {Z : Type*} [MeasurableSpace Z]
    (ζ : Measure Z) (g : Z → ℝ) (hg : AEMeasurable g ζ)
    (C : ℝ≥0∞) (hdom : Measure.map g ζ ≤ C • (volume : Measure ℝ))
    (J : Set ℝ) (hJ : MeasurableSet J) (himage : ∀ᵐ z ∂ζ, g z ∈ J) :
    Measure.map g ζ ≤ C • (volume.restrict J) := by
  have hm : ∀ᵐ y ∂Measure.map g ζ, y ∈ J := by
    rw [ae_iff]
    change Measure.map g ζ Jᶜ = 0
    rw [Measure.map_apply_of_aemeasurable hg hJ.compl]
    exact (ae_iff.mp himage)
  have h := Measure.restrict_mono_measure hdom J
  rw [Measure.restrict_eq_self_of_ae_mem hm, Measure.restrict_smul] at h
  exact h

def sourceLeg (H : ℝ × ℝ → ℝ) (i : Fin 3) (a t : ℝ) : ℝ :=
  ![t, a + H (a,t) - t, H (a,t)] i

theorem chart_source_compact_bound (H : ℝ × ℝ → ℝ) (x z r : ℝ) (hr : 0 < r)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r)) :
    ∃ L : ℝ, 0 < L ∧ ∀ a ∈ Metric.ball x (r/2), ∀ t ∈ Metric.ball z (r/2),
      ∀ i : Fin 3, |sourceLeg H i a t| ≤ L := by
  let K : Set (ℝ × ℝ) := Metric.closedBall x (r/2) ×ˢ Metric.closedBall z (r/2)
  have hK : IsCompact K := (isCompact_closedBall x (r/2)).prod (isCompact_closedBall z (r/2))
  have hsub : K ⊆ Metric.ball x r ×ˢ Metric.ball z r :=
    Set.prod_mono (Metric.closedBall_subset_ball (half_lt_self hr))
      (Metric.closedBall_subset_ball (half_lt_self hr))
  have hc : ContinuousOn (fun p : ℝ × ℝ => |p.1| + |p.2| + |H p|) K :=
    (continuous_fst.abs.add continuous_snd.abs).continuousOn.add
      ((hs.continuousOn.mono hsub).abs)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro a ha t ht i
  have hp : (a,t) ∈ K := ⟨Metric.ball_subset_closedBall ha, Metric.ball_subset_closedBall ht⟩
  have hb : |a| + |t| + |H (a,t)| ≤ max B 1 :=
    (le_abs_self _).trans ((hB (a,t) hp).trans (le_max_left _ _))
  fin_cases i
  · change |t| ≤ max B 1
    linarith [abs_nonneg a, abs_nonneg (H (a,t))]
  · change |a + H (a,t) - t| ≤ max B 1
    have h1 := abs_sub (a + H (a,t)) t
    have h2 := abs_add_le a (H (a,t))
    linarith
  · change |H (a,t)| ≤ max B 1
    linarith [abs_nonneg a, abs_nonneg t]

theorem chart_source_measurable (H : ℝ × ℝ → ℝ) (x z r : ℝ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (a : ℝ) (ha : a ∈ Metric.ball x r) (i : Fin 3) :
    AEMeasurable (sourceLeg H i a) (volume.restrict (Metric.ball z r)) := by
  have hc : ContinuousOn (fun t => H (a,t)) (Metric.ball z r) :=
    hs.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨ha,ht⟩)
  fin_cases i
  · exact measurable_id.aemeasurable
  · exact ((continuousOn_const.add hc).sub continuousOn_id).aemeasurable
      Metric.isOpen_ball.measurableSet
  · exact hc.aemeasurable Metric.isOpen_ball.measurableSet

theorem chart_source_jacobian (H : ℝ × ℝ → ℝ) (x z r κ : ℝ) (hκ : 0 < κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r,
      κ ≤ |PinnedCharts.zDifferential H p| ∧ κ ≤ |PinnedCharts.zDifferential H p - 1|)
    (a : ℝ) (ha : a ∈ Metric.ball x r) (i : Fin 3) :
    ∀ S : Set ℝ, MeasurableSet S →
      ENNReal.ofReal (min κ 1) * (volume.restrict (Metric.ball z r))
        (sourceLeg H i a ⁻¹' S) ≤ volume S := by
  intro S hS
  have hk0 : 0 < min κ 1 := lt_min hκ zero_lt_one
  have hj := PinnedJacobian.averaging_legs_measure_bound hk0 hs
    (fun p hp => ⟨(min_le_left κ 1).trans (hb p hp).1,
      (min_le_left κ 1).trans (hb p hp).2⟩) a ha S hS
  fin_cases i
  · apply PinnedJacobian.preimage_measure_lower_jacobian Metric.isOpen_ball
      (convex_ball z r) continuousOn_id differentiableOn_id hk0 _ hS
    intro t ht
    simp
  · exact hj.2
  · exact hj.1

theorem invariant_chart_essential_bound (H : ℝ × ℝ → ℝ) (x z r κ : ℝ)
    (hr : 0 < r) (hκ : 0 < κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r,
      κ ≤ |PinnedCharts.zDifferential H p| ∧ κ ≤ |PinnedCharts.zDifferential H p - 1|)
    (φ : ℝ → E) (hφ : Measurable φ)
    (hi : ∀ᵐ p ∂volume.restrict (Metric.ball x r ×ˢ Metric.ball z r),
      φ p.1 + φ (H p) = φ p.2 + φ (p.1 + H p - p.2)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ a ∂volume.restrict (Metric.ball x (r/2)), ‖φ a‖ ≤ M := by
  let I := Metric.ball x (r/2)
  let J := Metric.ball z (r/2)
  have hI : I ⊆ Metric.ball x r := Metric.ball_subset_ball (half_le_self hr.le)
  have hJ : J ⊆ Metric.ball z r := Metric.ball_subset_ball (half_le_self hr.le)
  have hs' := hs.mono (Set.prod_mono hI hJ)
  have hb' : ∀ p ∈ I ×ˢ J, κ ≤ |PinnedCharts.zDifferential H p| ∧
      κ ≤ |PinnedCharts.zDifferential H p - 1| := fun p hp => hb p ⟨hI hp.1,hJ hp.2⟩
  obtain ⟨L, hLpos, hL⟩ := chart_source_compact_bound H x z r hr hs
  let ν : Measure ℝ := volume.restrict (Icc (-L) L)
  let C : ℝ≥0∞ := (ENNReal.ofReal (min κ 1))⁻¹
  have hC : C ≠ ⊤ := by
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_min hκ zero_lt_one)))
  have hdom : ∀ᵐ a ∂volume.restrict I, ∀ i,
      AEMeasurable (sourceLeg H i a) (volume.restrict J) ∧
      Measure.map (sourceLeg H i a) (volume.restrict J) ≤ C • ν := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with a ha
    intro i
    have hm := chart_source_measurable H x z (r/2) hs' a ha i
    refine ⟨hm, ?_⟩
    apply map_domination_restrict_range (volume.restrict J) (sourceLeg H i a) hm C
      (map_domination_of_lower_jacobian (volume.restrict J) (sourceLeg H i a) hm
        (min κ 1) (lt_min hκ zero_lt_one)
        (chart_source_jacobian H x z (r/2) κ hκ hs' hb' a ha i))
      (Icc (-L) L) measurableSet_Icc
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with t ht
    exact abs_le.mp (hL a ha t ht i)
  have hip : ∀ᵐ p ∂(volume.restrict I).prod (volume.restrict J),
      φ p.1 = φ (sourceLeg H 0 p.1 p.2) + φ (sourceLeg H 1 p.1 p.2) -
        φ (sourceLeg H 2 p.1 p.2) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have him := hi.filter_mono (ae_mono
      (Measure.restrict_mono (Set.prod_mono hI hJ) le_rfl))
    filter_upwards [him] with p hp
    exact eq_sub_of_add_eq hp
  have hJpos : 0 < (volume.restrict J) univ := by
    rw [Measure.restrict_apply_univ]
    change 0 < volume (Metric.ball z (r/2))
    rw [Real.volume_ball]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact product_three_pullbacks_essential_bound (volume.restrict I) (volume.restrict J)
    ν hJpos φ hφ (sourceLeg H) C hC hdom φ hip

theorem liftedInvariant_locally_essentially_bounded {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : ℝ → ℂ) (hφ : Measurable φ) (hinv : PinnedMeasure.liftedInvariant d φ) (x : ℝ) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∀ᵐ a ∂volume.restrict (Metric.ball x r), ‖φ a‖ ≤ M := by
  obtain ⟨y,z,H,r,κ,hr,hκ,hy,hs,hb,hi⟩ :=
    PinnedMeasure.every_target_invariant_chart hd0 hdU hinv x
  obtain ⟨M,hM,hbound⟩ := invariant_chart_essential_bound H x z r κ hr hκ hs
    (fun p hp => ⟨(hb p hp).2.2.1,(hb p hp).2.2.2⟩) φ hφ hi
  exact ⟨r/2,M,half_pos hr,hM,hbound⟩

theorem circleInvariant_lift_locally_essentially_bounded {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : PinnedPeriodicity.Circle → ℂ) (hφ : Measurable φ)
    (hinv : PinnedPeriodicity.circleInvariant d φ) (x : ℝ) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ᵐ a ∂volume.restrict (Metric.ball x r),
      ‖PinnedPeriodicity.periodicLift φ a‖ ≤ M := by
  apply liftedInvariant_locally_essentially_bounded hd0 hdU
    (PinnedPeriodicity.periodicLift φ)
  · exact hφ.comp (AddCircle.continuous_mk' PinnedPeriodicity.period).measurable
  · exact PinnedPeriodicity.circleInvariant_lifted hd0 hdU hinv

theorem locallyIntegrable_of_local_essential_bound (f : ℝ → ℂ) (hf : Measurable f)
    (hb : ∀ x : ℝ, ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧
      ∀ᵐ a ∂volume.restrict (Metric.ball x r), ‖f a‖ ≤ M) :
    LocallyIntegrable f (volume : Measure ℝ) := by
  intro x
  obtain ⟨r,M,hr,hM,hm⟩ := hb x
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds x hr, ?_⟩
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Metric.ball x r)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_ball]; exact ENNReal.ofReal_lt_top⟩
  exact (integrable_const M).mono' hf.aestronglyMeasurable hm

theorem liftedInvariant_locallyIntegrable {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : ℝ → ℂ) (hφ : Measurable φ) (hinv : PinnedMeasure.liftedInvariant d φ) :
    LocallyIntegrable φ (volume : Measure ℝ) :=
  locallyIntegrable_of_local_essential_bound φ hφ
    (liftedInvariant_locally_essentially_bounded hd0 hdU φ hφ hinv)

theorem circleInvariant_lift_locallyIntegrable {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (φ : PinnedPeriodicity.Circle → ℂ) (hφ : Measurable φ)
    (hinv : PinnedPeriodicity.circleInvariant d φ) :
    LocallyIntegrable (PinnedPeriodicity.periodicLift φ) (volume : Measure ℝ) :=
  locallyIntegrable_of_local_essential_bound (PinnedPeriodicity.periodicLift φ)
    (hφ.comp (AddCircle.continuous_mk' PinnedPeriodicity.period).measurable)
    (circleInvariant_lift_locally_essentially_bounded hd0 hdU φ hφ hinv)

end Resonance.PinnedMeasurable
