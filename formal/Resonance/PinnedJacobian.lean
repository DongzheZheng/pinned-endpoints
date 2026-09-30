import Resonance.PinnedCharts

/-! Quantitative Lebesgue change of variables for the genuine averaging
legs of the pinned resonance atlas.  No integrability or boundedness of
a collision invariant is assumed in these geometric estimates. -/
open Real MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedJacobian
open Resonance.PinnedCharts
noncomputable section

/-- A pointwise lower bound for the absolute derivative gives a global lower
distance bound on the same interval, by the real mean value theorem. -/
theorem abs_image_sub_lower {f : ℝ→ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (hc : ContinuousOn f D) (hf : DifferentiableOn ℝ f D)
    {κ : ℝ} (_hκ : 0<κ) (hb : ∀ x∈D, κ≤|deriv f x|)
    {a b : ℝ} (ha : a∈D) (hbD : b∈D) :
    κ*|b-a| ≤ |f b-f a| := by
  have hinc : ∀ {a b : ℝ}, a∈D → b∈D → a<b →
      κ*|b-a| ≤ |f b-f a| := by
    intro a b ha hbD hab
    have hcc : Icc a b ⊆ D := hD.ordConnected.out ha hbD
    have hoo : Ioo a b ⊆ D := Ioo_subset_Icc_self.trans hcc
    obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope f hab (hc.mono hcc) (hf.mono hoo)
    have hm := hb t (hoo ht)
    rw [he,abs_div,abs_of_pos (sub_pos.mpr hab)] at hm
    have hh := (le_div_iff₀ (sub_pos.mpr hab)).mp hm
    simpa only [abs_of_pos (sub_pos.mpr hab)] using hh
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hinc ha hbD hab
  · simp [hab]
  · simpa only [abs_sub_comm b a,abs_sub_comm (f b) (f a)] using hinc hbD ha hab

theorem injectiveOn_of_abs_deriv_lower {f : ℝ→ℝ} {D : Set ℝ}
    (hD : Convex ℝ D) (hc : ContinuousOn f D) (hf : DifferentiableOn ℝ f D)
    {κ : ℝ} (hκ : 0<κ) (hb : ∀ x∈D, κ≤|deriv f x|) :
    InjOn f D := by
  intro a ha b hbD he
  have hh := abs_image_sub_lower hD hc hf hκ hb ha hbD
  rw [he,sub_self,abs_zero] at hh
  have hz : |b-a|=0 := by nlinarith [abs_nonneg (b-a)]
  exact (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm

theorem measurable_preimage_inter {f : ℝ→ℝ} {D E : Set ℝ}
    (hD : MeasurableSet D) (hc : ContinuousOn f D) (hE : MeasurableSet E) :
    MeasurableSet (f ⁻¹' E ∩ D) := by
  classical
  have hp : Measurable (D.piecewise f (fun _ => (0:ℝ))) :=
    hc.measurable_piecewise continuous_const.continuousOn hD
  have hm := (hp hE).inter hD
  convert hm using 1
  ext x
  by_cases hx : x∈D <;> simp [hx]

/-- The original source Lebesgue measure is controlled without assuming an
inverse map as input.  The exact one-dimensional Jacobian formula and the
mean value theorem supply both ingredients. -/
theorem preimage_measure_lower_jacobian {f : ℝ→ℝ} {D E : Set ℝ}
    (hD : IsOpen D) (hconv : Convex ℝ D)
    (hc : ContinuousOn f D) (hf : DifferentiableOn ℝ f D)
    {κ : ℝ} (hκ : 0<κ) (hb : ∀ x∈D, κ≤|deriv f x|)
    (hE : MeasurableSet E) :
    ENNReal.ofReal κ * (volume.restrict D) (f ⁻¹' E) ≤ volume E := by
  let S := f ⁻¹' E ∩ D
  have hS : MeasurableSet S := measurable_preimage_inter hD.measurableSet hc hE
  have hi : InjOn f S := (injectiveOn_of_abs_deriv_lower hconv hc hf hκ hb).mono
    (by intro x hx; exact hx.2)
  have hder : ∀ x∈S, HasDerivWithinAt f (deriv f x) S x := by
    intro x hx
    exact ((hf x hx.2).differentiableAt (hD.mem_nhds hx.2)).hasDerivAt.hasDerivWithinAt
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul hS hder hi (fun _=> (1:ℝ≥0∞))
  simp only [lintegral_const,one_mul,mul_one,Measure.restrict_apply_univ] at hj
  have hl : ENNReal.ofReal κ * volume S ≤
      ∫⁻ x in S, ENNReal.ofReal |deriv f x| := by
    calc
      ENNReal.ofReal κ * volume S = ∫⁻ _x in S, ENNReal.ofReal κ := by simp
      _ ≤ ∫⁻ x in S, ENNReal.ofReal |deriv f x| := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hS] with x hx
        exact ENNReal.ofReal_le_ofReal (hb x hx.2)
  rw [←hj] at hl
  have him : f '' S ⊆ E := by rintro _ ⟨x,hx,rfl⟩; exact hx.1
  rw [Measure.restrict_apply' hD.measurableSet]
  exact hl.trans (measure_mono him)


/-- Both nontrivial source legs of a common resonance chart obey the same
Lebesgue pullback bound, uniformly in the target coordinate. -/
theorem averaging_legs_measure_bound
    {H : ℝ×ℝ→ℝ} {x z r κ : ℝ} (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|zDifferential H p| ∧ κ≤|zDifferential H p-1|) :
    ∀ a∈Metric.ball x r, ∀ E : Set ℝ, MeasurableSet E →
      (ENNReal.ofReal κ * (volume.restrict (Metric.ball z r))
        ((fun t => H (a,t)) ⁻¹' E) ≤ volume E) ∧
      (ENNReal.ofReal κ * (volume.restrict (Metric.ball z r))
        ((fun t => a+H (a,t)-t) ⁻¹' E) ≤ volume E) := by
  intro a ha E hE
  have hdiff (t : ℝ) (ht : t∈Metric.ball z r) : DifferentiableAt ℝ H (a,t) :=
    ((hs (a,t) ⟨ha,ht⟩).differentiableWithinAt (by simp)).differentiableAt
      ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds ⟨ha,ht⟩)
  have hder (t : ℝ) (ht : t∈Metric.ball z r) :
      HasDerivAt (fun v => H (a,v)) (zDifferential H (a,t)) t := by
    have hc := (hdiff t ht).comp t (hasFDerivAt_prodMk_right a t).differentiableAt
    rw [zDifferential_eq_deriv (hdiff t ht)]
    exact hc.hasDerivAt
  have hwder (t : ℝ) (ht : t∈Metric.ball z r) :
      HasDerivAt (fun v => a+H (a,v)-v) (zDifferential H (a,t)-1) t :=
    ((hder t ht).const_add a).sub (hasDerivAt_id t)
  have hfd : DifferentiableOn ℝ (fun v => H (a,v)) (Metric.ball z r) :=
    fun t ht => (hder t ht).differentiableAt.differentiableWithinAt
  have hwd : DifferentiableOn ℝ (fun v => a+H (a,v)-v) (Metric.ball z r) :=
    fun t ht => (hwder t ht).differentiableAt.differentiableWithinAt
  constructor
  · apply preimage_measure_lower_jacobian Metric.isOpen_ball (convex_ball z r)
      hfd.continuousOn hfd hκ _ hE
    intro t ht
    rw [(hder t ht).deriv]
    exact (hb (a,t) ⟨ha,ht⟩).1
  · apply preimage_measure_lower_jacobian Metric.isOpen_ball (convex_ball z r)
      hwd.continuousOn hwd hκ _ hE
    intro t ht
    rw [(hwder t ht).deriv]
    exact (hb (a,t) ⟨ha,ht⟩).2

end
end Resonance.PinnedJacobian
