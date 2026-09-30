import Resonance.PinnedEndToEnd
import Resonance.PinnedMeasureNormalization

/-! The final endpoint package for the pinned classification.  Its input is
the original Euclidean-normalized regular coarea and finite complex-valued
AE-measurable data on the circle.  The conclusion uses normalized circle
Haar measure, unique coefficients, and the unique smooth periodic real lift.
The reverse statement concerns the displayed affine-dispersion functions
themselves and every actual resonance, including critical resonances. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedClassificationFinal
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedPeriodicity
open Resonance.PinnedCircleAE Resonance.PinnedEndToEnd
open Resonance.PinnedMeasureNormalization
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

/-- Probability Haar measure: the paper's `m = dx/(2π)`. -/
def circleHaar : Measure PinnedPeriodicity.Circle :=
  (ENNReal.ofReal period)⁻¹ • circleVolume

theorem circleHaar_univ : circleHaar univ = 1 := by
  simp only [circleHaar, Measure.smul_apply, smul_eq_mul]
  rw [AddCircle.measure_univ]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr period_pos))
    ENNReal.ofReal_ne_top

instance circleHaar_probability : IsProbabilityMeasure circleHaar := ⟨circleHaar_univ⟩

instance circleHaar_addHaar : circleHaar.IsAddHaarMeasure := by
  unfold circleHaar
  exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr period_pos)))

theorem circleHaar_ae_iff (p : PinnedPeriodicity.Circle → Prop) :
    (∀ᵐ k ∂circleHaar, p k) ↔ ∀ᵐ k ∂circleVolume, p k := by
  unfold circleHaar
  exact Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)

theorem circleHaar_mutually_absolutelyContinuous :
    circleHaar ≪ circleVolume ∧ circleVolume ≪ circleHaar := by
  unfold circleHaar
  exact ⟨Measure.smul_absolutelyContinuous,
    Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)⟩

theorem circleHaar_aemeasurable_iff (φ : PinnedPeriodicity.Circle → ℂ) :
    AEMeasurable φ circleHaar ↔ AEMeasurable φ circleVolume :=
  ⟨fun h => h.mono_ac circleHaar_mutually_absolutelyContinuous.2,
    fun h => h.mono_ac circleHaar_mutually_absolutelyContinuous.1⟩

theorem omega_zero_ne_pi {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) :
    omega d 0 ≠ omega d Real.pi := by
  intro he
  have h0 := omega_sq (by linarith : -(1/2:ℝ) < d) hdU 0
  have hp := omega_sq (by linarith : -(1/2:ℝ) < d) hdU Real.pi
  simp only [Real.cos_zero, Real.cos_pi] at h0 hp
  rw [he] at h0
  nlinarith

theorem affine_coefficients_unique {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {A B C D : ℂ}
    (he : ∀ x : ℝ, A+B*(omega d x : ℂ) = C+D*(omega d x : ℂ)) :
    A = C ∧ B = D := by
  have hz := he 0
  have hp := he Real.pi
  have hn : (omega d 0 : ℂ) - (omega d Real.pi : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast omega_zero_ne_pi hd0 hdU)
  have hm : (B-D)*((omega d 0 : ℂ)-(omega d Real.pi : ℂ)) = 0 := by
    linear_combination hz - hp
  have hBD : B=D := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hn)
  exact ⟨by simpa [hBD] using hz, hBD⟩

theorem affine_lift_continuous {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (A B : ℂ) : Continuous (fun x : ℝ => A+B*(omega d x : ℂ)) := by
  exact continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp
    (PinnedCharts.signed_omega_contDiff (by linarith) hdU 0).continuous))

theorem affine_coefficients_unique_ae {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {A B C D : ℂ}
    (he : (fun x : ℝ => A+B*(omega d x : ℂ)) =ᵐ[volume]
      (fun x => C+D*(omega d x : ℂ))) : A=C ∧ B=D := by
  have hf := Measure.eq_of_ae_eq he (affine_lift_continuous hd0 hdU A B)
    (affine_lift_continuous hd0 hdU C D)
  exact affine_coefficients_unique hd0 hdU (fun x => congrFun hf x)

theorem affine_circle_coefficients_unique_ae {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) {A B C D : ℂ}
    (he : (fun k => A+B*(circleDispersion d k : ℂ)) =ᵐ[circleHaar]
      (fun k => C+D*(circleDispersion d k : ℂ))) : A=C ∧ B=D := by
  have hl := circle_ae_lift ((circleHaar_ae_iff _).mp he)
  exact affine_coefficients_unique_ae hd0 hdU hl

/-- Unique coefficients for the exact paper measure and normalized Haar data.
No integrability, regular representative or differential relation is assumed. -/
theorem euclidean_coarea_classification_unique {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) (φ : PinnedPeriodicity.Circle → ℂ)
    (hφ : AEMeasurable φ circleHaar) (hi : euclideanCircleInvariant d φ) :
    ∃! AB : ℂ × ℂ, φ =ᵐ[circleHaar]
      (fun k => AB.1+AB.2*(circleDispersion d k : ℂ)) := by
  obtain ⟨A,B,hAB⟩ := aemeasurable_circleInvariant_classification hd0 hdU φ
    ((circleHaar_aemeasurable_iff φ).mp hφ) ((euclideanCircleInvariant_iff d φ).mp hi)
  have hAB' := (circleHaar_ae_iff _).mpr hAB
  refine ⟨(A,B),hAB',?_⟩
  rintro ⟨C,D⟩ hCD
  have h := affine_circle_coefficients_unique_ae hd0 hdU (hCD.symm.trans hAB')
  exact Prod.ext h.1 h.2

theorem affine_lift_smooth {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (A B : ℂ) : ContDiff ℝ ∞ (fun x : ℝ => A+B*(omega d x : ℂ)) := by
  exact contDiff_const.add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (PinnedCharts.signed_omega_contDiff (by linarith) hdU ∞)))

theorem affine_lift_periodic (d : ℝ) (A B : ℂ) :
    Function.Periodic (fun x : ℝ => A+B*(omega d x : ℂ)) period := by
  intro x
  dsimp only
  rw [PinnedPeriodicity.omega_periodic d x]

/-- The unique representative is smooth and periodic.  Uniqueness is literal
function equality, not merely equality of equivalence classes. -/
theorem euclidean_coarea_unique_smooth_representative {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) (φ : PinnedPeriodicity.Circle → ℂ)
    (hφ : AEMeasurable φ circleHaar) (hi : euclideanCircleInvariant d φ) :
    ∃! g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ Function.Periodic g period ∧
      periodicLift φ =ᵐ[volume] g := by
  obtain ⟨AB,hAB,_⟩ := euclidean_coarea_classification_unique hd0 hdU φ hφ hi
  refine ⟨(fun x => AB.1+AB.2*(omega d x : ℂ)),
    ⟨affine_lift_smooth hd0 hdU AB.1 AB.2,
      affine_lift_periodic d AB.1 AB.2, circle_ae_lift ((circleHaar_ae_iff _).mp hAB)⟩,?_⟩
  intro g hg
  exact Measure.eq_of_ae_eq (hg.2.2.symm.trans
    (circle_ae_lift ((circleHaar_ae_iff _).mp hAB))) hg.1.continuous
      (affine_lift_continuous hd0 hdU AB.1 AB.2)

/-- The converse is exact on every original real quartet.  It does not
discard the critical or the trivial resonances. -/
theorem affine_representative_all_resonances (d : ℝ) (A B : ℂ) (x y z : ℝ)
    (he : energyDefect d x y z = 0) :
    (A+B*(omega d x : ℂ))+(A+B*(omega d y : ℂ)) =
      (A+B*(omega d z : ℂ))+(A+B*(omega d (x+y-z) : ℂ)) :=
  PinnedClassification.complex_affine_omega_original_identity d x y z A B he

/-- In particular the displayed representatives satisfy the actual
Euclidean-normalized circle coarea invariant, with all four legs retained. -/
theorem affine_representative_euclidean_invariant {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) (A B : ℂ) :
    euclideanCircleInvariant d (fun k => A+B*(circleDispersion d k : ℂ)) := by
  apply (euclideanCircleInvariant_iff d _).mpr
  let φ : PinnedPeriodicity.Circle → ℂ := fun k => A+B*(circleDispersion d k : ℂ)
  have hφ : Continuous φ := continuous_const.add (continuous_const.mul
    (Complex.continuous_ofReal.comp (circleDispersion_continuous hd0 hdU)))
  have hm : MeasurableSet {k : CircleMomenta | circleInvariantRelation φ k} := by
    apply measurableSet_eq_fun
    · exact ((hφ.comp (continuous_apply 0)).add (hφ.comp (continuous_apply 1))).measurable
    · exact ((hφ.comp (continuous_apply 2)).add
        (hφ.comp (((continuous_apply 0).add (continuous_apply 1)).sub
          (continuous_apply 2)))).measurable
  change ∀ᵐ k ∂(cellCoarea d).map quotientCoordinates, circleInvariantRelation φ k
  apply (ae_map_iff quotientCoordinates_continuous.measurable.aemeasurable hm).mpr
  have hr : ∀ᵐ k ∂PinnedMeasure.liftedRegularCoarea d,
      k ∈ PinnedMeasure.regularSurface d :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (PinnedMeasure.regularSurface_measurable hd0 hdU))
  have hc : ∀ᵐ k ∂cellCoarea d, k ∈ PinnedMeasure.regularSurface d := ae_restrict_of_ae hr
  filter_upwards [hc] with k hk
  have hid := affine_representative_all_resonances d A B (k 0) (k 1) (k 2) hk.1
  simpa [φ, circleInvariantRelation, quotientCoordinates, circleDispersion,
    AddCircle.coe_add, AddCircle.coe_sub] using hid

/-- If an affine-dispersion function is real almost everywhere then both
coefficients are real.  No pointwise assumption on its initial measurable
representative is needed. -/
theorem affine_coefficients_real_of_ae {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) {A B : ℂ}
    (hreal : ∀ᵐ k ∂circleHaar, (A+B*(circleDispersion d k : ℂ)).im = 0) :
    A.im = 0 ∧ B.im = 0 := by
  have hec : (fun k => ((A+B*(circleDispersion d k : ℂ)).im : ℂ)) =ᵐ[circleVolume]
      (fun _ => (0:ℂ)) := by
    filter_upwards [(circleHaar_ae_iff _).mp hreal] with k hk
    simp only [hk, Complex.ofReal_zero]
  have hl := circle_ae_lift hec
  have hz : (fun x : ℝ => (A.im : ℂ)+(B.im : ℂ)*(omega d x : ℂ)) =ᵐ[volume]
      (fun x => (0:ℂ)+(0:ℂ)*(omega d x : ℂ)) := by
    filter_upwards [hl] with x hx
    simpa [periodicLift, Complex.add_im, Complex.mul_im] using hx
  have h := affine_coefficients_unique_ae hd0 hdU hz
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem euclidean_coarea_classification_real {d : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) (φ : PinnedPeriodicity.Circle → ℝ)
    (hφ : AEMeasurable φ circleHaar)
    (hi : euclideanCircleInvariant d (fun k => (φ k : ℂ))) :
    ∃! AB : ℝ × ℝ, φ =ᵐ[circleHaar]
      (fun k => AB.1+AB.2*circleDispersion d k) := by
  have hcφ := Complex.continuous_ofReal.measurable.comp_aemeasurable hφ
  obtain ⟨AB,hAB,_⟩ := euclidean_coarea_classification_unique hd0 hdU
    (fun k => (φ k : ℂ)) hcφ hi
  have hr : ∀ᵐ k ∂circleHaar, (AB.1+AB.2*(circleDispersion d k : ℂ)).im = 0 := by
    filter_upwards [hAB] with k hk
    rw [← hk]
    rfl
  have hreal := affine_coefficients_real_of_ae hd0 hdU hr
  have hABr : φ =ᵐ[circleHaar]
      (fun k => AB.1.re+AB.2.re*circleDispersion d k) := by
    filter_upwards [hAB] with k hk
    have he := congrArg Complex.re hk
    simpa using he
  refine ⟨(AB.1.re,AB.2.re),hABr,?_⟩
  rintro ⟨C,D⟩ hCD
  have he : (fun k => (C : ℂ)+(D : ℂ)*(circleDispersion d k : ℂ)) =ᵐ[circleHaar]
      (fun k => (AB.1.re : ℂ)+(AB.2.re : ℂ)*(circleDispersion d k : ℂ)) := by
    filter_upwards [hCD,hABr] with k hk hl
    exact_mod_cast hk.symm.trans hl
  have h := affine_circle_coefficients_unique_ae hd0 hdU he
  apply Prod.ext
  · exact_mod_cast h.1
  · exact_mod_cast h.2

end
end Resonance.PinnedClassificationFinal
