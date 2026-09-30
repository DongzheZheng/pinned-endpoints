import Resonance.PinnedCharts

/-! The genuine regular coarea density on the Euclidean real lift.  This module
does not define an arbitrary measure with an invariant-classification field.
The periodic quotient and global classification are separate proof obligations. -/
open Real MeasureTheory Set
open scoped ENNReal MeasureTheory Topology ContDiff
namespace Resonance.PinnedMeasure
open Resonance.PinnedGeometry Resonance.PinnedCharts
noncomputable section

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

def liftedEnergy (d : ℝ) (k : Ambient) : ℝ := energyDefect d (k 0) (k 1) (k 2)

def energyGradient (d : ℝ) (k : Ambient) : Ambient :=
  let w := k 0+k 1-k 2
  WithLp.toLp 2 ![velocity d (k 0)-velocity d w,
    velocity d (k 1)-velocity d w,velocity d w-velocity d (k 2)]

def regularSurface (d : ℝ) : Set Ambient :=
  {k | liftedEnergy d k=0 ∧ energyGradient d k≠0}

def coareaWeight (d : ℝ) (k : Ambient) : ℝ≥0∞ :=
  ENNReal.ofReal (((2*Real.pi)^3 * ‖energyGradient d k‖)⁻¹)

def liftedRegularCoarea (d : ℝ) : Measure Ambient :=
  ((μH[2] : Measure Ambient).restrict (regularSurface d)).withDensity (coareaWeight d)

theorem liftedEnergy_continuous {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    Continuous (liftedEnergy d) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hc := (signed_omega_contDiff hdL hdU 0).continuous
  unfold liftedEnergy energyDefect
  fun_prop

theorem energyGradient_continuous {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    Continuous (energyGradient d) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hc := velocity_continuous hdL hdU
  unfold energyGradient
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp <;> fun_prop

theorem regularSurface_measurable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    MeasurableSet (regularSurface d) := by
  exact ((liftedEnergy_continuous hd0 hdU).measurable (measurableSet_singleton 0)).inter
    (((energyGradient_continuous hd0 hdU).measurable (measurableSet_singleton 0)).compl)

theorem coareaWeight_measurable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    Measurable (coareaWeight d) := by
  have hc := (energyGradient_continuous hd0 hdU).measurable
  unfold coareaWeight
  fun_prop

theorem coareaWeight_pos {d : ℝ} {k : Ambient} (hk : k ∈ regularSurface d) :
    0 < coareaWeight d k := by
  apply ENNReal.ofReal_pos.mpr
  apply inv_pos.mpr
  exact mul_pos (by positivity) (norm_pos_iff.mpr hk.2)

theorem regularHausdorff_absolutelyContinuous {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    (μH[2] : Measure Ambient).restrict (regularSurface d) ≪ liftedRegularCoarea d := by
  apply withDensity_absolutelyContinuous' (coareaWeight_measurable hd0 hdU).aemeasurable
  filter_upwards [ae_restrict_mem (regularSurface_measurable hd0 hdU)] with k hk
  exact ne_of_gt (coareaWeight_pos hk)

def targetProjection : Ambient →L[ℝ] ℝ×ℝ :=
  ({ toFun := fun k => (k 0,k 2)
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Ambient →ₗ[ℝ] ℝ×ℝ).toContinuousLinearMap

def graph (H : ℝ×ℝ→ℝ) (p : ℝ×ℝ) : Ambient :=
  WithLp.toLp 2 ![p.1,H p,p.2]

theorem targetProjection_graph (H : ℝ×ℝ→ℝ) (p : ℝ×ℝ) :
    targetProjection (graph H p)=p := rfl

theorem graph_regular {d : ℝ} {H : ℝ×ℝ→ℝ} {p : ℝ×ℝ}
    (he : energyDefect d p.1 (H p) p.2=0)
    (hv : velocity d (H p) ≠ velocity d (p.1+H p-p.2)) :
    graph H p ∈ regularSurface d := by
  refine ⟨he,?_⟩
  intro hz
  have h := congrArg (fun k : Ambient => k 1) hz
  change velocity d (H p)-velocity d (p.1+H p-p.2)=0 at h
  exact hv (sub_eq_zero.mp h)

/-- Null sets for the full regular coarea measure pull back to every actual
regular graph with zero two-dimensional Lebesgue measure.  This is a true
Hausdorff/volume bridge, not an assumption about chart densities. -/
theorem graph_preimage_null {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (H : ℝ×ℝ→ℝ) {S : Set (ℝ×ℝ)} (hS : MeasurableSet S)
    (hreg : ∀ p∈S, graph H p ∈ regularSurface d)
    {A : Set Ambient} (hA : liftedRegularCoarea d A=0) :
    (volume.restrict S) (graph H ⁻¹' A)=0 := by
  have hH : ((μH[2] : Measure Ambient).restrict (regularSurface d)) A=0 :=
    regularHausdorff_absolutelyContinuous hd0 hdU hA
  rw [Measure.restrict_apply' (regularSurface_measurable hd0 hdU)] at hH
  have hproj : (μH[2] : Measure (ℝ×ℝ)) (targetProjection '' (A∩regularSurface d))=0 := by
    apply le_antisymm _ (zero_le _)
    have hb := targetProjection.lipschitz.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤2)
      (A∩regularSurface d)
    rw [hH,mul_zero] at hb
    exact hb
  rw [hausdorffMeasure_prod_real] at hproj
  rw [Measure.restrict_apply' hS]
  apply measure_mono_null _ hproj
  rintro p ⟨hp,hpS⟩
  exact ⟨graph H p,⟨hp,hreg p hpS⟩,targetProjection_graph H p⟩


def coordinateProjection (i : Fin 3) : Ambient →L[ℝ] ℝ :=
  ({ toFun := fun k => k i
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Ambient →ₗ[ℝ] ℝ).toContinuousLinearMap

/-- The displayed vector is the actual Fréchet gradient of the original energy. -/
theorem liftedEnergy_hasFDerivAt {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (k : Ambient) :
    HasFDerivAt (liftedEnergy d) (innerSL ℝ (energyGradient d k)) k := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hx := (omega_hasDerivAt hdL hdU (k 0)).comp_hasFDerivAt k
    (coordinateProjection 0).hasFDerivAt
  have hy := (omega_hasDerivAt hdL hdU (k 1)).comp_hasFDerivAt k
    (coordinateProjection 1).hasFDerivAt
  have hz := (omega_hasDerivAt hdL hdU (k 2)).comp_hasFDerivAt k
    (coordinateProjection 2).hasFDerivAt
  have hw := (omega_hasDerivAt hdL hdU (k 0+k 1-k 2)).comp_hasFDerivAt k
    (coordinateProjection 0+coordinateProjection 1-coordinateProjection 2).hasFDerivAt
  have heq : innerSL ℝ (energyGradient d k) =
      velocity d (k 0) • coordinateProjection 0 +
      velocity d (k 1) • coordinateProjection 1 -
      velocity d (k 2) • coordinateProjection 2 -
      velocity d (k 0+k 1-k 2) •
        (coordinateProjection 0+coordinateProjection 1-coordinateProjection 2) := by
    ext b
    have hreal (a b : ℝ) : inner ℝ a b = a*b := by
      rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
      simp only [Real.norm_eq_abs,←sq,sq_abs]
      ring
    simp [innerSL_apply_apply,PiLp.inner_apply,Fin.sum_univ_succ,
      energyGradient,coordinateProjection,hreal]
    ring
  rw [heq]
  exact ((hx.add hy).sub hz).sub hw

theorem liftedEnergy_derivative_norm {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (k : Ambient) :
    ‖fderiv ℝ (liftedEnergy d) k‖ = ‖energyGradient d k‖ := by
  rw [(liftedEnergy_hasFDerivAt hd0 hdU k).fderiv,innerSL_apply_norm]

/-- Regularity in the measure definition is exactly nonvanishing of the
Fréchet derivative of the original energy function. -/
theorem regularSurface_iff_derivative {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (k : Ambient) :
    k ∈ regularSurface d ↔ liftedEnergy d k=0 ∧ fderiv ℝ (liftedEnergy d) k≠0 := by
  simp only [regularSurface,Set.mem_setOf_eq]
  have hnorm := liftedEnergy_derivative_norm hd0 hdU k
  have hzero : fderiv ℝ (liftedEnergy d) k=0 ↔ energyGradient d k=0 := by
    rw [←norm_eq_zero,hnorm,norm_eq_zero]
  exact and_congr_right (fun _ => not_congr hzero.symm)

theorem coareaWeight_eq_derivative {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (k : Ambient) :
    coareaWeight d k = ENNReal.ofReal
      (((2*Real.pi)^3 * ‖fderiv ℝ (liftedEnergy d) k‖)^(-1:ℤ)) := by
  rw [liftedEnergy_derivative_norm hd0 hdU]
  simp [coareaWeight]

/-- The original four legs, with the fourth momentum determined before
evaluating the periodic dispersion or the invariant. -/
def invariantRelation (φ : ℝ→ℂ) (k : Ambient) : Prop :=
  φ (k 0)+φ (k 1)=φ (k 2)+φ (k 0+k 1-k 2)

def liftedInvariant (d : ℝ) (φ : ℝ→ℂ) : Prop :=
  ∀ᵐ k ∂liftedRegularCoarea d, invariantRelation φ k

theorem graph_invariant_ae {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : liftedInvariant d φ)
    (H : ℝ×ℝ→ℝ) {S : Set (ℝ×ℝ)} (hS : MeasurableSet S)
    (hreg : ∀ p∈S, graph H p ∈ regularSurface d) :
    ∀ᵐ p ∂volume.restrict S,
      φ p.1+φ (H p)=φ p.2+φ (p.1+H p-p.2) := by
  rw [liftedInvariant,ae_iff] at hφ
  have hn := graph_preimage_null hd0 hdU H hS hreg hφ
  rw [ae_iff]
  convert hn using 1

/-- The actual coarea-a.e. hypothesis reaches a nondegenerate open rectangle
around every target, including all four special circle points. -/
theorem every_target_invariant_chart {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hφ : liftedInvariant d φ) (x : ℝ) :
    ∃ y z : ℝ, ∃ H : ℝ×ℝ→ℝ, ∃ r κ : ℝ, 0<r ∧ 0<κ ∧ H (x,z)=y ∧
      ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r) ∧
      (∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r,
        energyDefect d p.1 (H p) p.2=0 ∧
        κ ≤ |velocity d (H p)-velocity d (p.1+H p-p.2)| ∧
        κ ≤ |zDifferential H p| ∧ κ ≤ |zDifferential H p-1|) ∧
      (∀ᵐ p ∂volume.restrict (Metric.ball x r ×ˢ Metric.ball z r),
        φ p.1+φ (H p)=φ p.2+φ (p.1+H p-p.2)) := by
  obtain ⟨y,z,H,r,κ,hr,hκ,hbase,hsmooth,hdata⟩ :=
    every_target_uniform_chart hd0 hdU x
  refine ⟨y,z,H,r,κ,hr,hκ,hbase,hsmooth,hdata,?_⟩
  apply graph_invariant_ae hd0 hdU hφ H (Metric.isOpen_ball.prod Metric.isOpen_ball).measurableSet
  intro p hp
  obtain ⟨he,hgap,_⟩ := hdata p hp
  apply graph_regular he
  intro hz
  rw [hz,sub_self,abs_zero] at hgap
  linarith

end
end Resonance.PinnedMeasure
