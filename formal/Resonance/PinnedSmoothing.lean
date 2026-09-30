import Resonance.PinnedJacobian

/-! Source averaging on the same pinned resonance graphs.  The estimates
below act on the complete source function; they do not assume regularity
of a collision invariant or define a replacement collision model. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedSmoothing
noncomputable section

theorem comp_integrable_of_map_domination
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {μ : Measure Z} {ν : Measure Y} {T : Z→Y} {C : ℝ≥0∞}
    (hT : AEMeasurable T μ) (hdom : μ.map T≤C • ν) (hC : C≠⊤)
    {f : Y→ℂ} (hf : Integrable f ν) : Integrable (f ∘ T) μ := by
  exact ((hf.smul_measure hC).mono_measure hdom).comp_aemeasurable hT

theorem lintegral_comp_enorm_le
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {μ : Measure Z} {ν : Measure Y} {T : Z→Y} {C : ℝ≥0∞}
    (hT : AEMeasurable T μ) (hdom : μ.map T≤C • ν) (hC : C≠⊤)
    {f : Y→ℂ} (hf : Integrable f ν) :
    (∫⁻ z, ‖f (T z)‖ₑ ∂μ) ≤ C*(∫⁻ y, ‖f y‖ₑ ∂ν) := by
  have hi := (hf.smul_measure hC).mono_measure hdom
  rw [←lintegral_map' hi.aestronglyMeasurable.enorm hT]
  calc
    (∫⁻ y, ‖f y‖ₑ ∂μ.map T) ≤ ∫⁻ y, ‖f y‖ₑ ∂C • ν :=
      lintegral_mono' hdom (le_refl _)
    _ = C*(∫⁻ y, ‖f y‖ₑ ∂ν) := lintegral_smul_measure C _

theorem weighted_comp_integrable
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {μ : Measure Z} {ν : Measure Y} {T : Z→Y} {C : ℝ≥0∞}
    (hT : AEMeasurable T μ) (hdom : μ.map T≤C • ν) (hC : C≠⊤)
    {f : Y→ℂ} (hf : Integrable f ν)
    {χ : Z→ℝ} (hχ : AEStronglyMeasurable χ μ) {B : ℝ}
    (hB : ∀ᵐ z∂μ, ‖χ z‖≤B) :
    Integrable (fun z => χ z • f (T z)) μ := by
  exact (comp_integrable_of_map_domination hT hdom hC hf).bdd_smul B hχ hB

theorem enorm_integral_weighted_comp_le
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {μ : Measure Z} {ν : Measure Y} {T : Z→Y} {C : ℝ≥0∞}
    (hT : AEMeasurable T μ) (hdom : μ.map T≤C • ν) (hC : C≠⊤)
    {f : Y→ℂ} (hf : Integrable f ν)
    {χ : Z→ℝ} {B : ℝ} (hB : ∀ᵐ z∂μ, ‖χ z‖≤B) :
    ‖∫ z, χ z • f (T z) ∂μ‖ₑ ≤
      ENNReal.ofReal B*C*(∫⁻ y, ‖f y‖ₑ ∂ν) := by
  calc
    ‖∫ z, χ z • f (T z) ∂μ‖ₑ ≤ ∫⁻ z, ‖χ z • f (T z)‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z, ENNReal.ofReal B * ‖f (T z)‖ₑ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hB] with z hz
      calc
        ‖χ z • f (T z)‖ₑ = ENNReal.ofReal ‖χ z • f (T z)‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (‖χ z‖*‖f (T z)‖) :=
          ENNReal.ofReal_le_ofReal (norm_smul_le _ _)
        _ = ENNReal.ofReal ‖χ z‖ * ‖f (T z)‖ₑ := by
          simp only [ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm]
        _ ≤ ENNReal.ofReal B * ‖f (T z)‖ₑ := by
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hz) _
    _ = ENNReal.ofReal B * ∫⁻ z, ‖f (T z)‖ₑ ∂μ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B * (C * ∫⁻ y, ‖f y‖ₑ ∂ν) := by
      gcongr
      exact lintegral_comp_enorm_le hT hdom hC hf
    _ = ENNReal.ofReal B*C*(∫⁻ y, ‖f y‖ₑ ∂ν) := by rw [mul_assoc]


/-- Parameter differentiation on a fixed compact source interval.  The
dominating derivative bound follows from the displayed joint continuity
on a compact rectangle, rather than from a new estimate on the invariant. -/
theorem compact_parameter_integral_hasDerivAt
    {I J : Set ℝ} (hI : IsOpen I) (hJ : IsCompact J)
    {F F' : ℝ×ℝ→ℂ}
    (hF : ContinuousOn F (I×ˢJ)) (hF' : ContinuousOn F' (I×ˢJ))
    (hder : ∀ x∈I, ∀ z∈J, HasDerivAt (fun a=>F (a,z)) (F' (x,z)) x)
    {x₀ : ℝ} (hx₀ : x₀∈I) :
    HasDerivAt (fun x => ∫ z in J, F (x,z)) (∫ z in J, F' (x₀,z)) x₀ := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hx₀)
  let r := δ/2
  have hr : 0<r := by dsimp [r]; positivity
  have hcball : Metric.closedBall x₀ r ⊆ I := by
    intro x hx
    apply hball
    simp only [Metric.mem_closedBall,Metric.mem_ball] at hx ⊢
    exact hx.trans_lt (by dsimp [r]; linarith)
  have hcompact : IsCompact (Metric.closedBall x₀ r ×ˢ J) :=
    (isCompact_closedBall x₀ r).prod hJ
  obtain ⟨B,hB⟩ := hcompact.exists_bound_of_continuousOn
    (hF'.mono (Set.prod_mono hcball (Subset.refl J)))
  have hFc (x : ℝ) (hx : x∈I) : ContinuousOn (fun z=>F (x,z)) J :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun z hz=>⟨hx,hz⟩)
  have hF'c (x : ℝ) (hx : x∈I) : ContinuousOn (fun z=>F' (x,z)) J :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun z hz=>⟨hx,hz⟩)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun x z=>F (x,z)) (F':=fun x z=>F' (x,z)) (bound:=fun _=>B)
    (Metric.ball_mem_nhds x₀ hr) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hI.mem_nhds hx₀] with x hx
    exact (hFc x hx).aestronglyMeasurable hJ.measurableSet
  · exact ContinuousOn.integrableOn_compact hJ (hFc x₀ hx₀)
  · exact (hF'c x₀ hx₀).aestronglyMeasurable hJ.measurableSet
  · filter_upwards [ae_restrict_mem hJ.measurableSet] with z hz
    intro x hx
    exact hB (x,z) ⟨Metric.ball_subset_closedBall hx,hz⟩
  · exact ContinuousOn.integrableOn_compact hJ continuous_const.continuousOn
  · filter_upwards [ae_restrict_mem hJ.measurableSet] with z hz
    intro x hx
    exact hder x (hcball (Metric.ball_subset_closedBall hx)) z hz


/-- A common source-map bound gives one uniform error estimate for its
weighted averages, including complex-valued source functions. -/
theorem weighted_average_difference_bound
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {μ : Measure Z} {ν : Measure Y} {T : Z→Y} {C : ℝ≥0∞}
    (hT : AEMeasurable T μ) (hdom : μ.map T≤C • ν) (hC : C≠⊤)
    {f g : Y→ℂ} (hf : Integrable f ν) (hg : Integrable g ν)
    {χ : Z→ℝ} (hχ : AEStronglyMeasurable χ μ) {B : ℝ}
    (hB : ∀ᵐ z∂μ, ‖χ z‖≤B) :
    ‖(∫ z, χ z • f (T z) ∂μ) - (∫ z, χ z • g (T z) ∂μ)‖ₑ ≤
      ENNReal.ofReal B*C*eLpNorm (f-g) 1 ν := by
  have hfi := weighted_comp_integrable hT hdom hC hf hχ hB
  have hgi := weighted_comp_integrable hT hdom hC hg hχ hB
  rw [←integral_sub hfi hgi]
  have heq : (fun z => χ z • f (T z) - χ z • g (T z)) =
      fun z => χ z • ((f-g) (T z)) := by ext z; simp only [Pi.sub_apply,Complex.real_smul]; ring
  rw [heq,eLpNorm_one_eq_lintegral_enorm]
  exact enorm_integral_weighted_comp_le hT hdom hC (hf.sub hg) hB

theorem weighted_averages_tendstoUniformlyOn
    {X Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {μ : Measure Z} {ν : Measure Y} {s : Set X}
    {T : X→Z→Y} {χ : X→Z→ℝ} {C : ℝ≥0∞} (hC : C≠⊤) {B : ℝ}
    (hT : ∀ x∈s, AEMeasurable (T x) μ)
    (hdom : ∀ x∈s, μ.map (T x)≤C • ν)
    (hχ : ∀ x∈s, AEStronglyMeasurable (χ x) μ)
    (hB : ∀ x∈s, ∀ᵐ z∂μ, ‖χ x z‖≤B)
    {f : ℕ→Y→ℂ} {g : Y→ℂ}
    (hf : ∀ n, Integrable (f n) ν) (hg : Integrable g ν)
    (hlim : Tendsto (fun n => eLpNorm (f n-g) 1 ν) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n x => ∫ z, χ x z • f n (T x z) ∂μ)
      (fun x => ∫ z, χ x z • g (T x z) ∂μ) atTop s := by
  have hBC : ENNReal.ofReal B*C≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  have hzero : Tendsto (fun n => ENNReal.ofReal B*C*eLpNorm (f n-g) 1 ν)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hlim (Or.inr hBC)
  rw [EMetric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hzero.eventually_lt_const hε] with n hn
  intro x hx
  have hh := weighted_average_difference_bound (hT x hx) (hdom x hx) hC
    (hf n) hg (hχ x hx) (hB x hx)
  rw [edist_comm,edist_eq_enorm_sub]
  exact hh.trans_lt hn


/-- Integration by parts on the actual source coordinate transfers the
parameter derivative of a smooth test function onto the source weight.
The quotient is formed from the original nonvanishing source derivative. -/
theorem source_derivative_transfer
    {J : Set ℝ} (hJ : IsOpen J) {a b : ℝ} (hab : a≤b) (hsub : Icc a b⊆J)
    {H χ X : ℝ→ℝ}
    (hH : ContDiffOn ℝ ∞ H J) (hχ : ContDiffOn ℝ ∞ χ J)
    (hX : ContDiffOn ℝ ∞ X J) (hZ : ∀ z∈J, deriv H z≠0)
    (hχa : χ a=0) (hχb : χ b=0)
    {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f) :
    (∫ z in Icc a b, (χ z*X z) • deriv f (H z)) =
      -(∫ z in Icc a b, deriv (fun t=>χ t*X t/deriv H t) z • f (H z)) := by
  let U : ℝ→ℝ := fun t=>χ t*X t/deriv H t
  let V : ℝ→ℂ := fun t=>f (H t)
  have hHd : ContDiffOn ℝ ∞ (deriv H) J := hH.deriv_of_isOpen hJ (by simp)
  have hU : ContDiffOn ℝ ∞ U J := (hχ.mul hX).div hHd hZ
  have hV : ContDiffOn ℝ ∞ V J := hf.comp_contDiffOn hH
  have hUd : ContDiffOn ℝ ∞ (deriv U) J := hU.deriv_of_isOpen hJ (by simp)
  have hVd : ContDiffOn ℝ ∞ (deriv V) J := hV.deriv_of_isOpen hJ (by simp)
  have hdH (z : ℝ) (hz : z∈J) : HasDerivAt H (deriv H z) z :=
    (((hH.differentiableOn (by simp)) z hz).differentiableAt (hJ.mem_nhds hz)).hasDerivAt
  have hdU (z : ℝ) (hz : z∈J) : HasDerivAt U (deriv U z) z :=
    (((hU.differentiableOn (by simp)) z hz).differentiableAt (hJ.mem_nhds hz)).hasDerivAt
  have hdV (z : ℝ) (hz : z∈J) : HasDerivAt V (deriv V z) z :=
    (((hV.differentiableOn (by simp)) z hz).differentiableAt (hJ.mem_nhds hz)).hasDerivAt
  have hchain (z : ℝ) (hz : z∈J) :
      deriv V z = deriv H z • deriv f (H z) :=
    (((hf.differentiable (by simp)) (H z)).hasDerivAt.scomp z (hdH z hz)).deriv
  have hucc : ContinuousOn U (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hU.continuousOn.mono hsub
  have hvcc : ContinuousOn V (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hV.continuousOn.mono hsub
  have hudcc : ContinuousOn (deriv U) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hUd.continuousOn.mono hsub
  have hvdcc : ContinuousOn (deriv V) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hVd.continuousOn.mono hsub
  have hibp : (∫ t in a..b, U t • deriv V t) =
      U b • V b - U a • V a - ∫ t in a..b, deriv U t • V t :=
    intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    hucc hvcc
    (fun z hz=>hdU z (hsub (by simpa [min_eq_left hab,max_eq_right hab] using (Ioo_subset_Icc_self hz))))
    (fun z hz=>hdV z (hsub (by simpa [min_eq_left hab,max_eq_right hab] using (Ioo_subset_Icc_self hz))))
    hudcc.intervalIntegrable hvdcc.intervalIntegrable
  have hUa : U a=0 := by simp [U,hχa]
  have hUb : U b=0 := by simp [U,hχb]
  simp only [hUa,hUb,Complex.real_smul,Complex.ofReal_zero,zero_mul,sub_self,zero_sub] at hibp
  have hl : (∫ z in a..b, U z • deriv V z) =
      ∫ z in Icc a b, (χ z*X z) • deriv f (H z) := by
    rw [intervalIntegral.integral_of_le hab,←integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro z hz
    change U z • deriv V z = (χ z*X z) • deriv f (H z)
    rw [hchain z (hsub hz)]
    change ((U z:ℂ)*(((deriv H z:ℝ):ℂ)*deriv f (H z))) =
      ((χ z*X z:ℝ):ℂ)*deriv f (H z)
    have halg : U z * deriv H z = χ z*X z := by
      dsimp [U]
      exact div_mul_cancel₀ _ (hZ z (hsub hz))
    rw [←mul_assoc,←Complex.ofReal_mul,halg]
  calc
    (∫ z in Icc a b, (χ z*X z) • deriv f (H z)) =
        ∫ z in a..b, U z • deriv V z := hl.symm
    _ = -(∫ z in a..b, deriv U z • V z) := hibp
    _ = -(∫ z in Icc a b, deriv (fun t=>χ t*X t/deriv H t) z • f (H z)) := by
      rw [intervalIntegral.integral_of_le hab,←integral_Icc_eq_integral_Ioc]


/-- Smooth compactly supported approximants exist for the same L¹ source
measure.  No pointwise bound for their derivatives is assumed. -/
theorem exists_smooth_L1_approximation {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
    {f : ℝ→ℂ} (hf : Integrable f ν) :
    ∃ fₙ : ℕ→ℝ→ℂ,
      (∀ n, HasCompactSupport (fₙ n) ∧ ContDiff ℝ ∞ (fₙ n) ∧ Integrable (fₙ n) ν) ∧
      Tendsto (fun n=>eLpNorm (fₙ n-f) 1 ν) atTop (𝓝 0) := by
  have hflp : MemLp f 1 ν := memLp_one_iff_integrable.mpr hf
  have hex (n : ℕ) : ∃ g : ℝ→ℂ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (f-g) 1 ν ≤ ENNReal.ofReal ((1/2:ℝ)^n) :=
    hflp.exist_eLpNorm_sub_le (by simp) le_rfl (by positivity)
  choose g hgcompact hgsmooth hgerror using hex
  refine ⟨g,?_,?_⟩
  · intro n
    exact ⟨hgcompact n,hgsmooth n,
      (hgsmooth n).continuous.integrable_of_hasCompactSupport (hgcompact n)⟩
  · have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
    have he : Tendsto (fun n=>ENNReal.ofReal ((1/2:ℝ)^n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpow
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    · intro n; exact zero_le _
    · intro n
      change eLpNorm (g n-f) 1 ν ≤ ENNReal.ofReal ((1/2:ℝ)^n)
      rw [eLpNorm_sub_comm]
      exact hgerror n


/-- A smooth-test integration-by-parts identity extends to the same L¹
source, because both source averages obey the already proved common
Jacobian bound.  This lemma does not assume the desired derivative of f. -/
theorem source_average_hasDerivAt_of_smooth_identity
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {ν : Measure ℝ}
    [IsFiniteMeasureOnCompacts ν]
    {I : Set ℝ} (hI : IsOpen I)
    {T : ℝ→Z→ℝ} {χ ψ : ℝ→Z→ℝ} {C : ℝ≥0∞} (hC : C≠⊤)
    {Bχ Bψ : ℝ}
    (hT : ∀ x∈I, AEMeasurable (T x) μ)
    (hdom : ∀ x∈I, μ.map (T x)≤C • ν)
    (hχ : ∀ x∈I, AEStronglyMeasurable (χ x) μ)
    (hψ : ∀ x∈I, AEStronglyMeasurable (ψ x) μ)
    (hbχ : ∀ x∈I, ∀ᵐ z∂μ, ‖χ x z‖≤Bχ)
    (hbψ : ∀ x∈I, ∀ᵐ z∂μ, ‖ψ x z‖≤Bψ)
    (hidentity : ∀ g : ℝ→ℂ, HasCompactSupport g → ContDiff ℝ ∞ g →
      ∀ x∈I, HasDerivAt (fun a=>∫ z, χ a z • g (T a z) ∂μ)
        (∫ z, ψ x z • g (T x z) ∂μ) x)
    {f : ℝ→ℂ} (hf : Integrable f ν) {x : ℝ} (hx : x∈I) :
    HasDerivAt (fun a=>∫ z, χ a z • f (T a z) ∂μ)
      (∫ z, ψ x z • f (T x z) ∂μ) x := by
  obtain ⟨g,hg,hconv⟩ := exists_smooth_L1_approximation hf
  have hfn : ∀ n, Integrable (g n) ν := fun n=>(hg n).2.2
  have hzero := weighted_averages_tendstoUniformlyOn hC hT hdom hχ hbχ hfn hf hconv
  have hone := weighted_averages_tendstoUniformlyOn hC hT hdom hψ hbψ hfn hf hconv
  apply hasDerivAt_of_tendstoUniformlyOn
    (f:=fun n a=>∫ z, χ a z • g n (T a z) ∂μ) hI hone _ _ hx
  · exact Eventually.of_forall (fun n=>hidentity (g n) (hg n).1 (hg n).2.1)
  · intro a ha
    exact hzero.tendsto_at ha

def partialX (H : ℝ×ℝ→ℝ) (p : ℝ×ℝ) : ℝ := fderiv ℝ H p (1,0)
def partialZ (H : ℝ×ℝ→ℝ) (p : ℝ×ℝ) : ℝ := fderiv ℝ H p (0,1)

def transferWeight (H χ : ℝ×ℝ→ℝ) : ℝ×ℝ→ℝ :=
  fun p => partialX χ p - partialZ
    (fun q=>χ q*partialX H q/partialZ H q) p

theorem contDiffOn_partialX {S : Set (ℝ×ℝ)} (hS : IsOpen S)
    {H : ℝ×ℝ→ℝ} (hH : ContDiffOn ℝ ∞ H S) :
    ContDiffOn ℝ ∞ (partialX H) S :=
  (hH.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_partialZ {S : Set (ℝ×ℝ)} (hS : IsOpen S)
    {H : ℝ×ℝ→ℝ} (hH : ContDiffOn ℝ ∞ H S) :
    ContDiffOn ℝ ∞ (partialZ H) S :=
  (hH.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_transferWeight {S : Set (ℝ×ℝ)} (hS : IsOpen S)
    {H χ : ℝ×ℝ→ℝ} (hH : ContDiffOn ℝ ∞ H S)
    (hχ : ContDiffOn ℝ ∞ χ S) (hZ : ∀ p∈S, partialZ H p≠0) :
    ContDiffOn ℝ ∞ (transferWeight H χ) S := by
  apply (contDiffOn_partialX hS hχ).sub
  apply contDiffOn_partialZ hS
  exact (hχ.mul (contDiffOn_partialX hS hH)).div (contDiffOn_partialZ hS hH) hZ


theorem transferWeight_zero_of_eventually_zero
    {H χ : ℝ×ℝ→ℝ} {p : ℝ×ℝ}
    (hχ : χ =ᶠ[𝓝 p] (fun _=>0)) : transferWeight H χ p=0 := by
  have hdx : fderiv ℝ χ p=0 := by
    rw [hχ.fderiv_eq]
    simp
  have hquot : (fun q=>χ q*partialX H q/partialZ H q) =ᶠ[𝓝 p] (fun _=>0) := by
    filter_upwards [hχ] with q hq
    simp [hq]
  have hdz : fderiv ℝ (fun q=>χ q*partialX H q/partialZ H q) p=0 := by
    rw [hquot.fderiv_eq]
    simp
  change fderiv ℝ χ p (1,0) -
    fderiv ℝ (fun q=>χ q*partialX H q/partialZ H q) p (0,1)=0
  rw [hdx,hdz]
  simp

theorem transferWeight_zero_on_open
    {O : Set (ℝ×ℝ)} (hO : IsOpen O) {H χ : ℝ×ℝ→ℝ}
    (hχ : EqOn χ 0 O) : EqOn (transferWeight H χ) 0 O := by
  intro p hp
  apply transferWeight_zero_of_eventually_zero
  filter_upwards [hO.mem_nhds hp] with q hq
  exact hχ hq

def iteratedWeight (H χ : ℝ×ℝ→ℝ) : ℕ→ℝ×ℝ→ℝ
  | 0 => χ
  | n+1 => transferWeight H (iteratedWeight H χ n)

theorem contDiffOn_iteratedWeight {S : Set (ℝ×ℝ)} (hS : IsOpen S)
    {H χ : ℝ×ℝ→ℝ} (hH : ContDiffOn ℝ ∞ H S)
    (hχ : ContDiffOn ℝ ∞ χ S) (hZ : ∀ p∈S, partialZ H p≠0) :
    ∀ n, ContDiffOn ℝ ∞ (iteratedWeight H χ n) S := by
  intro n
  induction n with
  | zero => exact hχ
  | succ n ih => exact contDiffOn_transferWeight hS hH ih hZ

theorem iteratedWeight_zero_on_open
    {O : Set (ℝ×ℝ)} (hO : IsOpen O) {H χ : ℝ×ℝ→ℝ}
    (hχ : EqOn χ 0 O) : ∀ n, EqOn (iteratedWeight H χ n) 0 O := by
  intro n
  induction n with
  | zero => exact hχ
  | succ n ih => exact transferWeight_zero_on_open hO ih


theorem partialX_hasDerivAt {H : ℝ×ℝ→ℝ} {x z : ℝ}
    (hH : DifferentiableAt ℝ H (x,z)) :
    HasDerivAt (fun a=>H (a,z)) (partialX H (x,z)) x :=
  hH.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x z))

theorem partialZ_hasDerivAt {H : ℝ×ℝ→ℝ} {x z : ℝ}
    (hH : DifferentiableAt ℝ H (x,z)) :
    HasDerivAt (fun a=>H (x,a)) (partialZ H (x,z)) z :=
  hH.hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z x).prodMk (hasDerivAt_id z))

theorem contDiffOn_source_section {I J : Set ℝ} {H : ℝ×ℝ→ℝ}
    (hH : ContDiffOn ℝ ∞ H (I×ˢJ)) {x : ℝ} (hx : x∈I) :
    ContDiffOn ℝ ∞ (fun z=>H (x,z)) J :=
  hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _z hz=>⟨hx,hz⟩)



/-- The smooth-test identity required by the L¹ closure lemma is derived
for the original nonlinear source map H. -/
theorem actual_smooth_average_derivative
    {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)
    {a b : ℝ} (hab : a≤b) (hsub : Icc a b⊆J)
    {H χ : ℝ×ℝ→ℝ}
    (hH : ContDiffOn ℝ ∞ H (I×ˢJ)) (hχ : ContDiffOn ℝ ∞ χ (I×ˢJ))
    (hZ : ∀ p∈I×ˢJ, partialZ H p≠0)
    (hχedge : ∀ x∈I, χ (x,a)=0 ∧ χ (x,b)=0)
    {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f) {x : ℝ} (hx : x∈I) :
    HasDerivAt (fun y=>∫ z in Icc a b, χ (y,z) • f (H (y,z)))
      (∫ z in Icc a b, transferWeight H χ (x,z) • f (H (x,z))) x := by
  let O := I×ˢJ
  have hO : IsOpen O := hI.prod hJ
  have hdH (p : ℝ×ℝ) (hp : p∈O) : DifferentiableAt ℝ H p :=
    ((hH.differentiableOn (by simp)) p hp).differentiableAt (hO.mem_nhds hp)
  have hdχ (p : ℝ×ℝ) (hp : p∈O) : DifferentiableAt ℝ χ p :=
    ((hχ.differentiableOn (by simp)) p hp).differentiableAt (hO.mem_nhds hp)
  have hfd : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  let F : ℝ×ℝ→ℂ := fun p=>χ p • f (H p)
  let F' : ℝ×ℝ→ℂ := fun p=>
    partialX χ p • f (H p) + (χ p*partialX H p) • deriv f (H p)
  have hA : ContDiffOn ℝ ∞ (fun p=>partialX χ p • f (H p)) O :=
    (contDiffOn_partialX hO hχ).smul (hf.comp_contDiffOn hH)
  have hB : ContDiffOn ℝ ∞ (fun p=>(χ p*partialX H p) • deriv f (H p)) O :=
    (hχ.mul (contDiffOn_partialX hO hH)).smul (hfd.comp_contDiffOn hH)
  have hFc : ContinuousOn F O := (hχ.smul (hf.comp_contDiffOn hH)).continuousOn
  have hF'c : ContinuousOn F' O := (hA.add hB).continuousOn
  have hFder (y : ℝ) (hy : y∈I) (z : ℝ) (hz : z∈J) :
      HasDerivAt (fun t=>F (t,z)) (F' (y,z)) y := by
    have hh := (partialX_hasDerivAt (hdχ (y,z) ⟨hy,hz⟩)).smul
      (((hf.differentiable (by simp)) (H (y,z))).hasDerivAt.scomp y
        (partialX_hasDerivAt (hdH (y,z) ⟨hy,hz⟩)))
    convert hh using 1
    change ((partialX χ (y,z) : ℝ) : ℂ) * f (H (y,z)) +
      ((χ (y,z)*partialX H (y,z) : ℝ) : ℂ) * deriv f (H (y,z)) =
      ((χ (y,z) : ℝ) : ℂ) * (((partialX H (y,z) : ℝ) : ℂ) * deriv f (H (y,z))) +
      ((partialX χ (y,z) : ℝ) : ℂ) * f (H (y,z))
    rw [Complex.ofReal_mul]
    ring
  have hp : I×ˢIcc a b ⊆ O := Set.prod_mono (Subset.refl I) hsub
  have hmain := compact_parameter_integral_hasDerivAt hI isCompact_Icc
    (hFc.mono hp) (hF'c.mono hp) (fun y hy z hz=>hFder y hy z (hsub hz)) hx
  let U : ℝ×ℝ→ℝ := fun p=>χ p*partialX H p/partialZ H p
  have hUs : ContDiffOn ℝ ∞ U O :=
    (hχ.mul (contDiffOn_partialX hO hH)).div (contDiffOn_partialZ hO hH) hZ
  have hdU (p : ℝ×ℝ) (hp : p∈O) : DifferentiableAt ℝ U p :=
    ((hUs.differentiableOn (by simp)) p hp).differentiableAt (hO.mem_nhds hp)
  have hsource := source_derivative_transfer hJ hab hsub
    (contDiffOn_source_section hH hx) (contDiffOn_source_section hχ hx)
    (contDiffOn_source_section (contDiffOn_partialX hO hH) hx)
    (fun z hz=>by rw [(partialZ_hasDerivAt (hdH (x,z) ⟨hx,hz⟩)).deriv]; exact hZ (x,z) ⟨hx,hz⟩)
    (hχedge x hx).1 (hχedge x hx).2 hf
  have hpartU (z : ℝ) (hz : z∈J) :
      deriv (fun t=>χ (x,t)*partialX H (x,t)/deriv (fun v=>H (x,v)) t) z =
        partialZ U (x,z) := by
    have he : (fun t=>χ (x,t)*partialX H (x,t)/deriv (fun v=>H (x,v)) t)
        =ᶠ[𝓝 z] (fun t=>U (x,t)) := by
      filter_upwards [hJ.mem_nhds hz] with t ht
      rw [(partialZ_hasDerivAt (hdH (x,t) ⟨hx,ht⟩)).deriv]
    rw [he.deriv_eq]
    exact (partialZ_hasDerivAt (hdU (x,z) ⟨hx,hz⟩)).deriv
  have hs' : (∫ z in Icc a b, (χ (x,z)*partialX H (x,z)) • deriv f (H (x,z))) =
      -(∫ z in Icc a b, partialZ U (x,z) • f (H (x,z))) := by
    calc
      _ = -(∫ z in Icc a b,
        deriv (fun t=>χ (x,t)*partialX H (x,t)/deriv (fun v=>H (x,v)) t) z • f (H (x,z))) :=
          hsource
      _ = _ := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro z hz
        change _ • f (H (x,z)) = _ • f (H (x,z))
        rw [hpartU z (hsub hz)]
  have hsect {G : ℝ×ℝ→ℂ} (hG : ContinuousOn G O) :
      IntegrableOn (fun z=>G (x,z)) (Icc a b) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz=>⟨hx,hsub hz⟩)
  have hAi := hsect hA.continuousOn
  have hBi := hsect hB.continuousOn
  have hCi := hsect
    ((contDiffOn_partialZ hO hUs).smul (hf.comp_contDiffOn hH)).continuousOn
  have heq : (∫ z in Icc a b, F' (x,z)) =
      ∫ z in Icc a b, transferWeight H χ (x,z) • f (H (x,z)) := by
    calc
      _ = (∫ z in Icc a b, partialX χ (x,z) • f (H (x,z))) +
          (∫ z in Icc a b, (χ (x,z)*partialX H (x,z)) • deriv f (H (x,z))) :=
        integral_add hAi hBi
      _ = (∫ z in Icc a b, partialX χ (x,z) • f (H (x,z))) -
          (∫ z in Icc a b, partialZ U (x,z) • f (H (x,z))) := by rw [hs',sub_eq_add_neg]
      _ = ∫ z in Icc a b,
          (partialX χ (x,z) • f (H (x,z)) - partialZ U (x,z) • f (H (x,z))) :=
        (integral_sub hAi hCi).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro z _hz
        change _ • f (H (x,z)) - _ • f (H (x,z)) =
          (partialX χ (x,z)-partialZ U (x,z)) • f (H (x,z))
        simp only [Complex.real_smul,Complex.ofReal_sub]
        ring
  rw [heq] at hmain
  exact hmain

end
end Resonance.PinnedSmoothing
