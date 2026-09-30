import Resonance.PinnedGeometry

/-! Actual implicit resonance charts.  The function is obtained by the inverse
function theorem applied to the original energy defect, not supplied as data. -/
open Real Filter
open scoped Topology ContDiff
namespace Resonance.PinnedCharts
open Resonance.PinnedGeometry
noncomputable section

abbrev ChartInput := (ℝ × ℝ) × ℝ

def xProjection : ChartInput →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ)
def zProjection : ChartInput →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ)
def yProjection : ChartInput →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ×ℝ) ℝ

def chartFunction (d : ℝ) (p : ChartInput) : ℝ :=
  energyDefect d p.1.1 p.2 p.1.2

def chartDerivative (d : ℝ) (p : ChartInput) : ChartInput →L[ℝ] ℝ :=
  velocity d p.1.1 • xProjection + velocity d p.2 • yProjection -
    velocity d p.1.2 • zProjection -
    velocity d (p.1.1+p.2-p.1.2) • (xProjection+yProjection-zProjection)

theorem signed_omega_contDiff {d : ℝ} (hdL : -(1/2:ℝ)<d) (hdU : d<1/2)
    (n : WithTop ℕ∞) : ContDiff ℝ n (omega d) := by
  apply ContDiff.sqrt
  · fun_prop
  · intro x
    exact ne_of_gt (signed_radicand_pos hdL hdU x)

theorem chartFunction_contDiff {d : ℝ} (hdL : -(1/2:ℝ)<d) (hdU : d<1/2)
    (n : WithTop ℕ∞) : ContDiff ℝ n (chartFunction d) := by
  have h := signed_omega_contDiff hdL hdU n
  unfold chartFunction energyDefect
  fun_prop

theorem chartFunction_hasFDerivAt {d : ℝ} (hdL : -(1/2:ℝ)<d) (hdU : d<1/2)
    (p : ChartInput) : HasFDerivAt (chartFunction d) (chartDerivative d p) p := by
  have hx := (omega_hasDerivAt hdL hdU p.1.1).comp_hasFDerivAt p
    xProjection.hasFDerivAt
  have hy := (omega_hasDerivAt hdL hdU p.2).comp_hasFDerivAt p
    yProjection.hasFDerivAt
  have hz := (omega_hasDerivAt hdL hdU p.1.2).comp_hasFDerivAt p
    zProjection.hasFDerivAt
  have hw := (omega_hasDerivAt hdL hdU (p.1.1+p.2-p.1.2)).comp_hasFDerivAt p
    (xProjection+yProjection-zProjection).hasFDerivAt
  exact ((hx.add hy).sub hz).sub hw

theorem chartFunction_fderiv {d : ℝ} (hdL : -(1/2:ℝ)<d) (hdU : d<1/2)
    (p : ChartInput) : fderiv ℝ (chartFunction d) p = chartDerivative d p :=
  (chartFunction_hasFDerivAt hdL hdU p).fderiv

theorem partial_y_apply (d : ℝ) (p : ChartInput) (b : ℝ) :
    (chartDerivative d p).comp (ContinuousLinearMap.inr ℝ (ℝ×ℝ) ℝ) b =
      (velocity d p.2 - velocity d (p.1.1+p.2-p.1.2))*b := by
  simp [chartDerivative,xProjection,yProjection,zProjection]
  ring

theorem partial_y_invertible {d : ℝ} (hdL : -(1/2:ℝ)<d) (hdU : d<1/2)
    (p : ChartInput) (h : velocity d p.2 ≠ velocity d (p.1.1+p.2-p.1.2)) :
    ((fderiv ℝ (chartFunction d) p).comp
      (ContinuousLinearMap.inr ℝ (ℝ×ℝ) ℝ)).IsInvertible := by
  rw [chartFunction_fderiv hdL hdU]
  let L := (chartDerivative d p).comp (ContinuousLinearMap.inr ℝ (ℝ×ℝ) ℝ)
  have h0 : velocity d p.2 - velocity d (p.1.1+p.2-p.1.2) ≠ 0 := sub_ne_zero.mpr h
  have hi : Function.Injective L := by
    intro a b he
    change L a=L b at he
    simp only [L,partial_y_apply] at he
    exact mul_left_cancel₀ h0 he
  let e : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofBijective L.toLinearMap
      ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  exact ⟨e,rfl⟩

/-- A local analytic branch through each genuine regular quartet. -/
theorem exists_analytic_resonance_branch {d x y z : ℝ}
    (hdL : -(1/2:ℝ)<d) (hdU : d<1/2)
    (he : energyDefect d x y z=0)
    (hy : velocity d y ≠ velocity d (x+y-z)) :
    ∃ H : ℝ×ℝ → ℝ,
      H (x,z)=y ∧ ContDiffAt ℝ ω H (x,z) ∧
      (∀ᶠ p in 𝓝 (x,z), energyDefect d p.1 (H p) p.2=0) := by
  let p : ChartInput := ((x,z),y)
  have hc : ContDiffAt ℝ ω (chartFunction d) p :=
    (chartFunction_contDiff hdL hdU ω).contDiffAt
  have hi := partial_y_invertible hdL hdU p hy
  let H := hc.implicitFunction (by simp) hi
  refine ⟨H,hc.implicitFunction_apply_self (by simp) hi,
    hc.contDiffAt_implicitFunction (by simp) hi,?_⟩
  have ht := hc.eventually_apply_implicitFunction (by simp) hi
  change ∀ᶠ q in 𝓝 (x,z), chartFunction d (q,H q)=chartFunction d p at ht
  simpa only [chartFunction,p,he] using ht


theorem branch_z_derivative {d x y z : ℝ} {H : ℝ×ℝ→ℝ}
    (hdL : -(1/2:ℝ)<d) (hdU : d<1/2)
    (hbase : H (x,z)=y) (hH : ContDiffAt ℝ ω H (x,z))
    (hres : ∀ᶠ p in 𝓝 (x,z), energyDefect d p.1 (H p) p.2=0)
    (hy : velocity d y ≠ velocity d (x+y-z)) :
    deriv (fun t => H (x,t)) z =
      (velocity d z-velocity d (x+y-z))/(velocity d y-velocity d (x+y-z)) := by
  have hpair : HasDerivAt (fun t : ℝ => (x,t)) (0,1) z :=
    (hasDerivAt_const z x).prodMk (hasDerivAt_id z)
  have hHz : DifferentiableAt ℝ (fun t : ℝ => H (x,t)) z :=
    (hH.differentiableAt (by simp)).comp z hpair.differentiableAt
  let a := deriv (fun t => H (x,t)) z
  have hda : HasDerivAt (fun t => H (x,t)) a z := hHz.hasDerivAt
  have hr : (fun t => energyDefect d x (H (x,t)) t) =ᶠ[𝓝 z] (fun _ => 0) :=
    hpair.continuousAt.tendsto.eventually hres
  have hzero : HasDerivAt (fun t => energyDefect d x (H (x,t)) t) 0 z :=
    (hasDerivAt_const z (0:ℝ)).congr_of_eventuallyEq hr
  have hy' := (omega_hasDerivAt hdL hdU (H (x,z))).comp z hda
  have hw' := (omega_hasDerivAt hdL hdU (x+H (x,z)-z)).comp (h := fun t => x+H (x,t)-t) z
    ((hda.const_add x).sub (hasDerivAt_id z))
  have hc := (((hasDerivAt_const z (omega d x)).add hy').sub
    (omega_hasDerivAt hdL hdU z)).sub hw'
  have he := hc.unique hzero
  rw [hbase] at he
  change a = _
  apply (eq_div_iff (sub_ne_zero.mpr hy)).mpr
  nlinarith only [he]

theorem branch_w_derivative {x z : ℝ} {H : ℝ×ℝ→ℝ}
    (hH : ContDiffAt ℝ ω H (x,z)) :
    deriv (fun t => x+H (x,t)-t) z = deriv (fun t => H (x,t)) z - 1 := by
  have hpair : HasDerivAt (fun t : ℝ => (x,t)) (0,1) z :=
    (hasDerivAt_const z x).prodMk (hasDerivAt_id z)
  have hHz : DifferentiableAt ℝ (fun t : ℝ => H (x,t)) z :=
    (hH.differentiableAt (by simp)).comp z hpair.differentiableAt
  exact ((hHz.hasDerivAt.const_add x).sub (hasDerivAt_id z)).deriv

/-- Both non-target graph maps really have nonzero derivatives in the averaging
variable.  The analytic branch and energy identity are constructed from the
actual nondegenerate quartet at every circle target. -/
theorem every_target_analytic_branch {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (x : ℝ) :
    ∃ y z : ℝ, ∃ H : ℝ×ℝ→ℝ,
      H (x,z)=y ∧ ContDiffAt ℝ ω H (x,z) ∧
      (∀ᶠ p in 𝓝 (x,z), energyDefect d p.1 (H p) p.2=0) ∧
      velocity d y ≠ velocity d (x+y-z) ∧
      deriv (fun t => H (x,t)) z ≠ 0 ∧
      deriv (fun t => x+H (x,t)-t) z ≠ 0 := by
  obtain ⟨y,z,he,hyz,hyw,hzw⟩ := nondegenerateAt_every_target hd0 hdU x
  have hdL : -(1/2:ℝ)<d := by linarith
  obtain ⟨H,hbase,hH,hres⟩ := exists_analytic_resonance_branch hdL hdU he hyw
  have hz := branch_z_derivative hdL hdU hbase hH hres hyw
  refine ⟨y,z,H,hbase,hH,hres,hyw,?_,?_⟩
  · rw [hz]
    exact div_ne_zero (sub_ne_zero.mpr hzw) (sub_ne_zero.mpr hyw)
  · rw [branch_w_derivative hH,hz]
    intro h
    have heq : velocity d z - velocity d (x+y-z) =
      velocity d y - velocity d (x+y-z) := by
      apply (div_eq_one_iff_eq (sub_ne_zero.mpr hyw)).mp
      linarith only [h]
    apply hyz
    linarith only [heq]


def zDifferential (H : ℝ×ℝ→ℝ) (p : ℝ×ℝ) : ℝ := fderiv ℝ H p (0,1)

theorem zDifferential_eq_deriv {H : ℝ×ℝ→ℝ} {x z : ℝ}
    (hH : DifferentiableAt ℝ H (x,z)) :
    zDifferential H (x,z)=deriv (fun t => H (x,t)) z := by
  have hp : HasDerivAt (fun t : ℝ => (x,t)) (0,1) z :=
    (hasDerivAt_const z x).prodMk (hasDerivAt_id z)
  exact (hH.hasFDerivAt.comp_hasDerivAt z hp).deriv.symm

theorem zDifferential_continuousAt {H : ℝ×ℝ→ℝ} {p : ℝ×ℝ}
    (hH : ContDiffAt ℝ ω H p) : ContinuousAt (zDifferential H) p := by
  unfold zDifferential
  exact (hH.continuousAt_fderiv (by simp)).clm_apply continuousAt_const

theorem velocity_continuous {d : ℝ} (hdL : -(1/2:ℝ)<d) (hdU : d<1/2) :
    Continuous (velocity d) := by
  unfold velocity
  exact (continuous_const.mul continuous_sin).div
    (signed_omega_contDiff hdL hdU 0).continuous
    (fun x => ne_of_gt (signed_omega_pos hdL hdU x))

theorem eventually_abs_lower {α : Type*} [TopologicalSpace α]
    {f : α→ℝ} {a : α} (hf : ContinuousAt f a) (ha : f a≠0) :
    ∀ᶠ x in 𝓝 a, |f a|/2 < |f x| := by
  have ho : IsOpen {q : ℝ | |f a|/2 < |q|} :=
    isOpen_lt continuous_const continuous_abs
  have hm : f a ∈ {q : ℝ | |f a|/2 < |q|} := by
    have hpos := abs_pos.mpr ha
    change |f a|/2 < |f a|
    linarith
  exact hf.tendsto.eventually (ho.mem_nhds hm)

/-- The complete local geometry required before averaging: an actual open
rectangle, analytic branch, exact original resonance, and one positive common
lower bound for the coarea denominator and both averaging derivatives. -/
theorem every_target_uniform_chart {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (x : ℝ) :
    ∃ y z : ℝ, ∃ H : ℝ×ℝ→ℝ, ∃ r κ : ℝ, 0<r ∧ 0<κ ∧ H (x,z)=y ∧
      ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r) ∧
      ∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r,
        energyDefect d p.1 (H p) p.2=0 ∧
        κ ≤ |velocity d (H p)-velocity d (p.1+H p-p.2)| ∧
        κ ≤ |zDifferential H p| ∧ κ ≤ |zDifferential H p-1| := by
  obtain ⟨y,z,H,hbase,hH,hres,hgap,hz,hw⟩ := every_target_analytic_branch hd0 hdU x
  have hdL : -(1/2:ℝ)<d := by linarith
  let g : ℝ×ℝ→ℝ := fun p => velocity d (H p)-velocity d (p.1+H p-p.2)
  have hgc : ContinuousAt g (x,z) := by
    apply ContinuousAt.sub
    · exact (velocity_continuous hdL hdU).continuousAt.comp hH.continuousAt
    · exact (velocity_continuous hdL hdU).continuousAt.comp
        ((continuousAt_fst.add hH.continuousAt).sub continuousAt_snd)
  have hg0 : g (x,z)≠0 := by
    dsimp [g]
    rw [hbase]
    exact sub_ne_zero.mpr hgap
  have hdz := zDifferential_eq_deriv (hH.differentiableAt (by simp))
  have hz0 : zDifferential H (x,z)≠0 := by rwa [hdz]
  have hw0 : zDifferential H (x,z)-1≠0 := by
    rwa [branch_w_derivative hH,←hdz] at hw
  have hzc := zDifferential_continuousAt hH
  have hwc : ContinuousAt (fun p => zDifferential H p - 1) (x,z) :=
    hzc.sub continuousAt_const
  let κ := min (|g (x,z)|/2)
    (min (|zDifferential H (x,z)|/2) (|zDifferential H (x,z)-1|/2))
  have hk : 0<κ := by
    exact lt_min (half_pos (abs_pos.mpr hg0))
      (lt_min (half_pos (abs_pos.mpr hz0)) (half_pos (abs_pos.mpr hw0)))
  have hevent : ∀ᶠ p in 𝓝 (x,z),
      ContDiffAt ℝ ω H p ∧ energyDefect d p.1 (H p) p.2=0 ∧
        κ ≤ |g p| ∧ κ ≤ |zDifferential H p| ∧ κ ≤ |zDifferential H p-1| := by
    filter_upwards [hH.eventually (by simp),hres,
      eventually_abs_lower hgc hg0,eventually_abs_lower hzc hz0,
      eventually_abs_lower hwc hw0] with p hHp hr hg hz' hw'
    refine ⟨hHp,hr,?_,?_,?_⟩
    · exact (min_le_left _ _).trans hg.le
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans hz'.le
    · exact ((min_le_right _ _).trans (min_le_right _ _)).trans hw'.le
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨y,z,H,r,κ,hr,hk,hbase,?_,?_⟩
  · intro p hp
    have hb : p ∈ Metric.ball (x,z) r := by
      simpa only [←ball_prod_same] using hp
    exact ((hsub hb).1.of_le (show (∞ : WithTop ℕ∞)≤ω by simp)).contDiffWithinAt
  · intro p hp
    have hb : p ∈ Metric.ball (x,z) r := by
      simpa only [←ball_prod_same] using hp
    exact (hsub hb).2

end
end Resonance.PinnedCharts
