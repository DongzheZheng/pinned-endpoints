import Resonance.PinnedCharts
import Resonance.PinnedElimination
import Resonance.PinnedODE
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
Classification work for the original pinned resonance. The invariant input is
the complete four-parent identity on the actual three-source nondegenerate
resonances. Differential identities below are derived from genuine local
branches; no ODE is included as an invariant hypothesis.
-/
open Real Filter Set
open scoped Topology ContDiff

namespace Resonance.PinnedClassification
open PinnedGeometry PinnedCharts
noncomputable section

def smoothInvariant (d : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x y z : ℝ, energyDefect d x y z = 0 →
    velocity d y ≠ velocity d z → velocity d y ≠ velocity d (x+y-z) →
    velocity d z ≠ velocity d (x+y-z) →
      φ x + φ y = φ z + φ (x+y-z)

def transverseIdentity (φ : ℝ → ℝ) (x : ℝ) (y : ℝ → ℝ) : Prop :=
  (fun t => φ x + φ (y t)) =ᶠ[nhds 0]
    (fun t => φ (-x+t) + φ (2*x+y t-t))

theorem transverse_nth_identity (φ y : ℝ → ℝ) (x : ℝ) (n : ℕ) (hn : 0 < n)
    (hφ : ContDiff ℝ n φ) (hy : ContDiffAt ℝ n y 0)
    (hi : transverseIdentity φ x y) :
    iteratedDeriv n (φ ∘ y) 0 = iteratedDeriv n (fun t => φ (-x+t)) 0 +
      iteratedDeriv n (fun t => φ (2*x+y t-t)) 0 := by
  have hz : ContDiffAt ℝ n (fun t : ℝ => -x+t) 0 := by fun_prop
  have hw : ContDiffAt ℝ n (fun t : ℝ => 2*x+y t-t) 0 := by fun_prop
  have h := hi.iteratedDeriv_eq n
  rw [iteratedDeriv_const_add hn] at h
  have hadd := iteratedDeriv_fun_add (hφ.contDiffAt.comp 0 hz) (hφ.contDiffAt.comp 0 hw)
  change iteratedDeriv n (fun t => φ (-x+t) + φ (2*x+y t-t)) 0 = _ at hadd
  rw [hadd] at h
  exact h

theorem transverse_second_identity (φ y : ℝ → ℝ) (x : ℝ)
    (hφ : ContDiff ℝ 2 φ) (hy : ContDiffAt ℝ 2 y 0)
    (hi : transverseIdentity φ x y) :
    (deriv y 0)^2 * iteratedDeriv 2 φ (y 0) + iteratedDeriv 2 y 0 * deriv φ (y 0) =
      iteratedDeriv 2 φ (-x) +
      ((deriv y 0 - 1)^2 * iteratedDeriv 2 φ (2*x+y 0) +
        iteratedDeriv 2 y 0 * deriv φ (2*x+y 0)) := by
  have hz : ContDiffAt ℝ 2 (fun t : ℝ => -x+t) 0 := by fun_prop
  have hw : ContDiffAt ℝ 2 (fun t : ℝ => 2*x+y t-t) 0 := by fun_prop
  have h := transverse_nth_identity φ y x 2 (by norm_num) hφ hy hi
  have hd : DifferentiableAt ℝ y 0 := hy.differentiableAt (by norm_num)
  rw [iteratedDeriv_scomp_two hφ.contDiffAt hy] at h
  change _ = iteratedDeriv 2 (φ ∘ (fun t : ℝ => -x+t)) 0 +
    iteratedDeriv 2 (φ ∘ (fun t : ℝ => 2*x+y t-t)) 0 at h
  rw [iteratedDeriv_scomp_two hφ.contDiffAt hz,
    iteratedDeriv_scomp_two hφ.contDiffAt hw] at h
  have hw1 : deriv (fun t : ℝ => 2*x+y t-t) 0 = deriv y 0 - 1 := by
    exact ((hd.hasDerivAt.const_add (2*x)).sub (hasDerivAt_id 0)).deriv
  have hw2 : iteratedDeriv 2 (fun t : ℝ => 2*x+y t-t) 0 = iteratedDeriv 2 y 0 := by
    change iteratedDeriv 2 (fun t => (2*x+y t) - id t) 0 = _
    rw [iteratedDeriv_fun_sub (contDiffAt_const.add hy) contDiffAt_id,
      iteratedDeriv_const_add (by norm_num)]
    simp [iteratedDeriv_id]
  have hz1 : deriv (fun t : ℝ => -x+t) 0 = 1 := (hasDerivAt_id 0 |>.const_add (-x)).deriv
  have hz2 : iteratedDeriv 2 (fun t : ℝ => -x+t) 0 = 0 := by
    rw [iteratedDeriv_const_add (by norm_num)]
    simp [iteratedDeriv_fun_id]
  simpa [hw1,hw2,hz1,hz2,smul_eq_mul] using h

theorem transverse_first_identity (φ y : ℝ → ℝ) (x : ℝ)
    (hφ : ContDiff ℝ 1 φ) (hy : ContDiffAt ℝ 1 y 0)
    (hi : transverseIdentity φ x y) :
    deriv φ (y 0) * deriv y 0 = deriv φ (-x) +
      deriv φ (2*x+y 0) * (deriv y 0-1) := by
  have hd := hy.differentiableAt (by norm_num)
  have hfd := hφ.differentiable (by norm_num)
  have hyφ := (hfd (y 0)).hasDerivAt.comp 0 hd.hasDerivAt
  have hzφ := (hfd (-x+0)).hasDerivAt.comp 0 ((hasDerivAt_id 0).const_add (-x))
  have hw : HasDerivAt (fun t : ℝ => 2*x+y t-t) (deriv y 0-1) 0 :=
    (hd.hasDerivAt.const_add (2*x)).sub (hasDerivAt_id 0)
  have hwφ := (hfd (2*x+y 0-0)).hasDerivAt.comp (h := fun t : ℝ => 2*x+y t-t) 0 hw
  have h := hi.deriv_eq
  have hleft := (hyφ.const_add (φ x)).deriv
  change deriv (fun t => φ x+φ (y t)) 0 = _ at hleft
  rw [hleft] at h
  have hright := (hzφ.add hwφ).deriv
  change deriv (fun t => φ (-x+t)+φ (2*x+y t-t)) 0 = _ at hright
  rw [hright] at h
  simpa only [mul_one,add_zero,sub_zero] using h

theorem transverse_third_identity (φ y : ℝ → ℝ) (x : ℝ)
    (hφ : ContDiff ℝ 3 φ) (hy : ContDiffAt ℝ 3 y 0)
    (hi : transverseIdentity φ x y) :
    (deriv y 0)^3 * iteratedDeriv 3 φ (y 0) +
      3 * iteratedDeriv 2 y 0 * deriv y 0 * iteratedDeriv 2 φ (y 0) +
      iteratedDeriv 3 y 0 * deriv φ (y 0) =
    iteratedDeriv 3 φ (-x) +
      ((deriv y 0 - 1)^3 * iteratedDeriv 3 φ (2*x+y 0) +
        3 * iteratedDeriv 2 y 0 * (deriv y 0 - 1) * iteratedDeriv 2 φ (2*x+y 0) +
        iteratedDeriv 3 y 0 * deriv φ (2*x+y 0)) := by
  have hz : ContDiffAt ℝ 3 (fun t : ℝ => -x+t) 0 := by fun_prop
  have hw : ContDiffAt ℝ 3 (fun t : ℝ => 2*x+y t-t) 0 := by fun_prop
  have h := transverse_nth_identity φ y x 3 (by norm_num) hφ hy hi
  have hd : DifferentiableAt ℝ y 0 := hy.differentiableAt (by norm_num)
  rw [iteratedDeriv_scomp_three hφ.contDiffAt hy] at h
  change _ = iteratedDeriv 3 (φ ∘ (fun t : ℝ => -x+t)) 0 +
    iteratedDeriv 3 (φ ∘ (fun t : ℝ => 2*x+y t-t)) 0 at h
  rw [iteratedDeriv_scomp_three hφ.contDiffAt hz,
    iteratedDeriv_scomp_three hφ.contDiffAt hw] at h
  have hw1 : deriv (fun t : ℝ => 2*x+y t-t) 0 = deriv y 0 - 1 :=
    ((hd.hasDerivAt.const_add (2*x)).sub (hasDerivAt_id 0)).deriv
  have hwn (n : ℕ) (hn : 2 ≤ n) (hn3 : n ≤ 3) :
      iteratedDeriv n (fun t : ℝ => 2*x+y t-t) 0 = iteratedDeriv n y 0 := by
    have hyn : ContDiffAt ℝ n y 0 := hy.of_le (by exact_mod_cast hn3)
    change iteratedDeriv n (fun t => (2*x+y t) - id t) 0 = _
    rw [iteratedDeriv_fun_sub (contDiffAt_const.add hyn) contDiffAt_id,
      iteratedDeriv_const_add (by omega)]
    simp [iteratedDeriv_id, show n ≠ 1 by omega, show n ≠ 0 by omega]
  have hz1 : deriv (fun t : ℝ => -x+t) 0 = 1 := (hasDerivAt_id 0 |>.const_add (-x)).deriv
  have hzn (n : ℕ) (hn : 2 ≤ n) : iteratedDeriv n (fun t : ℝ => -x+t) 0 = 0 := by
    rw [iteratedDeriv_const_add (by omega)]
    simp [iteratedDeriv_fun_id, show n ≠ 1 by omega, show n ≠ 0 by omega]
  simpa [hw1,hwn 2 le_rfl (by norm_num),hwn 3 (by norm_num) le_rfl,hz1,hzn 2 le_rfl,hzn 3 (by norm_num),
    smul_eq_mul,mul_assoc] using h

theorem exists_symmetric_transverse {d x : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (hs : sin x ≠ 0) (hc : cos x ≠ 0) :
    ∃ y : ℝ→ℝ, y 0=Real.pi-x ∧ ContDiffAt ℝ ω y 0 ∧
      transverseIdentity (omega d) x y ∧
      ∀ φ : ℝ→ℝ, smoothInvariant d φ → transverseIdentity φ x y := by
  have hdL : -(1/2:ℝ)<d := by linarith
  obtain ⟨hyz,hyw,hzw⟩ := symmetric_velocity_nondegenerate hd0 hdU hs hc
  have heq : x+(Real.pi-x)-(-x)=Real.pi+x := by ring
  obtain ⟨H,hH0,hH,hres⟩ := exists_analytic_resonance_branch hdL hdU
    (symmetric_resonance d x) (by simpa only [heq] using hyw)
  let p : ℝ→ℝ×ℝ := fun t => (x,-x+t)
  have hp : ContDiffAt ℝ ω p 0 := by dsimp [p]; fun_prop
  have hp0 : p 0=(x,-x) := by simp [p]
  let y : ℝ→ℝ := H ∘ p
  have hy0 : y 0=Real.pi-x := by simpa [y,p] using hH0
  have hy : ContDiffAt ℝ ω y 0 := by
    exact (show ContDiffAt ℝ ω H (p 0) by simpa only [hp0] using hH).comp 0 hp
  have hr : ∀ᶠ t in 𝓝 0, energyDefect d x (y t) (-x+t)=0 := by
    exact hp.continuousAt.tendsto.eventually (by simpa only [hp0] using hres)
  have hwc : ContinuousAt (fun t : ℝ => 2*x+y t-t) 0 := by fun_prop
  have hzc : ContinuousAt (fun t : ℝ => -x+t) 0 := by fun_prop
  have vy := (velocity_continuous hdL hdU).continuousAt.comp hy.continuousAt
  have vz := (velocity_continuous hdL hdU).continuousAt.comp hzc
  have vw := (velocity_continuous hdL hdU).continuousAt.comp hwc
  have hw0 : 2*x+y 0-0=Real.pi+x := by rw [hy0]; ring
  have ez : ∀ᶠ t in 𝓝 0, velocity d (y t) ≠ velocity d (-x+t) := by
    have h0 : velocity d (y 0)-velocity d (-x+0) ≠ 0 := by
      simpa only [hy0,add_zero] using sub_ne_zero.mpr hyz
    filter_upwards [eventually_abs_lower (vy.sub vz) h0] with t ht
    exact sub_ne_zero.mp (abs_pos.mp (lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by norm_num)) ht))
  have ew : ∀ᶠ t in 𝓝 0, velocity d (y t) ≠ velocity d (2*x+y t-t) := by
    have h0 : velocity d (y 0)-velocity d (2*x+y 0-0) ≠ 0 := by
      simpa only [hy0,show 2*x+(Real.pi-x)-0=Real.pi+x by ring] using sub_ne_zero.mpr hyw
    filter_upwards [eventually_abs_lower (vy.sub vw) h0] with t ht
    exact sub_ne_zero.mp (abs_pos.mp (lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by norm_num)) ht))
  have ezw : ∀ᶠ t in 𝓝 0, velocity d (-x+t) ≠ velocity d (2*x+y t-t) := by
    have h0 : velocity d (-x+0)-velocity d (2*x+y 0-0) ≠ 0 := by
      simpa only [add_zero,hw0] using sub_ne_zero.mpr hzw
    filter_upwards [eventually_abs_lower (vz.sub vw) h0] with t ht
    exact sub_ne_zero.mp (abs_pos.mp (lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by norm_num)) ht))
  refine ⟨y,hy0,hy,?_,?_⟩
  · filter_upwards [hr] with t ht
    dsimp [energyDefect] at ht
    have hw : x+y t-(-x+t)=2*x+y t-t := by ring
    rw [hw] at ht
    linarith
  · intro φ hi
    filter_upwards [hr,ez,ew,ezw] with t ht hz hw hzw
    have he : x+y t-(-x+t)=2*x+y t-t := by ring
    simpa only [he] using hi x (y t) (-x+t) ht hz (by simpa only [he] using hw)
      (by simpa only [he] using hzw)

theorem odd_symmetric_values {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hi : smoothInvariant d φ) (ho : ∀ t, φ (-t) = -φ t)
    (hp : Function.Periodic φ (2*Real.pi)) :
    φ (Real.pi-x) = -φ x ∧ φ (Real.pi+x)=φ x := by
  obtain ⟨hyz,hyw,hzw⟩ := symmetric_velocity_nondegenerate hd0 hdU hs hc
  have hw : x+(Real.pi-x)-(-x)=Real.pi+x := by ring
  have he := hi x (Real.pi-x) (-x) (symmetric_resonance d x) hyz
    (by simpa only [hw] using hyw) (by simpa only [hw] using hzw)
  rw [hw,ho x] at he
  have hper := hp (-(Real.pi-x))
  have hsimp : -(Real.pi-x)+2*Real.pi=Real.pi+x := by ring
  rw [hsimp,ho (Real.pi-x)] at hper
  constructor <;> linarith

theorem odd_symmetric_local_identity {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hi : smoothInvariant d φ) (ho : ∀ t, φ (-t) = -φ t)
    (hp : Function.Periodic φ (2*Real.pi)) :
    (fun t => φ (Real.pi-t)) =ᶠ[𝓝 x] (fun t => -φ t) ∧
    (fun t => φ (Real.pi+t)) =ᶠ[𝓝 x] φ := by
  have es := eventually_abs_lower continuous_sin.continuousAt hs
  have ec := eventually_abs_lower continuous_cos.continuousAt hc
  have ev : ∀ᶠ t in 𝓝 x, φ (Real.pi-t) = -φ t ∧ φ (Real.pi+t)=φ t := by
    filter_upwards [es,ec] with t ht hu
    have hst : sin t≠0 := abs_pos.mp (lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by norm_num)) ht)
    have hct : cos t≠0 := abs_pos.mp (lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by norm_num)) hu)
    exact odd_symmetric_values hd0 hdU hst hct hi ho hp
  exact ⟨ev.mono fun _ h=>h.1,ev.mono fun _ h=>h.2⟩

theorem odd_symmetric_jets {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hi : smoothInvariant d φ) (ho : ∀ t, φ (-t) = -φ t)
    (hp : Function.Periodic φ (2*Real.pi)) (n : ℕ) :
    (-1:ℝ)^n * iteratedDeriv n φ (Real.pi-x) = -iteratedDeriv n φ x ∧
    iteratedDeriv n φ (Real.pi+x) = iteratedDeriv n φ x ∧
    (-1:ℝ)^n * iteratedDeriv n φ (-x) = -iteratedDeriv n φ x := by
  obtain ⟨h1,h2⟩ := odd_symmetric_local_identity hd0 hdU hs hc hi ho hp
  have h3 : (fun t => φ (-t)) =ᶠ[𝓝 x] (fun t => -φ t) := Filter.Eventually.of_forall ho
  have e1 := h1.iteratedDeriv_eq n
  have e2 := h2.iteratedDeriv_eq n
  have e3 := h3.iteratedDeriv_eq n
  simp only [iteratedDeriv_comp_const_sub,iteratedDeriv_fun_neg,smul_eq_mul] at e1
  simp only [iteratedDeriv_comp_const_add] at e2
  simp only [iteratedDeriv_comp_neg,iteratedDeriv_fun_neg,smul_eq_mul] at e3
  exact ⟨e1,e2,e3⟩

theorem odd_second_derivative_generic {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hφ : ContDiff ℝ 2 φ) (hi : smoothInvariant d φ)
    (ho : ∀ t, φ (-t) = -φ t) (hp : Function.Periodic φ (2*Real.pi)) :
    iteratedDeriv 2 φ x = 0 := by
  have hdL : -(1/2:ℝ)<d := by linarith
  obtain ⟨y,hy0,hy,hew,hiy⟩ := exists_symmetric_transverse hd0 hdU hs hc
  have ey := transverse_first_identity (omega d) y x
    (signed_omega_contDiff hdL hdU 1) (hy.of_le (by simp)) hew
  have ep := transverse_second_identity φ y x hφ (hy.of_le (by simp)) (hiy φ hi)
  have j1 := odd_symmetric_jets hd0 hdU hs hc hi ho hp 1
  have j2 := odd_symmetric_jets hd0 hdU hs hc hi ho hp 2
  have hw : 2*x+y 0=Real.pi+x := by rw [hy0]; ring
  rw [hw,hy0] at ep ey
  simp only [omega_deriv hdL hdU,velocity_neg,velocity_pi_add] at ey
  norm_num [iteratedDeriv_one] at j1 j2
  obtain ⟨hyz,hyw,hzw⟩ := symmetric_velocity_nondegenerate hd0 hdU hs hc
  simp only [velocity_neg,velocity_pi_add] at hyz hyw hzw
  have hα0 : deriv y 0 ≠ 0 := by
    intro hz
    rw [hz] at ey
    apply hzw
    linarith
  have hα1 : deriv y 0 - 1 ≠ 0 := by
    intro hz
    have hone : deriv y 0=1 := by linarith
    rw [hone] at ey
    apply hyz
    linarith
  have hj1a : deriv φ (Real.pi-x)=deriv φ x := by linarith [j1.1]
  have hj2a : iteratedDeriv 2 φ (Real.pi-x)= -iteratedDeriv 2 φ x := j2.1
  have hj2m : iteratedDeriv 2 φ (-x)= -iteratedDeriv 2 φ x := j2.2.2
  rw [hj1a,j1.2.1,hj2a,j2.2.1,hj2m] at ep
  have hz : (2*(deriv y 0)*(deriv y 0-1))*iteratedDeriv 2 φ x=0 := by nlinarith [ep]
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) hα0) hα1)

theorem generic_symmetric_dense : Dense {x : ℝ | sin x≠0 ∧ cos x≠0} := by
  have hs : {x : ℝ | sin x=0}.Countable := by
    apply (Set.countable_range (fun n : ℤ => (n:ℝ)*Real.pi)).mono
    intro x hx
    exact sin_eq_zero_iff.mp hx
  have hc : {x : ℝ | cos x=0}.Countable := by
    apply (Set.countable_range (fun n : ℤ => (2*(n:ℝ)+1)*Real.pi/2)).mono
    intro x hx
    obtain ⟨n,hn⟩ := cos_eq_zero_iff.mp hx
    exact ⟨n,hn.symm⟩
  have h := (hs.union hc).dense_compl ℝ
  simpa only [Set.compl_union,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_setOf_eq,ne_eq] using h

theorem odd_second_derivative_zero {d : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 2 φ)
    (hi : smoothInvariant d φ) (ho : ∀ t, φ (-t) = -φ t)
    (hp : Function.Periodic φ (2*Real.pi)) :
    ∀ x, iteratedDeriv 2 φ x = 0 := by
  have hc := hφ.continuous_iteratedDeriv' 2
  have he : Set.EqOn (iteratedDeriv 2 φ) (fun _=>0) {x : ℝ | sin x≠0 ∧ cos x≠0} := by
    intro x hx
    exact odd_second_derivative_generic hd0 hdU hx.1 hx.2 hφ hi ho hp
  have hall := he.closure hc continuous_const
  intro x
  exact hall (generic_symmetric_dense x)

theorem odd_invariant_eq_zero {d : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 2 φ)
    (hi : smoothInvariant d φ) (ho : ∀ t, φ (-t) = -φ t)
    (hp : Function.Periodic φ (2*Real.pi)) : ∀ x, φ x=0 := by
  have hdd : ∀x, deriv (deriv φ) x=0 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_one] using
      odd_second_derivative_zero hd0 hdU hφ hi ho hp
  have hder : Differentiable ℝ (deriv φ) := by
    simpa only [iteratedDeriv_one] using hφ.differentiable_iteratedDeriv 1 (by norm_num)
  have hconst := is_const_of_deriv_eq_zero hder hdd
  let A := deriv φ 0
  have hf := hφ.differentiable (by norm_num)
  have hlin : Differentiable ℝ (fun x=>φ x-A*x) := by fun_prop
  have hlin' : ∀x, deriv (fun x=>φ x-A*x) x=0 := by
    intro x
    have hh := ((hf x).hasDerivAt.sub ((hasDerivAt_id x).const_mul A)).deriv
    change deriv (fun t=>φ t-A*t) x = _ at hh
    rw [hh]
    dsimp [A]
    rw [hconst x 0]
    ring
  have haff := is_const_of_deriv_eq_zero hlin hlin'
  have hzero : φ 0=0 := by have h:=ho 0; simp only [neg_zero] at h; linarith
  have hperiod := hp 0
  have hz := haff (2*Real.pi) 0
  simp only [zero_add,mul_zero,sub_zero,hzero] at hperiod hz
  have hA : A=0 := by nlinarith [Real.pi_pos]
  intro x
  have h:=haff x 0
  simpa only [hA,zero_mul,sub_zero,hzero] using h

theorem even_reflection_jets {φ : ℝ→ℝ}
    (he : ∀ t, φ (-t)=φ t) (hp : Function.Periodic φ (2*Real.pi))
    (x : ℝ) (n : ℕ) :
    (-1:ℝ)^n * iteratedDeriv n φ (-x)=iteratedDeriv n φ x ∧
    iteratedDeriv n φ (Real.pi+x)=(-1:ℝ)^n * iteratedDeriv n φ (Real.pi-x) := by
  have e1 : (fun t=>φ (-t)) =ᶠ[𝓝 x] φ := Filter.Eventually.of_forall he
  have e2 : (fun t=>φ (Real.pi+t)) =ᶠ[𝓝 x] (fun t=>φ (Real.pi-t)) := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hp (t-Real.pi)
    have ha : t-Real.pi+2*Real.pi=Real.pi+t := by ring
    have hb : t-Real.pi=-(Real.pi-t) := by ring
    rw [ha,hb,he] at h
    exact h
  have j1 := e1.iteratedDeriv_eq n
  have j2 := e2.iteratedDeriv_eq n
  simp only [iteratedDeriv_comp_neg,smul_eq_mul] at j1
  simp only [iteratedDeriv_comp_const_add,iteratedDeriv_comp_const_sub,smul_eq_mul] at j2
  exact ⟨j1,j2⟩

theorem even_derivative_velocity_relation {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hφ : ContDiff ℝ 1 φ) (hi : smoothInvariant d φ)
    (he : ∀ t, φ (-t)=φ t) (hp : Function.Periodic φ (2*Real.pi)) :
    velocity d (Real.pi-x) * deriv φ x = velocity d x * deriv φ (Real.pi-x) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  obtain ⟨y,hy0,hy,hew,hiy⟩ := exists_symmetric_transverse hd0 hdU hs hc
  have ey := transverse_first_identity (omega d) y x
    (signed_omega_contDiff hdL hdU 1) (hy.of_le (by simp)) hew
  have ep := transverse_first_identity φ y x hφ (hy.of_le (by simp)) (hiy φ hi)
  have jp := even_reflection_jets he hp x 1
  have hw : 2*x+y 0=Real.pi+x := by rw [hy0]; ring
  rw [hw,hy0] at ey ep
  simp only [omega_deriv hdL hdU,velocity_neg,velocity_pi_add] at ey
  norm_num [iteratedDeriv_one] at jp
  have hm : deriv φ (-x)= -deriv φ x := by linarith [jp.1]
  rw [hm,jp.2] at ep
  linear_combination velocity d (Real.pi-x)*ep - deriv φ (Real.pi-x)*ey

def evenQuotient (d : ℝ) (φ : ℝ→ℝ) (x : ℝ) : ℝ := deriv φ x / velocity d x

theorem velocity_ne_zero {d x : ℝ} (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) :
    velocity d x≠0 := by
  exact div_ne_zero (mul_ne_zero (ne_of_gt hd0) hs)
    (ne_of_gt (signed_omega_pos (by linarith) hdU x))

theorem even_quotient_reflection {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hφ : ContDiff ℝ 1 φ) (hi : smoothInvariant d φ)
    (he : ∀ t, φ (-t)=φ t) (hp : Function.Periodic φ (2*Real.pi)) :
    evenQuotient d φ (Real.pi-x)=evenQuotient d φ x := by
  have ha := velocity_ne_zero hd0 hdU hs
  have hb := velocity_ne_zero hd0 hdU (x:=Real.pi-x) (by simpa only [sin_pi_sub] using hs)
  apply (div_eq_div_iff hb ha).mpr
  have hh := even_derivative_velocity_relation hd0 hdU hs hc hφ hi he hp
  nlinarith only [hh]

theorem velocity_contDiff {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (n : WithTop ℕ∞) : ContDiff ℝ n (velocity d) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hv : velocity d=deriv (omega d) := by funext x; exact (omega_deriv hdL hdU x).symm
  rw [hv]
  exact (signed_omega_contDiff hdL hdU (n+1)).deriv'

theorem even_quotient_contDiffAt {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hφ : ContDiff ℝ 3 φ) :
    ContDiffAt ℝ 2 (evenQuotient d φ) x := by
  exact (hφ.contDiffAt.derivWithin (by norm_num)).div
    (velocity_contDiff hd0 hdU 2).contDiffAt (velocity_ne_zero hd0 hdU hs)

theorem quotient_product_jets {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hφ : ContDiff ℝ 3 φ) :
    iteratedDeriv 2 φ x = deriv (velocity d) x * evenQuotient d φ x +
      velocity d x * deriv (evenQuotient d φ) x ∧
    iteratedDeriv 3 φ x = iteratedDeriv 2 (velocity d) x * evenQuotient d φ x +
      2*deriv (velocity d) x * deriv (evenQuotient d φ) x +
      velocity d x * iteratedDeriv 2 (evenQuotient d φ) x := by
  have hv := velocity_contDiff hd0 hdU 2
  have hg := even_quotient_contDiffAt hd0 hdU hs hφ
  have hv0 := velocity_ne_zero hd0 hdU hs
  have hev := eventually_abs_lower hv.continuous.continuousAt hv0
  have heq : (fun t=>velocity d t*evenQuotient d φ t) =ᶠ[𝓝 x] deriv φ := by
    filter_upwards [hev] with t ht
    have ht0 : velocity d t≠0 := abs_pos.mp (lt_of_le_of_lt
      (div_nonneg (abs_nonneg _) (by norm_num)) ht)
    exact mul_div_cancel₀ (deriv φ t) ht0
  have j1 := heq.deriv_eq
  have j2 := heq.iteratedDeriv_eq 2
  have hm1 := ((hv.differentiable (by norm_num) x).hasDerivAt.mul
    (hg.differentiableAt (by norm_num)).hasDerivAt).deriv
  change deriv (fun t=>velocity d t*evenQuotient d φ t) x = _ at hm1
  rw [hm1] at j1
  have hm2 := iteratedDeriv_mul hv.contDiffAt hg
  change iteratedDeriv 2 (fun t=>velocity d t*evenQuotient d φ t) x = _ at hm2
  rw [hm2] at j2
  norm_num [Finset.sum_range_succ,iteratedDeriv_one,iteratedDeriv_zero] at j2
  constructor
  · simpa only [iteratedDeriv_succ,iteratedDeriv_one] using j1.symm
  · rw [show iteratedDeriv 3 φ=iteratedDeriv 2 (deriv φ) by
      exact iteratedDeriv_succ']
    rw [←j2]
    ring

theorem even_quotient_reflection_jets {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hφ : ContDiff ℝ 1 φ) (hi : smoothInvariant d φ)
    (he : ∀ t, φ (-t)=φ t) (hp : Function.Periodic φ (2*Real.pi)) (n : ℕ) :
    (-1:ℝ)^n * iteratedDeriv n (evenQuotient d φ) (Real.pi-x) =
      iteratedDeriv n (evenQuotient d φ) x := by
  have es := eventually_abs_lower continuous_sin.continuousAt hs
  have ec := eventually_abs_lower continuous_cos.continuousAt hc
  have eqs : (fun t=>evenQuotient d φ (Real.pi-t)) =ᶠ[𝓝 x] evenQuotient d φ := by
    filter_upwards [es,ec] with t ht hu
    have hst : sin t≠0 := abs_pos.mp (lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by norm_num)) ht)
    have hct : cos t≠0 := abs_pos.mp (lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by norm_num)) hu)
    exact even_quotient_reflection hd0 hdU hst hct hφ hi he hp
  simpa only [iteratedDeriv_comp_const_sub,smul_eq_mul] using eqs.iteratedDeriv_eq n

theorem omega_periodic (d : ℝ) : Function.Periodic (omega d) (2*Real.pi) := by
  intro x
  simp [omega,Collision.pinnedDispersion,cos_add_two_pi]

theorem omega_iterated_succ {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (n : ℕ) :
    iteratedDeriv (n+1) (omega d)=iteratedDeriv n (velocity d) := by
  rw [iteratedDeriv_succ']
  congr 1
  funext x
  exact omega_deriv (by linarith) hdU x

theorem even_transverse_third_reduced {φ y : ℝ→ℝ} {x : ℝ}
    (hφ : ContDiff ℝ 3 φ) (hy : ContDiffAt ℝ 3 y 0)
    (hy0 : y 0=Real.pi-x) (hi : transverseIdentity φ x y)
    (he : ∀ t, φ (-t)=φ t) (hp : Function.Periodic φ (2*Real.pi)) :
    ((deriv y 0)^3+(deriv y 0-1)^3)*iteratedDeriv 3 φ (Real.pi-x)+
      3*iteratedDeriv 2 y 0*iteratedDeriv 2 φ (Real.pi-x)+
      2*iteratedDeriv 3 y 0*deriv φ (Real.pi-x)+iteratedDeriv 3 φ x=0 := by
  have h := transverse_third_identity φ y x hφ hy hi
  have j1 := even_reflection_jets he hp x 1
  have j2 := even_reflection_jets he hp x 2
  have j3 := even_reflection_jets he hp x 3
  norm_num [iteratedDeriv_one] at j1 j2 j3
  have hw : 2*x+y 0=Real.pi+x := by rw [hy0]; ring
  rw [hw,hy0,j1.2,j2.2,j3.2] at h
  have hm : iteratedDeriv 3 φ (-x)= -iteratedDeriv 3 φ x := by linarith [j3.1]
  rw [hm] at h
  linear_combination h

theorem symmetric_branch_energy_jets {d x : ℝ} {y : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hy : ContDiffAt ℝ 2 y 0)
    (hy0 : y 0=Real.pi-x) (hi : transverseIdentity (omega d) x y) :
    2*velocity d (Real.pi-x)*deriv y 0=velocity d (Real.pi-x)-velocity d x ∧
    2*velocity d (Real.pi-x)*iteratedDeriv 2 y 0 =
      deriv (velocity d) x+(1-2*deriv y 0)*deriv (velocity d) (Real.pi-x) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have e1 := transverse_first_identity (omega d) y x (signed_omega_contDiff hdL hdU 1)
    (hy.of_le (by norm_num)) hi
  have e2 := transverse_second_identity (omega d) y x (signed_omega_contDiff hdL hdU 2) hy hi
  have j2 := even_reflection_jets (omega_neg d) (omega_periodic d) x 2
  norm_num at j2
  have hw : 2*x+y 0=Real.pi+x := by rw [hy0]; ring
  rw [hw,hy0] at e1 e2
  rw [j2.1,j2.2] at e2
  simp only [omega_deriv hdL hdU,velocity_neg,velocity_pi_add] at e1 e2
  have hj : iteratedDeriv 2 (omega d)=deriv (velocity d) := by
    simpa only [iteratedDeriv_one] using omega_iterated_succ hd0 hdU 1
  rw [hj] at e2
  constructor
  · linarith only [e1]
  · nlinarith only [e2]

/-- The quotient equation is obtained from the three derivatives of the same
actual branch, together with its original four-parent invariant identity. -/
theorem even_quotient_original_ode {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hφ : ContDiff ℝ 3 φ) (hi : smoothInvariant d φ)
    (he : ∀ t, φ (-t)=φ t) (hp : Function.Periodic φ (2*Real.pi)) :
    velocity d x*velocity d (Real.pi-x)*
      ((velocity d (Real.pi-x))^2-(velocity d x)^2)*iteratedDeriv 2 (evenQuotient d φ) x+
    2*(deriv (velocity d) x*(velocity d (Real.pi-x))^3+
       (velocity d x)^3*deriv (velocity d) (Real.pi-x))*deriv (evenQuotient d φ) x=0 := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hs' : sin (Real.pi-x)≠0 := by simpa only [sin_pi_sub] using hs
  have hb := velocity_ne_zero hd0 hdU hs'
  obtain ⟨y,hy0,hy,hew,hiy⟩ := exists_symmetric_transverse hd0 hdU hs hc
  have ej := symmetric_branch_energy_jets hd0 hdU (hy.of_le (by simp)) hy0 hew
  have ew := even_transverse_third_reduced (signed_omega_contDiff hdL hdU 3)
    (hy.of_le (by simp)) hy0 hew (omega_neg d) (omega_periodic d)
  have ep := even_transverse_third_reduced hφ (hy.of_le (by simp)) hy0 (hiy φ hi) he hp
  have qj := quotient_product_jets hd0 hdU hs hφ
  have qjb := quotient_product_jets hd0 hdU hs' hφ
  have q0 := even_quotient_reflection hd0 hdU hs hc hφ1 hi he hp
  have q1 := even_quotient_reflection_jets hd0 hdU hs hc hφ1 hi he hp 1
  have q2 := even_quotient_reflection_jets hd0 hdU hs hc hφ1 hi he hp 2
  norm_num [iteratedDeriv_one] at q1 q2
  have q1' : deriv (evenQuotient d φ) (Real.pi-x)= -deriv (evenQuotient d φ) x := by
    linarith only [q1]
  rw [q0,q1',q2] at qjb
  have pb : deriv φ (Real.pi-x)=velocity d (Real.pi-x)*evenQuotient d φ (Real.pi-x) := by
    exact (mul_div_cancel₀ (deriv φ (Real.pi-x)) hb).symm
  rw [q0] at pb
  rw [qj.2,qjb.1,qjb.2,pb] at ep
  have hj2 : iteratedDeriv 2 (omega d)=deriv (velocity d) := by
    simpa only [iteratedDeriv_one] using omega_iterated_succ hd0 hdU 1
  have hj3 : iteratedDeriv 3 (omega d)=iteratedDeriv 2 (velocity d) := omega_iterated_succ hd0 hdU 2
  rw [hj2,hj3,omega_deriv hdL hdU] at ew
  apply PinnedElimination.same_branch_third_elimination
    (velocity d x) (velocity d (Real.pi-x))
    (deriv (velocity d) x) (deriv (velocity d) (Real.pi-x))
    (iteratedDeriv 2 (velocity d) x) (iteratedDeriv 2 (velocity d) (Real.pi-x))
    (deriv y 0) (iteratedDeriv 2 y 0) (iteratedDeriv 3 y 0)
    (evenQuotient d φ x) (deriv (evenQuotient d φ) x) (iteratedDeriv 2 (evenQuotient d φ) x)
    hb ej.1 ej.2 ew
  linear_combination ep

theorem velocity_deriv_formula {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (x : ℝ) :
    deriv (velocity d) x=d*cos x/omega d x-d^2*(sin x)^2/(omega d x)^3 := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hw := ne_of_gt (signed_omega_pos hdL hdU x)
  have h := (((hasDerivAt_sin x).const_mul d).div (omega_hasDerivAt hdL hdU x) hw).deriv
  change deriv (velocity d) x = _ at h
  rw [h]
  dsimp [velocity]
  field_simp

theorem even_quotient_trigonometric_ode {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hφ : ContDiff ℝ 3 φ) (hi : smoothInvariant d φ)
    (he : ∀ t, φ (-t)=φ t) (hp : Function.Periodic φ (2*Real.pi)) :
    sin x*cos x*iteratedDeriv 2 (evenQuotient d φ) x+
      (1+(cos x)^2)*deriv (evenQuotient d φ) x=0 := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have h := even_quotient_original_ode hd0 hdU hs hc hφ hi he hp
  rw [velocity_deriv_formula hd0 hdU,velocity_deriv_formula hd0 hdU] at h
  simp only [velocity, sin_pi_sub, cos_pi_sub] at h
  have hAsq := omega_sq hdL hdU x
  have hBsq := omega_sq hdL hdU (Real.pi-x)
  simp only [cos_pi_sub] at hBsq
  apply PinnedElimination.pinned_coefficient_reduction d (sin x) (cos x)
    (omega d x) (omega d (Real.pi-x)) (deriv (evenQuotient d φ) x)
    (iteratedDeriv 2 (evenQuotient d φ) x) (ne_of_gt hd0) hs
    (ne_of_gt (signed_omega_pos hdL hdU x))
    (ne_of_gt (signed_omega_pos hdL hdU (Real.pi-x))) hAsq
    (by nlinarith only [hBsq]) (sin_sq_add_cos_sq x)
  simpa only [mul_neg,neg_mul,neg_div] using h

def regularEvenQuotient (d : ℝ) (φ : ℝ→ℝ) (x : ℝ) : ℝ := omega d x*deriv φ x/d

theorem regular_even_quotient_contDiff {d : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 3 φ) :
    ContDiff ℝ 2 (regularEvenQuotient d φ) := by
  have hder : ContDiff ℝ 2 (deriv φ) := hφ.deriv'
  exact ((signed_omega_contDiff (by linarith) hdU 2).mul hder).div_const d

theorem regular_quotient_eq_sine_mul {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) :
    regularEvenQuotient d φ x=sin x*evenQuotient d φ x := by
  have hw := ne_of_gt (signed_omega_pos (by linarith) hdU x)
  dsimp [regularEvenQuotient,evenQuotient,velocity]
  field_simp

theorem regular_even_quotient_ode {d x : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0)
    (hφ : ContDiff ℝ 3 φ) (hi : smoothInvariant d φ)
    (he : ∀ t, φ (-t)=φ t) (hp : Function.Periodic φ (2*Real.pi)) :
    cos x*iteratedDeriv 2 (regularEvenQuotient d φ) x+
      sin x*deriv (regularEvenQuotient d φ) x=0 := by
  have hg := even_quotient_contDiffAt hd0 hdU hs hφ
  have hcS : ContDiffAt ℝ 2 sin x := contDiff_sin.contDiffAt
  have es := eventually_abs_lower continuous_sin.continuousAt hs
  have eqs : regularEvenQuotient d φ =ᶠ[𝓝 x] (fun t=>sin t*evenQuotient d φ t) := by
    filter_upwards [es] with t ht
    have hst : sin t≠0 := abs_pos.mp (lt_of_le_of_lt (div_nonneg (abs_nonneg _) (by norm_num)) ht)
    exact regular_quotient_eq_sine_mul hd0 hdU hst
  have j1 := eqs.deriv_eq
  have j2 := eqs.iteratedDeriv_eq 2
  have hp1 := ((hasDerivAt_sin x).mul (hg.differentiableAt (by norm_num)).hasDerivAt).deriv
  change deriv (fun t=>sin t*evenQuotient d φ t) x = _ at hp1
  rw [hp1] at j1
  have hp2 := iteratedDeriv_mul hcS hg
  change iteratedDeriv 2 (fun t=>sin t*evenQuotient d φ t) x = _ at hp2
  rw [hp2] at j2
  norm_num [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one] at j2
  rw [j1,j2]
  have heq := even_quotient_trigonometric_ode hd0 hdU hs hc hφ hi he hp
  linear_combination heq + deriv (evenQuotient d φ) x*(sin_sq_add_cos_sq x)

theorem even_invariant_halfcircle {d : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 3 φ)
    (hi : smoothInvariant d φ) (he : ∀ t, φ (-t)=φ t)
    (hp : Function.Periodic φ (2*Real.pi)) :
    ∃A B:ℝ, ∀x∈Icc 0 Real.pi, φ x=A+B*omega d x := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have hh := regular_even_quotient_contDiff hd0 hdU hφ
  have je := even_reflection_jets he hp 0 1
  norm_num [iteratedDeriv_one] at je
  have h0 : deriv φ 0=0 := by linarith only [je.1]
  have hπ : deriv φ Real.pi=0 := by linarith only [je.2]
  obtain ⟨B,hB⟩ := PinnedODE.sine_solution_on_halfcircle hh
    (by simp only [regularEvenQuotient,h0,mul_zero,zero_div])
    (by simp only [regularEvenQuotient,hπ,mul_zero,zero_div])
    (fun x hx hc=>regular_even_quotient_ode hd0 hdU
      (ne_of_gt (sin_pos_of_pos_of_lt_pi hx.1 hx.2)) hc hφ hi he hp)
  have hder : ∀x∈Ioo 0 Real.pi, deriv φ x=B*velocity d x := by
    intro x hx
    have hrel := hB x ⟨hx.1.le,hx.2.le⟩
    change omega d x*deriv φ x/d=B*sin x at hrel
    have hrel' := (div_eq_iff (ne_of_gt hd0)).mp hrel
    have hw := ne_of_gt (signed_omega_pos hdL hdU x)
    dsimp [velocity]
    field_simp
    nlinarith only [hrel']
  let ψ : ℝ→ℝ := fun x=>φ x-B*omega d x
  have hψ : Differentiable ℝ ψ := by
    have hφd := hφ.differentiable (by norm_num)
    have hωd := (signed_omega_contDiff hdL hdU 1).differentiable (by norm_num)
    fun_prop
  have hψ' : ∀x∈Ioo 0 Real.pi, deriv ψ x=0 := by
    intro x hx
    have hd := ((hφ.differentiable (by norm_num) x).hasDerivAt.sub
      ((omega_hasDerivAt hdL hdU x).const_mul B)).deriv
    change deriv ψ x = _ at hd
    rw [hd,hder x hx]
    ring
  obtain ⟨A,hA⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo 0 Real.pi).isPreconnected hψ.differentiableOn hψ'
  have hEq : EqOn φ (fun x=>A+B*omega d x) (Ioo 0 Real.pi) := by
    intro x hx
    have ha := hA x hx
    dsimp [ψ] at ha
    linarith only [ha]
  have hcl := hEq.closure hφ.continuous (by
    have hc := (signed_omega_contDiff hdL hdU 0).continuous
    fun_prop)
  rw [closure_Ioo (ne_of_lt Real.pi_pos)] at hcl
  exact ⟨A,B,hcl⟩

theorem periodic_even_eq_of_halfcircle {f g : ℝ→ℝ}
    (hf : ∀t, f (-t)=f t) (hg : ∀t, g (-t)=g t)
    (hfp : Function.Periodic f (2*Real.pi)) (hgp : Function.Periodic g (2*Real.pi))
    (heq : EqOn f g (Icc 0 Real.pi)) : f=g := by
  have hT : (0:ℝ)<2*Real.pi := by positivity
  have reflect (f : ℝ→ℝ) (he : ∀t, f (-t)=f t)
      (hp : Function.Periodic f (2*Real.pi)) (t : ℝ) : f (2*Real.pi-t)=f t := by
    have h:=hp (-t)
    rw [show -t+2*Real.pi=2*Real.pi-t by ring,he] at h
    exact h
  funext x
  let y := toIcoMod hT 0 x
  have hy := toIcoMod_mem_Ico hT 0 x
  change 0≤y ∧ y<0+2*Real.pi at hy
  have hfx := hfp.zsmul (toIcoDiv hT 0 x) y
  have hgx := hgp.zsmul (toIcoDiv hT 0 x) y
  simp only [y,toIcoMod_add_toIcoDiv_zsmul hT 0 x] at hfx hgx
  rw [hfx,hgx]
  change f y=g y
  by_cases hle : y≤Real.pi
  · exact heq ⟨hy.1,hle⟩
  · have hz : 2*Real.pi-y∈Icc 0 Real.pi := ⟨by linarith [hy.2],by linarith⟩
    rw [←reflect f hf hfp y,←reflect g hg hgp y]
    exact heq hz

theorem even_invariant_classification {d : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 3 φ)
    (hi : smoothInvariant d φ) (he : ∀ t, φ (-t)=φ t)
    (hp : Function.Periodic φ (2*Real.pi)) :
    ∃A B:ℝ, ∀x, φ x=A+B*omega d x := by
  obtain ⟨A,B,hAB⟩ := even_invariant_halfcircle hd0 hdU hφ hi he hp
  have h : φ=(fun x=>A+B*omega d x) := periodic_even_eq_of_halfcircle he
    (fun t=>by rw [omega_neg]) hp (fun t=>by rw [omega_periodic d t]) hAB
  exact ⟨A,B,fun x=>congrFun h x⟩

theorem smoothInvariant_reflect {d : ℝ} {φ : ℝ→ℝ}
    (hi : smoothInvariant d φ) : smoothInvariant d (fun x=>φ (-x)) := by
  intro x y z he hyz hyw hzw
  have hw : -x+ -y- -z=-(x+y-z) := by ring
  have he' : energyDefect d (-x) (-y) (-z)=0 := by
    simpa only [energyDefect,hw,omega_neg] using he
  have h := hi (-x) (-y) (-z) he'
    (by simpa only [velocity_neg,ne_eq,neg_inj] using hyz)
    (by simpa only [hw,velocity_neg,ne_eq,neg_inj] using hyw)
    (by simpa only [hw,velocity_neg,ne_eq,neg_inj] using hzw)
  simpa only [hw] using h

theorem periodic_reflect {φ : ℝ→ℝ} {T : ℝ} (hp : Function.Periodic φ T) :
    Function.Periodic (fun x=>φ (-x)) T := by
  intro x
  have h := hp (-x-T)
  have h1 : -x-T+T= -x := by ring
  have h2 : -x-T= -(x+T) := by ring
  rw [h1,h2] at h
  exact h.symm

/-- C³ classification for the original dispersion and original complete
four-parent relation. Only actual three-source nondegenerate resonances are
required; the ODE and its endpoint conditions are conclusions of the proof. -/
theorem smooth_invariant_classification {d : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 3 φ)
    (hi : smoothInvariant d φ) (hp : Function.Periodic φ (2*Real.pi)) :
    ∃A B:ℝ, ∀x, φ x=A+B*omega d x := by
  let ψ : ℝ→ℝ := fun x=>φ x-φ (-x)
  have hψ : ContDiff ℝ 2 ψ := by
    have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
    dsimp [ψ]
    fun_prop
  have hiψ : smoothInvariant d ψ := by
    intro x y z he hyz hyw hzw
    have h1 := hi x y z he hyz hyw hzw
    have h2 := smoothInvariant_reflect hi x y z he hyz hyw hzw
    dsimp [ψ]
    dsimp at h2
    linear_combination h1-h2
  have hoψ : ∀x, ψ (-x)= -ψ x := by
    intro x
    dsimp [ψ]
    simp only [neg_neg]
    ring
  have hpψ : Function.Periodic ψ (2*Real.pi) := by
    intro x
    change φ (x+2*Real.pi)-φ (-(x+2*Real.pi))=φ x-φ (-x)
    have hpr := periodic_reflect hp x
    change φ (-(x+2*Real.pi))=φ (-x) at hpr
    rw [hp x,hpr]
  have hz := odd_invariant_eq_zero hd0 hdU hψ hiψ hoψ hpψ
  have heφ : ∀x, φ (-x)=φ x := by
    intro x
    have h := hz x
    dsimp [ψ] at h
    linarith only [h]
  exact even_invariant_classification hd0 hdU hφ hi heφ hp

def complexSmoothInvariant (d : ℝ) (φ : ℝ→ℂ) : Prop :=
  ∀x y z:ℝ, energyDefect d x y z=0 →
    velocity d y≠velocity d z → velocity d y≠velocity d (x+y-z) →
    velocity d z≠velocity d (x+y-z) → φ x+φ y=φ z+φ (x+y-z)

/-- The complex-valued version is obtained by the actual real-linear real
and imaginary parts, with no extra resonance or regularity assumptions. -/
theorem complex_smooth_invariant_classification {d : ℝ} {φ : ℝ→ℂ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 3 φ)
    (hi : complexSmoothInvariant d φ) (hp : Function.Periodic φ (2*Real.pi)) :
    ∃A B:ℂ, ∀x, φ x=A+B*(omega d x:ℂ) := by
  have hr : ContDiff ℝ 3 (fun x=>(φ x).re) := Complex.reCLM.contDiff.comp hφ
  have hm : ContDiff ℝ 3 (fun x=>(φ x).im) := Complex.imCLM.contDiff.comp hφ
  have hir : smoothInvariant d (fun x=>(φ x).re) := by
    intro x y z he hyz hyw hzw
    simpa only [Complex.add_re] using congrArg Complex.re (hi x y z he hyz hyw hzw)
  have him : smoothInvariant d (fun x=>(φ x).im) := by
    intro x y z he hyz hyw hzw
    simpa only [Complex.add_im] using congrArg Complex.im (hi x y z he hyz hyw hzw)
  obtain ⟨Ar,Br,hAr⟩ := smooth_invariant_classification hd0 hdU hr hir
    (fun x=>congrArg Complex.re (hp x))
  obtain ⟨Ai,Bi,hAi⟩ := smooth_invariant_classification hd0 hdU hm him
    (fun x=>congrArg Complex.im (hp x))
  refine ⟨⟨Ar,Ai⟩,⟨Br,Bi⟩,?_⟩
  intro x
  apply Complex.ext
  · simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using hAr x
  · simpa only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] using hAi x

theorem affine_omega_original_identity (d A B x y z : ℝ)
    (he : energyDefect d x y z=0) :
    (A+B*omega d x)+(A+B*omega d y)=
      (A+B*omega d z)+(A+B*omega d (x+y-z)) := by
  dsimp [energyDefect] at he
  linear_combination B*he

theorem smooth_invariant_iff_affine_omega {d : ℝ} {φ : ℝ→ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 3 φ)
    (hp : Function.Periodic φ (2*Real.pi)) :
    smoothInvariant d φ ↔ ∃A B:ℝ, ∀x, φ x=A+B*omega d x := by
  constructor
  · exact fun hi=>smooth_invariant_classification hd0 hdU hφ hi hp
  · rintro ⟨A,B,hAB⟩ x y z he _ _ _
    simp only [hAB]
    exact affine_omega_original_identity d A B x y z he

theorem complex_affine_omega_original_identity (d x y z : ℝ) (A B : ℂ)
    (he : energyDefect d x y z=0) :
    (A+B*(omega d x:ℂ))+(A+B*(omega d y:ℂ))=
      (A+B*(omega d z:ℂ))+(A+B*(omega d (x+y-z):ℂ)) := by
  have hr : omega d x+omega d y=omega d z+omega d (x+y-z) := by
    dsimp [energyDefect] at he
    linarith only [he]
  have hh : (omega d x:ℂ)+(omega d y:ℂ)=(omega d z:ℂ)+(omega d (x+y-z):ℂ) := by
    exact_mod_cast hr
  linear_combination B*hh

theorem complex_smooth_invariant_iff_affine_omega {d : ℝ} {φ : ℝ→ℂ}
    (hd0 : 0<d) (hdU : d<1/2) (hφ : ContDiff ℝ 3 φ)
    (hp : Function.Periodic φ (2*Real.pi)) :
    complexSmoothInvariant d φ ↔ ∃A B:ℂ, ∀x, φ x=A+B*(omega d x:ℂ) := by
  constructor
  · exact fun hi=>complex_smooth_invariant_classification hd0 hdU hφ hi hp
  · rintro ⟨A,B,hAB⟩ x y z he _ _ _
    simp only [hAB]
    exact complex_affine_omega_original_identity d x y z A B he

end
end Resonance.PinnedClassification
