import Resonance.PinnedCharts
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! Elementary interval integration for the explicit coefficient equation
derived from the original pinned dispersion. The resonance derivation is kept
in PinnedClassification; this module supplies only ordinary calculus. -/
open Real Set
open scoped ContDiff
namespace Resonance.PinnedODE
noncomputable section

theorem sine_affine_on_interval {h : ℝ→ℝ} {a b : ℝ}
    (hh : ContDiff ℝ 2 h)
    (hc : ∀x∈Ioo a b, cos x≠0)
    (he : ∀x∈Ioo a b, cos x*iteratedDeriv 2 h x+sin x*deriv h x=0) :
    ∃A B:ℝ, ∀x∈Ioo a b, h x=A*sin x+B := by
  let v : ℝ→ℝ := fun x=>deriv h x/cos x
  have hdd : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  have hv : DifferentiableOn ℝ v (Ioo a b) := by
    intro x hx
    exact ((hdd x).div (differentiableAt_cos) (hc x hx)).differentiableWithinAt
  have hv' : ∀x∈Ioo a b, deriv v x=0 := by
    intro x hx
    have hd := ((hdd x).hasDerivAt.div (hasDerivAt_cos x) (hc x hx)).deriv
    change deriv v x = _ at hd
    rw [hd]
    have he' := he x hx
    simp only [iteratedDeriv_succ,iteratedDeriv_zero] at he'
    have hn : deriv (deriv h) x*cos x-deriv h x*(-sin x)=0 := by nlinarith only [he']
    rw [hn,zero_div]
  obtain ⟨A,hA⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo a b).isPreconnected hv hv'
  have hf : Differentiable ℝ (fun x=>h x-A*sin x) := by
    have hd := hh.differentiable (by norm_num)
    fun_prop
  have hf' : ∀x∈Ioo a b, deriv (fun t=>h t-A*sin t) x=0 := by
    intro x hx
    have hhx := ((hh.differentiable (by norm_num) x).hasDerivAt.sub
      ((hasDerivAt_sin x).const_mul A)).deriv
    change deriv (fun t=>h t-A*sin t) x = _ at hhx
    rw [hhx]
    have ha := hA x hx
    change deriv h x/cos x=A at ha
    have hh' := (div_eq_iff (hc x hx)).mp ha
    linarith only [hh']
  obtain ⟨B,hB⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo a b).isPreconnected hf.differentiableOn hf'
  refine ⟨A,B,?_⟩
  intro x hx
  have hb := hB x hx
  linarith only [hb]

theorem sine_affine_on_closed_interval {h : ℝ→ℝ} {a b : ℝ}
    (hab : a<b) (hh : ContDiff ℝ 2 h)
    (hc : ∀x∈Ioo a b, cos x≠0)
    (he : ∀x∈Ioo a b, cos x*iteratedDeriv 2 h x+sin x*deriv h x=0) :
    ∃A B:ℝ, ∀x∈Icc a b, h x=A*sin x+B := by
  obtain ⟨A,B,hAB⟩ := sine_affine_on_interval hh hc he
  have heq : EqOn h (fun x=>A*sin x+B) (Ioo a b) := hAB
  have hcl := heq.closure hh.continuous (by fun_prop)
  rw [closure_Ioo hab.ne] at hcl
  exact ⟨A,B,hcl⟩

theorem sine_solution_on_halfcircle {h : ℝ→ℝ}
    (hh : ContDiff ℝ 2 h) (h0 : h 0=0) (hπ : h Real.pi=0)
    (he : ∀x∈Ioo 0 Real.pi, cos x≠0 →
      cos x*iteratedDeriv 2 h x+sin x*deriv h x=0) :
    ∃A:ℝ, ∀x∈Icc 0 Real.pi, h x=A*sin x := by
  have hp := Real.pi_pos
  have hcL : ∀x∈Ioo 0 (Real.pi/2), cos x≠0 := by
    intro x hx
    apply ne_of_gt
    exact cos_pos_of_mem_Ioo ⟨by linarith [hx.1],hx.2⟩
  have hcR : ∀x∈Ioo (Real.pi/2) Real.pi, cos x≠0 := by
    intro x hx
    have hp' : 0<cos (Real.pi-x) := cos_pos_of_mem_Ioo ⟨by linarith [hx.2],by linarith [hx.1]⟩
    rw [cos_pi_sub] at hp'
    linarith
  obtain ⟨A,B,hAB⟩ := sine_affine_on_closed_interval (by linarith : (0:ℝ)<Real.pi/2) hh hcL
    (fun x hx=>he x ⟨hx.1,by linarith [hx.2]⟩ (hcL x hx))
  obtain ⟨C,D,hCD⟩ := sine_affine_on_closed_interval (by linarith : Real.pi/2<Real.pi) hh hcR
    (fun x hx=>he x ⟨by linarith [hx.1],hx.2⟩ (hcR x hx))
  have hB : B=0 := by
    have hb := hAB 0 ⟨le_rfl,by linarith⟩
    simpa only [h0,sin_zero,mul_zero,zero_add,eq_comm] using hb
  have hD : D=0 := by
    have hd := hCD Real.pi ⟨by linarith,le_rfl⟩
    simpa only [hπ,sin_pi,mul_zero,zero_add,eq_comm] using hd
  have hAC : A=C := by
    have hl := hAB (Real.pi/2) ⟨by linarith,le_rfl⟩
    have hr := hCD (Real.pi/2) ⟨le_rfl,by linarith⟩
    simp only [sin_pi_div_two,mul_one,hB,hD,add_zero] at hl hr
    linarith
  refine ⟨A,?_⟩
  intro x hx
  by_cases hl : x≤Real.pi/2
  · simpa only [hB,add_zero] using hAB x ⟨hx.1,hl⟩
  · simpa only [hD,add_zero,←hAC] using hCD x ⟨le_of_lt (lt_of_not_ge hl),hx.2⟩

end
end Resonance.PinnedODE
