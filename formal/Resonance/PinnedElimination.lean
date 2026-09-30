import Resonance.PinnedCharts

/-! Exact algebra for the derivatives of one original symmetric resonance
branch. These are elimination lemmas, not classification statements and not
additional hypotheses imposed on a collision invariant. -/
namespace Resonance.PinnedElimination
noncomputable section

theorem same_branch_third_elimination
    (a b ca cb da db α β γ q q₁ q₂ : ℝ) (hb : b≠0)
    (hα : 2*b*α=b-a)
    (hβ : 2*b*β=ca+(1-2*α)*cb)
    (hω : (α^3+(α-1)^3)*db+3*β*cb+2*γ*b+da=0)
    (hφ : (α^3+(α-1)^3)*(db*q-2*cb*q₁+b*q₂)+
      3*β*(cb*q-b*q₁)+2*γ*b*q+da*q+2*ca*q₁+a*q₂=0) :
    a*b*(b^2-a^2)*q₂+2*(ca*b^3+a^3*cb)*q₁=0 := by
  have hred : ((α^3+(α-1)^3)*b+a)*q₂+
      (2*ca-2*(α^3+(α-1)^3)*cb-3*β*b)*q₁=0 := by
    linear_combination hφ-q*hω
  have hα' : α=(b-a)/(2*b) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hb)).mpr
    linarith only [hα]
  have hβ' : β=(ca+(1-2*α)*cb)/(2*b) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hb)).mpr
    linarith only [hβ]
  rw [hβ',hα'] at hred
  have hid :
      ((((b-a)/(2*b))^3+((b-a)/(2*b)-1)^3)*b+a)*q₂+
        (2*ca-2*(((b-a)/(2*b))^3+((b-a)/(2*b)-1)^3)*cb-
          3*((ca+(1-2*((b-a)/(2*b)))*cb)/(2*b))*b)*q₁ =
      (a*b*(b^2-a^2)*q₂+2*(ca*b^3+a^3*cb)*q₁)/(4*b^3) := by
    field_simp
    ring
  rw [hid] at hred
  exact (div_eq_zero_iff.mp hred).resolve_right
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hb))

theorem pinned_coefficient_reduction
    (d s c A B u v : ℝ) (hd : d≠0) (hs : s≠0) (hA : A≠0) (hB : B≠0)
    (hAsq : A^2=1-2*d*c) (hBsq : B^2=1+2*d*c) (hcirc : s^2+c^2=1)
    (h : (d*s/A)*(d*s/B)*((d*s/B)^2-(d*s/A)^2)*v+
      2*((d*c/A-d^2*s^2/A^3)*(d*s/B)^3+
        (d*s/A)^3*(-d*c/B-d^2*s^2/B^3))*u=0) :
    s*c*v+(1+c^2)*u=0 := by
  have hid : (d*s/A)*(d*s/B)*((d*s/B)^2-(d*s/A)^2)*v+
      2*((d*c/A-d^2*s^2/A^3)*(d*s/B)^3+
        (d*s/A)^3*(-d*c/B-d^2*s^2/B^3))*u =
      (-4*d^5*s^3/(A^3*B^3))*(s*c*v+(1+c^2)*u) := by
    field_simp
    ring_nf
    rw [hAsq,hBsq]
    linear_combination -4*d*u*hcirc
  rw [hid] at h
  exact (mul_eq_zero.mp h).resolve_left
    (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hd))
      (pow_ne_zero _ hs)) (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)))

end
end Resonance.PinnedElimination
