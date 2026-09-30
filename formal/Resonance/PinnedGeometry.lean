import Resonance.Collision

/-! Original pinned dispersion and actual resonance geometry on periodic real lifts.
No regularity or classification conclusion is assumed in an input structure. -/
open Real MeasureTheory
namespace Resonance.PinnedGeometry
noncomputable section

abbrev omega := Collision.pinnedDispersion
def velocity (d x : ℝ) : ℝ := d * sin x / omega d x
def energyDefect (d x y z : ℝ) : ℝ :=
  omega d x + omega d y - omega d z - omega d (x + y - z)
def liftLegs (x y z : ℝ) : Fin 4 → ℝ := ![x,y,z,x+y-z]

theorem signed_radicand_pos {d : ℝ} (hdL : -(1/2:ℝ) < d) (hdU : d < 1/2)
    (x : ℝ) : 0 < 1 - 2*d*cos x := by
  by_cases hd : 0 ≤ d
  · nlinarith [cos_le_one x]
  · have hd' : d < 0 := lt_of_not_ge hd
    nlinarith [neg_one_le_cos x]

theorem signed_omega_pos {d : ℝ} (hdL : -(1/2:ℝ) < d) (hdU : d < 1/2)
    (x : ℝ) : 0 < omega d x :=
  Real.sqrt_pos.mpr (signed_radicand_pos hdL hdU x)

theorem omega_sq {d : ℝ} (hdL : -(1/2:ℝ) < d) (hdU : d < 1/2) (x : ℝ) :
    omega d x ^ 2 = 1 - 2*d*cos x :=
  Real.sq_sqrt (signed_radicand_pos hdL hdU x).le

theorem omega_hasDerivAt {d : ℝ} (hdL : -(1/2:ℝ) < d) (hdU : d < 1/2) (x : ℝ) :
    HasDerivAt (omega d) (velocity d x) x := by
  have h := ((hasDerivAt_const x (1:ℝ)).sub
    ((Real.hasDerivAt_cos x).const_mul (2*d))).sqrt
      (ne_of_gt (signed_radicand_pos hdL hdU x))
  change HasDerivAt (fun y => Real.sqrt (1-2*d*cos y))
    ((0-2*d*(-sin x))/(2*Real.sqrt (1-2*d*cos x))) x at h
  convert h using 1; simp only [omega, Collision.pinnedDispersion, velocity]; ring

theorem omega_deriv {d : ℝ} (hdL : -(1/2:ℝ) < d) (hdU : d < 1/2) (x : ℝ) :
    deriv (omega d) x = velocity d x := (omega_hasDerivAt hdL hdU x).deriv

theorem omega_neg (d x : ℝ) : omega d (-x) = omega d x := by
  simp [omega, Collision.pinnedDispersion]

theorem omega_pi_sub (d x : ℝ) : omega d (Real.pi-x) = omega (-d) x := by
  simp [omega, Collision.pinnedDispersion, cos_pi_sub]

theorem omega_add_pi (d x : ℝ) : omega d (x+Real.pi) = omega (-d) x := by
  simp [omega, Collision.pinnedDispersion, cos_add_pi]

theorem velocity_neg (d x : ℝ) : velocity d (-x) = -velocity d x := by
  simp [velocity, omega_neg, neg_div]

theorem velocity_pi_sub (d x : ℝ) : velocity d (Real.pi-x) =
    d*sin x / omega d (Real.pi-x) := by simp [velocity, sin_pi_sub]

theorem velocity_pi_add (d x : ℝ) : velocity d (Real.pi+x) = -velocity d (Real.pi-x) := by
  rw [add_comm Real.pi x]
  simp [velocity, omega_pi_sub, omega_add_pi, sin_pi_sub, sin_add_pi, neg_div]

theorem omega_signed_shift (d x : ℝ) : omega d (x+Real.pi) = omega (-d) x :=
  omega_add_pi d x

theorem velocity_signed_shift (d x : ℝ) : velocity d (x+Real.pi) = velocity (-d) x := by
  simp [velocity, omega_add_pi, sin_add_pi]

theorem symmetric_resonance (d x : ℝ) : energyDefect d x (Real.pi-x) (-x) = 0 := by
  have he : x + (Real.pi-x) - (-x) = x+Real.pi := by ring
  unfold energyDefect
  rw [he, omega_neg, omega_add_pi, omega_pi_sub]
  ring

/-- All three non-target velocities in the same symmetric quartet are distinct. -/
theorem symmetric_velocity_nondegenerate {d x : ℝ}
    (hd0 : 0 < d) (hdU : d < 1/2) (hs : sin x ≠ 0) (hc : cos x ≠ 0) :
    velocity d (Real.pi-x) ≠ velocity d (-x) ∧
    velocity d (Real.pi-x) ≠ velocity d (Real.pi+x) ∧
    velocity d (-x) ≠ velocity d (Real.pi+x) := by
  have hdL : -(1/2:ℝ) < d := by linarith
  have hwa := signed_omega_pos hdL hdU x
  have hwb := signed_omega_pos hdL hdU (Real.pi-x)
  have hwa0 := ne_of_gt hwa
  have hwb0 := ne_of_gt hwb
  have hnum : d*sin x ≠ 0 := mul_ne_zero (ne_of_gt hd0) hs
  have ha : velocity d x ≠ 0 := div_ne_zero hnum hwa0
  have hb : velocity d (Real.pi-x) ≠ 0 := by
    rw [velocity_pi_sub]
    exact div_ne_zero hnum hwb0
  have hab : velocity d x ≠ velocity d (Real.pi-x) := by
    intro he
    rw [velocity, velocity_pi_sub] at he
    have hew : omega d x = omega d (Real.pi-x) := by
      have hh := (div_eq_div_iff hwa0 hwb0).mp he
      exact (mul_left_cancel₀ hnum hh).symm
    have h1 := omega_sq hdL hdU x
    have h2 := omega_sq hdL hdU (Real.pi-x)
    rw [cos_pi_sub, ← hew] at h2
    have hz : d*cos x = 0 := by nlinarith
    exact hc ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hd0))
  have hsum : velocity d (Real.pi-x) ≠ -velocity d x := by
    intro he
    have he' : d*sin x / omega d (Real.pi-x) = -(d*sin x / omega d x) := by
      simpa only [velocity, sin_pi_sub] using he
    field_simp [hwa0, hwb0] at he'
    have hz : d*sin x * (omega d x + omega d (Real.pi-x)) = 0 := by nlinarith [he']
    exact (ne_of_gt (add_pos hwa hwb)) ((mul_eq_zero.mp hz).resolve_left hnum)
  rw [velocity_neg, velocity_pi_add]
  exact ⟨hsum, fun he => hb (by linarith), fun he => hab (by linarith)⟩


/-- Actual unit-circle coordinates have an angle; no trigonometric witness is assumed. -/
theorem exists_angle_of_sq_add {a b : ℝ} (h : a^2+b^2=1) :
    ∃ y : ℝ, cos y = a ∧ sin y = b := by
  let z : ℂ := ⟨a,b⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    change Real.sqrt (a^2+b^2)=1
    rw [h]
    norm_num
  have hz : z ≠ 0 := by
    intro he
    rw [he, norm_zero] at hn
    norm_num at hn
  exact ⟨z.arg, by simpa [hn, z] using Complex.cos_arg hz,
    by simpa [hn, z] using Complex.sin_arg z⟩

def specialC (d : ℝ) : ℝ := 1 - Real.sqrt (1-2*d)
def specialQ (c : ℝ) : ℝ := Real.sqrt (4+4*c-7*c^2)
def specialA (c : ℝ) : ℝ := (c+specialQ c)/2
def specialB (c : ℝ) : ℝ := (specialQ c-c)/2

theorem specialC_data {d : ℝ} (hdL : -(1/2:ℝ) < d)
    (hdU : d < 1/2) (hd : d ≠ 0) :
    -(1/2:ℝ) < specialC d ∧ specialC d < 1 ∧ specialC d ≠ 0 ∧
    specialC d * (2-specialC d) = 2*d := by
  have hp : 0 < 1-2*d := by linarith
  have hs := Real.sq_sqrt hp.le
  have hu := Real.sqrt_pos.mpr hp
  have hupper : Real.sqrt (1-2*d) < 3/2 := by nlinarith
  dsimp [specialC]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · intro he
    apply hd
    nlinarith
  · nlinarith

theorem specialQ_data {c : ℝ} (hcL : -(1/2:ℝ) < c) (hcU : c < 1) :
    0 < specialQ c ∧ (specialQ c)^2 = 4+4*c-7*c^2 ∧
    |c| < specialQ c := by
  have hprod : 0 < (1-c)*(1+2*c) := mul_pos (by linarith) (by linarith)
  have hp : 0 < 4+4*c-7*c^2 := by nlinarith [sq_nonneg c]
  have hq := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  refine ⟨hq, hsq, ?_⟩
  have ha := sq_abs c
  have hn := abs_nonneg c
  change |c| < Real.sqrt (4+4*c-7*c^2)
  nlinarith

theorem special_AB_data {c : ℝ} (hcL : -(1/2:ℝ) < c) (hcU : c < 1)
    (hc : c ≠ 0) :
    0 < specialA c ∧ 0 < specialB c ∧ specialB c < 1 ∧
    specialA c - specialB c = c ∧
    specialA c * specialB c = (1-c)*(1+2*c) ∧
    (specialA c)^2 + (specialB c)^2 = 2+2*c-3*c^2 := by
  obtain ⟨hq, hqs, hqa⟩ := specialQ_data hcL hcU
  have hca : c ≤ |c| := le_abs_self c
  have hnca : -c ≤ |c| := neg_le_abs c
  have hqbound : specialQ c < 2+c := by
    have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
    nlinarith
  dsimp [specialA, specialB]
  refine ⟨by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem special_unit_circle {c : ℝ} (hcL : -(1/2:ℝ) < c) (hcU : c < 1)
    (hc : c ≠ 0) :
    (1-(specialA c)^2)^2 + (1-(specialB c)^2)^2 = (c*(2-c))^2 := by
  obtain ⟨_,_,_,_,hp,hs⟩ := special_AB_data hcL hcU hc
  have hs2 := congrArg (fun x : ℝ => x^2) hs
  have hp2 := congrArg (fun x : ℝ => x^2) hp
  nlinarith


theorem special_velocity_differences {c : ℝ}
    (hcL : -(1/2:ℝ) < c) (hcU : c < 1) (hc : c ≠ 0) :
    let A := specialA c
    let B := specialB c
    let d := c*(2-c)/2
    ((1-B^2)/(2*A) - (A^2-1)/(2*B) =
      -c*(1-c)*(A+B)/(2*A*B)) ∧
    ((1-B^2)/(2*A) - d = -c*(1-c)*(A+1)/(2*A)) ∧
    ((A^2-1)/(2*B) - d = c*(1-c)*(1-B)/(2*B)) := by
  obtain ⟨hA,hB,_,hm,hp,hs⟩ := special_AB_data hcL hcU hc
  dsimp only
  have hA0 := ne_of_gt hA
  have hB0 := ne_of_gt hB
  constructor
  · field_simp
    linear_combination -(specialA c + specialB c)*hs +
      (specialA c + specialB c)*hp
  constructor
  · field_simp
    nlinarith [hp, hs, hm, sq_nonneg (specialA c - specialB c)]
  · field_simp
    nlinarith [hp, hs, hm, sq_nonneg (specialA c - specialB c)]

/-- The signed auxiliary dispersion has an explicit, genuinely resonant quartet at target zero. -/
theorem exists_signed_special_resonance {d : ℝ} (hdL : -(1/2:ℝ) < d)
    (hdU : d < 1/2) (hd : d ≠ 0) :
    ∃ y : ℝ,
      energyDefect d 0 y (Real.pi/2) = 0 ∧
      velocity d y ≠ d ∧
      velocity d (y-Real.pi/2) ≠ d ∧
      velocity d y ≠ velocity d (y-Real.pi/2) ∧
      velocity d y ≠ 0 ∧ velocity d (y-Real.pi/2) ≠ 0 := by
  let c := specialC d
  let A := specialA c
  let B := specialB c
  obtain ⟨hcL,hcU,hc,hcd⟩ := specialC_data hdL hdU hd
  change -(1/2:ℝ)<c at hcL
  change c<1 at hcU
  change c≠0 at hc
  change c*(2-c)=2*d at hcd
  obtain ⟨hA,hB,hB1,hm,hp,hs⟩ := special_AB_data hcL hcU hc
  change 0<A at hA
  change 0<B at hB
  change B<1 at hB1
  change A-B=c at hm
  change A*B=(1-c)*(1+2*c) at hp
  change A^2+B^2=2+2*c-3*c^2 at hs
  have hcircle : ((1-A^2)/(2*d))^2 + ((1-B^2)/(2*d))^2 = 1 := by
    have h := special_unit_circle hcL hcU hc
    change (1-A^2)^2+(1-B^2)^2=(c*(2-c))^2 at h
    rw [hcd] at h
    field_simp
    nlinarith only [h]
  obtain ⟨y,hycos,hysin⟩ := exists_angle_of_sq_add hcircle
  have hzero : omega d 0 = 1-c := by
    simp [omega, Collision.pinnedDispersion, c, specialC]
  have hhalf : omega d (Real.pi/2) = 1 := by
    simp [omega, Collision.pinnedDispersion]
  have hyA : omega d y = A := by
    have hq := omega_sq hdL hdU y
    rw [hycos] at hq
    field_simp at hq
    have hypos := signed_omega_pos hdL hdU y
    have he : (omega d y)^2 = A^2 := by nlinarith only [hq]
    nlinarith only [he, hypos, hA]
  have hwB : omega d (y-Real.pi/2) = B := by
    have hq := omega_sq hdL hdU (y-Real.pi/2)
    rw [cos_sub_pi_div_two,hysin] at hq
    have hcancel : 2*d*((1-B^2)/(2*d))=1-B^2 := by field_simp
    rw [hcancel] at hq
    have hwpos := signed_omega_pos hdL hdU (y-Real.pi/2)
    have he : (omega d (y-Real.pi/2))^2 = B^2 := by nlinarith only [hq]
    nlinarith only [he, hwpos, hB]
  have hvy : velocity d y = (1-B^2)/(2*A) := by
    rw [velocity,hysin,hyA]
    field_simp
  have hvw : velocity d (y-Real.pi/2) = (A^2-1)/(2*B) := by
    rw [velocity,sin_sub_pi_div_two,hycos,hwB]
    field_simp
    ring
  obtain ⟨hv1,hv2,hv3⟩ := special_velocity_differences hcL hcU hc
  change (1-B^2)/(2*A)-(A^2-1)/(2*B) = -c*(1-c)*(A+B)/(2*A*B) at hv1
  change (1-B^2)/(2*A)-c*(2-c)/2 = -c*(1-c)*(A+1)/(2*A) at hv2
  change (A^2-1)/(2*B)-c*(2-c)/2 = c*(1-c)*(1-B)/(2*B) at hv3
  have hdexpr : c*(2-c)/2=d := by linarith
  rw [hdexpr] at hv2 hv3
  have hu0 : 1-c ≠ 0 := ne_of_gt (by linarith : 0<1-c)
  have hB0 := ne_of_gt hB
  have hA0 := ne_of_gt hA
  have hv1ne : -c*(1-c)*(A+B)/(2*A*B) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hc) hu0)
      (ne_of_gt (add_pos hA hB))) (mul_ne_zero (mul_ne_zero (by norm_num) hA0) hB0)
  have hv2ne : -c*(1-c)*(A+1)/(2*A) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hc) hu0)
      (ne_of_gt (by linarith))) (mul_ne_zero (by norm_num) hA0)
  have hv3ne : c*(1-c)*(1-B)/(2*B) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hc hu0)
      (ne_of_gt (by linarith))) (mul_ne_zero (by norm_num) hB0)
  have hA1 : A ≠ 1 := by
    intro he
    rw [he] at hm hp
    have heB : B=1-c := by linarith
    rw [heB] at hp
    have hz : c*(1-c)=0 := by nlinarith only [hp]
    exact (mul_ne_zero hc hu0) hz
  refine ⟨y,?_,?_,?_,?_,?_,?_⟩
  · simp only [energyDefect, zero_add,hzero,hhalf,hyA,hwB]
    linarith
  · rw [hvy]
    intro he
    apply hv2ne
    linarith
  · rw [hvw]
    intro he
    apply hv3ne
    linarith
  · rw [hvy,hvw]
    intro he
    apply hv1ne
    linarith
  · rw [hvy]
    exact ne_of_gt (div_pos (by nlinarith only [hB, hB1]) (by linarith only [hA]))
  · rw [hvw]
    apply div_ne_zero _ (mul_ne_zero (by norm_num) hB0)
    intro he
    apply hA1
    nlinarith only [he, hA]


/-- A geometric existence predicate: an actual quartet at the specified target,
with all three non-target velocities different. -/
def NondegenerateAt (d x : ℝ) : Prop :=
  ∃ y z : ℝ, energyDefect d x y z = 0 ∧
    velocity d y ≠ velocity d z ∧
    velocity d y ≠ velocity d (x+y-z) ∧
    velocity d z ≠ velocity d (x+y-z)

theorem nondegenerateAt_symmetric {d x : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (hs : sin x≠0) (hc : cos x≠0) :
    NondegenerateAt d x := by
  refine ⟨Real.pi-x,-x,symmetric_resonance d x,?_⟩
  have h := symmetric_velocity_nondegenerate hd0 hdU hs hc
  have he : x+(Real.pi-x)-(-x)=Real.pi+x := by ring
  simpa only [he] using h

theorem nondegenerateAt_neg {d x : ℝ} (h : NondegenerateAt d x) :
    NondegenerateAt d (-x) := by
  obtain ⟨y,z,he,hyz,hyw,hzw⟩ := h
  have hw : -x + -y - -z = -(x+y-z) := by ring
  refine ⟨-y,-z,?_,?_,?_,?_⟩
  · simpa only [energyDefect, hw, omega_neg] using he
  · simpa only [velocity_neg, ne_eq, neg_inj] using hyz
  · simpa only [hw, velocity_neg, ne_eq, neg_inj] using hyw
  · simpa only [hw, velocity_neg, ne_eq, neg_inj] using hzw

theorem nondegenerateAt_pi_shift {d x : ℝ} (h : NondegenerateAt (-d) x) :
    NondegenerateAt d (x+Real.pi) := by
  obtain ⟨y,z,he,hyz,hyw,hzw⟩ := h
  have hw : (x+Real.pi)+(y+Real.pi)-(z+Real.pi)=(x+y-z)+Real.pi := by ring
  refine ⟨y+Real.pi,z+Real.pi,?_,?_,?_,?_⟩
  · simpa only [energyDefect, hw, omega_signed_shift] using he
  · simpa only [velocity_signed_shift] using hyz
  · simpa only [hw, velocity_signed_shift] using hyw
  · simpa only [hw, velocity_signed_shift] using hzw

theorem nondegenerateAt_two_pi_shift {d x : ℝ} (h : NondegenerateAt d x) :
    NondegenerateAt d (x+2*Real.pi) := by
  have h1 : NondegenerateAt (-d) (x+Real.pi) :=
    nondegenerateAt_pi_shift (by simpa only [neg_neg] using h)
  have h2 := nondegenerateAt_pi_shift h1
  have he : (x+Real.pi)+Real.pi=x+2*Real.pi := by ring
  simpa only [he] using h2

theorem velocity_zero (d : ℝ) : velocity d 0 = 0 := by simp [velocity]
theorem velocity_half_pi (d : ℝ) : velocity d (Real.pi/2) = d := by
  simp [velocity, omega, Collision.pinnedDispersion]

theorem nondegenerateAt_zero {d : ℝ} (hdL : -(1/2:ℝ)<d)
    (hdU : d<1/2) (hd : d≠0) : NondegenerateAt d 0 := by
  obtain ⟨y,he,hy,hw,hyw,_,_⟩ := exists_signed_special_resonance hdL hdU hd
  refine ⟨y,Real.pi/2,he,?_,?_,?_⟩
  · simpa only [velocity_half_pi] using hy
  · simpa only [zero_add] using hyw
  · simpa only [zero_add,velocity_half_pi] using hw.symm

theorem nondegenerateAt_half_pi {d : ℝ} (hdL : -(1/2:ℝ)<d)
    (hdU : d<1/2) (hd : d≠0) : NondegenerateAt d (Real.pi/2) := by
  obtain ⟨y,he,_,_,hyw,hy0,hw0⟩ := exists_signed_special_resonance hdL hdU hd
  have hw : Real.pi/2+(y-Real.pi/2)-0=y := by ring
  refine ⟨y-Real.pi/2,0,?_,?_,?_,?_⟩
  · unfold energyDefect at he ⊢
    rw [hw]
    simp only [zero_add] at he
    linarith only [he]
  · simpa only [velocity_zero] using hw0
  · simpa only [hw] using hyw.symm
  · simpa only [hw,velocity_zero] using hy0.symm

theorem nondegenerateAt_pi {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    NondegenerateAt d Real.pi := by
  have hdL' : -(1/2:ℝ)< -d := by linarith
  have hdU' : -d<1/2 := by linarith
  have h := nondegenerateAt_pi_shift
    (nondegenerateAt_zero hdL' hdU' (neg_ne_zero.mpr (ne_of_gt hd0)))
  simpa only [zero_add] using h

theorem nondegenerateAt_three_half_pi {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    NondegenerateAt d (3*Real.pi/2) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have h := nondegenerateAt_two_pi_shift
    (nondegenerateAt_neg (nondegenerateAt_half_pi hdL hdU (ne_of_gt hd0)))
  have he : -(Real.pi/2)+2*Real.pi=3*Real.pi/2 := by ring
  simpa only [he] using h

/-- All targets in an entire closed period are covered, including its four exceptional points. -/
theorem nondegenerateAt_on_period {d x : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (hx0 : 0≤x) (hxT : x≤2*Real.pi) : NondegenerateAt d x := by
  have hdL : -(1/2:ℝ)<d := by linarith
  by_cases hs : sin x=0
  · obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hs
    have hn0r : (0:ℝ)≤n := by nlinarith only [hn,hx0,Real.pi_pos]
    have hn2r : (n:ℝ)≤2 := by nlinarith only [hn,hxT,Real.pi_pos]
    have hn0 : (0:ℤ)≤n := by exact_mod_cast hn0r
    have hn2 : n≤2 := by exact_mod_cast hn2r
    have hcases : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases hcases with h | h | h
    · subst n
      have hx : x=0 := by simpa using hn.symm
      rw [hx]
      exact nondegenerateAt_zero hdL hdU (ne_of_gt hd0)
    · subst n
      have hx : x=Real.pi := by simpa using hn.symm
      rw [hx]
      exact nondegenerateAt_pi hd0 hdU
    · subst n
      have hx : x=2*Real.pi := by simpa using hn.symm
      rw [hx]
      simpa only [zero_add] using
        nondegenerateAt_two_pi_shift (nondegenerateAt_zero hdL hdU (ne_of_gt hd0))
  · by_cases hc : cos x=0
    · obtain ⟨n,hn⟩ := Real.cos_eq_zero_iff.mp hc
      have hn0r : (0:ℝ)≤n := by
        by_contra h
        have hnneg : (n:ℝ)<0 := lt_of_not_ge h
        have hnnegI : n<0 := by exact_mod_cast hnneg
        have hnle : n≤-1 := by omega
        have hnleR : (n:ℝ)≤-1 := by exact_mod_cast hnle
        nlinarith only [hn,hx0,Real.pi_pos,hnleR]
      have hn1r : (n:ℝ)≤1 := by
        by_contra h
        have hnmore : (1:ℝ)<n := lt_of_not_ge h
        have hnmoreI : (1:ℤ)<n := by exact_mod_cast hnmore
        have hnge : 2≤n := by omega
        have hngeR : (2:ℝ)≤n := by exact_mod_cast hnge
        nlinarith only [hn,hxT,Real.pi_pos,hngeR]
      have hn0 : (0:ℤ)≤n := by exact_mod_cast hn0r
      have hn1 : n≤1 := by exact_mod_cast hn1r
      have hcases : n=0 ∨ n=1 := by omega
      rcases hcases with h | h
      · subst n
        have hx : x=Real.pi/2 := by simpa using hn
        rw [hx]
        exact nondegenerateAt_half_pi hdL hdU (ne_of_gt hd0)
      · subst n
        have hx : x=3*Real.pi/2 := by norm_num at hn ⊢; exact hn
        rw [hx]
        exact nondegenerateAt_three_half_pi hd0 hdU
    · exact nondegenerateAt_symmetric hd0 hdU hs hc


theorem nondegenerateAt_periodic (d : ℝ) :
    Function.Periodic (NondegenerateAt d) (2*Real.pi) := by
  intro x
  apply propext
  constructor
  · intro h
    have h1 := nondegenerateAt_neg
      (nondegenerateAt_two_pi_shift (nondegenerateAt_neg h))
    have he : -(-(x+2*Real.pi)+2*Real.pi)=x := by ring
    simpa only [he] using h1
  · exact nondegenerateAt_two_pi_shift

/-- Every real representative of every target on the original circle has a
nondegenerate resonant quartet; no exceptional target or Umklapp lift is deleted. -/
theorem nondegenerateAt_every_target {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (x : ℝ) :
    NondegenerateAt d x := by
  have hT : 0<2*Real.pi := by positivity
  let x0 := toIcoMod hT 0 x
  have hx0 := toIcoMod_mem_Ico hT 0 x
  have hx : NondegenerateAt d x0 :=
    nondegenerateAt_on_period hd0 hdU hx0.1 (by simpa only [zero_add] using hx0.2.le)
  have he := (nondegenerateAt_periodic d).zsmul (toIcoDiv hT 0 x) x0
  rw [show x0+toIcoDiv hT 0 x • (2*Real.pi)=x from
    toIcoMod_add_toIcoDiv_zsmul hT 0 x] at he
  exact he.symm ▸ hx

end
end Resonance.PinnedGeometry
