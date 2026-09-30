import Resonance.PinnedSmoothing
import Resonance.PinnedMeasurable

/-! Iterated source averaging for the same nondegenerate resonance charts.
The derivatives fall on compactly supported averaging weights, not on the
measurable invariant. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedAveraging
noncomputable section
open Resonance.PinnedSmoothing

theorem contDiffOn_of_derivative_chain {I : Set ℝ} (hI : IsOpen I)
    {A : ℕ → ℝ → ℂ}
    (hA : ∀ n x, x ∈ I → HasDerivAt (A n) (A (n+1) x) x) :
    ∀ n, ContDiffOn ℝ ∞ (A n) I := by
  have hall : ∀ m n : ℕ, ContDiffOn ℝ m (A n) I := by
    intro m
    induction m with
    | zero =>
      intro n
      exact contDiffOn_zero.mpr (fun x hx => (hA n x hx).continuousAt.continuousWithinAt)
    | succ m ih =>
      intro n
      rw [show ((m+1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞)+1 by simp]
      apply (contDiffOn_succ_iff_deriv_of_isOpen hI).mpr
      refine ⟨fun x hx => (hA n x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · simp
      · apply (ih (n+1)).congr
        intro x hx
        exact (hA n x hx).deriv
  intro n
  exact contDiffOn_infty.mpr (fun m => hall m n)

/-- The common inverse-Jacobian bound and local source integrability imply
all orders of target regularity.  Bounds for every differentiated weight
are consequences of a compact rectangle, not extra hypotheses. -/
theorem actual_L1_average_contDiffOn
    {I I₀ J K Z₀ : Set ℝ}
    (hI : IsOpen I) (hI₀ : IsOpen I₀) (hJ : IsOpen J)
    (hK : IsCompact K) (hIK : I ⊆ K) (hKI : K ⊆ I₀)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ J)
    (hZ₀ : IsOpen Z₀) (ha₀ : a ∈ Z₀) (hb₀ : b ∈ Z₀)
    {H χ : ℝ × ℝ → ℝ}
    (hH : ContDiffOn ℝ ∞ H (I₀ ×ˢ J))
    (hχ : ContDiffOn ℝ ∞ χ (I₀ ×ˢ J))
    (hZ : ∀ p ∈ I₀ ×ˢ J, partialZ H p ≠ 0)
    (hzero : EqOn χ 0 (I₀ ×ˢ Z₀))
    {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmap : ∀ x ∈ I, AEMeasurable (fun z => H (x,z)) (volume.restrict (Icc a b)))
    (hdom : ∀ x ∈ I,
      (volume.restrict (Icc a b)).map (fun z => H (x,z)) ≤ C • ν)
    {f : ℝ → ℂ} (hf : Integrable f ν) :
    ContDiffOn ℝ ∞ (fun x => ∫ z in Icc a b, χ (x,z) • f (H (x,z))) I := by
  let W := iteratedWeight H χ
  have hWs : ∀ n, ContDiffOn ℝ ∞ (W n) (I₀ ×ˢ J) :=
    contDiffOn_iteratedWeight (hI₀.prod hJ) hH hχ hZ
  have hWzero : ∀ n, EqOn (W n) 0 (I₀ ×ˢ Z₀) :=
    iteratedWeight_zero_on_open (hI₀.prod hZ₀) hzero
  have hWI : I ×ˢ J ⊆ I₀ ×ˢ J := Set.prod_mono (hIK.trans hKI) (Subset.refl J)
  have hbnd (n : ℕ) : ∃ B : ℝ, ∀ x ∈ I, ∀ z ∈ Icc a b, ‖W n (x,z)‖ ≤ B := by
    obtain ⟨B,hB⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
      ((hWs n).continuousOn.mono (Set.prod_mono hKI hsub))
    exact ⟨B,fun x hx z hz => hB (x,z) ⟨hIK hx,hz⟩⟩
  have hmeas (n : ℕ) (x : ℝ) (hx : x ∈ I) :
      AEStronglyMeasurable (fun z => W n (x,z)) (volume.restrict (Icc a b)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Icc
    exact (hWs n).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hKI (hIK hx),hsub hz⟩)
  let A : ℕ → ℝ → ℂ := fun n x => ∫ z in Icc a b, W n (x,z) • f (H (x,z))
  have hA (n : ℕ) (x : ℝ) (hx : x ∈ I) : HasDerivAt (A n) (A (n+1) x) x := by
    obtain ⟨B,hB⟩ := hbnd n
    obtain ⟨B',hB'⟩ := hbnd (n+1)
    apply source_average_hasDerivAt_of_smooth_identity hI hC hmap hdom
      (hmeas n) (hmeas (n+1))
      (fun x hx => (ae_restrict_mem measurableSet_Icc).mono (fun z hz => hB x hx z hz))
      (fun x hx => (ae_restrict_mem measurableSet_Icc).mono (fun z hz => hB' x hx z hz))
      _ hf hx
    intro g _hgcompact hgsmooth y hy
    exact actual_smooth_average_derivative hI hJ hab hsub (hH.mono hWI)
      ((hWs n).mono hWI) (fun p hp => hZ p (hWI hp))
      (fun y hy => ⟨hWzero n ⟨hKI (hIK hy),ha₀⟩,
        hWzero n ⟨hKI (hIK hy),hb₀⟩⟩) hgsmooth hy
  exact contDiffOn_of_derivative_chain hI hA 0

end
end Resonance.PinnedAveraging
