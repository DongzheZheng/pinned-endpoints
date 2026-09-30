import Resonance.PinnedMeasure

/-! The fundamental-cell versus full-real-lift dictionary for the original
periodic coarea.  All three momentum coordinates are translated together
with their integer windings; the fourth leg retains their signed sum. -/
open Real MeasureTheory Set
open scoped ENNReal MeasureTheory Topology ContDiff
namespace Resonance.PinnedPeriodicity
open Resonance.PinnedGeometry Resonance.PinnedCharts Resonance.PinnedMeasure
noncomputable section

def period : ℝ := 2*Real.pi

theorem period_pos : 0<period := by unfold period; positivity

def latticeShift (n : Fin 3→ℤ) : Ambient :=
  WithLp.toLp 2 (fun i => (n i:ℝ)*period)

def fundamentalCell : Set Ambient := {k | ∀ i, k i∈Ico 0 period}

def cellCoarea (d : ℝ) : Measure Ambient :=
  (liftedRegularCoarea d).restrict fundamentalCell

theorem fundamentalCell_measurable : MeasurableSet fundamentalCell := by
  simp only [fundamentalCell,setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_Ico.preimage (coordinateProjection i).continuous.measurable

theorem omega_periodic (d : ℝ) : Function.Periodic (omega d) period := by
  intro x
  simp [period,omega,Resonance.Collision.pinnedDispersion]

theorem velocity_periodic (d : ℝ) : Function.Periodic (velocity d) period := by
  intro x
  simp [velocity,period,omega,Resonance.Collision.pinnedDispersion]

theorem periodic_coordinate {β : Type*} {f : ℝ→β}
    (hf : Function.Periodic f period) (n : Fin 3→ℤ) (k : Ambient) (i : Fin 3) :
    f ((k+latticeShift n) i)=f (k i) := by
  simpa [latticeShift,zsmul_eq_mul] using hf.zsmul (n i) (k i)

theorem periodic_fourth {β : Type*} {f : ℝ→β}
    (hf : Function.Periodic f period) (n : Fin 3→ℤ) (k : Ambient) :
    f ((k+latticeShift n) 0+(k+latticeShift n) 1-(k+latticeShift n) 2)=
      f (k 0+k 1-k 2) := by
  have he : (k+latticeShift n) 0+(k+latticeShift n) 1-(k+latticeShift n) 2 =
      (k 0+k 1-k 2)+((n 0+n 1-n 2:ℤ):ℝ)*period := by
    simp [latticeShift]
    ring
  rw [he]
  simpa [zsmul_eq_mul] using hf.zsmul (n 0+n 1-n 2) (k 0+k 1-k 2)

theorem liftedEnergy_lattice (d : ℝ) (n : Fin 3→ℤ) (k : Ambient) :
    liftedEnergy d (k+latticeShift n)=liftedEnergy d k := by
  simp only [liftedEnergy,energyDefect]
  rw [periodic_coordinate (omega_periodic d),periodic_coordinate (omega_periodic d),
    periodic_coordinate (omega_periodic d),periodic_fourth (omega_periodic d)]

theorem energyGradient_lattice (d : ℝ) (n : Fin 3→ℤ) (k : Ambient) :
    energyGradient d (k+latticeShift n)=energyGradient d k := by
  dsimp only [energyGradient]
  rw [periodic_coordinate (velocity_periodic d),periodic_coordinate (velocity_periodic d),
    periodic_coordinate (velocity_periodic d),periodic_fourth (velocity_periodic d)]

theorem regularSurface_lattice (d : ℝ) (n : Fin 3→ℤ) (k : Ambient) :
    k+latticeShift n∈regularSurface d ↔ k∈regularSurface d := by
  simp only [regularSurface,mem_setOf_eq,liftedEnergy_lattice,energyGradient_lattice]

theorem invariantRelation_lattice {φ : ℝ→ℂ} (hp : Function.Periodic φ period)
    (n : Fin 3→ℤ) (k : Ambient) :
    invariantRelation φ (k+latticeShift n) ↔ invariantRelation φ k := by
  simp only [invariantRelation]
  rw [periodic_coordinate hp,periodic_coordinate hp,periodic_coordinate hp,periodic_fourth hp]

/-- Every real representative has an exact half-open-cell representative;
no null-boundary convention is used in this coverage. -/
theorem exists_cell_representative (k : Ambient) :
    ∃ n : Fin 3→ℤ, ∃ q∈fundamentalCell, k=q+latticeShift n := by
  let n : Fin 3→ℤ := fun i => toIcoDiv period_pos 0 (k i)
  let q : Ambient := WithLp.toLp 2 (fun i => toIcoMod period_pos 0 (k i))
  refine ⟨n,q,?_,?_⟩
  · intro i
    exact toIcoMod_mem_Ico' period_pos (k i)
  · ext i
    have he := toIcoMod_add_toIcoDiv_zsmul period_pos 0 (k i)
    simpa only [q,n,latticeShift,WithLp.ofLp_toLp,Pi.add_apply,zsmul_eq_mul] using he.symm


/-- A periodic null set in one exact fundamental cell is null for the
complete regular coarea on all real lifts.  This proof uses countably many
isometric translates, and does not discard coordinate boundaries. -/
theorem periodic_null_of_cell_null {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {A : Set Ambient}
    (hper : ∀ (n : Fin 3→ℤ) (k : Ambient),
      k+latticeShift n∈A ↔ k∈A)
    (hA : cellCoarea d A=0) : liftedRegularCoarea d A=0 := by
  have hbase : (μH[2] : Measure Ambient) ((A∩fundamentalCell)∩regularSurface d)=0 := by
    rw [cellCoarea,Measure.restrict_apply' fundamentalCell_measurable] at hA
    have hh := regularHausdorff_absolutelyContinuous hd0 hdU hA
    rwa [Measure.restrict_apply' (regularSurface_measurable hd0 hdU)] at hh
  let B := (A∩fundamentalCell)∩regularSurface d
  have hshift (n : Fin 3→ℤ) :
      (μH[2] : Measure Ambient) ((fun q => q+latticeShift n) '' B)=0 := by
    rw [(isometry_add_right (latticeShift n)).hausdorffMeasure_image (Or.inl (by norm_num))]
    exact hbase
  have hall := measure_iUnion_null hshift
  have hsub : A∩regularSurface d ⊆
      ⋃ n : Fin 3→ℤ, (fun q => q+latticeShift n) '' B := by
    rintro k ⟨hkA,hkreg⟩
    obtain ⟨n,q,hq,he⟩ := exists_cell_representative k
    apply mem_iUnion.mpr
    refine ⟨n,q,?_,he.symm⟩
    refine ⟨⟨?_,hq⟩,?_⟩
    · exact (hper n q).mp (he ▸ hkA)
    · exact (regularSurface_lattice d n q).mp (he ▸ hkreg)
  have hnull := measure_mono_null hsub hall
  apply withDensity_absolutelyContinuous _ _ 
  rw [Measure.restrict_apply' (regularSurface_measurable hd0 hdU)]
  exact hnull

/-- For a periodic function, the invariant equation on the original
half-open momentum cell is equivalent to the equation on all real lifts.
Every Umklapp translate remains in this equivalence. -/
theorem invariant_cell_iff_lifted {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ→ℂ} (hp : Function.Periodic φ period) :
    (∀ᵐ k ∂cellCoarea d, invariantRelation φ k) ↔ liftedInvariant d φ := by
  constructor
  · intro h
    rw [ae_iff] at h
    rw [liftedInvariant,ae_iff]
    apply periodic_null_of_cell_null hd0 hdU _ h
    intro n k
    exact not_congr (invariantRelation_lattice hp n k)
  · intro h
    exact ae_restrict_of_ae h


abbrev Circle := AddCircle period
abbrev CircleMomenta := Fin 3→Circle

def quotientCoordinates (k : Ambient) : CircleMomenta := fun i => (k i : Circle)

theorem quotientCoordinates_continuous : Continuous quotientCoordinates := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' period).comp (coordinateProjection i).continuous

/-- The regular coarea on the periodic momentum variables, defined by its
exact half-open Euclidean fundamental domain.  Critical energy points remain
excluded as in regularSurface; this is not an unqualified distribution δ(F). -/
def circleRegularCoarea (d : ℝ) : Measure CircleMomenta :=
  (cellCoarea d).map quotientCoordinates

def circleInvariantRelation (φ : Circle→ℂ) (k : CircleMomenta) : Prop :=
  φ (k 0)+φ (k 1)=φ (k 2)+φ (k 0+k 1-k 2)

def circleInvariant (d : ℝ) (φ : Circle→ℂ) : Prop :=
  ∀ᵐ k ∂circleRegularCoarea d, circleInvariantRelation φ k

def periodicLift (φ : Circle→ℂ) : ℝ→ℂ := fun x => φ (x:Circle)

theorem periodicLift_periodic (φ : Circle→ℂ) :
    Function.Periodic (periodicLift φ) period := by
  intro x
  simp [periodicLift]

theorem circleInvariant_lifted {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : Circle→ℂ} (hφ : circleInvariant d φ) :
    liftedInvariant d (periodicLift φ) := by
  apply (invariant_cell_iff_lifted hd0 hdU (periodicLift_periodic φ)).mp
  have h := ae_of_ae_map quotientCoordinates_continuous.measurable.aemeasurable hφ
  filter_upwards [h] with k hk
  simpa [circleInvariantRelation,invariantRelation,periodicLift,quotientCoordinates,
    AddCircle.coe_add,AddCircle.coe_sub] using hk

/-- The invariant hypothesis on the original periodic variables supplies
the same full-parent identity on every constructed real source-average
chart, without a separate hypothesis about winding sectors. -/
theorem circleInvariant_every_target_chart {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : Circle→ℂ} (hφ : circleInvariant d φ) (x : ℝ) :
    ∃ y z : ℝ, ∃ H : ℝ×ℝ→ℝ, ∃ r κ : ℝ, 0<r ∧ 0<κ ∧ H (x,z)=y ∧
      ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r) ∧
      (∀ p ∈ Metric.ball x r ×ˢ Metric.ball z r,
        energyDefect d p.1 (H p) p.2=0 ∧
        κ ≤ |velocity d (H p)-velocity d (p.1+H p-p.2)| ∧
        κ ≤ |zDifferential H p| ∧ κ ≤ |zDifferential H p-1|) ∧
      (∀ᵐ p ∂volume.restrict (Metric.ball x r ×ˢ Metric.ball z r),
        periodicLift φ p.1+periodicLift φ (H p)=
          periodicLift φ p.2+periodicLift φ (p.1+H p-p.2)) :=
  every_target_invariant_chart hd0 hdU (circleInvariant_lifted hd0 hdU hφ) x

end
end Resonance.PinnedPeriodicity
