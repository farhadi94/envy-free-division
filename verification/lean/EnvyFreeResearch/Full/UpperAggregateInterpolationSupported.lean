import EnvyFreeResearch.Full.UpperAggregateInterpolationPhysical
import EnvyFreeResearch.Full.UpperAggregateInterpolationStream
import EnvyFreeResearch.Full.UpperDomainDifferenceSequence

/-!
# Fixed physical joins do not create interpolation charges

The analytic row difference and envelope are supported on the fixed error
domain. Intersecting a recorded virtual union with that physical domain leaves
its discrepancy unchanged. Actual circular correction and difference operations
commute with this intersection, literally including endpoint ownership.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators unitInterval

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperRecordedDomain UpperLogicalCells UpperGridInterpolation UpperDomainDifference UpperPhysical

/-- A virtual circular piece intersected with the physical error domain is
exactly the physical piece on that intersection, in every empty/full/wrap case. -/
theorem physicalPiece_inter (R V : Set ℝ) (amount : I) (start : UpperCircular.Circle)
    (first last : ℝ) :
    physicalPiece (R ∩ V) amount start first last = R ∩ physicalPiece V amount start first last := by
  unfold physicalPiece
  split_ifs <;> ext x <;> simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false] <;> tauto

/-- Replaying the recorded descriptors on a virtual domain exactly tracks
physical deletion inside a fixed reserve; old physical joins remain internal. -/
theorem applyCorrection_inter (R : Set ℝ) (physical virtual : List Component)
    (hdom : domain physical = R ∩ domain virtual) (record : Correction) :
    domain (applyCorrection physical record) = R ∩ domain (applyCorrection virtual record) := by
  simp only [applyCorrection, removeCorrection_domain, hdom, physicalPiece_inter]
  ext x
  simp only [mem_inter_iff, mem_sdiff]
  tauto

theorem remaining_inter (R : Set ℝ) (physical virtual : List Component)
    (hdom : domain physical = R ∩ domain virtual) (records : List Correction) :
    domain (remaining physical records) = R ∩ domain (remaining virtual records) := by
  induction records generalizing physical virtual with
  | nil => exact hdom
  | cons record records ih =>
    exact ih _ _ (applyCorrection_inter R physical virtual hdom record)

/-- The returned correction itself has the same exact virtual/physical
factorization, including a first rejecting proposal that is never committed. -/
theorem correctionPiece_inter (R : Set ℝ) (physical virtual : List Component)
    (hdom : domain physical = R ∩ domain virtual) (record : Correction) :
    correctionPiece physical record = R ∩ correctionPiece virtual record := by
  simp only [correctionPiece, hdom, physicalPiece_inter]

/-- Each logical cell already has the required physical intersection form;
its first null endpoint is retained exactly. -/
theorem logicalCell_inter {g : ℕ} (R : Set ℝ) (cuts : Fin (g + 2) → ℝ) (e : Fin (g + 1)) :
    cell R cuts e = R ∩ (Ioc (cuts e.castSucc) (cuts e.succ) ∪
      if e = 0 then {cuts 0} else ∅) := by
  unfold cell
  split_ifs <;> ext x <;> simp only [mem_union, mem_inter_iff, mem_empty_iff_false] <;> tauto

variable {Row : Type*} [Fintype Row] [Nonempty Row] {g : ℕ}

/-- All envelope component measures are literally supported on the error
domain, so fixed gaps and physical joins add no boundary error. -/
theorem envelope_inter_domain (μ : Row → Measure ℝ) (normalizer : Row → ℝ)
    (buffer : List Component) (cuts : Fin (g + 2) → ℝ) (i j : Row) (E : Set ℝ) :
    UpperEnvelope.estimate (physicalRows μ normalizer buffer cuts)
      (UpperEnvelope.uniformCells (cell (domain buffer) cuts)) i j (domain buffer ∩ E) =
    UpperEnvelope.estimate (physicalRows μ normalizer buffer cuts)
      (UpperEnvelope.uniformCells (cell (domain buffer) cuts)) i j E := by
  unfold UpperEnvelope.estimate
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  rw [UpperEnvelope.uniformCell_real _ (fun e => cell_measurable _ (domain_measurable _) _ e),
    UpperEnvelope.uniformCell_real _ (fun e => cell_measurable _ (domain_measurable _) _ e)]
  congr 2
  ext x
  constructor
  · rintro ⟨hc, _, hE⟩
    exact ⟨hc, hE⟩
  · rintro ⟨hc, hE⟩
    exact ⟨hc, cell_subset _ _ e hc, hE⟩

theorem discrepancy_inter_domain (μ : Row → Measure ℝ) (normalizer : Row → ℝ)
    (buffer : List Component) (cuts : Fin (g + 2) → ℝ) (i j : Row) (E : Set ℝ) :
    discrepancy μ normalizer buffer cuts i j (domain buffer ∩ E) =
      discrepancy μ normalizer buffer cuts i j E := by
  simp only [discrepancy, ← inter_assoc, inter_self, envelope_inter_domain]

/-- The actual physical union may contain arbitrarily many old component
joins. Only its virtual selected-interval boundaries need be original grid
points or generated endpoints. -/
theorem physical_intersection_error_le {Generated : Type*} [Fintype Generated]
    (μ : Row → Measure ℝ) [∀ r, IsFiniteMeasure (μ r)] [∀ r, NullSingletonClass (μ r)]
    (normalizer : Row → ℝ) (buffer : List Component) (cuts : Fin (g + 2) → ℝ)
    (hmono : Monotone cuts) (hzero : cuts 0 = 0) (points : Generated → ℝ)
    (virtual : List Component) (actual : Set ℝ) (hactual : actual = domain buffer ∩ domain virtual)
    (hendpoints : ∀ c ∈ virtual,
      ((∃ p, cuts p = c.left) ∨ ∃ j, points j = c.left) ∧
      ((∃ p, cuts p = c.right) ∨ ∃ j, points j = c.right)) (i j : Row) :
    |(μ i).real actual / normalizer i - (μ j).real actual / normalizer j -
      UpperEnvelope.estimate (physicalRows μ normalizer buffer cuts)
        (UpperEnvelope.uniformCells (cell (domain buffer) cuts)) i j actual| ≤
      ∑ p, physicalError μ normalizer buffer cuts (points p) i j := by
  rw [hactual, envelope_inter_domain]
  exact physical_recorded_union_error_le μ normalizer buffer cuts hmono hzero points virtual hendpoints i j

/-- The simultaneous event stated for actual physical sets. Their virtual
boundary list uses only the immutable grid and generated points; arbitrary
old joins are supplied by intersection with the fixed error domain. -/
def BadSupportedRecordedUnion {Generated : Type*} (μ : Row → Measure ℝ) (normalizer : Row → ℝ)
    (buffer : List Component) (cuts : Fin (g + 2) → ℝ) (points : Generated → ℝ) (b : ℝ) : Prop :=
  ∃ i j virtual actual, RecordedEndpoints cuts points virtual ∧ actual = domain buffer ∩ domain virtual ∧
    b * UpperGridSensitivity.distance (physicalRows μ normalizer buffer cuts) i j <
      |(μ i).real actual / normalizer i - (μ j).real actual / normalizer j -
        UpperEnvelope.estimate (physicalRows μ normalizer buffer cuts)
          (UpperEnvelope.uniformCells (cell (domain buffer) cuts)) i j actual|

theorem badSupportedRecordedUnion_iff {Generated : Type*} [Fintype Generated]
    (μ : Row → Measure ℝ) (normalizer : Row → ℝ) (buffer : List Component)
    (cuts : Fin (g + 2) → ℝ) (points : Generated → ℝ) (b : ℝ) :
    BadSupportedRecordedUnion μ normalizer buffer cuts points b ↔
      BadRecordedUnion μ normalizer buffer cuts points b := by
  constructor
  · rintro ⟨i, j, virtual, actual, hends, hactual, hbad⟩
    rw [hactual, envelope_inter_domain] at hbad
    exact ⟨i, j, virtual, hends, hbad⟩
  · rintro ⟨i, j, virtual, hends, hbad⟩
    refine ⟨i, j, virtual, domain buffer ∩ domain virtual, hends, rfl, ?_⟩
    rw [envelope_inter_domain]
    exact hbad

end EnvyFreeResearch.Full.UpperAggregateInterpolation
