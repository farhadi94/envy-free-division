import EnvyFreeResearch.Full.RefinedUpperBoundaryError
import EnvyFreeResearch.Full.UpperVirtualCorrections

/-! Actual correction error with all inherited accepted endpoints charged.
Rejected attempts are absent from the physical descriptor list. The endpoint
count depends only on completed recipients, not the number of retries. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.RefinedUpperRetainedGeometry
open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperCorrectionLoop
  UpperCircularStage UpperAggregateInterpolation UpperGridInterpolation UpperLogicalCells
  UpperCorrectionTrace UpperVirtualCorrections

variable {n : ℕ}
abbrev Index (s : LoopState n) := (Fin s.accepted.length ⊕ Unit) × Bool

def points (s : LoopState n) (candidate : Correction) (p : Index s) : ℝ :=
  let r := Sum.elim s.accepted.get (fun _ => candidate) p.1
  if p.2 then r.last else r.first

theorem accepted_endpoints (s : LoopState n) (candidate : Correction)
    (record : Correction) (hr : record ∈ s.accepted) : EndpointIn (points s candidate) record := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
  exact ⟨⟨(.inl i, false), rfl⟩, ⟨(.inl i, true), rfl⟩⟩

theorem candidate_endpoints (s : LoopState n) (candidate : Correction) :
    EndpointIn (points s candidate) candidate :=
  ⟨⟨(.inr (), false), rfl⟩, ⟨(.inr (), true), rfl⟩⟩

theorem point_count (s : LoopState n) : Fintype.card (Index s) = 2 * (s.accepted.length + 1) := by
  simp [Index, Fintype.card_prod, Fintype.card_sum, Nat.mul_comm]

/-- A concrete candidate correction has normalized discrepancy at most 4kA
when its own and all previously accepted endpoints have error at most 2A.
Old physical joins do not enter the count. -/
theorem candidate_error {Row : Type*} [Fintype Row] [Nonempty Row] {g k : ℕ}
    (μ : Row → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (normalizer : Row → ℝ) (buffer : List Component)
    (physical virtual : List Component)
    (hdom : domain physical = domain buffer ∩ domain virtual)
    (cuts : Fin (g + 2) → ℝ) (hcuts : Monotone cuts) (hzero : cuts 0 = 0)
    (hvirtual : ∀ p, Recorded virtual p → ∃ e, cuts e = p)
    (policy : Policy n) (s : LoopState n) (hconsistent : Consistent physical s)
    (job : Job n) (start : UpperCircular.Circle)
    (hcount : s.accepted.length < k) (i j : Row) (A : ℝ) (hA : 0 ≤ A)
    (hprior : ∀ record ∈ s.accepted,
      physicalError μ normalizer buffer cuts record.first i j ≤ 2 * A ∧
      physicalError μ normalizer buffer cuts record.last i j ≤ 2 * A)
    (hnew :
      physicalError μ normalizer buffer cuts
        (descriptor policy s.current job.owner job.deficit start).first i j ≤ 2 * A ∧
      physicalError μ normalizer buffer cuts
        (descriptor policy s.current job.owner job.deficit start).last i j ≤ 2 * A) :
    let C := payment policy s.current job.owner job.deficit start
    |(μ i).real C / normalizer i - (μ j).real C / normalizer j -
      UpperEnvelope.estimate (physicalRows μ normalizer buffer cuts)
        (UpperEnvelope.uniformCells (cell (domain buffer) cuts)) i j C| ≤ 4 * k * A := by
  let candidate := descriptor policy s.current job.owner job.deficit start
  let ps := points s candidate
  have hend := virtualPayment_recorded cuts ps virtual hvirtual s
    (accepted_endpoints s candidate) candidate (candidate_endpoints s candidate)
  have hactual := actual_payment_inter policy physical virtual (domain buffer) hdom s hconsistent job start
  have hb := physical_intersection_error_le μ normalizer buffer cuts hcuts hzero ps
    (virtualPayment virtual s candidate) _ hactual hend i j
  have hgood (p : Index s) : physicalError μ normalizer buffer cuts (ps p) i j ≤ 2 * A := by
    rcases p with ⟨r, b⟩
    cases r with
    | inl r =>
      have h := hprior (s.accepted.get r) (List.get_mem _ _)
      cases b with
      | false => exact h.1
      | true => exact h.2
    | inr r =>
      cases b with
      | false => exact hnew.1
      | true => exact hnew.2
  apply hb.trans
  calc
    _ ≤ ∑ _ : Index s, 2 * A := Finset.sum_le_sum (fun p _ => hgood p)
    _ = (Fintype.card (Index s) : ℝ) * (2 * A) := by simp
    _ ≤ (2 * (k : ℝ)) * (2 * A) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show Fintype.card (Index s) ≤ 2 * k by rw [point_count]; omega))
      (by positivity)
    _ = 4 * k * A := by ring

end EnvyFreeResearch.Full.RefinedUpperRetainedGeometry
