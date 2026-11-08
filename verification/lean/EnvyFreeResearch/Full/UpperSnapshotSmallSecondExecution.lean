import EnvyFreeResearch.Full.UpperSnapshotSmallFirstLaws

/-! The second actual circle starts from the complete first-stage history.
Its conditional laws hold for each first-stage tape, including adaptive
legal root policies. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ}

def secondRun (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (first second : Circle) : (Fin J → ℝ) × State n :=
  partitionRun policy (firstRemainder policy origin cutter cuts selected t first) cutter
    (remainderTargets J t) second

def secondPiece (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (first second : Circle) (j : Fin J) : State n :=
  partState hJ policy (firstRemainder policy origin cutter cuts selected t first) cutter
    (remainderTargets J t) second j

theorem second_query_bound (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (first second : Circle) :
    (secondRun (J := J) policy origin cutter cuts selected t first second).2.history.length ≤
      origin.history.length + (J + 2) * (n + 1) := by
  have h1 := firstRestored_query_bound policy origin cutter cuts selected t first
  have h2 := execute_query_bound policy (firstRemainder policy origin cutter cuts selected t first)
    cutter (shifts (remainderTargets J t)) second
  change (secondRun (J := J) policy origin cutter cuts selected t first second).2.history.length ≤
    (firstRestored policy origin cutter cuts selected t first).history.length + J*(n+1) at h2
  nlinarith

theorem second_cut_bound (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m + 2) → ℝ) (selected : Finset (Fin (m + 1))) (t : ℝ)
    (first second : Circle) :
    ((secondRun (J := J) policy origin cutter cuts selected t first second).2.history.map Prod.fst).countP isCut ≤
      (origin.history.map Prod.fst).countP isCut + (J + 2) := by
  have h1 := firstRestored_cut_bound policy origin cutter cuts selected t first
  have h2 := execute_cut_bound policy (firstRemainder policy origin cutter cuts selected t first)
    cutter (shifts (remainderTargets J t)) second
  change ((secondRun (J := J) policy origin cutter cuts selected t first second).2.history.map Prod.fst).countP isCut ≤
    ((firstRestored policy origin cutter cuts selected t first).history.map Prod.fst).countP isCut + J at h2
  omega

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
  (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
  (selected : Finset (Fin (m + 1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
include hpolicy hgood hpositive hzero hmono hsep ht ht1

theorem second_piece_wellFormed (hJ : 0 < J) (first second : Circle) (j : Fin J) :
    WellFormed μ (secondPiece hJ policy origin cutter cuts selected t first second j) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hw := (first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first).2.1
  exact partState_wellFormed μ hJ policy hpolicy _ hw cutter
    (firstRemainder_positive μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 first)
    _ second j

theorem second_piece_mass (hJ : 0 < J) (hfit : (J : ℝ)*t < 1)
    (first second : Circle) (j : Fin J) (hj : j.val + 1 < J) :
    total (secondPiece hJ policy origin cutter cuts selected t first second j) cutter =
      t * (μ cutter).real (domain origin.cells) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hw := (first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first).2.1
  have hp := firstRemainder_positive μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 first
  change total (partState hJ policy _ cutter _ second j) cutter = _
  rw [remainder_partition_value μ policy hpolicy _ hw cutter hp hJ t ht hfit second j hj,
    firstRemainder_mass μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1]
  field_simp

theorem second_conditional_signed_mean (hmeas : MeasurablePolicy policy) (hJ : 2 ≤ J)
    (hfit : (J : ℝ)*t < 1) (signed : SignedMeasure ℝ)
    (hwhole : signed (domain origin.cells) = 0) (first : Circle) :
    (∫ second, signed (domain (secondPiece (J := J) (by omega) policy origin cutter cuts selected t first second
      ⟨0, by omega⟩).cells) ∂(volume : Measure Circle)) =
      -(t/(1-t))*signed (domain (firstEndowment policy origin cutter cuts selected t first).cells) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hw := first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first
  have hp := firstRemainder_positive μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 first
  change (∫ second, signed (domain (partState (J := J) (by omega) policy _ cutter _ second ⟨0, by omega⟩).cells)
    ∂(volume : Measure Circle)) = _
  rw [remainder_first_signed_expectation μ policy hpolicy _ hw.2.1 cutter hp hmeas hJ t ht hfit signed,
    hw.2.2, VectorMeasure.of_sdiff (domain_measurable _) (domain_measurable _)]
  · rw [hwhole]
    ring
  · intro x hx
    obtain ⟨c,hc,hx⟩ := mem_domain.mp hx
    have hc' := (List.mem_filter.mp hc).1
    have hd := mem_domain.mpr ⟨c,hc',hx⟩
    rwa [firstRestored_domain] at hd

end EnvyFreeResearch.Full.UpperSnapshotSmall
