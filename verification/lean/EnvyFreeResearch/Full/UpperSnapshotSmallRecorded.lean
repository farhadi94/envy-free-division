import EnvyFreeResearch.Full.UpperSnapshotSmallExpectation

/-! The shared-circle partition as cached recorded component states. Every
piece is a pure filter of the final refined atoms and retains the full history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable Chores
variable {n J : ℕ}

def selectState (state : State n) (keep : Component → Bool) : State n :=
  ⟨state.cells.filter keep, state.history⟩

def prefixAtom (amount : I) (start : Circle) (first last : ℝ) (c : Component) : Bool :=
  if amount = 0 then false else if amount = 1 then true else
    if value start < value (start + project amount) then decide (first < c.right ∧ c.right ≤ last)
    else decide (¬(last < c.right ∧ c.right ≤ first))

def partState (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (q : Fin (J + 1) → I) (start : Circle) (j : Fin J) : State n :=
  let result := partitionRun policy origin cutter q start
  selectState result.2 (fun c =>
    prefixAtom (q j.succ) start (result.1 ⟨0, hJ⟩) (boundary hJ result.1 j.succ) c &&
      !prefixAtom (q j.castSucc) start (result.1 ⟨0, hJ⟩) (boundary hJ result.1 j.castSucc) c)

theorem prefixAtom_iff (cs : List Component) (amount : I) (start : Circle) (first last : ℝ)
    (hfirst : SeparatedAt first cs) (hlast : SeparatedAt last cs)
    (c : Component) (hc : c ∈ cs) (x : ℝ) (hx : x ∈ c.carrier) :
    prefixAtom amount start first last c = true ↔
      x ∈ physicalPiece (domain cs) amount start first last := by
  have hmem : x ∈ domain cs := mem_domain.mpr ⟨c, hc, hx⟩
  unfold prefixAtom physicalPiece
  split_ifs with hz ho hw
  · simp
  · simpa using hmem
  · simpa only [decide_eq_true_eq, mem_inter_iff, hmem, true_and] using
      (separated_Ioc_iff cs first last hfirst hlast c hc hx).symm
  · simpa only [decide_eq_true_eq, mem_sdiff, hmem, true_and] using
      not_congr (separated_Ioc_iff cs last first hlast hfirst c hc hx).symm

theorem partitionRun_separated (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (q : Fin (J + 1) → I) (start : Circle) (j : Fin (J + 1)) :
    SeparatedAt (boundary hJ (partitionRun policy origin cutter q start).1 j)
      (partitionRun policy origin cutter q start).2.cells := by
  apply UpperGridCells.refineEndpoints_separated
  unfold boundary
  split_ifs <;> exact List.mem_ofFn.mpr ⟨_, rfl⟩

theorem first_partitionRun_separated (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (q : Fin (J + 1) → I) (start : Circle) :
    SeparatedAt ((partitionRun policy origin cutter q start).1 ⟨0, hJ⟩)
      (partitionRun policy origin cutter q start).2.cells := by
  apply UpperGridCells.refineEndpoints_separated
  exact List.mem_ofFn.mpr ⟨⟨0, hJ⟩, rfl⟩

theorem partState_domain (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (q : Fin (J + 1) → I) (start : Circle) (j : Fin J) :
    domain (partState hJ policy origin cutter q start j).cells = actualPart hJ policy origin cutter q start j := by
  let result := partitionRun policy origin cutter q start
  have hfirst := first_partitionRun_separated hJ policy origin cutter q start
  have hdom : domain result.2.cells = domain origin.cells := execute_domain _ _ _ _ _
  have he (i : Fin (J + 1)) (c : Component) (hc : c ∈ result.2.cells) (x : ℝ) (hx : x ∈ c.carrier) :
      prefixAtom (q i) start (result.1 ⟨0, hJ⟩) (boundary hJ result.1 i) c = true ↔
        x ∈ actualPrefix hJ policy origin cutter q start i := by
    have h := prefixAtom_iff result.2.cells (q i) start _ _ hfirst
      (partitionRun_separated hJ policy origin cutter q start i) c hc x hx
    rw [hdom] at h
    exact h
  have hsub : actualPart hJ policy origin cutter q start j ⊆ domain result.2.cells := by
    rw [hdom]
    exact sdiff_subset.trans (prefix_subset hJ _ _ _ _ _)
  change domain (result.2.cells.filter _) = _
  rw [domain_filter_carrier result.2.cells _ (actualPart hJ policy origin cutter q start j)]
  · exact inter_eq_right.mpr hsub
  · intro c hc x hx
    have h1 := he j.succ c hc x hx
    have h0 := he j.castSucc c hc x hx
    dsimp only [result] at h1 h0
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
    exact and_congr h1 (not_congr h0)

theorem partState_history (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (q : Fin (J + 1) → I) (start : Circle) (j : Fin J) :
    (partState hJ policy origin cutter q start j).history = (partitionRun policy origin cutter q start).2.history := rfl

section Correctness
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]

theorem selectState_wellFormed (state : State n) (hstate : WellFormed μ state) (keep : Component → Bool) :
    WellFormed μ (selectState state keep) := by
  refine ⟨hstate.1.filter _, hstate.2.1.filter _, hstate.2.2.1, ?_⟩
  intro i p hp
  exact hstate.2.2.2 i p (filter_recorded _ _ hp)

theorem partState_wellFormed (hJ : 0 < J) (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells))
    (q : Fin (J + 1) → I) (start : Circle) (j : Fin J) :
    WellFormed μ (partState hJ policy origin cutter q start j) :=
  selectState_wellFormed μ _ (execute_wellFormed μ policy hpolicy origin hgood cutter hpositive _ _) _

theorem partState_cached (hJ : 0 < J) (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
    (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
    (hpositive : 0 < (μ cutter).real (domain origin.cells))
    (q : Fin (J + 1) → I) (start : Circle) (j : Fin J) (i : Fin n) :
    total (partState hJ policy origin cutter q start j) i =
      (μ i).real (actualPart hJ policy origin cutter q start j) := by
  rw [total_correct μ _ (partState_wellFormed μ hJ policy hpolicy origin hgood cutter hpositive q start j),
    partState_domain]

end Correctness
end EnvyFreeResearch.Full.UpperSnapshotSmall
