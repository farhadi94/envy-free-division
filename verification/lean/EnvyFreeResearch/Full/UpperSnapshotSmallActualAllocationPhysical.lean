import EnvyFreeResearch.Full.UpperSnapshotSmallActualAllocation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators unitInterval ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperStageMeasurable UpperLogicalPreparation Chores
variable {n m J : ℕ}

theorem firstEndowment_subset (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first : Circle) :
    domain (firstEndowment policy origin cutter cuts selected t first).cells ⊆ domain origin.cells := by
  intro x hx
  obtain ⟨c,hc,hx⟩ := mem_domain.mp hx
  have hh := mem_domain.mpr ⟨c,(List.mem_filter.mp hc).1,hx⟩
  rwa [firstRestored_domain] at hh

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (measureProfile μ) policy)
  (origin : State n) (hgood : WellFormed μ origin) (cutter : Fin n)
  (hpositive : 0 < (μ cutter).real (domain origin.cells))
  (cuts : Fin (m+2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
  (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
  (selected : Finset (Fin (m+1))) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
include hpolicy hgood hpositive hzero hmono hsep ht ht1

theorem firstAllocation_wellFormed (first second : Circle) :
    WellFormed μ (firstAllocationFrom origin cutter cuts selected t first
      (firstRun policy origin cutter cuts selected t first)
      (secondRun (J:=J) policy origin cutter cuts selected t first second)) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hw := first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first
  have hp := firstRemainder_positive μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 first
  have hr := execute_records μ policy hpolicy _ hw.2.1 cutter hp (shifts (remainderTargets J t)) second
  have ho := execute_wellFormed μ policy hpolicy _ hw.2.1 cutter hp (shifts (remainderTargets J t)) second
  rw [firstAllocationFrom_actual]
  exact ⟨hw.1.1,hw.1.2.1,ho.2.2.1,UpperEndpointCache.recordedHistory_mono _ hw.1.2.2.2 hr.1⟩

theorem second_all_parts (hJ : 0 < J) (hfit : (J : ℝ)*t < 1) (first second : Circle) :
    (⋃ j, domain (secondPiece hJ policy origin cutter cuts selected t first second j).cells) =
      domain (firstRemainder policy origin cutter cuts selected t first).cells ∧
    Pairwise (fun i j => Disjoint (domain (secondPiece hJ policy origin cutter cuts selected t first second i).cells)
      (domain (secondPiece hJ policy origin cutter cuts selected t first second j).cells)) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hw := (first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first).2.1
  have hp := firstRemainder_positive μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 first
  have hh := shared_circle_partition μ policy hpolicy _ hw cutter hp hJ (remainderTargets J t)
    (remainderTargets_strict hJ t ht hfit) (remainderTargets_zero hJ t ht hfit)
    (remainderTargets_last t) second
  exact ⟨hh.2.2.1,hh.2.2.2.1⟩

theorem first_second_cover (hJ : 0 < J) (hfit : (J : ℝ)*t < 1) (first second : Circle) :
    domain (firstEndowment policy origin cutter cuts selected t first).cells ∪
      (⋃ j, domain (secondPiece hJ policy origin cutter cuts selected t first second j).cells) =
      domain origin.cells := by
  rw [(second_all_parts μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit first second).1]
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  rw [(first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first).2.2]
  have hsub := firstEndowment_subset policy origin cutter cuts selected t first
  ext x
  constructor
  · rintro (hx | hx)
    · exact hsub hx
    · exact hx.1
  · intro hx
    by_cases hf : x ∈ domain (firstEndowment policy origin cutter cuts selected t first).cells
    · exact Or.inl hf
    · exact Or.inr ⟨hx,hf⟩

theorem first_second_disjoint (hJ : 0 < J) (hfit : (J : ℝ)*t < 1)
    (first second : Circle) (j : Fin J) :
    Disjoint (domain (firstEndowment policy origin cutter cuts selected t first).cells)
      (domain (secondPiece hJ policy origin cutter cuts selected t first second j).cells) := by
  have hs := firstSource_positive μ origin hgood cutter hpositive cuts selected t ht ht1
  have hc := (second_all_parts μ policy hpolicy origin hgood cutter hpositive cuts hzero hmono hsep selected t ht ht1 hJ hfit first second).1
  have hsub : domain (secondPiece hJ policy origin cutter cuts selected t first second j).cells ⊆
      domain origin.cells \ domain (firstEndowment policy origin cutter cuts selected t first).cells := by
    rw [← (first_partition μ policy hpolicy origin hgood cutter cuts selected t hs first).2.2,← hc]
    intro x hx
    exact mem_iUnion.mpr ⟨j,hx⟩
  exact disjoint_sdiff_right.mono_right hsub

end EnvyFreeResearch.Full.UpperSnapshotSmall
