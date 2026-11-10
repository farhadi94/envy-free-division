import EnvyFreeResearch.Full.RefinedUpperPreparationSeeds
import EnvyFreeResearch.Full.UpperComponentGroups
import EnvyFreeResearch.Full.UpperRepairAllocation
import EnvyFreeResearch.Full.UpperRecordedGridProgram

/-! Actual old-plus-seed packages and finite assignment, with no extra queries. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.RefinedUpperPreparation
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalPreparation UpperRepairJobs UpperSeedMatrix UpperBatchPermutation
variable {n k coarse fine : ℕ}

def packages (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) : State n :=
  UpperComponentAssembly.packages old (dataSeedState hk active origin data L pi threshold)
    (fun j => (jobEquiv hk j).2) data.2.2.history c

theorem packages_history (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) :
    (packages hk active origin old data L pi threshold c).history = data.2.2.history := rfl

theorem packages_measurable {X : Type} [MeasurableSpace X] (hk : 2 ≤ k) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (data : X → UpperGridData.Data n coarse fine)
    (L : ℕ) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (horigin : Measurable origin) (hold : ∀ c, Measurable (fun x => old x c)) (hdata : Measurable data)
    (hpi : Measurable pi)
    (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (c : Fin k) :
    Measurable (fun x => packages hk active (origin x) (old x) (data x) L (pi x) (threshold x) c) :=
  UpperComponentAssembly.packages_measurable old _ _ _ hold
    (dataSeedState_measurable hk active origin data L pi threshold horigin hdata hpi hthreshold)
    (state_history_measurable.comp (measurable_snd.comp (measurable_snd.comp hdata))) c


section Actual
variable [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem seeds_subset (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (j : Fin (jobCount k - 1 + 1)) :
    domain (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
      L pi threshold j).cells ⊆ domain origin.cells := by
  rw [dataSeedState_domain μ policy hpolicy active origin hgood hpositive]
  exact (Seeds.seed_subset _ _ _ _).trans (iUnion_subset fun a =>
    seedCells_subset μ policy hpolicy active origin hgood hpositive hk q m L draw pi j a)

theorem seeds_disjoint (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2 * (jobCount k * L) < q + 1)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) :
    Pairwise (fun i j => Disjoint
      (domain (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
        L pi threshold i).cells)
      (domain (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
        L pi threshold j).cells)) := by
  intro i j hij
  rw [dataSeedState_domain μ policy hpolicy active origin hgood hpositive,
    dataSeedState_domain μ policy hpolicy active origin hgood hpositive]
  exact Seeds.seed_disjoint _ _
    (seedCells_disjoint μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget pi) threshold hij

theorem packages_domain (hk : 2 ≤ k) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) :
    domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L pi threshold c).cells =
      Seeds.package (seedSystem hk policy active origin q m L draw pi)
        (seedCells hk policy active origin q m L draw pi) (fun c => domain (old c).cells) threshold c := by
  rw [packages, UpperComponentAssembly.packages_domain]
  simp_rw [dataSeedState_domain μ policy hpolicy active origin hgood hpositive]
  rfl

theorem packages_wellFormed (hk : 2 ≤ k) (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (holdHistory : ∀ c, (old c).history ⊆ origin.history)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
    (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) :
    WellFormed μ (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L pi threshold c) := by
  obtain ⟨trace, _, hhistory⟩ := UpperRecordedGridProgram.prepare_executes policy active origin q m draw
  have hext : origin.history ⊆ (UpperGridMerge.prepare policy active origin q m draw).2.2.history := by
    rw [hhistory]
    exact fun _ h => List.mem_append_left _ h
  apply UpperComponentAssembly.packages_wellFormed μ old _ _ _ hold
    (dataSeedState_wellFormed μ policy hpolicy active origin hgood hpositive hk q m L draw pi threshold)
    (seeds_disjoint μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget pi threshold)
    (fun c j => (holdbuffer c).mono_right
      (seeds_subset μ policy hpolicy active origin hgood hpositive hk q m L draw pi threshold j))
    (UpperGridMerge.prepare_wellFormed μ policy hpolicy active origin hgood hpositive q m draw).2.2.1
    (fun c _ h => hext (holdHistory c h)) (fun _ => Subset.rfl) c


theorem packages_values (hk : 2 ≤ k) (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2*(jobCount k*L) < q+1)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (i c : Fin k) :
    let data := UpperGridMerge.prepare policy active origin q m draw
    (μ (active i)).real (domain (packages hk active origin old data L pi threshold c).cells) /
      (μ (active i)).real (domain (dataRetained active origin data L).cells) =
      dataMatrix hk active origin old data L pi threshold i c := by
  dsimp only
  rw [packages_domain μ policy hpolicy active origin hgood hpositive]
  have h := UpperLogicalIsolation.normalized_package_mass (fun i => μ (active i))
    (fun i => (μ (active i)).real (domain (dataRetained active origin
      (UpperGridMerge.prepare policy active origin q m draw) L).cells))
    (fun _ => measureReal_nonneg) (seedSystem hk policy active origin q m L draw pi)
    (seedCells hk policy active origin q m L draw pi)
    (seedCells_measurable μ policy hpolicy active origin hgood hpositive hk q m L draw pi)
    (seedCells_disjoint μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget pi)
    (fun c => domain (old c).cells)
    (fun c j a => (holdbuffer c).mono_right
      (seedCells_subset μ policy hpolicy active origin hgood hpositive hk q m L draw pi j a))
    (fun j a r => dataWeights_physical μ policy hpolicy active origin hgood hpositive q m L draw _ a r)
    threshold i c
  have holdEq : (fun r c => (μ (active r)).real (domain (old c).cells) /
      (μ (active r)).real (domain (dataRetained active origin
        (UpperGridMerge.prepare policy active origin q m draw) L).cells)) =
      UpperLogicalIsolation.oldMatrix active old (dataRetained active origin
        (UpperGridMerge.prepare policy active origin q m draw) L) := by
    funext r c
    unfold UpperLogicalIsolation.oldMatrix
    rw [total_correct μ (old c) (hold c),dataRetained_execute,
      total_correct μ _ (retainedState_wellFormed μ policy hpolicy active origin hgood hpositive q m draw _)]
  rw [holdEq] at h
  exact h

theorem packages_pairwise (hk : 2 ≤ k) (old : Fin k → State n)
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2*(jobCount k*L) < q+1)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) :
    Pairwise (fun i j => Disjoint
      (domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw) L pi threshold i).cells)
      (domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw) L pi threshold j).cells)) := by
  intro i j hij
  rw [packages_domain μ policy hpolicy active origin hgood hpositive,
    packages_domain μ policy hpolicy active origin hgood hpositive]
  exact Seeds.packages_disjoint _ _
    (seedCells_disjoint μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget pi)
    _ holdpair (fun c j a => (holdbuffer c).mono_right
      (seedCells_subset μ policy hpolicy active origin hgood hpositive hk q m L draw pi j a)) threshold hij

theorem packages_retained_disjoint (hk : 2 ≤ k) (old : Fin k → State n)
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2*(jobCount k*L) < q+1)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k-1+1) → Fin (L+1)) (c : Fin k) :
    Disjoint (domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw) L pi threshold c).cells)
      (domain (dataRetained active origin (UpperGridMerge.prepare policy active origin q m draw) L).cells) := by
  rw [packages_domain μ policy hpolicy active origin hgood hpositive,Seeds.package]
  apply disjoint_union_left.mpr
  constructor
  · apply (holdbuffer c).mono_right
    rw [dataRetained_execute]
    exact reserveState_subset μ policy hpolicy active origin hgood hpositive q m draw 0 _
  · apply disjoint_iUnion_left.mpr
    intro j
    split_ifs
    · apply (disjoint_iUnion_left.mpr (fun a =>
        witnesses_retained_disjoint μ policy hpolicy active origin hgood hpositive q m L draw hbudget _ a)).mono_left
      exact Seeds.seed_subset _ _ _ _
    · exact empty_disjoint _

end Actual
end EnvyFreeResearch.Full.RefinedUpperPreparation
