import EnvyFreeResearch.Full.UpperComponentGroups
import EnvyFreeResearch.Full.UpperLogicalIsolation
import EnvyFreeResearch.Full.UpperRecordedGridProgram

/-! Actual recorded old-plus-seed package states, computed entirely from
returned grid data. Cache provenance from immutable old snapshots is explicit. -/

noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperRepairPackages

open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperLogicalIsolation UpperLogicalPreparation UpperRepairJobs UpperSeedMatrix UpperBatchPermutation

variable {n k coarse fine : ℕ}

def packages (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) : State n :=
  UpperComponentAssembly.packages old (dataSeedState hk active origin data L theta labels pi threshold)
    (fun j => (jobEquiv hk j).2) data.2.2.history c

theorem packages_history (hk : 2 ≤ k) (active : Fin k → Fin n) (origin : State n) (old : Fin k → State n)
    (data : UpperGridData.Data n coarse fine) (L : ℕ) (theta : I) (labels : Fin (coarse + 1) → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) :
    (packages hk active origin old data L theta labels pi threshold c).history = data.2.2.history := rfl

theorem packages_measurable {X : Type} [MeasurableSpace X] (hk : 2 ≤ k) (active : Fin k → Fin n)
    (origin : X → State n) (old : X → Fin k → State n) (data : X → UpperGridData.Data n coarse fine)
    (L : ℕ) (theta : I) (labels : X → Fin (coarse + 1) → I) (pi : X → Equiv.Perm (Fin k))
    (threshold : X → Fin (jobCount k - 1 + 1) → Fin (L + 1))
    (horigin : Measurable origin) (hold : ∀ c, Measurable (fun x => old x c)) (hdata : Measurable data)
    (hlabels : ∀ c, Measurable (fun x => labels x c)) (hpi : Measurable pi)
    (hthreshold : ∀ j, Measurable (fun x => threshold x j)) (c : Fin k) :
    Measurable (fun x => packages hk active (origin x) (old x) (data x) L theta (labels x) (pi x) (threshold x) c) :=
  UpperComponentAssembly.packages_measurable old _ _ _ hold
    (dataSeedState_measurable hk active origin data L theta labels pi threshold horigin hdata hlabels hpi hthreshold)
    (state_history_measurable.comp (measurable_snd.comp (measurable_snd.comp hdata))) c

section Actual
variable [Nonempty (Fin k)]
  (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
  (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
  (active : Fin k → Fin n) (origin : State n) (hgood : WellFormed μ origin)
  (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
include hpolicy hgood hpositive

theorem seeds_subset (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (j : Fin (jobCount k - 1 + 1)) :
    domain (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold j).cells ⊆ domain origin.cells := by
  rw [dataSeedState_domain μ policy hpolicy active origin hgood hpositive]
  exact (Seeds.seed_subset _ _ _ _).trans (iUnion_subset fun a =>
    seedCells_subset μ policy hpolicy active origin hgood hpositive hk q m L draw theta labels pi j a)

theorem seeds_disjoint (hk : 2 ≤ k) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (hbudget : 2 * (jobCount k * L) < q + 1) (theta : I) (labels : Parent k q → I)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) :
    Pairwise (fun i j => Disjoint
      (domain (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
        L theta labels pi threshold i).cells)
      (domain (dataSeedState hk active origin (UpperGridMerge.prepare policy active origin q m draw)
        L theta labels pi threshold j).cells)) := by
  intro i j hij
  rw [dataSeedState_domain μ policy hpolicy active origin hgood hpositive,
    dataSeedState_domain μ policy hpolicy active origin hgood hpositive]
  exact Seeds.seed_disjoint _ _
    (seedCells_disjoint μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget theta labels pi) threshold hij

theorem packages_domain (hk : 2 ≤ k) (old : Fin k → State n) (q m L : ℕ) (draw : Fin m → Fin k × I)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) :
    domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold c).cells =
      Seeds.package (seedSystem hk policy active origin q m L draw theta labels pi)
        (seedCells hk policy active origin q m L draw theta labels pi) (fun c => domain (old c).cells) threshold c := by
  rw [packages, UpperComponentAssembly.packages_domain]
  simp_rw [dataSeedState_domain μ policy hpolicy active origin hgood hpositive]
  rfl

theorem packages_wellFormed (hk : 2 ≤ k) (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (holdHistory : ∀ c, (old c).history ⊆ origin.history)
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) :
    WellFormed μ (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold c) := by
  obtain ⟨trace, _, hhistory⟩ := UpperRecordedGridProgram.prepare_executes policy active origin q m draw
  have hext : origin.history ⊆ (UpperGridMerge.prepare policy active origin q m draw).2.2.history := by
    rw [hhistory]
    exact fun _ h => List.mem_append_left _ h
  apply UpperComponentAssembly.packages_wellFormed μ old _ _ _ hold
    (dataSeedState_wellFormed μ policy hpolicy active origin hgood hpositive hk q m L draw theta labels pi threshold)
    (seeds_disjoint μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget theta labels pi threshold)
    (fun c j => (holdbuffer c).mono_right
      (seeds_subset μ policy hpolicy active origin hgood hpositive hk q m L draw theta labels pi threshold j))
    (UpperGridMerge.prepare_wellFormed μ policy hpolicy active origin hgood hpositive q m draw).2.2.1
    (fun c _ h => hext (holdHistory c h)) (fun _ => Subset.rfl) c

theorem packages_values (hk : 2 ≤ k) (old : Fin k → State n) (hold : ∀ c, WellFormed μ (old c))
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (i c : Fin k) :
    (μ (active i)).real (domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold c).cells) /
      (μ (active i)).real (domain (reserveState policy active origin q m draw theta labels).cells) =
      cachedMatrix hk policy active origin old q m L draw theta labels pi threshold i c := by
  rw [packages_domain μ policy hpolicy active origin hgood hpositive]
  exact packages_physical μ policy hpolicy active origin hgood hpositive hk old hold holdbuffer
    q m L draw hbudget theta labels pi threshold i c


theorem packages_pairwise (hk : 2 ≤ k) (old : Fin k → State n)
    (holdpair : Pairwise (fun i j => Disjoint (domain (old i).cells) (domain (old j).cells)))
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
    (theta : I) (labels : Parent k q → I) (pi : Equiv.Perm (Fin k))
    (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) :
    Pairwise (fun i j => Disjoint
      (domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw)
        L theta labels pi threshold i).cells)
      (domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw)
        L theta labels pi threshold j).cells)) := by
  intro i j hij
  rw [packages_domain μ policy hpolicy active origin hgood hpositive,
    packages_domain μ policy hpolicy active origin hgood hpositive]
  exact UpperLogicalIsolation.packages_disjoint μ policy hpolicy active origin hgood hpositive hk old
    holdpair holdbuffer q m L draw hbudget theta labels pi threshold hij

theorem packages_reserve_disjoint (hk : 2 ≤ k) (old : Fin k → State n)
    (holdbuffer : ∀ c, Disjoint (domain (old c).cells) (domain origin.cells))
    (q m L : ℕ) (draw : Fin m → Fin k × I) (hbudget : 2 * (jobCount k * L) < q + 1)
    (theta : I) (cap : ℝ) (labels : Parent k q → I)
    (hpass : UpperLogicalPreparationGuard.guard policy active origin q m (requests k L) theta cap draw labels = true)
    (pi : Equiv.Perm (Fin k)) (threshold : Fin (jobCount k - 1 + 1) → Fin (L + 1)) (c : Fin k) :
    Disjoint (domain (packages hk active origin old (UpperGridMerge.prepare policy active origin q m draw)
      L theta labels pi threshold c).cells)
      (domain (reserveState policy active origin q m draw theta labels).cells) := by
  rw [packages_domain μ policy hpolicy active origin hgood hpositive, Seeds.package]
  apply disjoint_union_left.mpr
  refine ⟨(holdbuffer c).mono_right
    (reserveState_subset μ policy hpolicy active origin hgood hpositive q m draw theta labels), ?_⟩
  apply disjoint_iUnion_left.mpr
  intro j
  split_ifs
  · exact (seeds_avoid_reserve μ policy hpolicy active origin hgood hpositive hk q m L draw hbudget
      theta cap labels hpass pi threshold).mono_left (subset_iUnion (fun j => Seeds.seed _ _ threshold j) j)
  · exact empty_disjoint _

end Actual
end EnvyFreeResearch.Full.UpperRepairPackages
