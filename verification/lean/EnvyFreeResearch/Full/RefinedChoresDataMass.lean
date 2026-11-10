import EnvyFreeResearch.Full.RefinedChoresGroupCommit
import EnvyFreeResearch.Full.RefinedChoresTerminalSelect

/-! Active mass, fixed closed roots and protected-source bookkeeping.
Unselected preprocessing roots remain physically present in the closed pool. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.Frontier ChoreComposition
open scoped Classical BigOperators
variable {n : ℕ} {RootId : Type*}

def Data.activeMass (data : Data n RootId) : ℕ := ∑ s, (data.packages s).ids.length

def Data.Omitted (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (c : Fin n) (r : Fin n → ℝ) (H : ℝ) : Prop :=
  ∀ s : Fin data.size, c ∉ ProtectedPivot.eligible (original (data.source s)) H r data.protectedLabel

variable [Fintype RootId] (data : Data n RootId) (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
include good

theorem total_mass : data.activeMass + (data.closed.flatMap Package.ids).length = Fintype.card RootId := by
  have h := good.all_ids.length_eq
  simpa only [Data.allPackages,List.flatMap_append,List.length_append,List.length_flatMap,
    List.map_ofFn,List.sum_ofFn,Function.comp_def,Finset.length_toList,Finset.card_univ,
    Data.activeMass,Nat.add_comm] using h

theorem active_mass_preserved (after : Data n RootId) (hafter : after.Good original cost r H)
    (hclosed : after.closed=data.closed) : after.activeMass=data.activeMass := by
  have h₁ := total_mass data original cost r H good
  have h₂ := total_mass after original cost r H hafter
  rw [hclosed] at h₂
  omega

theorem actual_class_available_mass (normal : data.Normal)
    (hmass : data.activeMass=RefinedChoresPool.poolSize n) :
    ∃ cl : RefinedChoresPool.Class n,
      n+1 ≤ (Finset.univ.filter (fun s => data.classify normal original r H s = cl)).card := by
  apply RefinedChoresPool.cannot_stall n Finset.univ (data.classify normal original r H)
    (fun s => (data.packages s).ids.length)
  · intro s _
    exact active_weight_bound data original cost r H good s
  · exact hmass

omit good in
theorem TerminalGroup.protected_active (normal : data.Normal)
    (group : TerminalGroup data normal original r H) (c : Fin n)
    (homitted : data.Omitted original c r H) (s : group.Root) :
    data.sourceSet normal (group.roots s) ≠ Finset.univ ∨
      c ∉ ProtectedPivot.eligible (original (data.source (group.roots s))) H r group.label := by
  by_cases hf : data.sourceSet normal (group.roots s)=Finset.univ
  · right
    have hp := source_full_label data normal (group.roots s) hf
    rw [group.label_eq] at hp
    rw [hp]
    exact homitted _
  · exact Or.inl hf

omit good in
theorem Group.commit_omitted (normal : data.Normal) (group : Group data normal original r H)
    (out : RefinedChoresPhysicalPayment.Result (Root := group.Root) group.component)
    (c : Fin n) (ho : data.Omitted original c r H) :
    (Group.commit data normal original r H group out).Omitted original c r H := by
  intro s
  refine Fin.cases ?_ (fun i => ?_) s
  · exact ho (group.roots (Group.survivor data normal original r H group out))
  · exact ho ((remainingRoots data group.roots).get i)

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.actual_class_available_mass
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.commit_omitted
