import EnvyFreeResearch.Full.ChoresTerminalScan
import EnvyFreeResearch.Full.ChoresRevealSelection

/-! The terminal cohort is the literal list selected by the finite scan.
Restriction retains every old package, closing all rejected live roots. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Equalizers Snapshot Frontier Scheduler
open scoped Classical

variable {n : ℕ} {RootId : Type*} [Fintype RootId]
  (data : Outer.Data n RootId) (original : RootId → Snapshot.Output n)
  (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
  (t : Reveal.TerminalClass n) (roots : List (Fin data.size))
  (hchoice : Reveal.actualChoice (fun s => (original (data.source s)).equalizers) p r H
    (data.pending.partition.component p) data.pending.partition.representative=.terminal t roots)

include hchoice

theorem cohort_facts : roots.Nodup ∧ roots.length=t.participants.card+1 ∧
    ∀ s : Fin roots.length,
      Reveal.classify (original ((data.filter roots).source s)).equalizers p r H
        ((data.filter roots).pending.partition.component p)
        (data.filter roots).pending.partition.representative=.inl t := by
  have h := Reveal.actual_choice_correct (fun s => (original (data.source s)).equalizers) p r H
    (data.pending.partition.component p) data.pending.partition.representative
  rw [hchoice] at h
  exact ⟨h.1,h.2.1,fun s => h.2.2 _ (List.get_mem _ s)⟩

theorem cohort_nonempty : Nonempty (Fin roots.length) := by
  have h := (cohort_facts data original p r H t roots hchoice).2.1
  exact ⟨⟨0,by omega⟩⟩

theorem cohort_more_roots : Fintype.card (t.participants) < Fintype.card (Fin roots.length) := by
  simp only [Fintype.card_coe,Fintype.card_fin]
  rw [(cohort_facts data original p r H t roots hchoice).2.1]
  omega

theorem cohort_good (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (good : data.Good original cost r H) :
    (data.filter roots).Good original cost r H :=
  Outer.filter_good data original cost r H good roots
    (cohort_facts data original p r H t roots hchoice).1

theorem cohort_retains_allocations :
    ((data.filter roots).allPackages.flatMap ChoreComposition.Package.allocations).Perm
      (data.allPackages.flatMap ChoreComposition.Package.allocations) :=
  Outer.filter_allocations_perm data roots
    (cohort_facts data original p r H t roots hchoice).1

end EnvyFreeResearch.Full.Chores.Terminal
