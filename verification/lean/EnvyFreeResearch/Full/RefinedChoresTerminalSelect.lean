import EnvyFreeResearch.Full.RefinedChoresGroupSelect
import EnvyFreeResearch.Full.RefinedChoresTerminalScans

/-! Actual terminal cohorts and protected-pivot exclusion for root-local
components. Different roots need not share any component partition. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.Frontier RefinedChoresRootState
open scoped Classical
variable {n : ℕ} {RootId : Type*}

def terminalTag (p : Fin n) : Reveal.TerminalClass n → RefinedChoresPool.Class n
  | .inl (A,B) => .inl (.inr (p,A,B))
  | .inr A => .inr (p,A)

structure TerminalGroup (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ) where
  label : Fin n
  terminalClass : Reveal.TerminalClass n
  roots : Fin (terminalClass.participants.card+1) ↪ Fin data.size
  label_eq : ∀ s, data.sourceLabel normal (roots s) = label
  class_eq : ∀ s, Reveal.classify (original (data.source (roots s))).equalizers label r H
    (data.sourceSet normal (roots s)) (data.pending (roots s)).partition.representative = .inl terminalClass

variable (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)

theorem terminal_class_scan (s : Fin data.size) (p : Fin n) (t : Reveal.TerminalClass n)
    (h : data.classify normal original r H s = terminalTag p t) :
    data.sourceLabel normal s = p ∧ Reveal.classify (original (data.source s)).equalizers p r H
      (data.sourceSet normal s) (data.pending s).partition.representative = .inl t := by
  cases t with
  | inl pair =>
    obtain ⟨A,B⟩ := pair
    unfold Data.classify terminalTag at h
    cases hs : data.scan normal original r H s with
    | outside q => simp only [hs] at h; cases h
    | exhausted q => simp only [hs] at h; cases h
    | atomic a =>
      rw [hs] at h
      have he := Sum.inr.inj (Sum.inl.inj h)
      have hp : data.sourceLabel normal s = p := congrArg (fun x => x.1) he
      refine ⟨hp,?_⟩
      have hs' : Frontier.scan (original (data.source s)).equalizers p r H (data.sourceSet normal s) = .atomic a := by
        rw [← hp]
        exact hs
      rw [Reveal.classify,hs']
      have hpair := congrArg (fun x : Fin n × Finset (Fin n) × Finset (Fin n) => x.2) he
      simpa only [hp] using congrArg (fun x : Finset (Fin n) × Finset (Fin n) =>
        (Sum.inl (Sum.inl x) : Reveal.TerminalClass n ⊕ Fin n)) hpair
  | inr A =>
    unfold Data.classify terminalTag at h
    cases hs : data.scan normal original r H s with
    | outside q => simp only [hs] at h; cases h
    | atomic a => simp only [hs] at h; cases h
    | exhausted q =>
      rw [hs] at h
      have he := Sum.inr.inj h
      have hp : data.sourceLabel normal s = p := congrArg Prod.fst he
      refine ⟨hp,?_⟩
      have hs' : Frontier.scan (original (data.source s)).equalizers p r H (data.sourceSet normal s) = .exhausted q := by
        rw [← hp]
        exact hs
      rw [Reveal.classify,hs']
      have hA := congrArg Prod.snd he
      simpa only [hp] using congrArg (fun x : Finset (Fin n) =>
        (Sum.inl (Sum.inr x) : Reveal.TerminalClass n ⊕ Fin n)) hA

theorem terminal_group_exists (p : Fin n) (t : Reveal.TerminalClass n)
    (hcount : n+1 ≤ (Finset.univ.filter (fun s => data.classify normal original r H s = terminalTag p t)).card) :
    Nonempty (TerminalGroup data normal original r H) := by
  have hcard : Fintype.card (Fin (t.participants.card+1)) ≤
      (Finset.univ.filter (fun s => data.classify normal original r H s = terminalTag p t)).card := by
    have hc : t.participants.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ t.participants
    simp only [Fintype.card_fin]
    omega
  obtain ⟨roots,hroots⟩ := Function.Embedding.exists_of_card_le_finset hcard
  have hs (s : Fin (t.participants.card+1)) := terminal_class_scan data normal original r H (roots s) p t
    (Finset.mem_filter.mp (hroots ⟨s,rfl⟩)).2
  exact ⟨⟨p,t,roots,fun s => (hs s).1,fun s => (hs s).2⟩⟩

theorem source_full_label (s : Fin data.size) (hfull : data.sourceSet normal s = Finset.univ) :
    data.sourceLabel normal s = data.protectedLabel := by
  have hm : data.protectedLabel ∈ data.sourceSet normal s := hfull ▸ Finset.mem_univ _
  change data.protectedLabel ∈ componentSet (data.pending s) (data.sink normal s) at hm
  rw [mem_componentSet] at hm
  exact hm.symm.trans (data.protected_fixed s)

variable (group : TerminalGroup data normal original r H)
abbrev TerminalGroup.Root := Fin (group.terminalClass.participants.card+1)

theorem TerminalGroup.protected (c : Fin n)
    (homitted : ∀ root, c ∉ ProtectedPivot.eligible (original root) H r data.protectedLabel)
    (s : group.Root) : data.sourceSet normal (group.roots s) ≠ Finset.univ ∨
      c ∉ ProtectedPivot.eligible (original (data.source (group.roots s))) H r group.label := by
  by_cases hf : data.sourceSet normal (group.roots s) = Finset.univ
  · right
    have hp := source_full_label data normal (group.roots s) hf
    rw [group.label_eq] at hp
    rw [hp]
    exact homitted _
  · exact Or.inl hf

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.terminal_group_exists
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.protected
