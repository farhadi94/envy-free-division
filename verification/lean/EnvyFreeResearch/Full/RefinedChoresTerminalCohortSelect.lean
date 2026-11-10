import EnvyFreeResearch.Full.RefinedChoresTerminalSelect

/-! Actual terminal classes give donor paths inside each independently
scanned source component, before any affine query program is executed. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.Frontier Chores.Equalizers
open RefinedChoresRootState RefinedChoresPartialGraph
open scoped Classical
variable {n : ℕ} {RootId : Type*}

theorem terminal_participants_subset (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) (representative : Fin n → Fin n) (t : Reveal.TerminalClass n)
    (hclass : Reveal.classify table p r H C representative = .inl t)
    (hr : 0 ≤ r p) (hH : 0 < H) : t.participants ⊆ C := by
  have hv := stop_valid (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p
    (owner_eligible (weight table p) (rankOf table p) r H p (rank_owner table p) hr hH)
  cases t with
  | inl pair =>
    obtain ⟨A,B⟩ := pair
    obtain ⟨a,ha,hA,_⟩ := Reveal.classify_atomic table p r H C A B representative hclass
    have hb : largestBad (weight table p) r H
        (rankOf table p (stop (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p).agent) = some a := by
      cases hb : largestBad (weight table p) r H
          (rankOf table p (stop (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p).agent) with
      | none =>
        simp only [scan,hb] at ha
        cases hs : stop (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p <;>
          simp only [hs] at ha <;> cases ha
      | some b =>
        have he : b = a := Outcome.atomic.inj (by simpa only [scan,hb] using ha)
        simp only [he]
    intro i hi
    change i ∈ A at hi
    rw [← hA] at hi
    obtain ⟨hi,hri⟩ := Finset.mem_filter.mp hi
    have hlo := (largestBad_some (weight table p) r H _ a hb).1
    exact before_stop_internal _ _ _ _ hv i hi (by omega)
  | inr A =>
    obtain ⟨q,hq,hA⟩ := Reveal.classify_exhausted table p r H C A representative hclass
    change A ⊆ C
    rw [← hA]
    cases hs : stop (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p with
    | outside j =>
      cases hb : largestBad (weight table p) r H (rankOf table p j) <;>
        simp [scan,hs,Stop.agent,hb] at hq
    | exhausted j =>
      rw [hs] at hv
      exact hv.2.1

variable (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H)
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
include hr hH

theorem TerminalGroup.participants_subset (s : group.Root) :
    group.terminalClass.participants ⊆ data.sourceSet normal (group.roots s) :=
  terminal_participants_subset _ group.label r H _ _ group.terminalClass (group.class_eq s) (hr _) hH

theorem TerminalGroup.path (s : group.Root) (j : Fin n) (hj : j ∈ group.terminalClass.participants) :
    Relation.ReflTransGen (fun a b => b ∈ (data.frames (group.roots s)).allowed a) j group.label := by
  have h := donor_path (data.frames (group.roots s)) (data.tracked (group.roots s))
    (data.sink normal (group.roots s)) j
    (TerminalGroup.participants_subset data normal original r H group hr hH s hj)
  simpa only [← group.label_eq s,Data.sourceLabel] using h

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.path
