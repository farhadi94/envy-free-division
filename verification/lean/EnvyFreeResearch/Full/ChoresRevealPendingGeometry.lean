import EnvyFreeResearch.Full.ChoresRevealPending

/-! Recorded outside proposals retain the exact stopping-mark and
all-small suffix facts needed when their component cycle is later paid. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Reveal
open Frontier Equalizers
open scoped Classical

variable {n : ℕ}

theorem scan_outside_data (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) (q : Fin n) (h : scan table p r H C=.outside q) :
    stop (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p=.outside q ∧
      largestBad (weight table p) r H (rankOf table p q)=none := by
  unfold scan at h
  cases hs : stop (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p with
  | outside j =>
    rw [hs] at h
    dsimp only [Stop.agent] at h
    cases hb : largestBad (weight table p) r H (rankOf table p j) with
    | some a => rw [hb] at h; cases h
    | none =>
      rw [hb] at h
      have hj : j=q := Outcome.outside.inj h
      subst j
      exact ⟨rfl,hb⟩
  | exhausted j =>
    rw [hs] at h
    dsimp only [Stop.agent] at h
    cases hb : largestBad (weight table p) r H (rankOf table p j) with
    | some a => rw [hb] at h; cases h
    | none => rw [hb] at h; cases h

theorem scan_outside_stop (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) (q : Fin n) (h : scan table p r H C=.outside q)
    (hr : 0 ≤ r p) (hH : 0 < H) :
    (Stop.outside q).Valid (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C ∧
      ∀ a : Fin n, rankOf table p q ≤ a.val → Small (weight table p) r H a := by
  obtain ⟨hstop,hscan⟩ := scan_outside_data table p r H C q h
  have hv := stop_valid (rankOf table p) (eligible (weight table p) (rankOf table p) r H) C p
    (owner_eligible (weight table p) (rankOf table p) r H p (rank_owner table p) hr hH)
  rw [hstop] at hv
  exact ⟨hv,largestBad_none (weight table p) r H _ hscan⟩

theorem outside_agent_scan (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) (representative : Fin n → Fin n) (target : Fin n)
    (hclass : classify table p r H C representative=.inr target) :
    scan table p r H C=.outside (outsideAgent table p r H C) := by
  obtain ⟨q,hq,_⟩ := classify_outside table p r H C representative target hclass
  simp only [outsideAgent,hq]

end EnvyFreeResearch.Full.Chores.Reveal
