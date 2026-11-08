import EnvyFreeResearch.Full.ChoresRevealSelection
import EnvyFreeResearch.Full.ChoresFrontierInterface
import EnvyFreeResearch.Full.ChoresProtectedPivot

/-! Actual cohort labels retain the physical scan semantics. In particular,
the protected cutter is omitted from every exhausted participant set even
when the source component has already absorbed all agents. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Reveal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers Snapshot Frontier
open scoped Classical

variable {n : ℕ}

theorem classify_atomic (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C A B : Finset (Fin n)) (representative : Fin n → Fin n)
    (h : classify table p r H C representative=.inl (.inl (A,B))) :
    ∃ a : Fin n, scan table p r H C=.atomic a ∧
      atomicParticipants (eligible (weight table p) (rankOf table p) r H) (rankOf table p) a=A ∧
      largeMask (weight table p) r H a=B := by
  unfold classify at h
  cases hs : scan table p r H C with
  | outside q => rw [hs] at h; cases h
  | exhausted q =>
    rw [hs] at h
    have hn := Sum.inl.inj h
    cases hn
  | atomic a =>
    rw [hs] at h
    have hp := Sum.inl.inj (Sum.inl.inj h)
    exact ⟨a,rfl,congrArg Prod.fst hp,congrArg Prod.snd hp⟩

theorem classify_exhausted (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C A : Finset (Fin n)) (representative : Fin n → Fin n)
    (h : classify table p r H C representative=.inl (.inr A)) :
    ∃ q : Fin n, scan table p r H C=.exhausted q ∧
      eligible (weight table p) (rankOf table p) r H=A := by
  unfold classify at h
  cases hs : scan table p r H C with
  | outside q => rw [hs] at h; cases h
  | atomic a =>
    rw [hs] at h
    have hn := Sum.inl.inj h
    cases hn
  | exhausted q =>
    rw [hs] at h
    exact ⟨q,rfl,Sum.inr.inj (Sum.inl.inj h)⟩

theorem classify_outside (table : Table n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) (representative : Fin n → Fin n) (target : Fin n)
    (h : classify table p r H C representative=.inr target) :
    ∃ q : Fin n, scan table p r H C=.outside q ∧ representative q=target := by
  unfold classify at h
  cases hs : scan table p r H C with
  | outside q =>
    rw [hs] at h
    exact ⟨q,rfl,Sum.inr.inj h⟩
  | atomic a => rw [hs] at h; cases h
  | exhausted q => rw [hs] at h; cases h

variable {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U : Set ℝ} {c : Fin n} {out : Output n}

theorem snapshot_eligible_eq (hs : Sound cost U c out) (p : Fin n) (r : Fin n → ℝ) (H : ℝ) :
    eligible (weight out.equalizers p) (rankOf out.equalizers p) r H=
      ProtectedPivot.eligible out H r p := by
  ext i
  simp only [Frontier.eligible,ProtectedPivot.eligible,Finset.mem_filter,Finset.mem_univ,true_and,
    snapshot_tail_gap hs p i]

theorem protected_eligible_proper (hs : Sound cost U c out) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (hprotected : c ∉ ProtectedPivot.eligible out H r p) :
    eligible (weight out.equalizers p) (rankOf out.equalizers p) r H ≠ Finset.univ := by
  rw [snapshot_eligible_eq hs]
  intro h
  exact hprotected (h ▸ Finset.mem_univ _)

variable {xs : List (Output n)} {H : ℝ} {R : Set ℝ}
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (s : Fin xs.length) (hs : Sound cost U c (xs.get s)) (p : Fin n)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (C : Finset (Fin n)) (representative : Fin n → Fin n)

include hsep hs hr hH hscale

theorem tracked_atomic_member (A B : Finset (Fin n))
    (hclass : classify (xs.get s).equalizers p (fun i => (cost i).real R) H C representative=.inl (.inl (A,B))) :
    ∃ a : Fin n,
      atomicParticipants (eligible (weight (xs.get s).equalizers p) (rankOf (xs.get s).equalizers p)
        (fun i => (cost i).real R) H) (rankOf (xs.get s).equalizers p) a=A ∧
      largeMask (weight (xs.get s).equalizers p) (fun i => (cost i).real R) H a=B ∧
      PhysicalCorrect cost ((xs.get s).piece p) ((xs.get s).parents p) (xs.get s).equalizers p
        (baselines (xs.get s).parents) (fun i => (cost i).real R) H C (.atomic a) := by
  obtain ⟨a,ha,hA,hB⟩ := classify_atomic _ p _ H C A B representative hclass
  have hphysical := (tracked_scan_correct hsep s hs p hr hH hscale C).1
  rw [ha] at hphysical
  exact ⟨a,hA,hB,hphysical⟩

theorem tracked_exhausted_member (A : Finset (Fin n))
    (hprotected : c ∉ ProtectedPivot.eligible (xs.get s) H (fun i => (cost i).real R) p)
    (hclass : classify (xs.get s).equalizers p (fun i => (cost i).real R) H C representative=.inl (.inr A)) :
    A ≠ Finset.univ ∧ ∃ q : Fin n,
      eligible (weight (xs.get s).equalizers p) (rankOf (xs.get s).equalizers p)
        (fun i => (cost i).real R) H=A ∧
      PhysicalCorrect cost ((xs.get s).piece p) ((xs.get s).parents p) (xs.get s).equalizers p
        (baselines (xs.get s).parents) (fun i => (cost i).real R) H C (.exhausted q) := by
  obtain ⟨q,hq,hA⟩ := classify_exhausted _ p _ H C A representative hclass
  have hphysical := (tracked_scan_correct hsep s hs p hr hH hscale C).1
  rw [hq] at hphysical
  refine ⟨?_,q,hA,hphysical⟩
  rw [← hA]
  exact protected_eligible_proper hs p _ H hprotected

theorem tracked_outside_member (target : Fin n)
    (hcomponent : ∀ i, i ∈ C ↔ representative i=representative p)
    (hclass : classify (xs.get s).equalizers p (fun i => (cost i).real R) H C representative=.inr target) :
    target ≠ representative p ∧ ∃ q : Fin n, representative q=target ∧
      PhysicalCorrect cost ((xs.get s).piece p) ((xs.get s).parents p) (xs.get s).equalizers p
        (baselines (xs.get s).parents) (fun i => (cost i).real R) H C (.outside q) := by
  obtain ⟨q,hq,heq⟩ := classify_outside _ p _ H C representative target hclass
  have hphysical := (tracked_scan_correct hsep s hs p hr hH hscale C).1
  rw [hq] at hphysical
  refine ⟨?_,q,heq,hphysical⟩
  intro ht
  exact hphysical.2.1 ((hcomponent q).mpr (heq.trans ht))

end EnvyFreeResearch.Full.Chores.Reveal
