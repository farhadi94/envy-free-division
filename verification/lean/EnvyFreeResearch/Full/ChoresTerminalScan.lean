import EnvyFreeResearch.Full.ChoresRevealPhysical
import EnvyFreeResearch.Full.ChoresOuterFilterSound

/-! Terminal cohorts are selected from the actual immutable-table scan.
The participant, whole-value and omitted-observer obligations of affine
compensation are consequences of that scan and clearance. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Terminal
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion OriginalAtoms Equalizers Snapshot Frontier
open scoped Classical

variable {n : ℕ}

def offer (out : Snapshot.Output n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) : List (Parent n) :=
  (scan out.equalizers p r H C).offer out.equalizers p (out.parents p)

def front (out : Snapshot.Output n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) : List (Parent n) :=
  (scan out.equalizers p r H C).front out.equalizers p

def atom (out : Snapshot.Output n) (p : Fin n) (r : Fin n → ℝ) (H : ℝ)
    (C : Finset (Fin n)) : Set ℝ :=
  match scan out.equalizers p r H C with
  | .atomic a =>
      ((atomsFromTable out.equalizers p).get
        (Fin.cast (atoms_from_table_length out.equalizers p).symm a)).domain (out.piece p)
  | _ => ∅

variable {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  {U : Set ℝ} {c : Fin n} {out : Snapshot.Output n}

theorem gap_eq (hs : Sound cost U c out) (p i : Fin n) :
    Clearance.gap out i p=(cost i).real (out.piece p)-baselines out.parents i := by
  rw [Clearance.gap,baselines,Output.piece,
    material_value cost _ (hs.parent_cache p).1 (hs.parent_cache p).2.1]

variable {xs : List (Snapshot.Output n)} {H : ℝ} {R : Set ℝ}
  (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (s : Fin xs.length) (hs : Sound cost U c (xs.get s)) (p : Fin n)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (C : Finset (Fin n)) (representative : Fin n → Fin n)
  (t : Reveal.TerminalClass n)
  (hclass : Reveal.classify (xs.get s).equalizers p (fun i => (cost i).real R) H C representative=.inl t)
  (hprotected : C ≠ Finset.univ ∨ c ∉ ProtectedPivot.eligible (xs.get s) H (fun i => (cost i).real R) p)

include hsep hs hr hH hscale hclass hprotected

theorem scan_common :
    p ∈ t.participants ∧ t.participants ⊆ C ∧ t.participants ≠ Finset.univ ∧
      (∀ i ∈ t.participants, Clearance.gap (xs.get s) i p ≤
        (cost i).real (material (offer (xs.get s) p (fun i => (cost i).real R) H C))) ∧
      (∀ i, i ∉ t.participants →
        (cost i).real (material (offer (xs.get s) p (fun i => (cost i).real R) H C)) ≤
          Clearance.gap (xs.get s) i p) := by
  have hv := (tracked_scan_correct hsep s hs p hr hH hscale C).1
  cases t with
  | inl pair =>
    obtain ⟨A,B⟩ := pair
    obtain ⟨a,ha,hA,hB⟩ := Reveal.classify_atomic _ p _ H C A B representative hclass
    rw [ha] at hv
    simp only [PhysicalCorrect] at hv
    rw [hA,hB] at hv
    refine ⟨hv.1,hv.2.1,hv.2.2.1,?_,?_⟩
    · intro i hi
      simpa only [offer,ha,gap_eq hs] using hv.2.2.2.2.2.2.1 i hi
    · intro i hi
      simpa only [offer,ha,gap_eq hs] using hv.2.2.2.2.2.2.2.1 i hi
  | inr A =>
    obtain ⟨q,hq,hA⟩ := Reveal.classify_exhausted _ p _ H C A representative hclass
    rw [hq] at hv
    simp only [PhysicalCorrect] at hv
    rw [hA] at hv
    have howner : p ∈ A := by
      rw [← hA]
      exact owner_eligible _ _ _ H p (rank_owner _ p) (hr p).le (by linarith)
    have hproper : A ≠ Finset.univ := by
      rcases hprotected with hC | hc
      · intro hAall
        exact hC (Finset.eq_univ_of_forall (fun i => hv.1 (hAall ▸ Finset.mem_univ i)))
      · rw [← hA]
        exact Reveal.protected_eligible_proper hs p _ H hc
    refine ⟨howner,hv.1,hproper,?_,?_⟩
    · intro i hi
      simpa only [offer,hq,gap_eq hs] using hv.2.2.1 i hi
    · intro i hi
      simpa only [offer,hq,gap_eq hs] using hv.2.2.2.1 i hi

omit hprotected t hclass in
theorem scan_exhausted_bounds (A : Finset (Fin n))
    (hclass : Reveal.classify (xs.get s).equalizers p (fun i => (cost i).real R) H C representative=.inl (.inr A)) :
    (∀ i, (cost i).real (material (offer (xs.get s) p (fun i => (cost i).real R) H C)) ≤
      (n : ℝ)*(cost i).real R/H) ∧
    (∀ i, i ∉ A → H*(cost i).real R ≤ Clearance.gap (xs.get s) i p) ∧
    (∀ i, i ∉ A → (H-(n : ℝ)/H)*(cost i).real R ≤ Clearance.gap (xs.get s) i p-
      (cost i).real (material (offer (xs.get s) p (fun i => (cost i).real R) H C))) := by
  obtain ⟨q,hq,hA⟩ := Reveal.classify_exhausted _ p _ H C A representative hclass
  have hv := (tracked_scan_correct hsep s hs p hr hH hscale C).1
  rw [hq] at hv
  simp only [PhysicalCorrect] at hv
  rw [hA] at hv
  exact ⟨by simpa only [offer,hq] using hv.2.2.2.2.2.1,
    by simpa only [gap_eq hs] using hv.2.2.2.2.1,
    by simpa only [offer,hq,gap_eq hs] using hv.2.2.2.2.2.2⟩

omit hprotected t hclass in
theorem scan_atomic_bounds (A B : Finset (Fin n))
    (hclass : Reveal.classify (xs.get s).equalizers p (fun i => (cost i).real R) H C representative=.inl (.inl (A,B))) :
    B.Nonempty ∧ B ≠ Finset.univ ∧
      atom (xs.get s) p (fun i => (cost i).real R) H C ⊆
        material (offer (xs.get s) p (fun i => (cost i).real R) H C) ∧
      (∀ i ∈ B, H*(cost i).real R ≤
        (cost i).real (atom (xs.get s) p (fun i => (cost i).real R) H C)) ∧
      (∀ i, i ∉ B →
        (cost i).real (material (offer (xs.get s) p (fun i => (cost i).real R) H C)) ≤
          (n : ℝ)*(cost i).real R/H) := by
  obtain ⟨a,ha,hA,hB⟩ := Reveal.classify_atomic _ p _ H C A B representative hclass
  have hv := (tracked_scan_correct hsep s hs p hr hH hscale C).1
  rw [ha] at hv
  simp only [PhysicalCorrect] at hv
  rw [hA,hB] at hv
  obtain ⟨_,_,_,hBn,hBp,hF,_,_,hlarge,hsmall,_⟩ := hv
  exact ⟨hBn,hBp,by simpa only [atom,offer,ha] using hF,
    by simpa only [atom,ha] using hlarge,
    by simpa only [offer,ha] using hsmall⟩

end EnvyFreeResearch.Full.Chores.Terminal
