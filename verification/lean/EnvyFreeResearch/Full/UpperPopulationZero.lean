import EnvyFreeResearch.Full.UpperZeroRows

/-! Finite population reductions read only cached residue values. Cake zero
rows freeze simultaneously; retained rows are strictly positive. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperZeroRows
open UpperRecordedDomain UpperCorrectionExecution
variable {n : ℕ}

def positiveRows (origin : State n) (active : Finset (Fin n)) : Finset (Fin n) :=
  active \ zeroRows origin active

variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
  [∀ i, NullSingletonClass (μ i)]

theorem positiveRows_correct (origin : State n) (hgood : WellFormed μ origin)
    (active : Finset (Fin n)) (i : Fin n) :
    i ∈ positiveRows origin active ↔ i ∈ active ∧ 0 < (μ i).real (domain origin.cells) := by
  simp only [positiveRows, Finset.mem_sdiff, zeroRows_correct μ origin hgood]
  have hn : 0 ≤ (μ i).real (domain origin.cells) := measureReal_nonneg
  constructor
  · rintro ⟨hi,hnot⟩
    exact ⟨hi, lt_of_le_of_ne hn (fun hz => hnot ⟨hi,hz.symm⟩)⟩
  · rintro ⟨hi,hpos⟩
    exact ⟨hi,fun h => hpos.ne' h.2⟩

theorem positiveRows_subset (origin : State n) (active : Finset (Fin n)) :
    positiveRows origin active ⊆ active := Finset.sdiff_subset

theorem cake_freeze_zeros (origin : State n) (hgood : WellFormed μ origin)
    (old : GlobalCompletion.Table (Fin n)) (active : Finset (Fin n))
    (hEF : GlobalCompletion.EnvyFree .cake old)
    (hguard : GlobalCompletion.Guard .cake old (↑active) (fun i => (μ i).real (domain origin.cells))) :
    GlobalCompletion.Guard .cake old (↑(positiveRows origin active))
      (fun i => (μ i).real (domain origin.cells)) := by
  apply GlobalCompletion.freeze_preserves_guard .cake old (↑active) _ _
    (fun _ h => positiveRows_subset origin active h) hguard
  intro f hf hnot i hi
  have hz : (μ f).real (domain origin.cells) = 0 := by
    by_contra hne
    apply hnot
    exact (positiveRows_correct μ origin hgood active f).mpr
      ⟨hf, lt_of_le_of_ne measureReal_nonneg (fun h => hne h.symm)⟩
  change (μ f).real (domain origin.cells) ≤ _
  rw [hz]
  exact hEF f i

theorem positiveRows_empty_all_zero (origin : State n) (hgood : WellFormed μ origin)
    (active : Finset (Fin n)) (hempty : positiveRows origin active = ∅) :
    ∀ i ∈ active, (μ i).real (domain origin.cells) = 0 := by
  intro i hi
  by_contra hne
  have hm := (positiveRows_correct μ origin hgood active i).mpr
    ⟨hi,lt_of_le_of_ne measureReal_nonneg (fun h => hne h.symm)⟩
  simpa [hempty] using hm

/-- Any enumeration of the retained cached population satisfies the physical
positivity precondition needed by Repair and Snapshot. -/
theorem active_embedding_positive {k : ℕ} (origin : State n) (hgood : WellFormed μ origin)
    (active : Finset (Fin n)) (embed : Fin k → Fin n)
    (hmem : ∀ a, embed a ∈ positiveRows origin active) :
    ∀ a, 0 < (μ (embed a)).real (domain origin.cells) :=
  fun a => ((positiveRows_correct μ origin hgood active (embed a)).mp (hmem a)).2

end EnvyFreeResearch.Full.UpperZeroRows
