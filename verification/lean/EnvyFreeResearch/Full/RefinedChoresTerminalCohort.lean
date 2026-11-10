import EnvyFreeResearch.Full.RefinedChoresTerminalCohortSelect

/-! The actual affine terminal query program for a cohort selected from the
current root-local pool. Its physical preconditions follow from the stored
scan class and immutable snapshot clearance. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Frontier Chores.Snapshot Chores.QueryProgram Chores.ComponentPayments Chores.ComponentRecording
open Chores.SubCoreEntry ChoreComposition RefinedChoresRootState RefinedChoresPartialGraph
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H)

def TerminalGroup.selectedOriginal (s : group.Root) : Snapshot.Output n := original (data.source (group.roots s))
def TerminalGroup.components (s : group.Root) : Finset (Fin n) := data.sourceSet normal (group.roots s)
def TerminalGroup.gaps := RefinedChoresTerminalScans.gaps (TerminalGroup.selectedOriginal data normal original r H group)
def TerminalGroup.blocks := RefinedChoresTerminalScans.blocks (TerminalGroup.selectedOriginal data normal original r H group)
  group.label r H (TerminalGroup.components data normal original r H group)
def TerminalGroup.masked := RefinedChoresTerminalScans.cache (TerminalGroup.selectedOriginal data normal original r H group)
  group.label r H (TerminalGroup.components data normal original r H group)

variable (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)

def TerminalGroup.program := RefinedChoresClosed.program group.terminalClass.participants group.label
  (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
  (data.packages ∘ group.roots) (TerminalGroup.gaps data normal original r H group)
  (TerminalGroup.masked data normal original r H group) (by simp [TerminalGroup.Root])

def TerminalGroup.output (out : RefinedChoresClosed.Result (Root := group.Root) group.terminalClass.participants) :=
  RefinedChoresClosed.outputPackage group.terminalClass.participants group.label
    (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
    (data.packages ∘ group.roots) (TerminalGroup.gaps data normal original r H group) out
    (by simp [TerminalGroup.Root])

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost i).real R)
    (homitted : ∀ s : Fin data.size, c ∉ ProtectedPivot.eligible
      (original (data.source s)) H r data.protectedLabel)
    (good : data.Good original cost r H)
include hsound horiginal hsep hr hH hscale hr_eq homitted

theorem TerminalGroup.common (s : group.Root) :
    group.label ∈ group.terminalClass.participants ∧
      group.terminalClass.participants ⊆ TerminalGroup.components data normal original r H group s ∧
      group.terminalClass.participants ≠ Finset.univ ∧
      (∀ i ∈ group.terminalClass.participants, TerminalGroup.gaps data normal original r H group s group.label i ≤
        (cost i).real (TerminalGroup.blocks data normal original r H group s group.label)) ∧
      (∀ i ∉ group.terminalClass.participants,
        (cost i).real (TerminalGroup.blocks data normal original r H group s group.label) ≤
          TerminalGroup.gaps data normal original r H group s group.label i) := by
  subst r
  exact RefinedChoresTerminalScans.common (TerminalGroup.selectedOriginal data normal original _ H group)
    group.label H (TerminalGroup.components data normal original _ H group) cost c
    (fun s => hsound (data.source (group.roots s))) xs (fun s => index (data.source (group.roots s)))
    (fun s => horiginal (data.source (group.roots s))) R hsep hr hH hscale group.terminalClass
    (fun s => (data.pending (group.roots s)).partition.representative) group.class_eq
    (fun s => by
      by_cases hf : data.sourceSet normal (group.roots s) = Finset.univ
      · right
        have hp := source_full_label data normal (group.roots s) hf
        rw [group.label_eq] at hp
        rw [hp]
        exact homitted _
      · exact Or.inl hf) s

include good
/-- This is an actual ordinary-oracle execution; no successful terminal
contract or common component partition is assumed. -/
theorem TerminalGroup.program_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : RefinedChoresClosed.Result (Root := group.Root) group.terminalClass.participants,
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (TerminalGroup.program data normal original r H group hr0 hH0) prior
        (some (out,TerminalGroup.output data normal original r H group hr0 hH0 out)) trace ∧
      (TerminalGroup.output data normal original r H group hr0 hH0 out).Valid ∧
      (TerminalGroup.output data normal original r H group hr0 hH0 out).live = none ∧
      PhysicalCorrect (affineUtility cost
        (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
        (offsets (TerminalGroup.gaps data normal original r H group) (fun _ => group.label)))
        Subtype.val out.allocation ∧
      PartsCorrect cost (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
        Subtype.val out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card group.terminalClass.participants) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ SubCore.sourceBudget (Fintype.card group.terminalClass.participants) ∧
      Masked.CacheCorrect (measureProfile cost)
        (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) out.cache ∧
      ∃ j : group.terminalClass.participants, material (out.parts j).suffixParts =
        TerminalGroup.blocks data normal original r H group (out.allocation.assigned j) group.label := by
  have hc := TerminalGroup.common data normal original r H group cost xs index c hsound horiginal R
    hsep hr hH hscale hr_eq homitted
  apply RefinedChoresClosed.program_correct group.terminalClass.participants group.label
    (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
    (data.packages ∘ group.roots) (TerminalGroup.gaps data normal original r H group)
    cost (TerminalGroup.blocks data normal original r H group)
    (TerminalGroup.masked data normal original r H group)
  · exact RefinedChoresTerminalScans.cache_correct (TerminalGroup.selectedOriginal data normal original r H group)
      group.label r H (TerminalGroup.components data normal original r H group) cost c
      (fun s => hsound (data.source (group.roots s)))
  · intro s i
    exact Clearance.gap_nonnegative (hsound (data.source (group.roots s))).choose_spec i group.label
  · exact ⟨group.label,(hc 0).1⟩
  · intro s i hi
    exact sub_nonneg.mpr ((hc s).2.2.2.1 i hi)
  · intro s
    exact good.live _
  · intro s
    exact active_package_valid data original cost r H good _
  · intro s a
    exact ((data.tracked (group.roots s)).exact a a).mpr (allowed_refl _ _ a)
  · intro i hi s
    exact (hc s).2.2.2.2 i hi
  · exact hpolicy

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.program_correct
