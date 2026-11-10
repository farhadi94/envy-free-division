import EnvyFreeResearch.Full.RefinedChoresDataChoice
import EnvyFreeResearch.Full.RefinedChoresDataFacts
import EnvyFreeResearch.Full.RefinedChoresPhysicalPayment
import EnvyFreeResearch.Full.ChoresTerminalScan

/-! An actual normal cohort in the physical root-local pool. Only its
source label, source set and dyadic size bucket are synchronized. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Equalizers Chores.Snapshot Chores.Frontier Chores.Scheduler ChoreComposition Chores.QueryProgram
open RefinedChoresRootState RefinedChoresPartialGraph
open scoped Classical
variable {n : ℕ} {RootId : Type*}

structure Group (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ) where
  label : Fin n
  component : Finset (Fin n)
  roots : Fin (component.card+1) ↪ Fin data.size
  label_eq : ∀ s, data.sourceLabel normal (roots s) = label
  component_eq : ∀ s, data.sourceSet normal (roots s) = component
  bucket : Fin (RefinedChoresPool.buckets n)
  bucket_eq : ∀ s, rawBucket n (data.packages (roots s)).ids.length = bucket
  target : Fin (component.card+1) → Fin n
  scan_eq : ∀ s, data.scan normal original r H (roots s) = .outside (target s)
  target_outside : ∀ s, target s ∉ component

variable (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : Group data normal original r H)

abbrev Group.Root := Fin (group.component.card+1)

theorem Group.path (s : group.Root) (j : Fin n) (hj : j ∈ group.component) :
    Relation.ReflTransGen (fun a b => b ∈ (data.frames (group.roots s)).allowed a) j group.label := by
  have h := donor_path (data.frames (group.roots s)) (data.tracked (group.roots s))
    (data.sink normal (group.roots s)) j
    (by change j ∈ data.sourceSet normal (group.roots s); rw [group.component_eq]; exact hj)
  simpa only [← group.label_eq s,Data.sourceLabel] using h

theorem Group.nonempty : group.component.Nonempty := by
  let s : group.Root := 0
  have h := component_self (data.pending (group.roots s)) (data.sink normal (group.roots s))
  change data.sourceLabel normal (group.roots s) ∈ data.sourceSet normal (group.roots s) at h
  rw [group.label_eq,group.component_eq] at h
  exact ⟨group.label,h⟩

def Group.gaps (s : group.Root) (p i : Fin n) : ℝ :=
  Clearance.gap (original (data.source (group.roots s))) i p

def Group.offers (s : group.Root) : List (Parent n) :=
  ((original (data.source (group.roots s))).equalizers (group.label,group.target s)).parts.suffixParts

def Group.blocks (s : group.Root) (_p : Fin n) : Set ℝ := material ((Group.offers data normal original r H group) s)
def Group.masked : Masked.Cache group.Root n := fun s _ => (Group.offers data normal original r H group) s

def Group.program : Program (Query (Fin n)) ℝ
    (Option (RefinedChoresPhysicalPayment.Result (Root := group.Root) group.component × Package (Fin n) RootId)) :=
  RefinedChoresPhysicalPayment.program group.component group.label
    (data.frames ∘ group.roots) (group.path) (data.packages ∘ group.roots) (Group.gaps data normal original r H group) group.target
    (Group.masked data normal original r H group) (by simp [Group.Root])

def Group.output (out : RefinedChoresPhysicalPayment.Result (Root := group.Root) group.component) :=
  RefinedChoresPhysicalPayment.outputPackage group.component group.label
    (data.frames ∘ group.roots) group.path (data.packages ∘ group.roots)
    (Group.gaps data normal original r H group) out group.target (by simp [Group.Root])

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length) (c : Fin n)
    (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
    (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost i).real R)
    (good : data.Good original cost r H)
include hsound horiginal hsep hr hH hscale hr_eq good

theorem Group.protects (s : group.Root) (i : Fin n) (hi : i ∉ group.component) :
    (cost i).real ((Group.blocks data normal original r H group) s group.label) ≤ (Group.gaps data normal original r H group) s group.label i := by
  obtain ⟨U,hs⟩ := hsound (data.source (group.roots s))
  have hs' : Snapshot.Sound cost U c (xs.get (index (data.source (group.roots s)))) :=
    by simpa only [horiginal] using hs
  have hscan := group.scan_eq s
  simp only [Data.scan,group.label_eq,group.component_eq,hr_eq,horiginal] at hscan
  have h := (Frontier.tracked_scan_correct hsep (index (data.source (group.roots s))) hs'
    group.label hr hH hscale group.component).1
  rw [hscan] at h
  have hout := h.2.2.2.1 i hi
  simpa only [Group.blocks,Group.offers,Group.gaps,Outcome.offer,horiginal,Terminal.gap_eq hs'] using hout

omit horiginal hsep hr hH hscale hr_eq good in
theorem Group.cache_correct : Masked.CacheCorrect (measureProfile cost)
    (ComponentPayments.domains (Group.blocks data normal original r H group) (fun _ => group.label)) (Group.masked data normal original r H group) := by
  intro s i
  obtain ⟨U,hs⟩ := hsound (data.source (group.roots s))
  exact ⟨(snapshot_equalizers hs group.label (group.target s)).2.2.1.1,
    (snapshot_equalizers hs group.label (group.target s)).2.2.1.2.1,rfl⟩

/-- The ordinary group is an actual execution of the original query oracle.
All source-component and reserve hypotheses are derived from the physical
pool state and its immutable-table scan. -/
theorem Group.program_correct
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : RefinedChoresPhysicalPayment.Result (Root := group.Root) group.component,
      ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (Group.program data normal original r H group) prior
        (some (out,Group.output data normal original r H group out)) trace ∧
      (Group.output data normal original r H group out).Valid ∧
      SubCoreEntry.PhysicalCorrect
        (SubCoreEntry.clippedUtility cost
          (ComponentPayments.domains (Group.blocks data normal original r H group) (fun _ => group.label))
          (ComponentPayments.offsets (Group.gaps data normal original r H group) (fun _ => group.label)))
        Subtype.val out.allocation ∧
      ComponentRecording.PartsCorrect cost
        (ComponentPayments.domains (Group.blocks data normal original r H group) (fun _ => group.label))
        Subtype.val out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card ↥group.component) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ SubCore.sourceBudget (Fintype.card ↥group.component) ∧
      Masked.CacheCorrect (measureProfile cost)
        (ComponentPayments.domains (Group.blocks data normal original r H group) (fun _ => group.label)) out.cache := by
  apply RefinedChoresPhysicalPayment.program_correct group.component group.label
    (data.frames ∘ group.roots) group.path (data.packages ∘ group.roots)
    (Group.gaps data normal original r H group) cost (Group.blocks data normal original r H group)
    group.target (Group.masked data normal original r H group)
  · exact Group.cache_correct data normal original r H group cost c hsound
  · intro s i
    exact Clearance.gap_nonnegative (hsound (data.source (group.roots s))).choose_spec i group.label
  · simpa using Finset.card_pos.mpr (Group.nonempty data normal original r H group)
  · intro s
    exact good.live (group.roots s)
  · intro s
    exact active_package_valid data original cost r H good (group.roots s)
  · intro s a
    exact ((data.tracked (group.roots s)).exact a a).mpr
      (allowed_refl (data.pending (group.roots s)) (data.visited (group.roots s)) a)
  · exact group.target_outside
  · intro s
    have h := sink_allowed (data.frames (group.roots s)) (data.tracked (group.roots s))
      (data.sink normal (group.roots s)) (sink_unpaid data normal (group.roots s))
    change (data.frames (group.roots s)).allowed (data.sourceLabel normal (group.roots s)) ⊆
      data.sourceSet normal (group.roots s) at h
    simpa only [group.label_eq,group.component_eq,Function.comp_apply] using h
  · intro s
    have hcomp : data.component (group.roots s) group.label = group.component := by
      rw [← group.label_eq s,component_source,group.component_eq]
    change (data.frames (group.roots s)).forbidden group.label ⊆ group.component
    exact (good.frontier (group.roots s) group.label).forbidden_internal.trans hcomp.le
  · intro s
    exact Outer.original_equalized cost (hsound (data.source (group.roots s))).choose_spec
      (data.frames (group.roots s)) (good.original_frame (group.roots s)) group.label (group.target s)
  · intro s i
    exact Outer.original_frontier_gap cost (hsound (data.source (group.roots s))).choose_spec
      (data.frames (group.roots s)) (good.original_frame (group.roots s)) group.label (group.target s) i
  · exact Group.protects data normal original r H group cost xs index c hsound horiginal R
      hsep hr hH hscale hr_eq good
  · exact hpolicy

end EnvyFreeResearch.Full.RefinedChoresData

#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.program_correct
