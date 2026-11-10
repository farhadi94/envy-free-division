import EnvyFreeResearch.Full.RefinedChoresTerminalCohort
import EnvyFreeResearch.Full.RefinedChoresClosedCachesNext
import EnvyFreeResearch.Full.RefinedChoresDataPatch
import EnvyFreeResearch.Full.ChoresOuterNextCache

/-! Literal terminal donor caches and their physical realization. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Frontier Chores.Equalizers Chores.Snapshot ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H)

def TerminalGroup.equalizer (s : group.Root) (a j : Fin n) : List (Parent n) :=
  ((original (data.source (group.roots s))).equalizers (a,j)).parts.prefixParts

def TerminalGroup.front (s : group.Root) (a : Fin n) : List (Parent n) :=
  Terminal.front (original (data.source (group.roots s))) a r H (data.sourceSet normal (group.roots s))

variable (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)

def TerminalGroup.next (out : Result (Root := group.Root) group.terminalClass.participants) : group.Root → Fin n → List (Parent n) :=
  nextCache group.terminalClass.participants group.label (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
    (TerminalGroup.gaps data normal original r H group) out
    (TerminalGroup.equalizer data normal original r H group) (TerminalGroup.front data normal original r H group)

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
include hsound

theorem TerminalGroup.parent_unit (s : group.Root) (a : Fin n) :
    (original (data.source (group.roots s))).piece a ⊆ Ioc (0 : ℝ) 1 :=
  Outer.valid_material_unit cost _ ((hsound _).choose_spec.parent_cache a).1

theorem TerminalGroup.equalizer_valid (s : group.Root) (a j : Fin n) :
    CacheValid (measureProfile cost) (material (TerminalGroup.equalizer data normal original r H group s a j))
      (TerminalGroup.equalizer data normal original r H group s a j) := by
  have hc := (snapshot_equalizers (hsound (data.source (group.roots s))).choose_spec a j).2.1
  exact ⟨hc.1,hc.2.1,rfl⟩

theorem TerminalGroup.equalizer_subset (s : group.Root) (a j : Fin n) :
    material (TerminalGroup.equalizer data normal original r H group s a j) ⊆ (original (data.source (group.roots s))).piece a :=
  Outer.original_equalizer_subset cost (hsound _).choose_spec a j

theorem TerminalGroup.front_valid (s : group.Root) (a : Fin n) :
    CacheValid (measureProfile cost) (material (TerminalGroup.front data normal original r H group s a))
      (TerminalGroup.front data normal original r H group s a) := by
  obtain ⟨U,hs⟩ := hsound (data.source (group.roots s))
  exact Frontier.front_cache_valid cost _ _ (snapshot_parent_cache hs a) _ a _
    (snapshot_equalizers hs a) (hs.own_equalizers a).1 _

theorem TerminalGroup.front_subset (s : group.Root) (a : Fin n) :
    material (TerminalGroup.front data normal original r H group s a) ⊆
      (original (data.source (group.roots s))).piece a := by
  obtain ⟨U,hs⟩ := hsound (data.source (group.roots s))
  exact Frontier.front_subset cost _ _ (snapshot_parent_cache hs a) _ a _
    (snapshot_equalizers hs a) (hs.own_equalizers a).1 _

theorem TerminalGroup.blocks_complement (s : group.Root) :
    TerminalGroup.blocks data normal original r H group s group.label =
      (original (data.source (group.roots s))).piece group.label \
        material (TerminalGroup.front data normal original r H group s group.label) := by
  obtain ⟨U,hs⟩ := hsound (data.source (group.roots s))
  exact offer_complement cost _ _ (snapshot_parent_cache hs group.label) _ group.label _
    (snapshot_equalizers hs group.label) (hs.own_equalizers group.label).1 (scan (original (data.source (group.roots s))).equalizers group.label r H (data.sourceSet normal (group.roots s)))

variable (out : Result (Root := group.Root) group.terminalClass.participants)
    (hparts : ComponentRecording.PartsCorrect cost
      (ComponentPayments.domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
include hparts

theorem TerminalGroup.next_valid (s : group.Root) (a : Fin n) :
    Valid (measureProfile cost) (TerminalGroup.next data normal original r H group hr0 hH0 out s a) ∧
      Ordered (TerminalGroup.next data normal original r H group hr0 hH0 out s a) :=
  next_cache_valid group.terminalClass.participants group.label (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
    (TerminalGroup.gaps data normal original r H group) out
    (TerminalGroup.equalizer data normal original r H group) (TerminalGroup.front data normal original r H group)
    cost (fun s a => (original (data.source (group.roots s))).piece a)
    (TerminalGroup.blocks data normal original r H group) (TerminalGroup.parent_unit data normal original r H group cost c hsound)
    (TerminalGroup.front_valid data normal original r H group cost c hsound)
    (TerminalGroup.equalizer_valid data normal original r H group cost c hsound)
    (TerminalGroup.front_subset data normal original r H group cost c hsound)
    (TerminalGroup.blocks_complement data normal original r H group cost c hsound) hparts s a

theorem TerminalGroup.next_subset (s : group.Root) (a : Fin n) :
    material (TerminalGroup.next data normal original r H group hr0 hH0 out s a) ⊆ (original (data.source (group.roots s))).piece a :=
  next_cache_subset group.terminalClass.participants group.label (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
    (TerminalGroup.gaps data normal original r H group) out
    (TerminalGroup.equalizer data normal original r H group) (TerminalGroup.front data normal original r H group)
    cost (fun s a => (original (data.source (group.roots s))).piece a)
    (TerminalGroup.blocks data normal original r H group) (TerminalGroup.parent_unit data normal original r H group cost c hsound)
    (TerminalGroup.front_valid data normal original r H group cost c hsound)
    (TerminalGroup.equalizer_valid data normal original r H group cost c hsound)
    (TerminalGroup.front_subset data normal original r H group cost c hsound)
    (TerminalGroup.blocks_complement data normal original r H group cost c hsound) hparts
    (TerminalGroup.equalizer_subset data normal original r H group cost c hsound) s a

include good

theorem TerminalGroup.next_cost (s : group.Root) (i a : Fin n) :
    (nextAllocation group.terminalClass.participants group.label (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
      (TerminalGroup.gaps data normal original r H group) out s).cost i a =
      (cost i).real (material (TerminalGroup.next data normal original r H group hr0 hH0 out s a)) := by
  apply next_cache_cost group.terminalClass.participants group.label (data.frames ∘ group.roots) (TerminalGroup.path data normal original r H group hr0 hH0)
    (TerminalGroup.gaps data normal original r H group) out
    (TerminalGroup.equalizer data normal original r H group) (TerminalGroup.front data normal original r H group)
    cost (fun s a => (original (data.source (group.roots s))).piece a)
    (TerminalGroup.blocks data normal original r H group) (TerminalGroup.parent_unit data normal original r H group cost c hsound)
    (TerminalGroup.front_valid data normal original r H group cost c hsound)
    (TerminalGroup.equalizer_valid data normal original r H group cost c hsound)
    (TerminalGroup.front_subset data normal original r H group cost c hsound)
    (TerminalGroup.blocks_complement data normal original r H group cost c hsound) hparts
  · intro s i a j
    exact Outer.original_equalizer_value cost (hsound _).choose_spec _ (good.original_frame _) i a j
  · intro s i
    have h := Outer.original_gap cost (hsound (data.source (group.roots s))).choose_spec
      (data.frames (group.roots s)) (good.original_frame _) group.label i
    exact h

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.next_cost
