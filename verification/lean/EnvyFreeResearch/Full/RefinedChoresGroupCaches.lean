import EnvyFreeResearch.Full.RefinedChoresGroupPaid
import EnvyFreeResearch.Full.RefinedChoresDonorCachesNext
import EnvyFreeResearch.Full.RefinedChoresClosedCachesFrontier
import EnvyFreeResearch.Full.ChoresOuterNextCache

/-! All-observer caches for the actual ordinary cohort, instantiated from
immutable equalizer tables and the physical SubCore record. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Frontier Chores.Equalizers Chores.Snapshot ChoreComposition
open RefinedChoresPhysicalPayment RefinedChoresDonorCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : Group data normal original r H)

def Group.equalizer (s : group.Root) (a j : Fin n) : List (Parent n) :=
  ((original (data.source (group.roots s))).equalizers (a,j)).parts.prefixParts

def Group.front (s : group.Root) (a : Fin n) : List (Parent n) :=
  Group.equalizer data normal original r H group s a (group.target s)

def Group.next (out : Result (Root := group.Root) group.component) : group.Root → Fin n → List (Parent n) :=
  nextCache group.component group.label (data.frames ∘ group.roots) group.path
    (Group.gaps data normal original r H group) out
    (Group.equalizer data normal original r H group) (Group.front data normal original r H group)

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost U c (original root))
    (good : data.Good original cost r H)
include hsound

theorem Group.parent_unit (s : group.Root) (a : Fin n) :
    (original (data.source (group.roots s))).piece a ⊆ Ioc (0 : ℝ) 1 :=
  Outer.valid_material_unit cost _ ((hsound _).choose_spec.parent_cache a).1

theorem Group.equalizer_valid (s : group.Root) (a j : Fin n) :
    CacheValid (measureProfile cost) (material (Group.equalizer data normal original r H group s a j))
      (Group.equalizer data normal original r H group s a j) := by
  have hc := (snapshot_equalizers (hsound (data.source (group.roots s))).choose_spec a j).2.1
  exact ⟨hc.1,hc.2.1,rfl⟩

theorem Group.equalizer_subset (s : group.Root) (a j : Fin n) :
    material (Group.equalizer data normal original r H group s a j) ⊆ (original (data.source (group.roots s))).piece a :=
  Outer.original_equalizer_subset cost (hsound _).choose_spec a j

theorem Group.blocks_complement (s : group.Root) :
    Group.blocks data normal original r H group s group.label =
      (original (data.source (group.roots s))).piece group.label \
        material (Group.front data normal original r H group s group.label) := by
  obtain ⟨U,hs⟩ := hsound (data.source (group.roots s))
  exact offer_complement cost _ _ (snapshot_parent_cache hs group.label) _ group.label _
    (snapshot_equalizers hs group.label) (hs.own_equalizers group.label).1 (.outside (group.target s))

variable (out : Result (Root := group.Root) group.component)
    (hparts : ComponentRecording.PartsCorrect cost
      (ComponentPayments.domains (Group.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
include hparts

theorem Group.next_valid (s : group.Root) (a : Fin n) :
    Valid (measureProfile cost) (Group.next data normal original r H group out s a) ∧
      Ordered (Group.next data normal original r H group out s a) :=
  next_cache_valid group.component group.label (data.frames ∘ group.roots) group.path
    (Group.gaps data normal original r H group) out
    (Group.equalizer data normal original r H group) (Group.front data normal original r H group)
    cost (fun s a => (original (data.source (group.roots s))).piece a)
    (Group.blocks data normal original r H group) (Group.parent_unit data normal original r H group cost c hsound)
    (fun s a => Group.equalizer_valid data normal original r H group cost c hsound s a _)
    (Group.equalizer_valid data normal original r H group cost c hsound)
    (fun s a => Group.equalizer_subset data normal original r H group cost c hsound s a _)
    (Group.blocks_complement data normal original r H group cost c hsound) hparts s a

theorem Group.next_subset (s : group.Root) (a : Fin n) :
    material (Group.next data normal original r H group out s a) ⊆ (original (data.source (group.roots s))).piece a :=
  next_cache_subset group.component group.label (data.frames ∘ group.roots) group.path
    (Group.gaps data normal original r H group) out
    (Group.equalizer data normal original r H group) (Group.front data normal original r H group)
    cost (fun s a => (original (data.source (group.roots s))).piece a)
    (Group.blocks data normal original r H group) (Group.parent_unit data normal original r H group cost c hsound)
    (fun s a => Group.equalizer_valid data normal original r H group cost c hsound s a _)
    (Group.equalizer_valid data normal original r H group cost c hsound)
    (fun s a => Group.equalizer_subset data normal original r H group cost c hsound s a _)
    (Group.blocks_complement data normal original r H group cost c hsound) hparts
    (Group.equalizer_subset data normal original r H group cost c hsound) s a

include good

theorem Group.next_cost (s : group.Root) (i a : Fin n) :
    (nextAllocation group.component group.label (data.frames ∘ group.roots) group.path
      (Group.gaps data normal original r H group) out s).cost i a =
      (cost i).real (material (Group.next data normal original r H group out s a)) := by
  apply next_cache_cost group.component group.label (data.frames ∘ group.roots) group.path
    (Group.gaps data normal original r H group) out
    (Group.equalizer data normal original r H group) (Group.front data normal original r H group)
    cost (fun s a => (original (data.source (group.roots s))).piece a)
    (Group.blocks data normal original r H group) (Group.parent_unit data normal original r H group cost c hsound)
    (fun s a => Group.equalizer_valid data normal original r H group cost c hsound s a _)
    (Group.equalizer_valid data normal original r H group cost c hsound)
    (fun s a => Group.equalizer_subset data normal original r H group cost c hsound s a _)
    (Group.blocks_complement data normal original r H group cost c hsound) hparts
  · intro s i a j
    exact Outer.original_equalizer_value cost (hsound _).choose_spec _ (good.original_frame _) i a j
  · intro s i
    have h := Outer.original_gap cost (hsound (data.source (group.roots s))).choose_spec
      (data.frames (group.roots s)) (good.original_frame _) group.label i
    exact h

/-- Full private complements remain small, including frozen donor roots. -/
theorem Group.next_complement_small (hr : ∀ i, 0 ≤ r i) (hH : 0 < H)
    (hsmall : ∀ s i, (cost i).real (Group.blocks data normal original r H group s group.label) ≤ (n:ℝ)*r i/H)
    (s : group.Root) (a i : Fin n) :
    (cost i).real ((original (data.source (group.roots s))).piece a \
      material (Group.next data normal original r H group out s a)) ≤ (n:ℝ)*r i/H := by
  apply ComponentAssignment.dispatch_property out.allocation
    (fun s a => Group.equalizer data normal original r H group s a ((data.frames (group.roots s)).owner a))
    (fun j => donorCache group.component group.label (data.frames ∘ group.roots) group.path
      (Group.gaps data normal original r H group) out
      (Group.equalizer data normal original r H group) (Group.front data normal original r H group) j)
    (fun s cache => (cost i).real ((original (data.source (group.roots s))).piece a \ material (cache a)) ≤ (n:ℝ)*r i/H)
  · intro t
    have h := good.complement_small (data.source (group.roots t)) a i
    rw [good.live_cache] at h
    simpa only [(data.tracked (group.roots t)).owner_identity,Equiv.Perm.one_apply,Group.equalizer] using h
  · intro j
    have hc := donor_cache_correct group.component group.label (data.frames ∘ group.roots) group.path
      (Group.gaps data normal original r H group) out
      (Group.equalizer data normal original r H group) (Group.front data normal original r H group)
      cost (fun s a => (original (data.source (group.roots s))).piece a)
      (Group.blocks data normal original r H group) (Group.parent_unit data normal original r H group cost c hsound)
      (fun s a => Group.equalizer_valid data normal original r H group cost c hsound s a _)
      (Group.equalizer_valid data normal original r H group cost c hsound)
      (fun s a => Group.equalizer_subset data normal original r H group cost c hsound s a _)
      (Group.blocks_complement data normal original r H group cost c hsound) hparts j a
    rw [hc.2.2]
    apply RefinedChoresClosedCaches.proposal_complement_small data original cost r H good c hsound hr hH
      (group.roots (out.allocation.assigned j))
      ((active_package_valid data original cost r H good _).live_good _ (good.live _))
      _ rfl _ _ _ a i
    · intro b hb
      change owners group.component group.label (data.frames ∘ group.roots) group.path out j b ∈
        (data.frames (group.roots (out.allocation.assigned j))).allowed b
      simp only [owners,dite_eq_left j.property]
      apply RefinedChoresDirectedMatching.donor_allowed_other
      · intro a
        exact ((data.tracked (group.roots (out.allocation.assigned j))).exact a a).mpr
          (RefinedChoresPartialGraph.allowed_refl _ _ a)
      · exact hb
    · intro k
      apply (measureReal_mono (μ := cost k) (ComponentPayments.suffix_subset cost
        (Group.blocks data normal original r H group) Subtype.val (fun _ => group.label) out hparts j)).trans
      exact hsmall (out.allocation.assigned j) k

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.next_cost
