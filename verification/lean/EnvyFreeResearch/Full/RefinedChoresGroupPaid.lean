import EnvyFreeResearch.Full.RefinedChoresDataGroup
import EnvyFreeResearch.Full.RefinedChoresDataOpen
import EnvyFreeResearch.Full.RefinedChoresGroupIds
import EnvyFreeResearch.Full.ChoresRevealPendingGeometry

/-! The actual unused root of an ordinary SubCore cohort becomes the new
live root. Its immutable geometry, pending frontier and factorial capacity
are proved directly from the input pool and recorded scan. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Frontier Chores.Scheduler ChoreComposition RefinedChoresRootState
open RefinedChoresStateCapacity RefinedChoresPhysicalPayment
open scoped Classical BigOperators
variable {n : ℕ} {RootId : Type*} (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : Group data normal original r H)

theorem Group.label_mem (s : group.Root) : group.label ∈ (data.pending (group.roots s)).partition.labels := by
  rw [← group.label_eq s]
  exact (data.sink normal (group.roots s)).property

theorem Group.unpaid (s : group.Root) : group.label ∉ (data.pending (group.roots s)).pending := by
  rw [← group.label_eq s]
  exact sink_unpaid data normal (group.roots s)

theorem Group.component_at (s : group.Root) :
    componentSet (data.pending (group.roots s)) ((data.pending (group.roots s)).component group.label) = group.component := by
  change data.component (group.roots s) group.label = group.component
  rw [← group.label_eq s,component_source,group.component_eq]

theorem Group.target_ne (s : group.Root) :
    (data.pending (group.roots s)).partition.representative (group.target s) ≠ group.label := by
  intro h
  apply group.target_outside s
  rw [← Group.component_at data normal original r H group s,mem_componentSet]
  exact h.trans ((data.pending (group.roots s)).partition.mem_labels group.label |>.mp
    (Group.label_mem data normal original r H group s)).symm

def Group.paidTracked (s : group.Root) :
    Tracked (RefinedChoresDeferredPayment.pay (data.frames (group.roots s)) group.component group.label (group.target s)) :=
  payAt _ (data.tracked (group.roots s)) group.component group.label
    (Group.label_mem data normal original r H group s) (Group.unpaid data normal original r H group s)
    (group.target s) (Group.target_ne data normal original r H group s)

def Group.survivor (out : Result (Root := group.Root) group.component) : group.Root :=
  ComponentAssignment.unused out.allocation (by simp [Group.Root])

def Group.liveOutput (out : Result (Root := group.Root) group.component) : LiveOutput data where
  source := data.source (group.roots (Group.survivor data normal original r H group out))
  frame := RefinedChoresDeferredPayment.pay
    (data.frames (group.roots (Group.survivor data normal original r H group out)))
    group.component group.label (group.target (Group.survivor data normal original r H group out))
  package := Group.output data normal original r H group out
  tracked := Group.paidTracked data normal original r H group _
  protected_fixed := data.protected_fixed _
  frontier := Function.update (data.frontier (group.roots (Group.survivor data normal original r H group out)))
    group.label (group.target (Group.survivor data normal original r H group out))

variable [Fintype RootId] (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (good : data.Good original cost r H)
include good

theorem Group.output_ids (out : Result (Root := group.Root) group.component) :
    (Group.output data normal original r H group out).ids.Perm
      (Finset.univ.toList.flatMap (fun s => (data.packages (group.roots s)).ids)) := by
  apply RefinedChoresGroupIds.output_ids
  · simp [Group.Root]
  · exact fun s => good.live _
  · exact fun s => active_package_valid data original cost r H good _
  · intro s a
    exact ((data.tracked (group.roots s)).exact a a).mpr
      (RefinedChoresPartialGraph.allowed_refl _ _ a)

theorem Group.paid_capacity (out : Result (Root := group.Root) group.component) :
    (Group.output data normal original r H group out).ids.length ≤
      capacity (Group.paidTracked data normal original r H group
        (Group.survivor data normal original r H group out)).state := by
  let s := Group.survivor data normal original r H group out
  have hsize : size (data.pending (group.roots s)) group.label = group.component.card := by
    calc
      _ = (componentSet (data.pending (group.roots s)) ((data.pending (group.roots s)).component group.label)).card := by
        apply congrArg Finset.card
        apply Finset.ext
        intro a
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_componentSet]
        change _ ↔ (data.pending (group.roots s)).partition.representative a =
          (data.pending (group.roots s)).partition.representative group.label
        rw [(data.pending (group.roots s)).partition.mem_labels group.label |>.mp
          (Group.label_mem data normal original r H group s)]
      _ = _ := congrArg Finset.card (Group.component_at data normal original r H group s)
  have hmass := (Group.output_ids data normal original r H group cost good out).length_eq
  simp only [List.length_flatMap,Finset.sum_map_toList] at hmass
  have hcap : capacity (Group.paidTracked data normal original r H group s).state =
      2*(size (data.pending (group.roots s)) group.label+1)*capacity (data.pending (group.roots s)) :=
    capacity_reveal (data.pending (group.roots s)) group.label
      (Group.label_mem data normal original r H group s) (proposal (group.target s))
      (proposalAt_valid _ _ _ (Group.target_ne data normal original r H group s))
      (Group.unpaid data normal original r H group s)
  change _ ≤ capacity (Group.paidTracked data normal original r H group s).state
  rw [hmass,hcap,hsize]
  have hs := active_bucket_lower data original cost r H good (group.roots s)
  rw [group.bucket_eq] at hs
  have hw : ∀ w ∈ List.ofFn (fun t : group.Root => (data.packages (group.roots t)).ids.length),
      w < 2^(group.bucket.val+1) := by
    intro w hw
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hw
    have h := active_bucket_upper data original cost r H good (group.roots t)
    simpa only [group.bucket_eq] using h
  have hb := RefinedChoresBucketCapacity.group_sum_le (d := group.component.card)
    (List.ofFn (fun t : group.Root => (data.packages (group.roots t)).ids.length))
    (by simp [Group.Root]) hs hw
  simp only [List.sum_ofFn] at hb
  exact hb.trans (Nat.mul_le_mul_left _ (good.weight_bounded (group.roots s)))

theorem Group.liveOutput_good (out : Result (Root := group.Root) group.component)
    (hvalid : (Group.output data normal original r H group out).Valid)
    (hr : ∀ i, 0 ≤ r i) (hH : 0 < H) :
    LiveOutput.Good data (Group.liveOutput data normal original r H group out) original r H := by
  let s := Group.survivor data normal original r H group out
  refine ⟨hvalid,rfl,good.source _,?_,?_,?_,Group.paid_capacity data normal original r H group cost good out⟩
  · exact ⟨(good.original_frame _).baseline,(good.original_frame _).values⟩
  · intro a
    change RefinedChoresPendingFrontier.Pending _ _ r H _
      (componentSet (data.pending (group.roots s)) ((data.pending (group.roots s)).component a))
      ((RefinedChoresDeferredPayment.pay (data.frames (group.roots s)) group.component group.label (group.target s)).allowed a)
      ((RefinedChoresDeferredPayment.pay (data.frames (group.roots s)) group.component group.label (group.target s)).forbidden a)
      (Function.update (data.frontier (group.roots s)) group.label (group.target s) a)
    by_cases ha : a = group.label
    · subst a
      rw [Group.component_at]
      have hscan := group.scan_eq s
      simp only [Data.scan,group.label_eq,group.component_eq] at hscan
      obtain ⟨hstop,hsmall⟩ := Reveal.scan_outside_stop _ group.label r H group.component
        (group.target s) hscan (hr _) hH
      have hinv := good.frontier (group.roots s) group.label
      change RefinedChoresPendingFrontier.Pending _ _ _ _ _
        (componentSet (data.pending (group.roots s)) ((data.pending (group.roots s)).component group.label)) _ _ _ at hinv
      rw [Group.component_at] at hinv
      have hallowed : (data.frames (group.roots s)).allowed group.label ⊆ group.component := by
        have h := sink_allowed (data.frames (group.roots s)) (data.tracked (group.roots s))
          (data.sink normal (group.roots s)) (sink_unpaid data normal (group.roots s))
        simpa only [← group.label_eq s,← group.component_eq s,Data.sourceLabel,Data.sourceSet,Data.pending] using h
      have hfull := RefinedChoresPendingFrontier.at_sink _ _ _ _ _ _ _ _ _ hinv
        (hallowed hinv.frontier_allowed)
      simpa only [RefinedChoresDeferredPayment.pay,ite_true,Function.update_self,Group.liveOutput,s] using
        RefinedChoresPendingFrontier.pay _ _ _ _ _ _ _ _ _ _ hfull hstop hsmall
    · simpa only [RefinedChoresDeferredPayment.pay,ha,ite_false,Function.update_of_ne ha,Group.liveOutput,s,Data.component] using
        good.frontier (group.roots s) a
  · intro i a
    change (RefinedChoresDeferredPayment.pay (data.frames (group.roots s)) group.component group.label (group.target s)).frontierGap i a =
      (RefinedChoresDeferredPayment.pay (data.frames (group.roots s)) group.component group.label (group.target s)).gap i
        (Function.update (data.frontier (group.roots s)) group.label (group.target s) a) a
    by_cases ha : a = group.label
    · subst a
      simp only [RefinedChoresDeferredPayment.pay,ite_true,Function.update_self,Frame.gap]
    · simpa only [RefinedChoresDeferredPayment.pay,ha,ite_false,Function.update_of_ne ha,Frame.gap] using
        good.frontier_value (group.roots s) i a

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.Group.liveOutput_good
