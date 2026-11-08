import EnvyFreeResearch.Full.ChoresComponentAdvance

/-! The physical open group satisfies the finite committed-update relation,
and a group of k+1 roots consumes every old package exactly once. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentBatch
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ)
  (hmany : Fintype.card (Task state hall cycle) < Fintype.card Root)
  (out : Result state hall cycle)

def rootList : List Root :=
  ComponentAssignment.unused out.allocation hmany ::
    (Task state hall cycle).toList.map (donorRoot state hall cycle out)

def inputGroup : List (Package (Fin n) RootId) :=
  (rootList state hall cycle hmany out).map packages

theorem root_list_nodup : (rootList state hall cycle hmany out).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hmem
    have hj' := Finset.mem_toList.mp hj
    have h := ComponentAssignment.unused_spec out.allocation hmany
      (⟨j, hj'⟩ : Task state hall cycle)
    exact h (by simpa only [donorRoot, dite_eq_left hj'] using heq)
  · apply (List.nodup_map_iff_inj_on (Finset.nodup_toList _)).mpr
    intro i hi j hj heq
    have hi' := Finset.mem_toList.mp hi
    have hj' := Finset.mem_toList.mp hj
    have h : out.allocation.assigned ⟨i, hi'⟩ = out.allocation.assigned ⟨j, hj'⟩ := by
      simpa only [donorRoot, dite_eq_left hi', dite_eq_left hj'] using heq
    exact congrArg Subtype.val (out.allocation.assigned.injective h)

theorem root_list_complete
    (hcard : Fintype.card Root = Fintype.card (Task state hall cycle) + 1) :
    (rootList state hall cycle hmany out).Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup (root_list_nodup state hall cycle hmany out)
    (Finset.nodup_toList _)).mpr
  intro s
  constructor
  · intro _
    simp
  · intro _
    rcases ComponentAssignment.every_root out.allocation hcard s with hs | ⟨j, hj⟩
    · exact List.mem_cons.mpr (Or.inl hs)
    · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr
        ⟨j, Finset.mem_toList.mpr j.property, (donorRoot_task state hall cycle out j).trans hj⟩))

theorem input_group_eq :
    inputGroup state hall cycle packages hmany out =
      packages (ComponentAssignment.unused out.allocation hmany) ::
        (donations state hall cycle visited packages frames gap out).map Donation.package := by
  simp only [inputGroup, rootList, List.map_cons, List.map_map, donations, ordinaryTasks,
    Function.comp_def]

theorem input_group_complete
    (hcard : Fintype.card Root = Fintype.card (Task state hall cycle) + 1) :
    (inputGroup state hall cycle packages hmany out).Perm (Finset.univ.toList.map packages) :=
  (root_list_complete state hall cycle hmany out hcard).map packages

variable (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks : Root → Fin n → Set ℝ)
  (hparts : PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out)
  (hcorrect : PhysicalCorrect
    (clippedUtility cost (domains blocks state.partition.representative)
      (offsets gap state.partition.representative)) Subtype.val out.allocation)
  (hcache : Masked.CacheCorrect (measureProfile cost)
    (domains blocks state.partition.representative) out.cache)
  (hlive : ∀ s, (packages s).live = some (frames s))
  (hvalid : ∀ s, (packages s).Valid)
  (hallowed : ∀ s p i, i ∈ (frames s).allowed p ↔ Edge (visited.graph s) p i)
  (hequalized : ∀ s p i, (frames s).equalizerCost i p i = (frames s).baseline i)
  (hforbidden : ∀ s p, p ∈ state.selected hall cycle →
    (frames s).forbidden p ⊆ state.partition.component p)
  (hfrontier : ∀ s p, p ∈ state.selected hall cycle → ∀ i,
    (frames s).gap i (ComponentFrames.nextAgent state s p) p =
      (cost i).real (blocks s p) - gap s p i)
  (hprotect : ∀ p ∈ state.selected hall cycle, ∀ s i,
    i ∉ state.partition.component p → (cost i).real (blocks s p) ≤ gap s p i)
  (hcontain : ∀ s p, p ∈ state.selected hall cycle → ∀ i j, j ∈ (frames s).allowed p →
    (frames s).gap i j p ≤ (frames s).gap i (ComponentFrames.nextAgent state s p) p)

include hparts hcorrect hcache hlive hvalid hallowed hequalized hforbidden hfrontier hprotect hcontain

theorem output_group_update :
    GroupUpdate (inputGroup state hall cycle packages hmany out)
      (outputPackage state hall cycle visited packages frames gap hmany out) := by
  rw [input_group_eq state hall cycle visited packages frames gap hmany out]
  let survivor := ComponentAssignment.unused out.allocation hmany
  have hframes : ∀ s, (frames s).Good := fun s => (hvalid s).live_good _ (hlive s)
  apply GroupUpdate.ordinary _ _ (frames survivor)
    (ComponentFrames.advance state hall cycle visited frames survivor) (hlive survivor) rfl rfl rfl
    (donations_wellFormed state hall cycle visited packages frames gap out hlive hframes hallowed)
  · intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    rfl
  · exact ComponentFrames.advance_good state hall cycle visited frames survivor
      (hallowed survivor) (hequalized survivor)
  · exact exclusive_payment state hall cycle visited packages frames gap out cost blocks
      hparts hcorrect hcache survivor (ComponentAssignment.unused_spec out.allocation hmany)
      (hlive survivor) (hallowed survivor) (hforbidden survivor) (hfrontier survivor)
      hprotect (hcontain survivor)

theorem output_ids
    (hcard : Fintype.card Root = Fintype.card (Task state hall cycle) + 1) :
    (outputPackage state hall cycle visited packages frames gap hmany out).ids.Perm
      (Finset.univ.toList.flatMap (fun s => (packages s).ids)) := by
  have h := group_update_ids (output_group_update state hall cycle visited packages frames gap
    hmany out cost blocks hparts hcorrect hcache hlive hvalid hallowed hequalized hforbidden
    hfrontier hprotect hcontain)
  exact h.trans (by simpa only [List.flatMap_map] using
    (input_group_complete state hall cycle packages hmany out hcard).flatMap_right Package.ids)

end EnvyFreeResearch.Full.Chores.ComponentBatch
