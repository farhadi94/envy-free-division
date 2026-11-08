import EnvyFreeResearch.Full.ChoresComponentBatch

/-! Actual recorded SubCore comparisons discharge the component-cycle payment certificate. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentBatch
open Set MeasureTheory Components Scheduler ComponentPayments ComponentRecording ComponentDonors
open Persistent Suffix SubCoreEntry SubCorePhysical ChoreComposition IntervalOracle
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
  (state : PendingState Root (Fin n)) (hall : state.partition.labels ⊆ state.pending)
  (cycle : ProposalCycle (state.outgoing hall)) (visited : Visited state)
  (packages : Root → Package (Fin n) RootId) (frames : Root → Frame (Fin n) RootId)
  (gap : Root → Fin n → Fin n → ℝ) (out : Result state hall cycle)
  (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (blocks : Root → Fin n → Set ℝ)
  (hparts : PartsCorrect cost (domains blocks state.partition.representative) Subtype.val out)
  (hcorrect : PhysicalCorrect
    (clippedUtility cost (domains blocks state.partition.representative)
      (offsets gap state.partition.representative)) Subtype.val out.allocation)

theorem member_task (p i : Fin n) (hp : p ∈ state.selected hall cycle)
    (hi : i ∈ state.partition.component p) : i ∈ Task state hall cycle := by
  change i ∈ state.partition.tasks (state.selected hall cycle)
  rw [Partition.mem_tasks, (state.partition.mem_component p i).mp hi]
  exact hp

include hparts hcorrect

theorem component_comparisons (p i j : Fin n) (hp : p ∈ state.selected hall cycle)
    (hi : i ∈ state.partition.component p) (hj : j ∈ state.partition.component p) :
    EnvyFreeResearch.R7Chores.clipped (utilities state hall cycle gap out i j) ≤
      EnvyFreeResearch.R7Chores.clipped (utilities state hall cycle gap out i i) := by
  have hti := member_task state hall cycle p i hp hi
  have htj := member_task state hall cycle p j hp hj
  let ti : Task state hall cycle := ⟨i, hti⟩
  let tj : Task state hall cycle := ⟨j, htj⟩
  have hlabel : state.partition.representative (tj : Fin n) =
      state.partition.representative (ti : Fin n) :=
    ((state.partition.mem_component p j).mp hj).trans ((state.partition.mem_component p i).mp hi).symm
  have h := clipped_comparison cost blocks Subtype.val state.partition.representative gap out
    hparts hcorrect ti tj hlabel
  simpa only [utilities, dite_eq_left hti, dite_eq_left htj, credit,
    EnvyFreeResearch.R7Chores.clipped] using h

theorem component_threshold
    (hcache : Masked.CacheCorrect (measureProfile cost)
      (domains blocks state.partition.representative) out.cache)
    (unused : Root) (hunused : ∀ j, out.allocation.assigned j ≠ unused)
    (p i : Fin n) (hp : p ∈ state.selected hall cycle) (hi : i ∈ state.partition.component p)
    (hfrontier : (frames unused).gap i (ComponentFrames.nextAgent state unused p) p =
      (cost i).real (blocks unused p) - gap unused p i) :
    EnvyFreeResearch.R7Chores.clipped
      ((frames unused).gap i (ComponentFrames.nextAgent state unused p) p) ≤
      EnvyFreeResearch.R7Chores.retainedCredit (utilities state hall cycle gap out) i := by
  have hti := member_task state hall cycle p i hp hi
  let ti : Task state hall cycle := ⟨i, hti⟩
  have h := unused_threshold cost blocks Subtype.val state.partition.representative gap out
    hparts hcorrect hcache unused hunused ti
  rw [hfrontier, EnvyFreeResearch.R7Chores.retained_credit_exact]
  simpa only [utilities, dite_eq_left hti, credit, EnvyFreeResearch.R7Chores.clipped,
    ti, (state.partition.mem_component p i).mp hi] using h

omit hcorrect in
theorem component_protected (p i j : Fin n) (hp : p ∈ state.selected hall cycle)
    (hj : j ∈ state.partition.component p)
    (hprotect : ∀ s, (cost i).real (blocks s p) ≤ gap s p i) :
    utilities state hall cycle gap out i j ≤ 0 := by
  have htj := member_task state hall cycle p j hp hj
  let tj : Task state hall cycle := ⟨j, htj⟩
  have h := protected_utility_nonpositive cost blocks Subtype.val state.partition.representative
    gap out hparts i tj (by
      change (cost i).real (blocks (out.allocation.assigned tj) (state.partition.representative j)) ≤ _
      rw [(state.partition.mem_component p j).mp hj]
      exact hprotect _)
  simpa only [utilities, dite_eq_left htj] using h

/-- No payment certificate is assumed: its two cases are derived from the
actual SubCore output, recorded suffixes, and the local scan's protection facts. -/
theorem exclusive_payment
    (hcache : Masked.CacheCorrect (measureProfile cost)
      (domains blocks state.partition.representative) out.cache)
    (unused : Root) (hunused : ∀ j, out.allocation.assigned j ≠ unused)
    (hlive : (packages unused).live = some (frames unused))
    (hallowed : ∀ p i, i ∈ (frames unused).allowed p ↔ Edge (visited.graph unused) p i)
    (hforbidden : ∀ p ∈ state.selected hall cycle,
      (frames unused).forbidden p ⊆ state.partition.component p)
    (hfrontier : ∀ p ∈ state.selected hall cycle, ∀ i,
      (frames unused).gap i (ComponentFrames.nextAgent state unused p) p =
        (cost i).real (blocks unused p) - gap unused p i)
    (hprotect : ∀ p ∈ state.selected hall cycle, ∀ s i,
      i ∉ state.partition.component p → (cost i).real (blocks s p) ≤ gap s p i)
    (hcontain : ∀ p ∈ state.selected hall cycle, ∀ i j, j ∈ (frames unused).allowed p →
      (frames unused).gap i j p ≤
        (frames unused).gap i (ComponentFrames.nextAgent state unused p) p) :
    ExclusivePayment (packages unused)
      (donations state hall cycle visited packages frames gap out)
      (ComponentFrames.advance state hall cycle visited frames unused) := by
  intro i j p hij
  by_cases hp : p ∈ state.selected hall cycle
  · rw [selected_payments state hall cycle visited packages frames gap out p i hp,
      selected_extras state hall cycle visited packages frames gap out p i j hp]
    by_cases hi : i ∈ state.partition.component p
    · rw [ite_eq_left hi]
      have hq := ComponentFrames.nextAgent_outside state hall unused
        (⟨p, state.selected_subset hall cycle hp⟩ : state.Component)
      have ha := ComponentFrames.allowed_internal state visited frames unused p
        (state.selected_subset hall cycle hp) hallowed
      have h := ordinary_component_cases (state.partition.component p) ((frames unused).allowed p)
        ((frames unused).forbidden p) (fun k => (frames unused).gap i k p)
        ((frames unused).frontierGap i p)
        ((frames unused).gap i (ComponentFrames.nextAgent state unused p) p)
        (ComponentFrames.nextAgent state unused p) i j (utilities state hall cycle gap out)
        hq ha (hforbidden p hp) rfl
        (fun a ha => component_comparisons state hall cycle gap out cost blocks hparts hcorrect p i a hp hi ha)
        (by simpa only [EnvyFreeResearch.R7Chores.retained_credit_exact] using
          (component_threshold state hall cycle frames gap out cost blocks hparts hcorrect
            hcache unused hunused p i hp hi (hfrontier p hp i)))
      simpa only [Frame.reserve, Frame.gap, ComponentFrames.advance, ite_eq_left hp,
        Package.reserve, hlive] using h
    · rw [ite_eq_right hi]
      have he := protected_component_zero (state.partition.component p)
        (utilities state hall cycle gap out) i j (fun a ha =>
          component_protected state hall cycle gap out cost blocks hparts p i a hp ha
            (fun s => hprotect p hp s i hi))
      have hn : (frames unused).gap i (ComponentFrames.nextAgent state unused p) p ≤ 0 := by
        rw [hfrontier p hp i]
        exact sub_nonpos.mpr (hprotect p hp unused i hi)
      have hz := ComponentFrames.reserve_zero state hall cycle visited frames unused p hp i j hn
        (hcontain p hp i)
      exact Or.inl ⟨by rw [he], by rw [hz]; exact package_reserve_nonnegative _ _ _ _⟩
  · rw [other_payments state hall cycle visited packages frames gap out p i hp,
      other_extras state hall cycle visited packages frames gap out p i j hp,
      ComponentFrames.reserve_unchanged state hall cycle visited frames unused p hp]
    left
    exact ⟨le_rfl, by simp only [Package.reserve, hlive]; exact le_rfl⟩

end EnvyFreeResearch.Full.Chores.ComponentBatch
