import EnvyFreeResearch.Full.RefinedChoresDeferredPayment
import EnvyFreeResearch.Full.RefinedChoresDirectedMatching
import EnvyFreeResearch.Full.ChoresComponentPayments
import EnvyFreeResearch.Full.ChoresComponentAssignment

/-!
A physical, recorded SubCore call paying a single source component. Roots
need agree only on that source set; the pending targets and all other SCCs
may differ. This module supplies the new local physical primitive. The
global asynchronous scheduler and its population recursion are separate.
-/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresPhysicalPayment
open Set MeasureTheory OracleProtocol IntervalOracle
open Chores Chores.ComponentRecording Chores.ComponentPayments Chores.SubCorePhysical
open Chores.SubCoreEntry Chores.Persistent Chores.QueryProgram Chores.OrderedUnion
open ChoreComposition
open scoped Classical

variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (C : Finset (Fin n)) (p : Fin n)

abbrev Task := C
abbrev Result := Recorded (Chores.Suffix.ClippedRecord n) (Task C) Root n

def donorRoot (out : Result (Root := Root) C) (j : Fin n) : Root :=
  if hj : j ∈ C then out.allocation.assigned ⟨j,hj⟩ else Classical.choice inferInstance

def utilities (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) C) (i j : Fin n) : ℝ :=
  if hj : j ∈ C then utility Subtype.val (fun _ => p) gap out i ⟨j,hj⟩ else 0

variable (frames : Root → Frame (Fin n) RootId)
    (hpath : ∀ s j, j ∈ C → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)

def owners (out : Result (Root := Root) C) (j : Fin n) : Equiv.Perm (Fin n) :=
  if hj : j ∈ C then RefinedChoresDirectedMatching.donor
    (fun a b => b ∈ (frames (out.allocation.assigned ⟨j,hj⟩)).allowed a) p j (hpath _ j hj)
  else 1

def donations (packages : Root → Package (Fin n) RootId)
    (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) C) : List (Donation (Fin n) RootId) :=
  ordinaryTasks C (packages ∘ donorRoot C out) (frames ∘ donorRoot C out) (fun _ => p)
    (owners C p frames hpath out) (utilities C p gap out)

variable (packages : Root → Package (Fin n) RootId)
    (gap : Root → Fin n → Fin n → ℝ)

theorem donors_valid (out : Result (Root := Root) C) (hvalid : ∀ s, (packages s).Valid) :
    ∀ d ∈ donations C p frames hpath packages gap out, d.package.Valid := by
  intro d hd
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hd
  exact hvalid _

theorem donors_wellFormed (out : Result (Root := Root) C)
    (hlive : ∀ s, (packages s).live = some (frames s))
    (hvalid : ∀ s, (packages s).Valid)
    (hreflexive : ∀ s a, a ∈ (frames s).allowed a) :
    ∀ d ∈ donations C p frames hpath packages gap out, d.WellFormed := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
  have hj' : j ∈ C := Finset.mem_toList.mp hj
  constructor
  · exact hlive _
  · apply ordinary_proposal_good
    · exact (hvalid _).live_good _ (hlive _)
    · simp only [owners, dite_eq_left hj']
      exact RefinedChoresDirectedMatching.donor_recipient _ _ _ _
    · intro a ha
      simp only [owners, dite_eq_left hj', Function.comp_apply, donorRoot]
      exact RefinedChoresDirectedMatching.donor_allowed_other _ (hreflexive _) p j _ a ha

theorem payment_at (out : Result (Root := Root) C) (i a : Fin n) :
    payments (donations C p frames hpath packages gap out) i a =
      if i ∈ C ∧ p = a then R7Chores.retainedCredit (utilities C p gap out) i else 0 := by
  rw [donations, ordinary_tasks_payments]
  simp only [Finset.mem_filter]

theorem extra_at (out : Result (Root := Root) C) (i j a : Fin n) :
    extras (donations C p frames hpath packages gap out) i j a =
      if j ∈ C ∧ p = a then R7Chores.retainedDeficit (utilities C p gap out) i j else 0 := by
  rw [donations, ordinary_tasks_extras]
  simp only [R7Chores.batchLoss, Finset.mem_filter]

variable (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (blocks : Root → Fin n → Set ℝ)
    (out : Result (Root := Root) C)
    (hparts : PartsCorrect cost (domains blocks (fun _ => p)) Subtype.val out)
    (hcorrect : PhysicalCorrect (clippedUtility cost
      (domains blocks (fun _ => p)) (offsets gap (fun _ => p))) Subtype.val out.allocation)

include hparts hcorrect in
theorem paid_comparison (i j : Fin n) (hj : j ∈ C)
    (hprotect : ∀ s i, i ∉ C → (cost i).real (blocks s p) ≤ gap s p i) :
    extras (donations C p frames hpath packages gap out) i j p ≤
      payments (donations C p frames hpath packages gap out) i p := by
  rw [extra_at, payment_at]
  by_cases hi : i ∈ C
  · simp only [hi, hj, and_self, ite_true]
    apply (R7Chores.stripping_reduces_deficits (utilities C p gap out) i j).trans
    have h := clipped_comparison cost blocks Subtype.val (fun _ => p) gap out hparts hcorrect
      (⟨i,hi⟩ : Task C) (⟨j,hj⟩ : Task C) rfl
    simpa only [utilities, dite_eq_left hi, dite_eq_left hj, credit,
      R7Chores.retained_credit_exact, R7Chores.clipped] using h
  · simp only [hi, hj, and_self, false_and, ite_true, ite_false]
    have h := protected_utility_nonpositive cost blocks Subtype.val (fun _ => p) gap out
      hparts i (⟨j,hj⟩ : Task C) (hprotect _ i hi)
    have hu : utilities C p gap out i j ≤ 0 := by simpa only [utilities, dite_eq_left hj] using h
    exact (R7Chores.stripping_reduces_deficits _ _ _).trans (by
      simpa only [R7Chores.clipped, max_eq_left hu] using (le_rfl : (0:ℝ) ≤ 0))

theorem payment_nonnegative (i a : Fin n) :
    0 ≤ payments (donations C p frames hpath packages gap out) i a := by
  rw [payment_at]
  split_ifs
  · exact R7Chores.retained_credit_nonnegative _ _
  · rfl

variable (target : Root → Fin n)

include hparts hcorrect in
theorem paid_threshold (s : Root) (hs : ∀ j, out.allocation.assigned j ≠ s)
    (hcache : Masked.CacheCorrect (measureProfile cost) (domains blocks (fun _ => p)) out.cache)
    (hfrontier : ∀ i, (frames s).gap i (target s) p = (cost i).real (blocks s p) - gap s p i)
    (hprotect : ∀ s i, i ∉ C → (cost i).real (blocks s p) ≤ gap s p i) (i : Fin n) :
    max 0 ((frames s).gap i (target s) p) ≤
      payments (donations C p frames hpath packages gap out) i p := by
  rw [payment_at, hfrontier]
  by_cases hi : i ∈ C
  · simp only [hi, and_self, ite_true]
    have h := unused_threshold cost blocks Subtype.val (fun _ => p) gap out hparts hcorrect
      hcache s hs (⟨i,hi⟩ : Task C)
    simpa only [utilities, dite_eq_left hi, credit, R7Chores.retained_credit_exact,
      R7Chores.clipped] using h
  · simp only [hi, false_and, ite_false]
    exact max_le le_rfl (sub_nonpos.mpr (hprotect s i hi))

def outputPackage (hmany : Fintype.card (Task C) < Fintype.card Root) : Package (Fin n) RootId :=
  let s := Chores.ComponentAssignment.unused out.allocation hmany
  mergeOpen (packages s) (donations C p frames hpath packages gap out)
    (RefinedChoresDeferredPayment.pay (frames s) C p (target s))

include hparts hcorrect in
theorem output_valid
    (hmany : Fintype.card (Task C) < Fintype.card Root)
    (hlive : ∀ s, (packages s).live = some (frames s))
    (hvalid : ∀ s, (packages s).Valid)
    (hreflexive : ∀ s a, a ∈ (frames s).allowed a)
    (htarget : ∀ s, target s ∉ C)
    (hallowed : ∀ s, (frames s).allowed p ⊆ C)
    (hforbidden : ∀ s, (frames s).forbidden p ⊆ C)
    (hequal : ∀ s, (frames s).equalizerCost (target s) p (target s) = (frames s).baseline (target s))
    (hcache : Masked.CacheCorrect (measureProfile cost) (domains blocks (fun _ => p)) out.cache)
    (hfrontier : ∀ s i, (frames s).gap i (target s) p = (cost i).real (blocks s p) - gap s p i)
    (hprotect : ∀ s i, i ∉ C → (cost i).real (blocks s p) ≤ gap s p i) :
    (outputPackage C p frames hpath packages gap out target hmany).Valid := by
  let s := Chores.ComponentAssignment.unused out.allocation hmany
  have hs : ∀ j, out.allocation.assigned j ≠ s := Chores.ComponentAssignment.unused_spec _ hmany
  apply RefinedChoresDeferredPayment.paid_package_valid (packages s) (hvalid s)
    (frames s) (hlive s) _
    (donors_wellFormed C p frames hpath packages gap out hlive hvalid hreflexive)
    (donors_valid C p frames hpath packages gap out hvalid) C p (target s)
    (htarget s) (hallowed s) (hforbidden s) (hequal s)
  · intro i j hj
    exact paid_comparison C p frames hpath packages gap cost blocks out hparts hcorrect i j hj hprotect
  · intro i j hj
    simp only [extra_at, hj, false_and, ite_false]
  · exact paid_threshold C p frames hpath packages gap cost blocks out hparts hcorrect target
      s hs hcache (hfrontier s) hprotect
  · intro a ha i j
    simp only [extra_at, Ne.symm ha, and_false, ite_false]
  · exact payment_nonnegative C p frames hpath packages gap out

def program (cache : Masked.Cache Root n)
    (hmany : Fintype.card (Task C) < Fintype.card Root) :
    Program (Query (Fin n)) ℝ (Option (Result (Root := Root) C × Package (Fin n) RootId)) :=
  (clippedProgram (Subtype.val : Task C → Fin n) (offsets gap (fun _ => p)) cache hmany.le).bind
    (fun result => match result with
      | none => .returned none
      | some out => .returned (some (out, outputPackage C p frames hpath packages gap out target hmany)))

/-- An actual ordinary-query execution, including the final all-observer
recording pass, pays a proposal without requiring common target components
or an immediate survivor reset. -/
theorem program_correct
    (cache : Masked.Cache Root n)
    (hc : Masked.CacheCorrect (measureProfile cost) (domains blocks (fun _ => p)) cache)
    (hgap : ∀ s i, 0 ≤ gap s p i)
    (hpositive : 0 < Fintype.card (Task C))
    (hmany : Fintype.card (Task C) < Fintype.card Root)
    (hlive : ∀ s, (packages s).live = some (frames s))
    (hvalid : ∀ s, (packages s).Valid)
    (hreflexive : ∀ s a, a ∈ (frames s).allowed a)
    (htarget : ∀ s, target s ∉ C)
    (hallowed : ∀ s, (frames s).allowed p ⊆ C)
    (hforbidden : ∀ s, (frames s).forbidden p ⊆ C)
    (hequal : ∀ s, (frames s).equalizerCost (target s) p (target s) = (frames s).baseline (target s))
    (hfrontier : ∀ s i, (frames s).gap i (target s) p = (cost i).real (blocks s p) - gap s p i)
    (hprotect : ∀ s i, i ∉ C → (cost i).real (blocks s p) ≤ gap s p i)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Result (Root := Root) C, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (program C p frames hpath packages gap target cache hmany) prior
        (some (out, outputPackage C p frames hpath packages gap out target hmany)) trace ∧
      (outputPackage C p frames hpath packages gap out target hmany).Valid ∧
      PhysicalCorrect (clippedUtility cost (domains blocks (fun _ => p)) (offsets gap (fun _ => p)))
        Subtype.val out.allocation ∧
      PartsCorrect cost (domains blocks (fun _ => p)) Subtype.val out ∧
      trace.length ≤ budget n (Fintype.card (Task C)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ Chores.SubCore.sourceBudget (Fintype.card (Task C)) ∧
      Masked.CacheCorrect (measureProfile cost) (domains blocks (fun _ => p)) out.cache := by
  obtain ⟨out, trace, hexec, hcorrect, hparts, hlen, hcuts, hcache⟩ :=
    clipped_correct cost (domains blocks (fun _ => p)) cache hc
      (Subtype.val : Task C → Fin n) (offsets gap (fun _ => p)) hgap hpositive hmany
      oracle hpolicy prior
  refine ⟨out, trace, ?_, ?_, hcorrect, hparts, hlen, hcuts, hcache⟩
  · simpa only [program, List.append_nil] using hexec.bind
      (fun result => match result with
        | none => Program.returned none
        | some out => Program.returned
            (some (out, outputPackage C p frames hpath packages gap out target hmany)))
      (Executes.returned _ (prior ++ trace))
  · exact output_valid C p frames hpath packages gap cost blocks out hparts hcorrect target
      hmany hlive hvalid hreflexive htarget hallowed hforbidden hequal hcache hfrontier hprotect

end EnvyFreeResearch.Full.RefinedChoresPhysicalPayment

#print axioms EnvyFreeResearch.Full.RefinedChoresPhysicalPayment.program_correct
