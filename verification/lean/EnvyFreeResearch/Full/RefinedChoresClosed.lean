import EnvyFreeResearch.Full.ChoresComponentAffineTables
import EnvyFreeResearch.Full.ChoresComponentAssignment
import EnvyFreeResearch.Full.RefinedChoresPhysicalPayment

/-! Closed affine compensation batches with root-local permission graphs.
Participants need a return path to the same label in each root, but the
source components and all remaining components may differ between roots. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresClosed
open Set MeasureTheory OracleProtocol IntervalOracle
open Chores.OrderedUnion
open ChoreComposition Chores Chores.Persistent Chores.Suffix Chores.SubCoreEntry
open Chores.SubCorePhysical Chores.ComponentPayments Chores.ComponentRecording
open Chores.QueryProgram
open scoped Classical
variable {n : ℕ} {Root RootId : Type*} [Fintype Root] [Nonempty Root]
    (A : Finset (Fin n)) (p : Fin n)

abbrev Result := Recorded (Record n) A Root n

def donorRoot (out : Result (Root := Root) A) (j : Fin n) : Root :=
  if hj : j ∈ A then out.allocation.assigned ⟨j,hj⟩ else Classical.choice inferInstance

def utilities (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) A) (i j : Fin n) : ℝ :=
  if hj : j ∈ A then utility Subtype.val (fun _ => p) gap out i ⟨j,hj⟩ else 0

variable (frames : Root → Frame (Fin n) RootId)
    (hpath : ∀ s j, j ∈ A → Relation.ReflTransGen (fun a b => b ∈ (frames s).allowed a) j p)

def owners (out : Result (Root := Root) A) (j : Fin n) : Equiv.Perm (Fin n) :=
  if hj : j ∈ A then RefinedChoresDirectedMatching.donor
    (fun a b => b ∈ (frames (out.allocation.assigned ⟨j,hj⟩)).allowed a) p j (hpath _ j hj)
  else 1

def donations (packages : Root → Package (Fin n) RootId)
    (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) A) : List (Donation (Fin n) RootId) :=
  ComponentAffine.tasks A (packages ∘ donorRoot A out) (frames ∘ donorRoot A out) p
    (owners A p frames hpath out) (utilities A p gap out)

variable (packages : Root → Package (Fin n) RootId)
    (gap : Root → Fin n → Fin n → ℝ) (out : Result (Root := Root) A)
    (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (blocks : Root → Fin n → Set ℝ)
    (hparts : PartsCorrect cost (domains blocks (fun _ => p)) Subtype.val out)
    (hcorrect : PhysicalCorrect
      (affineUtility cost (domains blocks (fun _ => p)) (offsets gap (fun _ => p)))
      Subtype.val out.allocation)
include hparts hcorrect

theorem own_nonnegative (i : Fin n) (hi : i ∈ A) : 0 ≤ utilities A p gap out i i := by
  have h := affine_own_nonnegative cost blocks Subtype.val (fun _ => p) gap out hparts hcorrect (⟨i,hi⟩ : A)
  simpa only [utilities,dite_eq_left hi] using h

theorem comparisons (i j : Fin n) (hi : i ∈ A) (hj : j ∈ A) :
    utilities A p gap out i j ≤ utilities A p gap out i i := by
  have h := affine_comparison cost blocks Subtype.val (fun _ => p) gap out hparts hcorrect
    (⟨i,hi⟩ : A) (⟨j,hj⟩ : A) rfl
  exact (le_max_right _ _).trans (by simpa only [utilities,dite_eq_left hi,dite_eq_left hj] using h)

omit hcorrect in
theorem protected_utility (i j : Fin n) (hj : j ∈ A)
    (hprotect : ∀ s, (cost i).real (blocks s p) ≤ gap s p i) :
    utilities A p gap out i j ≤ 0 := by
  have h := protected_utility_nonpositive cost blocks Subtype.val (fun _ => p) gap out hparts
    i (⟨j,hj⟩ : A) (hprotect _)
  simpa only [utilities,dite_eq_left hj] using h

theorem donations_wellFormed (hlive : ∀ s, (packages s).live = some (frames s))
    (hframes : ∀ s, (frames s).Good) (hreflexive : ∀ s a, a ∈ (frames s).allowed a) :
    ∀ d ∈ donations A p frames hpath packages gap out, d.WellFormed := by
  intro d hd
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
  have hj' : j ∈ A := Finset.mem_toList.mp hj
  constructor
  · exact hlive _
  · apply affine_proposal_good
    · exact hframes _
    · simp only [owners,dite_eq_left hj']
      exact RefinedChoresDirectedMatching.donor_recipient _ _ _ _
    · intro a ha
      simp only [owners,dite_eq_left hj',Function.comp_apply,donorRoot]
      exact RefinedChoresDirectedMatching.donor_allowed_other _ (hreflexive _) p j _ a ha
    · exact own_nonnegative A p gap out cost blocks hparts hcorrect j hj'

theorem payment_coverage
    (hprotect : ∀ i ∉ A, ∀ s, (cost i).real (blocks s p) ≤ gap s p i)
    (i j a : Fin n) :
    extras (donations A p frames hpath packages gap out) i j a ≤
      payments (donations A p frames hpath packages gap out) i a := by
  apply ComponentAffine.task_payment_coverage
  · exact own_nonnegative A p gap out cost blocks hparts hcorrect
  · intro i hi j hj
    exact comparisons A p gap out cost blocks hparts hcorrect i j hi hj
  · intro i hi j hj
    exact protected_utility A p gap out cost blocks hparts i j hj (hprotect i hi)

def outputPackage (hmany : Fintype.card A < Fintype.card Root) : Package (Fin n) RootId :=
  mergeClosed (packages (ComponentAssignment.unused out.allocation hmany))
    (donations A p frames hpath packages gap out)

theorem output_valid (hmany : Fintype.card A < Fintype.card Root)
    (hlive : ∀ s, (packages s).live = some (frames s)) (hvalid : ∀ s, (packages s).Valid)
    (hreflexive : ∀ s a, a ∈ (frames s).allowed a)
    (hprotect : ∀ i ∉ A, ∀ s, (cost i).real (blocks s p) ≤ gap s p i) :
    (outputPackage A p frames hpath packages gap out hmany).Valid := by
  have hframes : ∀ s, (frames s).Good := fun s => (hvalid s).live_good _ (hlive s)
  apply merge_closed_valid _ (hvalid _) _
    (donations_wellFormed A p frames hpath packages gap out cost blocks hparts hcorrect
      hlive hframes hreflexive)
  · intro d hd
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
    exact hvalid _
  · intro i j a hij
    exact payment_coverage A p frames hpath packages gap out cost blocks hparts hcorrect hprotect i j a

omit hparts hcorrect in
def program (cache : Masked.Cache Root n) (hmany : Fintype.card A < Fintype.card Root) :
    Program (Query (Fin n)) ℝ (Option (Result (Root := Root) A × Package (Fin n) RootId)) :=
  (ComponentRecording.affineProgram Subtype.val (offsets gap (fun _ => p)) cache hmany.le).bind
    (fun result => match result with
      | none => .returned none
      | some out => .returned (some (out,outputPackage A p frames hpath packages gap out hmany)))

omit hparts hcorrect in
theorem program_correct
    (cache : Masked.Cache Root n)
    (hc : Masked.CacheCorrect (measureProfile cost) (domains blocks (fun _ => p)) cache)
    (hgap : ∀ s i, 0 ≤ gap s p i) (hpositive : A.Nonempty)
    (hmany : Fintype.card A < Fintype.card Root)
    (hwhole : ∀ s i, i ∈ A → 0 ≤ (cost i).real (blocks s p) - gap s p i)
    (hlive : ∀ s, (packages s).live = some (frames s)) (hvalid : ∀ s, (packages s).Valid)
    (hreflexive : ∀ s a, a ∈ (frames s).allowed a)
    (hprotect : ∀ i ∉ A, ∀ s, (cost i).real (blocks s p) ≤ gap s p i)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out : Result (Root := Root) A, ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (program A p frames hpath packages gap cache hmany) prior
        (some (out,outputPackage A p frames hpath packages gap out hmany)) trace ∧
      (outputPackage A p frames hpath packages gap out hmany).Valid ∧
      (outputPackage A p frames hpath packages gap out hmany).live = none ∧
      PhysicalCorrect (affineUtility cost (domains blocks (fun _ => p)) (offsets gap (fun _ => p)))
        Subtype.val out.allocation ∧
      PartsCorrect cost (domains blocks (fun _ => p)) Subtype.val out ∧
      trace.length ≤ ComponentRecording.budget n (Fintype.card A) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ Chores.SubCore.sourceBudget (Fintype.card A) ∧
      Masked.CacheCorrect (measureProfile cost) (domains blocks (fun _ => p)) out.cache ∧
      ∃ j : A, material (out.parts j).suffixParts = blocks (out.allocation.assigned j) p := by
  have hpos : 0 < Fintype.card A := by simpa using Finset.card_pos.mpr hpositive
  obtain ⟨out,trace,hexec,hcorrect,hparts,hlen,hcuts,hcache⟩ :=
    ComponentRecording.affine_correct cost (domains blocks (fun _ => p)) cache hc
      Subtype.val (offsets gap (fun _ => p)) hgap hpos hmany oracle hpolicy prior
      (fun s i => hwhole s i i.property)
  refine ⟨out,trace,?_,?_,rfl,hcorrect,hparts,hlen,hcuts,hcache,?_⟩
  · simpa only [program,List.append_nil] using hexec.bind
      (fun result => match result with
        | none => Program.returned none
        | some out => Program.returned
            (some (out,outputPackage A p frames hpath packages gap out hmany)))
      (Executes.returned _ (prior ++ trace))
  · exact output_valid A p frames hpath packages gap out cost blocks hparts hcorrect
      hmany hlive hvalid hreflexive hprotect
  · obtain ⟨j,hj,_⟩ := affine_whole_retained cost blocks Subtype.val (fun _ => p) gap
      out hparts hcorrect hcache
    exact ⟨j,hj⟩

end EnvyFreeResearch.Full.RefinedChoresClosed
#print axioms EnvyFreeResearch.Full.RefinedChoresClosed.program_correct
