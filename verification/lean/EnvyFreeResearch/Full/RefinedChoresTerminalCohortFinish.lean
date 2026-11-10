import EnvyFreeResearch.Full.RefinedChoresTerminalCohortBase
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortMargin
import EnvyFreeResearch.Full.RefinedChoresTerminalCohortRemainder
import EnvyFreeResearch.Full.ChoresComponentPopulationExhausted
import EnvyFreeResearch.Full.ChoresTerminalAggregateSeparation

/-! Actual recursive terminal completion programs on the concrete closed
 allocation and the recorded full residue. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory OracleProtocol IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open QueryProgram Chores.ComponentPayments Chores.ComponentRecording Chores.ComponentExtraction Chores.SubCoreEntry ChoreComposition
open RefinedChoresClosed RefinedChoresClosedCaches
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]
    (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (group : TerminalGroup data normal original r H) (hr0 : ∀ i, 0 ≤ r i) (hH0 : 0 < H)
    (out : Result (Root := group.Root) group.terminalClass.participants)
    (oldPrivate : RootId → Fin n → List (Parent n)) (R0 : List (Parent n))

def TerminalGroup.finishExhausted
    (hpositive : group.terminalClass.participants.Nonempty)
    (hproper : group.terminalClass.participants ≠ Finset.univ) (children : Population.ChildPrograms n) :=
  Population.exhaustedProgram group.terminalClass.participants hpositive hproper
    (TerminalGroup.base data normal original r H group hr0 hH0 out)
    (Outer.fullResidueCache R0 (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)) children

def TerminalGroup.finishAtomic (B : Finset (Fin n))
    (hpositive : B.Nonempty) (hproper : B ≠ Finset.univ) (children : Population.ChildPrograms n) :=
  Population.atomicProgram B hpositive hproper
    (TerminalGroup.base data normal original r H group hr0 hH0 out) (extractedCache out)
    (Outer.fullResidueCache R0 (TerminalGroup.remainingPrivate data normal original r H group hr0 hH0 out oldPrivate)) children

/-- The class discriminator is computed by the terminal scan. The guards
 make this a total program on arbitrary data; physical correctness proves
 that the selected branch always has a nonempty proper child population. -/
def TerminalGroup.finishClass (children : Population.ChildPrograms n) :
    Program (Query (Fin n)) ℝ (Completion.Allocation n (Fin n)) :=
  match group.terminalClass with
  | .inl (_,B) =>
    if h : B.Nonempty ∧ B ≠ Finset.univ then
      TerminalGroup.finishAtomic data normal original r H group hr0 hH0 out oldPrivate R0 B h.1 h.2 children
    else .returned (TerminalGroup.base data normal original r H group hr0 hH0 out)
  | .inr A =>
    if h : A.Nonempty ∧ A ≠ Finset.univ then
      Population.exhaustedProgram A h.1 h.2
        (TerminalGroup.base data normal original r H group hr0 hH0 out)
        (Outer.fullResidueCache R0 (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)) children
    else .returned (TerminalGroup.base data normal original r H group hr0 hH0 out)

theorem TerminalGroup.finish_class_atomic (B : Finset (Fin n))
    (hpositive : B.Nonempty) (hproper : B ≠ Finset.univ)
    (htype : group.terminalClass = .inl (group.terminalClass.participants,B))
    (children : Population.ChildPrograms n) :
    TerminalGroup.finishClass data normal original r H group hr0 hH0 out oldPrivate R0 children =
      TerminalGroup.finishAtomic data normal original r H group hr0 hH0 out oldPrivate R0 B hpositive hproper children := by
  unfold TerminalGroup.finishClass
  rw [htype]
  exact dif_pos ⟨hpositive,hproper⟩

theorem TerminalGroup.finish_class_exhausted
    (hpositive : group.terminalClass.participants.Nonempty)
    (hproper : group.terminalClass.participants ≠ Finset.univ)
    (htype : group.terminalClass = .inr group.terminalClass.participants)
    (children : Population.ChildPrograms n) :
    TerminalGroup.finishClass data normal original r H group hr0 hH0 out oldPrivate R0 children =
      TerminalGroup.finishExhausted data normal original r H group hr0 hH0 out oldPrivate R0 hpositive hproper children := by
  unfold TerminalGroup.finishClass
  rw [htype]
  exact dif_pos ⟨hpositive,hproper⟩

variable (cost : Population.Costs n)
    (c : Fin n) (hsound : ∀ root, ∃ U, Snapshot.Sound cost.measure U c (original root))
    (good : data.Good original cost.measure r H)
    (hparts : PartsCorrect cost.measure
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label)) Subtype.val out)
    (hcorrect : PhysicalCorrect (affineUtility cost.measure
      (domains (TerminalGroup.blocks data normal original r H group) (fun _ => group.label))
      (offsets (TerminalGroup.gaps data normal original r H group) (fun _ => group.label)))
      Subtype.val out.allocation)
    (hvalid : (TerminalGroup.output data normal original r H group hr0 hH0 out).Valid)
    (hold : Outer.PrivateCorrect (measureProfile cost.measure) (fun root => (original root).piece) data.cache oldPrivate)
    (G : PackageGeometry.Pieces RootId (Fin n))
    (hG : ∀ root a, G.piece root a = (original root).piece a)
    (xs : List (Snapshot.Output n)) (index : RootId → Fin xs.length)
    (horiginal : ∀ root, original root = xs.get (index root)) (R : Set ℝ)
    (hR : CacheValid (measureProfile cost.measure) R R0) (hd : ∀ root a, Disjoint R (G.piece root a))
    (hsep : Clearance.Separated (Clearance.entries xs) cost.measure H R)
    (hr : ∀ i, 0 < (cost.measure i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
    (hr_eq : r = fun i => (cost.measure i).real R)
    (J : ℕ) (hroots : Fintype.card RootId ≤ J) (hreserve : (J : ℝ)*(n : ℝ)^2 ≤ H)
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost.measure) oracle)
    (children : Population.ChildPrograms n) (Q C : ℕ → ℕ)
    (hchildren : ∀ k hkpos hklt (agent : Fin k ↪ Fin n),
      Population.Specification cost agent (children k hkpos hklt agent) (Q k+n*C k) (C k))
include hsound good hparts hcorrect hvalid hold hG horiginal hR hd hsep hr hH hscale hr_eq hroots hreserve hpolicy hchildren

theorem TerminalGroup.finish_exhausted_correct
    (hpositive : group.terminalClass.participants.Nonempty)
    (hproper : group.terminalClass.participants ≠ Finset.univ)
    (htype : group.terminalClass = .inr group.terminalClass.participants) (hnH : (n : ℝ)+2 ≤ H)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle
      (TerminalGroup.finishExhausted data normal original r H group hr0 hH0 out oldPrivate R0 hpositive hproper children)
      prior result trace ∧
      trace.length ≤ Q group.terminalClass.participantsᶜ.card+n*C group.terminalClass.participantsᶜ.card ∧
      virtualCuts trace ≤ C group.terminalClass.participantsᶜ.card ∧
      result.Sound cost.measure id (R ∪ ⋃ root, ⋃ a, G.piece root a) := by
  have hb := TerminalGroup.base_sound data normal original r H group hr0 hH0 out cost.measure c hsound good hparts hcorrect hvalid G hG
  have hp := TerminalGroup.domain_partition data normal original r H group hr0 hH0 out cost.measure c hsound good hparts hcorrect G hG oldPrivate hold R hd
  have hc := TerminalGroup.full_cache_correct data normal original r H group hr0 hH0 out cost.measure c hsound good hparts G hG oldPrivate hold R R0 hR hd
  obtain ⟨result,trace,he,hq,hc',hs⟩ := Population.exhausted_program_correct cost oracle hpolicy
    group.terminalClass.participants hpositive hproper _ _ _ hb hp.1 _ hc
    (fun i hi j hj => by
      rw [TerminalGroup.base_material data normal original r H group hr0 hH0 out cost.measure c hsound good hparts hcorrect G hG j,
        TerminalGroup.base_material data normal original r H group hr0 hH0 out cost.measure c hsound good hparts hcorrect G hG i]
      exact TerminalGroup.exhausted_residue_dominance data normal original r H group hr0 hH0 out cost.measure c hsound good hparts
        xs index horiginal R hsep hr hH hscale hr_eq hcorrect hvalid G hG htype oldPrivate hold J hroots hreserve hnH i hi ⟨j,hj⟩)
    children Q C hchildren prior
  exact ⟨result,trace,he,hq,hc',hp.2 ▸ hs⟩

theorem TerminalGroup.finish_atomic_correct (B : Finset (Fin n))
    (hpositive : B.Nonempty) (hproper : B ≠ Finset.univ)
    (htype : group.terminalClass = .inl (group.terminalClass.participants,B))
    (hwhole : ∃ j : group.terminalClass.participants, material (out.parts j).suffixParts =
      TerminalGroup.blocks data normal original r H group (out.allocation.assigned j) group.label)
    (hlarge : 2*(2 : ℝ)^(n+2) ≤ H) (hsmall : (2 : ℝ)^(n+2)*(n : ℝ)^2 ≤ H)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ result trace, Executes oracle
      (TerminalGroup.finishAtomic data normal original r H group hr0 hH0 out oldPrivate R0 B hpositive hproper children)
      prior result trace ∧
      trace.length ≤ 19*2^n*n+(Q Bᶜ.card+n*C Bᶜ.card)+(Q B.card+n*C B.card) ∧
      virtualCuts trace ≤ 19*2^n+C Bᶜ.card+C B.card ∧
      result.Sound cost.measure id (R ∪ ⋃ root, ⋃ a, G.piece root a) := by
  have hb := TerminalGroup.base_sound data normal original r H group hr0 hH0 out cost.measure c hsound good hparts hcorrect hvalid G hG
  have hp := TerminalGroup.domain_partition data normal original r H group hr0 hH0 out cost.measure c hsound good hparts hcorrect G hG oldPrivate hold R hd
  have hx := TerminalGroup.extraction_partition data normal original r H group hr0 hH0 out oldPrivate cost.measure c hsound good hparts hold G hG R hd
  have hX := TerminalGroup.extracted_cache_correct data normal original r H group out cost.measure c hsound good hparts G hG
  have hrem := TerminalGroup.remainder_cache_correct data normal original r H group hr0 hH0 out oldPrivate cost.measure c hsound good hparts hold G hG R R0 hR hd
  have heq := Outer.full_removed_exact G
    (TerminalGroup.poolPrivate data normal original r H group hr0 hH0 out oldPrivate)
    (TerminalGroup.marked data normal original r H group out)
    (TerminalGroup.private_subset data normal original r H group hr0 hH0 out oldPrivate cost.measure c hsound good hparts hold G hG) R hd
  rw [TerminalGroup.marked_exact data normal original r H group hr0 hH0 out oldPrivate cost.measure good] at heq
  rw [← heq] at hrem
  have hbound := TerminalGroup.atomic_extracted_bounds data normal original r H group out cost.measure c hsound hparts
    xs index horiginal R hsep hr hH hscale hr_eq B htype hwhole
  have hu := TerminalGroup.remaining_bounds data normal original r H group hr0 hH0 out oldPrivate cost.measure c hsound good hparts hold G hG R hr_eq J hroots
  obtain ⟨result,trace,he,hq,hc,hs⟩ := Population.atomic_program_correct cost oracle hpolicy B hpositive hproper
    _ _ (extracted out) _ hb (by rw [hx.2]; exact hp.1) hx.1 _ _ hX hrem
    (fun i => Terminal.atomic_large_separation n J H ((2 : ℝ)^(n+2)) _ _ _ hH0 (by positivity)
      (hr _).le hreserve hlarge (hbound.2.2.1 _ (Population.group_embedding_mem B i)) (hu _).2)
    (fun i => Terminal.atomic_small_separation n H ((2 : ℝ)^(n+2)) _ _ _ hH0 (by positivity)
      (hr _).le hsmall (hbound.2.2.2 _ (Finset.mem_compl.mp (Population.group_embedding_mem Bᶜ i))) (hu _).1)
    children Q C hchildren prior
  refine ⟨result,trace,he,hq,hc,?_⟩
  rw [hx.2,hp.2] at hs
  exact hs

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.TerminalGroup.finish_atomic_correct
