import EnvyFreeResearch.Full.ChoresComponentActiveProjection
import EnvyFreeResearch.Full.ChoresComponentBoundaryCache

/-! One ambient recording pass around a native-population child protocol.
Query relabelling preserves its actual query count; extra work is charged to
Cut-created endpoints, and the output keeps the same provenance for ancestors.
The child's correctness and provenance are explicit recursive hypotheses. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ActivePopulation
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion
open scoped Classical

variable {n k : ℕ}

theorem known_lift (agent : Fin k → Fin n) (old : Set ℝ) (trace : History (Query (Fin k)) ℝ) :
    Boundary.Known old (ActiveCore.liftHistory agent trace) = Boundary.Known old trace := by
  simp only [Boundary.Known, cutReplies_lift]

theorem scoped_lift (agent : Fin k → Fin n) (old : Set ℝ) (trace : History (Query (Fin k)) ℝ)
    (h : Boundary.Scoped old trace) : Boundary.Scoped old (ActiveCore.liftHistory agent trace) := by
  induction trace generalizing old with
  | nil => trivial
  | cons qr rest ih =>
    rcases qr with ⟨q, r⟩
    refine ⟨?_, ?_⟩
    · cases q <;> exact h.1
    · have ht := ih (Boundary.Known old [(q, r)]) h.2
      simpa only [← known_lift agent old [(q, r)], ActiveCore.liftHistory, List.map_cons, List.map_nil] using ht

theorem endpoints_known (known : Set ℝ) (out : Completion.Allocation n (Fin k))
    (h : ∀ i, Boundary.CacheKnown known (out.pieces i)) :
    ∀ x ∈ endpoints out, x ∈ known := by
  intro x hx
  obtain ⟨parts, hparts, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hparts
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
  rcases (show x = p.left ∨ x = p.right from by simpa using hx) with rfl | rfl
  · exact (h i p hp).1
  · exact (h i p hp).2

theorem restore_known (known : Set ℝ) (cache : List (Parent n))
    (h : Boundary.CacheKnown known cache) (out : Completion.Allocation k (Fin k)) :
    ∀ i, Boundary.CacheKnown known ((restore cache out).pieces i) := by
  intro i p hp
  exact h p (List.mem_filter.mp hp).1

structure Recorded (n k : ℕ) where
  allocation : Completion.Allocation n (Fin k)
  cache : List (Parent n)

def program (agent : Fin k → Fin n) (cache : List (Parent n))
    (native : Program (Query (Fin k)) ℝ (Completion.Allocation k (Fin k))) :
    Program (Query (Fin n)) ℝ (Recorded n k) :=
  (ActiveCore.liftProgram agent native).bind (fun out =>
    (Boundary.recordProgram cache (endpoints out)).bind (fun fresh =>
      .returned ⟨restore fresh out, fresh⟩))

/-- Ambient restoration has additive Q + n*C cost. Its explicit recursive
premise contains the native child's successful execution, actual EF, and
old-or-Cut provenance; this lemma does not assert a closed main algorithm. -/
theorem program_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : Fin k → Fin n) (U : Set ℝ) (cache : List (Parent n))
    (hc : CacheValid (measureProfile cost) U cache)
    (native : Program (Query (Fin k)) ℝ (Completion.Allocation k (Fin k)))
    (Q C : ℕ)
    (hnative : ∀ oracle : AdaptiveOracle.Policy (Query (Fin k)) ℝ,
      AdaptiveOracle.IsLegalPolicy (measureProfile (fun i => cost (agent i))) oracle →
      ∃ out trace, Executes oracle native [] out trace ∧ trace.length ≤ Q ∧ virtualCuts trace ≤ C ∧
        out.Sound (fun i => cost (agent i)) id U ∧
        Boundary.Scoped {x | Aligned (projectCache agent cache) x} trace ∧
        (∀ x ∈ endpoints out, x ∈ Boundary.Known {x | Aligned (projectCache agent cache) x} trace))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (program agent cache native) prior out trace ∧
      trace.length ≤ Q + n * C ∧ virtualCuts trace ≤ C ∧
      out.allocation.Sound cost agent U ∧ CacheValid (measureProfile cost) U out.cache ∧
      (∀ x, Aligned cache x → Aligned out.cache x) ∧ out.cache.length ≤ cache.length + C ∧
      Boundary.Scoped {x | Aligned cache x} trace ∧
      (∀ x ∈ endpoints out.allocation, x ∈ Boundary.Known {x | Aligned cache x} trace) := by
  let childPolicy := ActiveCore.localPolicy agent oracle prior
  have hchild : AdaptiveOracle.IsLegalPolicy (measureProfile (fun i => cost (agent i))) childPolicy :=
    ActiveCore.local_policy_legal (measureProfile cost) agent oracle hpolicy prior
  obtain ⟨child, first, hfirst, hQ, hC, hsound, hscope, hpoints⟩ := hnative childPolicy hchild
  let source := ActiveCore.liftHistory agent first
  have hfirst' : Executes oracle (ActiveCore.liftProgram agent native) prior child source := by
    simpa only [source, ActiveCore.liftHistory, List.map_nil, List.append_nil] using
      ActiveCore.lift_executes agent oracle prior hfirst
  have hsource : ∀ x ∈ endpoints child, Boundary.FromTrace cache source x := by
    intro x hx
    have hp := hpoints x hx
    rcases hp with hp | hp
    · exact Or.inl ((project_aligned agent cache x).mp hp)
    · change x ∈ Boundary.cutReplies first at hp
      exact Or.inr (by simpa only [source, cutReplies_lift] using hp)
  obtain ⟨fresh, second, hsecond, hQ₂, hC₂, hfresh, halign, hold, hsize⟩ :=
    Boundary.record_correct (measureProfile cost) oracle hpolicy U cache hc (endpoints child)
      source hsource (prior ++ source)
  have hnew := Boundary.record_known (measureProfile cost) oracle cache hc.1 hc.2.1
    (endpoints child) source hsource (prior ++ source) fresh second hsecond
  have hsourceScope : Boundary.Scoped {x | Aligned cache x} source := by
    apply scoped_lift agent
    simpa only [project_aligned] using hscope
  let out : Recorded n k := ⟨restore fresh child, fresh⟩
  refine ⟨out, source ++ second, ?_, ?_, ?_, restore_sound cost agent U fresh hfresh child hsound halign,
    hfresh, hold, ?_, (Boundary.scoped_append _ source second).mpr ⟨hsourceScope, hnew.2⟩, ?_⟩
  · have htail := hsecond.bind (fun fresh => Program.returned (⟨restore fresh child, fresh⟩ : Recorded n k))
      (Executes.returned out _)
    simpa only [program, List.append_nil] using hfirst'.bind
      (fun child => (Boundary.recordProgram cache (endpoints child)).bind (fun fresh =>
        Program.returned (⟨restore fresh child, fresh⟩ : Recorded n k))) htail
  · rw [List.length_append, ActiveCore.lift_length]
    have hCsource : virtualCuts source ≤ C := by simpa only [source, ActiveCore.lift_cuts] using hC
    exact Nat.add_le_add hQ (hQ₂.trans (Nat.mul_le_mul_left n hCsource))
  · change (source ++ second).countP (fun qr => isCutQuery qr.1) ≤ C
    rw [List.countP_append]
    change virtualCuts source + virtualCuts second ≤ C
    rw [hC₂, Nat.add_zero]
    simpa only [source, ActiveCore.lift_cuts] using hC
  · have hCsource : virtualCuts source ≤ C := by simpa only [source, ActiveCore.lift_cuts] using hC
    exact hsize.trans (Nat.add_le_add_left hCsource cache.length)
  · intro x hx
    exact Boundary.known_mono _ source second
      (endpoints_known _ (restore fresh child) (restore_known _ fresh hnew.1 child) x hx)

end EnvyFreeResearch.Full.Chores.ActivePopulation
