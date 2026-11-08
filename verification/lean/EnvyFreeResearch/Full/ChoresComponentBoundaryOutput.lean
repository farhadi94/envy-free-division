import EnvyFreeResearch.Full.ChoresComponentBoundaryCore
import EnvyFreeResearch.Full.ChoresComponentBoundaryInitial

/-! Every returned interval-Core boundary is an input endpoint or an actual
Cut reply. The proof joins the physical initial partition, the complete
persistent table execution, and its established record-reference invariant. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Boundary
open Set OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Persistent PhysicalCore
open scoped Classical

variable {n : ℕ}

theorem prefix_points_known (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (points : Set ℝ) (frame : Frame n) (store : Store n)
    (hvalid : ValidStore P frame store) (hzero : ∀ p i, (frame.empty p).formal i = (0, 0))
    (hold : StoreKnown points store)
    (prior : History (Query (Fin n)) ℝ) (out : PrefixResult n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (prefixProgram frame store) prior out trace) :
    ∀ p, (out.state.endpoint p).point ∈ Known points trace := by
  obtain ⟨table, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  cases hout : lookup table.cache (fullKey n) with
  | none => rw [hout] at hsecond; cases hsecond
  | some state =>
    rw [hout] at hsecond
    cases hsecond
    simp only [List.append_nil] at htrace
    subst trace
    obtain ⟨_, _, hcache, _⟩ := layers_run_properties P hmono oracle hpolicy frame store
      hvalid hzero n prior table first hfirst
    have href := (lookup_sound table.store table.cache hcache (fullKey n) state hout).1
    have hknown := layers_store_known oracle points frame store hold n prior table first hfirst
    intro p
    exact hknown ((fullKey n).2 p) (state.endpoint p) (href p)

def CoreKnown (points : Set ℝ) : IntervalCore.Outcome n → Prop
  | .zero _ => True
  | .prefixes parent state => ∀ p, ParentKnown points (parent p) ∧
      (state.endpoint p).point ∈ points

theorem core_points_known (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (points : Set ℝ) (c : Fin n) (a b : ℝ) (ha : a ∈ points) (hb : b ∈ points)
    (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1)
    (prior : History (Query (Fin n)) ℝ) (out : IntervalCore.Outcome n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (IntervalCore.coreProgram c a b) prior out trace) :
    CoreKnown (Known points trace) out := by
  obtain ⟨initial, first, second, hfirst, hsecond, htrace⟩ := Executes.split_bind _ _ h
  have hipoints := initial_known oracle points c a b ha hb prior initial first hfirst
  obtain ⟨initial', first', hfirst', _, _, hicorrect⟩ :=
    initial_program_correct P hmono oracle hpolicy c a b hbound prior
  obtain ⟨heq, hteq⟩ := hfirst.deterministic hfirst'
  subst initial'
  subst first'
  cases initial with
  | zero i =>
    cases hsecond
    trivial
  | partition total parents =>
    obtain ⟨_, _, hlen, hchain, _⟩ := hicorrect
    let parent := indexed parents hlen
    have hpknown : ∀ p, ParentKnown (Known points first) (parent p) :=
      fun p => hipoints _ (indexed_mem parents hlen p)
    have hbounds : ∀ p, 0 ≤ (parent p).left ∧ (parent p).left ≤ (parent p).right ∧ (parent p).right ≤ 1 := by
      intro p
      have hb' := hchain.member_bounds P parents a b _ (indexed_mem parents hlen p)
      exact ⟨hbound.1.trans hb'.1, hb'.2.1, hb'.2.2.trans hbound.2.2⟩
    have hvalues : ∀ i p, (parent p).value i = P.cumulative i (parent p).right - P.cumulative i (parent p).left :=
      fun i p => hchain.member_value P parents a b _ (indexed_mem parents hlen p) i
    let frame := IntervalCore.parentFrame parent
    have hvalid : ValidStore P frame (initialStore frame) :=
      initialStore_valid P hmono _ _ _ hbounds hvalues
    have hknown : StoreKnown (Known points first) (initialStore frame) := by
      intro p r hr
      rcases (show r = frame.empty p ∨ r = frame.whole p from by simpa [initialStore] using hr) with rfl | rfl
      · exact (hpknown p).1
      · exact (hpknown p).2
    rw [IntervalCore.finishProgram, dite_eq_left hlen] at hsecond
    obtain ⟨prefixResult, tail, empty, htail, hreturn, hsecond⟩ := Executes.split_bind _ _ hsecond
    cases hreturn
    simp only [List.append_nil] at hsecond
    subst second
    subst trace
    have hprefix := prefix_points_known P hmono oracle hpolicy (Known points first) frame
      (initialStore frame) hvalid (fun _ _ => rfl) hknown (prior ++ first) prefixResult tail htail
    intro p
    refine ⟨⟨known_mono points first tail (hpknown p).1,
      known_mono points first tail (hpknown p).2⟩, ?_⟩
    simpa only [known_append] using hprefix p

theorem core_endpoints_known (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (points : Set ℝ) (c : Fin n) (a b : ℝ) (ha : a ∈ points) (hb : b ∈ points)
    (hbound : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1)
    (prior : History (Query (Fin n)) ℝ) (out : IntervalCore.Outcome n)
    (trace : History (Query (Fin n)) ℝ)
    (h : Executes oracle (IntervalCore.coreProgram c a b) prior out trace) :
    ∀ x ∈ coreEndpoints out, x ∈ Known points trace := by
  have hk := core_points_known P hmono oracle hpolicy points c a b ha hb hbound prior out trace h
  cases out with
  | zero i => simp [coreEndpoints]
  | prefixes parent state =>
    intro x hx
    simp only [coreEndpoints, List.mem_append, List.mem_ofFn] at hx
    rcases hx with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact (hk p).1.1
    · exact (hk p).2
    · exact (hk p).1.2

end EnvyFreeResearch.Full.Chores.Boundary
