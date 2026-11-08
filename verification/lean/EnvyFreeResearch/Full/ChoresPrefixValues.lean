import EnvyFreeResearch.Full.ChoresPrefixCore

/-!
# Physical meaning of a successful prefix Core

The unperturbed endpoint values and the parent interval bounds are consequences
of the persistent-store invariant. No formal infinitesimal is charged to an
agent, and the whole-record certificate is an equality of physical endpoints.
-/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.PhysicalCore

open Set OracleProtocol IntervalOracle QueryProgram Persistent
open scoped BigOperators

lemma record_point_between {n : ℕ} (P : Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (p : Fin n) (r : Record n) (hr : r ∈ store p) :
    (frame.empty p).point ≤ r.point ∧ r.point ≤ (frame.whole p).point := by
  have horder : List.Pairwise (fun r s : Record n => r.point ≤ s.point) (store p) :=
    (hvalid p).1.imp (fun h => h.1)
  have hfirst := horder.rel_head_of_rel_head_head hr le_rfl
  have hlast := horder.rel_getLast_of_rel_getLast_getLast hr le_rfl
  have he : (store p).head (List.ne_nil_of_mem hr) = frame.empty p :=
    Option.some.inj ((List.head?_eq_some_head (List.ne_nil_of_mem hr)).symm.trans (hvalid p).2.2.1)
  have hw : (store p).getLast (List.ne_nil_of_mem hr) = frame.whole p :=
    Option.some.inj ((List.getLast?_eq_some_getLast (List.ne_nil_of_mem hr)).symm.trans (hvalid p).2.2.2)
  simpa only [he, hw] using And.intro hfirst hlast

def prefixValue {n : ℕ} (P : Profile (Fin n)) (frame : Frame n)
    (s : State n n) (i p : Fin n) : ℝ :=
  P.cumulative i (s.endpoint p).point - P.cumulative i (frame.base p)

/-- Every comparison in the returned formal state implies the corresponding
ordinary real-valued comparison on the actual physical interval prefixes. -/
theorem real_envy_free {n : ℕ} (P : Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (s : State n n) (href : References store (fullKey n) s)
    (hEF : EnvyFree (fullKey n) s) :
    ∀ i p, prefixValue P frame s i (s.matching i) ≤ prefixValue P frame s i p := by
  intro i p
  have h := recordLE_primary_le (hEF i p)
  have hs := ((hvalid (s.matching i)).2.1 _ (href (s.matching i))).1 i
  have hp := ((hvalid p).2.1 _ (href p)).1 i
  simpa only [fullKey, OrderIso.coe_toOrderEmbedding, OrderIso.refl_apply, hs, hp, prefixValue] using h

theorem physical_prefix_bounds {n : ℕ} (P : Profile (Fin n))
    {frame : Frame n} {store : Store n} (hvalid : ValidStore P frame store)
    (s : State n n) (href : References store (fullKey n) s) :
    ∀ p, (frame.empty p).point ≤ (s.endpoint p).point ∧
      (s.endpoint p).point ≤ (frame.whole p).point :=
  fun p => record_point_between P hvalid p (s.endpoint p) (href p)

/-- Initialization from cached whole-parent values gives the physical interval
statement directly. Acquiring these cached values is handled by the separate
initial cutting program, rather than counted as free here. -/
theorem initialized_prefix_program_correct {n : ℕ} (hn : 0 < n) (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ) (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (left right : Fin n → ℝ) (value : Fin n → Fin n → ℝ)
    (hbound : ∀ p, 0 ≤ left p ∧ left p ≤ right p ∧ right p ≤ 1)
    (hvalue : ∀ i p, value i p = P.cumulative i (right p) - P.cumulative i (left p)) :
    let frame := initialFrame left right value
    ∃ result : PrefixResult n, ∃ trace : History (Query (Fin n)) ℝ,
      AdaptiveOracle.run (prefixProgram frame (initialStore frame)).protocol oracle ()
        (n * (n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1))) [] = ⟨trace, .returned result⟩ ∧
      trace.length ≤ n * (n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1)) ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ n ^ 2 * ((2 * (n - 1)).choose (n - 1) - 1) ∧
      (∀ p, left p ≤ (result.state.endpoint p).point ∧ (result.state.endpoint p).point ≤ right p) ∧
      (∀ i p, prefixValue P frame result.state i (result.state.matching i) ≤
        prefixValue P frame result.state i p) ∧
      ∃ i, (result.state.endpoint (result.state.matching i)).point = right (result.state.matching i) := by
  dsimp only
  let frame := initialFrame left right value
  obtain ⟨result, trace, hrun, hlen, hcuts, hvalid, href, hEF, _, i, hi⟩ :=
    prefix_program_correct hn P hmono oracle hpolicy frame (initialStore frame)
      (initialStore_valid P hmono left right value hbound hvalue) (fun _ _ => rfl)
      (initialFrame_proper hn left right value)
  exact ⟨result, trace, hrun, hlen, hcuts, physical_prefix_bounds P hvalid result.state href,
    real_envy_free P hvalid result.state href hEF, i, congrArg Record.point hi⟩

end EnvyFreeResearch.Full.Chores.PhysicalCore
