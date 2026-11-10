import EnvyFreeResearch.Full.RefinedChoresDataInitial
import EnvyFreeResearch.Full.RefinedChoresPool

/-! The root-local scan/class map is computed from actual stored tables.
No-stalling is derived from the physical package-ID partition and capacity. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedChoresData
open Set MeasureTheory IntervalOracle Chores Chores.InitialPartition Chores.OrderedUnion
open Chores.Equalizers Chores.Snapshot Chores.Frontier Chores.Scheduler ChoreComposition
open RefinedChoresRootState RefinedChoresPartialGraph RefinedChoresNormalize
open RefinedChoresStateCapacity RefinedChoresBucketCapacity
open scoped Classical BigOperators
variable {n : ℕ} {RootId : Type*}

def Data.sink (data : Data n RootId) (normal : data.Normal) (s : Fin data.size) :
    (data.pending s).Component :=
  (reachable_sink (data.pending s) (data.visited s) (normal s) data.protectedLabel).choose

theorem sink_unpaid (data : Data n RootId) (normal : data.Normal) (s : Fin data.size) :
    (data.sink normal s : Fin n) ∉ (data.pending s).pending :=
  (reachable_sink (data.pending s) (data.visited s) (normal s) data.protectedLabel).choose_spec.1

def Data.sourceLabel (data : Data n RootId) (normal : data.Normal) (s : Fin data.size) : Fin n :=
  data.sink normal s

def Data.sourceSet (data : Data n RootId) (normal : data.Normal) (s : Fin data.size) : Finset (Fin n) :=
  componentSet (data.pending s) (data.sink normal s)

theorem component_source (data : Data n RootId) (normal : data.Normal) (s : Fin data.size) :
    data.component s (data.sourceLabel normal s) = data.sourceSet normal s := by
  exact congrArg (componentSet (data.pending s)) ((data.pending s).component_label (data.sink normal s))

def rawBucket (n w : ℕ) : Fin (RefinedChoresPool.buckets n) :=
  ⟨min (Nat.log 2 w) (4*n^2),by unfold RefinedChoresPool.buckets; have := min_le_right (Nat.log 2 w) (4*n^2); omega⟩

def Data.scan (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ) (s : Fin data.size) : Frontier.Outcome n :=
  Frontier.scan (original (data.source s)).equalizers (data.sourceLabel normal s) r H (data.sourceSet normal s)

def Data.classify (data : Data n RootId) (normal : data.Normal)
    (original : RootId → Snapshot.Output n) (r : Fin n → ℝ) (H : ℝ)
    (s : Fin data.size) : RefinedChoresPool.Class n :=
  let p := data.sourceLabel normal s
  let table := (original (data.source s)).equalizers
  match data.scan normal original r H s with
  | .outside _ => .inl (.inl (p,data.sourceSet normal s,rawBucket n (data.packages s).ids.length))
  | .atomic a => .inl (.inr (p,
      atomicParticipants (eligible (weight table p) (rankOf table p) r H) (rankOf table p) a,
      largeMask (weight table p) r H a))
  | .exhausted _ => .inr (p,eligible (weight table p) (rankOf table p) r H)

variable [Fintype RootId] (data : Data n RootId)
    (original : RootId → Snapshot.Output n)
    (cost : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (r : Fin n → ℝ) (H : ℝ) (good : data.Good original cost r H)
include good

theorem active_weight_bound (s : Fin data.size) : (data.packages s).ids.length ≤ unpaid n := by
  letI : Nonempty (Fin n) := ⟨data.protectedLabel⟩
  exact (good.weight_bounded s).trans (by simpa only [Fintype.card_fin] using capacity_bound (data.pending s))

theorem active_weight_positive (s : Fin data.size) : 0 < (data.packages s).ids.length := by
  simp only [Package.ids,good.live s,Option.toList_some,List.length_append,List.length_map,
    List.length_cons,List.length_nil]
  omega

theorem active_bucket_exact (s : Fin data.size) :
    (rawBucket n (data.packages s).ids.length).val = Nat.log 2 (data.packages s).ids.length := by
  have hn : 1 ≤ n := by have := data.protectedLabel.isLt; omega
  have h := (Nat.log_le_clog 2 (data.packages s).ids.length).trans
    (Nat.clog_le_of_le_pow ((active_weight_bound data original cost r H good s).trans (unpaid_le_power hn)))
  exact min_eq_left h

theorem active_bucket_lower (s : Fin data.size) :
    2^(rawBucket n (data.packages s).ids.length).val ≤ (data.packages s).ids.length := by
  rw [active_bucket_exact data original cost r H good]
  exact Nat.pow_log_le_self _ (by have := active_weight_positive data original cost r H good s; omega)

theorem active_bucket_upper (s : Fin data.size) :
    (data.packages s).ids.length < 2^((rawBucket n (data.packages s).ids.length).val+1) := by
  rw [active_bucket_exact data original cost r H good]
  exact Nat.lt_pow_succ_log_self (by decide) _

theorem active_mass (hclosed : data.closed = []) :
    (∑ s : Fin data.size, (data.packages s).ids.length) = Fintype.card RootId := by
  have h := good.all_ids.length_eq
  simpa only [Data.allPackages,hclosed,List.nil_append,List.length_flatMap,List.map_ofFn,
    List.sum_ofFn,Function.comp_def,Finset.length_toList,Finset.card_univ] using h

/-- An actual current pool with the prescribed number of original roots
always supplies a sufficiently populated computed scan class. -/
theorem actual_class_available (normal : data.Normal) (hclosed : data.closed = [])
    (hpool : Fintype.card RootId = RefinedChoresPool.poolSize n) :
    ∃ cl : RefinedChoresPool.Class n,
      n+1 ≤ (Finset.univ.filter (fun s => data.classify normal original r H s = cl)).card := by
  apply RefinedChoresPool.cannot_stall n Finset.univ (data.classify normal original r H)
    (fun s => (data.packages s).ids.length)
  · intro s _
    exact active_weight_bound data original cost r H good s
  · exact (active_mass data original cost r H good hclosed).trans hpool

end EnvyFreeResearch.Full.RefinedChoresData
#print axioms EnvyFreeResearch.Full.RefinedChoresData.actual_class_available
