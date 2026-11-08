import EnvyFreeResearch.Full.ChoresOuterDriverProgram
import EnvyFreeResearch.Full.ChoresOuterDriverOutside
import EnvyFreeResearch.Full.ChoresOuterDriverBudget
import EnvyFreeResearch.Full.ChoresOuterBatchGood

/-! Success and the complete executed-group ledger for the concrete outer
scheduler, proved by its actual fuel recursion. -/
noncomputable section
namespace EnvyFreeResearch.Full.Chores.Outer
open Set MeasureTheory Scheduler Components OracleProtocol IntervalOracle InitialPartition QueryProgram
open scoped Classical
variable {n : ℕ} {RootId : Type*} [Fintype RootId]

structure DriverInvariant (data : Data n RootId) (privateCache : RootId → Fin n → List (Parent n))
    (original : RootId → Snapshot.Output n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (c pivot : Fin n) (r : Fin n → ℝ) (H : ℝ) : Prop where
  good : data.Good original cost r H
  pool : PoolFloor data
  protection : Protected data original c pivot r H
  complement : PrivateCorrect (measureProfile cost) (fun root => (original root).piece) data.cache privateCache

variable [NeZero n] (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
  (xs : List (Snapshot.Output n)) (c pivot : Fin n)
  (hsound : ∀ s, ∃ U, Snapshot.Sound cost U c (xs.get s))
  (R : Set ℝ) (H : ℝ) (hsep : Clearance.Separated (Clearance.entries xs) cost H R)
  (hr : ∀ i, 0 < (cost i).real R) (hH : 1 < H) (hscale : (n : ℝ) < H*H)
  (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
  (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
include hsound hsep hr hH hscale hpolicy

theorem driver_executes (fuel : ℕ) (data : Data n (Fin xs.length))
    (privateCache : Fin xs.length → Fin n → List (Parent n))
    (hinv : DriverInvariant data privateCache xs.get cost c pivot (fun i => (cost i).real R) H)
    (hfuel : data.pending.rank ≤ fuel+2) (prior : History (Query (Fin n)) ℝ) :
    ∃ out : TerminalEntrance xs.get (fun i => (cost i).real R) H,
    ∃ trace : History (Query (Fin n)) ℝ,
      Executes oracle (driverProgram xs.get pivot (fun i => (cost i).real R) H fuel data privateCache)
        prior (some out) trace ∧
      DriverInvariant out.data out.privateCache xs.get cost c pivot (fun i => (cost i).real R) H ∧
      out.data.size ≤ data.size ∧
      trace.length ≤ (data.size-out.data.size)*ComponentRecording.budget n n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ (data.size-out.data.size)*SubCore.sourceBudget n := by
  induction fuel generalizing data privateCache prior with
  | zero =>
    have hp := positive_fuel data.pending 0 hfuel
    omega
  | succ fuel ih =>
    cases ha : nextAction data with
    | reveal p hp hfresh =>
      cases hc : revelationChoice data xs.get p (fun i => (cost i).real R) H with
      | terminal t roots =>
        let out : TerminalEntrance xs.get (fun i => (cost i).real R) H :=
          ⟨data,privateCache,p,hp,hfresh,t,roots,hc⟩
        refine ⟨out,[],?_,hinv,le_rfl,by simp,by simp⟩
        simp only [driverProgram,ha]
        split
        next t' roots' hc' =>
          have he := hc.symm.trans hc'
          cases he
          exact Executes.returned (some out) prior
        next q rr hq => cases (hc.symm.trans hq)
      | outside target roots =>
        obtain ⟨updated,hcommit,hgood,hpool,hprotected,hd,hsize,hcache⟩ :=
          driver_outside_step cost xs id c pivot hsound R H hsep hr hH hscale data hinv.good
            hinv.pool hinv.protection p hp hfresh roots target hc
        change outsideCommit data xs.get p hp (fun i => (cost i).real R) H roots target=some updated at hcommit
        have hprivate : PrivateCorrect (measureProfile cost) (fun root => (xs.get root).piece)
            updated.cache privateCache := by rw [hcache]; exact hinv.complement
        have hi : DriverInvariant updated privateCache xs.get cost c pivot (fun i => (cost i).real R) H :=
          ⟨hgood,hpool,hprotected,hprivate⟩
        obtain ⟨out,trace,hex,hout,hend,hQ,hC⟩ := ih updated privateCache hi (by omega) prior
        refine ⟨out,trace,?_,hout,hend.trans hsize,
          filter_query_budget _ _ _ _ _ hsize hQ,filter_query_budget _ _ _ _ _ hsize hC⟩
        simp only [driverProgram,ha]
        split
        next t rr ht => cases (hc.symm.trans ht)
        next q rr hq =>
          have he := hc.symm.trans hq
          cases he
          rw [hcommit]
          exact hex
    | merge hall cycle =>
      obtain ⟨outputs,first,hfirst,hgroups,hcorrect,hQfirst,hCfirst⟩ :=
        batch_executes data hall cycle cost xs id c hsound R H hsep hr hH hscale hinv.good
          (cohorts data hall cycle) oracle hpolicy prior
      let hs : (data.pending.selected hall cycle).Nonempty :=
        Finset.card_pos.mp (by have := data.pending.selected_two hall cycle; omega)
      let keep := Partition.keepLabel pivot (data.pending.selected hall cycle) hs
      let hk := Partition.keepLabel_mem pivot (data.pending.selected hall cycle) hs
      let updated := commitBatch data hall cycle xs.get outputs keep hk
      let priv := batchPrivateCache data hall cycle xs.get privateCache outputs
      have hg : updated.Good xs.get cost (fun i => (cost i).real R) H :=
        commit_batch_good data hall cycle cost xs id c hsound R H hsep hr hH hscale
          hinv.good outputs hcorrect hgroups keep hk
      have hp : PoolFloor updated := commit_pool_floor data hall cycle xs.get outputs keep hk hinv.pool hgroups
      have hprotect : Protected updated xs.get c pivot (fun i => (cost i).real R) H :=
        hinv.protection.merge_restrict _ (data.pending.selected_subset hall cycle) hs
          (batchSurvivor data hall cycle outputs) rfl rfl
      have hprivate : PrivateCorrect (measureProfile cost) (fun root => (xs.get root).piece) updated.cache priv :=
        batch_private_correct data hall cycle cost xs id c hsound privateCache outputs hinv.complement hcorrect
      have hd : updated.pending.rank < data.pending.rank := commit_rank data hall cycle xs.get outputs keep hk
      have hcharge : outputs.length+updated.size ≤ data.size :=
        commit_group_charge data hall cycle xs.get outputs keep hk hgroups
      have hi : DriverInvariant updated priv xs.get cost c pivot (fun i => (cost i).real R) H :=
        ⟨hg,hp,hprotect,hprivate⟩
      obtain ⟨out,tail,htail,hout,hend,hQtail,hCtail⟩ := ih updated priv hi (by omega) (prior++first)
      have hlen : (cohorts data hall cycle).length=outputs.length := by
        simpa only [List.length_map] using (congrArg List.length hgroups).symm
      have hcard : Fintype.card (ComponentBatch.Task data.pending hall cycle) ≤ n := by
        simpa only [ComponentBatch.Task,Fintype.card_coe,Fintype.card_fin] using
          data.pending.partition.tasks_card_le (data.pending.selected hall cycle)
      rw [hlen] at hQfirst hCfirst
      have hQ : first.length ≤ outputs.length*ComponentRecording.budget n n :=
        hQfirst.trans (Nat.mul_le_mul_left _ (recorded_budget_mono n hcard))
      have hC : first.countP (fun qr => isCutQuery qr.1) ≤ outputs.length*SubCore.sourceBudget n :=
        hCfirst.trans (Nat.mul_le_mul_left _ (source_budget_mono hcard))
      refine ⟨out,first++tail,?_,hout,by omega,?_,?_⟩
      · simp only [driverProgram,ha]
        exact hfirst.bind _ htail
      · rw [List.length_append]
        exact append_group_budget _ _ _ _ _ _ _ hend hcharge hQ hQtail
      · rw [List.countP_append]
        exact append_group_budget _ _ _ _ _ _ _ hend hcharge hC hCtail

end EnvyFreeResearch.Full.Chores.Outer
