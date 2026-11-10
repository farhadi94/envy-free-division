import EnvyFreeResearch.Full.RefinedUpperRepairFailure
import EnvyFreeResearch.Full.RefinedUpperGlobalProtocolValidity
import EnvyFreeResearch.Full.RefinedUpperGlobalPhysicalPendingStart

/-! Rejected paid calls preserve phase readiness. The old and refreshed
well-formed endpoint caches give equal buffer totals on unchanged cells. -/
noncomputable section
open MeasureTheory Set
namespace EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
open UpperRecordedDomain UpperCorrectionExecution GlobalCompletion
variable {n : ℕ}
variable (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)]

theorem pending_refresh_total (whole : Set ℝ) (p : Pending n)
    (hp : p.Physical μ whole) (history : UpperCircularStage.History n)
    (hphysical : (p.refresh history).Physical μ whole) (i : Fin n) :
    total (p.refresh history).buffer i = total p.buffer i := by
  rw [total_correct μ _ hphysical.buffer_wf, total_correct μ _ hp.buffer_wf]
  rfl

theorem pending_refresh_firstFactor (whole : Set ℝ) (p : Pending n)
    (hp : p.Physical μ whole) (history : UpperCircularStage.History n)
    (hphysical : (p.refresh history).Physical μ whole)
    (inst : Nonempty (Fin p.anchor.active.card)) (direction : Direction) :
    @Pending.firstFactor n (p.refresh history) inst direction =
      @Pending.firstFactor n p inst direction := by
  have hbuffer : (p.refresh history).localBuffer = p.localBuffer := by
    funext i
    exact pending_refresh_total μ whole p hp history hphysical _
  unfold Pending.firstFactor
  rw [hbuffer]
  rfl

theorem pending_refresh_basic_of_physical (whole : Set ℝ) (p : Pending n)
    (chores : Bool) (hp : p.Basic μ chores whole)
    (history : UpperCircularStage.History n)
    (hphysical : (p.refresh history).Physical μ whole) :
    (p.refresh history).Basic μ chores whole := by
  refine ⟨hphysical,hp.anchor_valid,hp.population,hp.snapshot_ef,hp.shrunk_ef,?_,hp.strong⟩
  intro i hi
  rw [pending_refresh_total μ whole p hp.physical history hphysical]
  exact hp.positive i hi

theorem pending_refresh_firstReady_of_physical (whole : Set ℝ) (p : Pending n)
    (chores : Bool) (G : ℝ) (hp : p.FirstReady μ chores whole G)
    (history : UpperCircularStage.History n)
    (hphysical : (p.refresh history).Physical μ whole) :
    (p.refresh history).FirstReady μ chores whole G := by
  refine ⟨pending_refresh_basic_of_physical μ whole p chores hp.toBasic history hphysical,
    hp.permutation_identity,hp.witness_active,hp.target_active,?_,?_⟩
  · rw [pending_refresh_total μ whole p hp.physical history hphysical]
    exact hp.certificate
  · intro inst
    calc
      G = @Pending.firstFactor n p inst (if chores then .chore else .cake) := hp.factor_eq inst
      _ = @Pending.firstFactor n (p.refresh history) inst (if chores then .chore else .cake) :=
        (pending_refresh_firstFactor μ whole p hp.physical history hphysical inst _).symm

theorem pending_refresh_secondReady_of_physical (whole : Set ℝ) (p : Pending n)
    (chores : Bool) (hp : p.SecondReady μ chores whole)
    (history : UpperCircularStage.History n)
    (hphysical : (p.refresh history).Physical μ whole) :
    (p.refresh history).SecondReady μ chores whole := by
  refine ⟨pending_refresh_basic_of_physical μ whole p chores hp.toBasic history hphysical,
    hp.permutation_identity,hp.edge,?_⟩
  rw [pending_refresh_total μ whole p hp.physical history hphysical]
  exact hp.bad

theorem pending_refresh_repairReady_of_physical (whole : Set ℝ) (p : Pending n)
    (chores : Bool) (hp : p.RepairReady μ chores whole)
    (history : UpperCircularStage.History n)
    (hphysical : (p.refresh history).Physical μ whole) :
    (p.refresh history).RepairReady μ chores whole := by
  refine ⟨pending_refresh_basic_of_physical μ whole p chores hp.toBasic history hphysical,
    hp.edge,?_,?_⟩
  · intro i hi
    rw [pending_refresh_total μ whole p hp.physical history hphysical]
    exact hp.own_loss i hi
  · rw [pending_refresh_total μ whole p hp.physical history hphysical]
    exact hp.large

theorem pending_refresh_basic (whole : Set ℝ) (p : Pending n)
    (chores : Bool) (hp : p.Basic μ chores whole)
    (history : UpperCircularStage.History n)
    (htruth : UpperEndpointCache.Truthful μ history) (hext : p.buffer.history ⊆ history) :
    (p.refresh history).Basic μ chores whole :=
  pending_refresh_basic_of_physical μ whole p chores hp history
    (pending_refresh_physical μ whole p hp.physical history htruth hext)

theorem pending_refresh_firstReady (whole : Set ℝ) (p : Pending n)
    (chores : Bool) (G : ℝ) (hp : p.FirstReady μ chores whole G)
    (history : UpperCircularStage.History n)
    (htruth : UpperEndpointCache.Truthful μ history) (hext : p.buffer.history ⊆ history) :
    (p.refresh history).FirstReady μ chores whole G :=
  pending_refresh_firstReady_of_physical μ whole p chores G hp history
    (pending_refresh_physical μ whole p hp.physical history htruth hext)

theorem pending_refresh_secondReady (whole : Set ℝ) (p : Pending n)
    (chores : Bool) (hp : p.SecondReady μ chores whole)
    (history : UpperCircularStage.History n)
    (htruth : UpperEndpointCache.Truthful μ history) (hext : p.buffer.history ⊆ history) :
    (p.refresh history).SecondReady μ chores whole :=
  pending_refresh_secondReady_of_physical μ whole p chores hp history
    (pending_refresh_physical μ whole p hp.physical history htruth hext)

theorem pending_refresh_repairReady (whole : Set ℝ) (p : Pending n)
    (chores : Bool) (hp : p.RepairReady μ chores whole)
    (history : UpperCircularStage.History n)
    (htruth : UpperEndpointCache.Truthful μ history) (hext : p.buffer.history ⊆ history) :
    (p.refresh history).RepairReady μ chores whole :=
  pending_refresh_repairReady_of_physical μ whole p chores hp history
    (pending_refresh_physical μ whole p hp.physical history htruth hext)

end EnvyFreeResearch.Full.RefinedUpperGlobalPhysical
