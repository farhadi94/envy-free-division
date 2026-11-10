import EnvyFreeResearch.Full.MoatExperiment
import EnvyFreeResearch.Full.MoatTranscript
import EnvyFreeResearch.Full.NonnegativeMainEvents

noncomputable section
namespace EnvyFreeResearch.Full.MoatRetention
open Set MeasureTheory IntervalOracle IntervalAllocation OracleProtocol ProtocolMeasurable Metric
open NonnegativeOracle NonnegativeProfile NonnegativeSuccess NonnegativeRandomOutput
open NonnegativeRetainedFailure NonnegativeAllocation NonnegativeEndpointLaw NonnegativeEndpointCapture
open NonnegativeReplay NonnegativeProbability
open MoatSelection MoatExperiment
open scoped Classical ENNReal
abbrev Circle := NonnegativeCircle.Circle

noncomputable def center {n : ℕ} (z : Input n) : ℝ := representative z.2

theorem center_measurable {n : ℕ} : Measurable (center (n := n)) :=
  measurable_representative.comp measurable_snd

theorem center_atomless {n : ℕ} (a : ℝ) :
    MoatDetection.law n {z | center z = a} = 0 := by
  have heq : {z : Input n | center z = a} = univ ×ˢ {x : Circle | representative x = a} := by
    ext z
    simp [center]
  rw [heq, MoatDetection.law, Measure.prod_prod]
  change NonnegativeDetection.observerLaw n univ * volume (representative ⁻¹' {a}) = 0
  rw [representative_fiber_null, mul_zero]

abbrev baseline := @NonnegativeMainEvents.baseline
abbrev baseline_measurable := @NonnegativeMainEvents.baseline_measurable

def failure {n : ℕ} {Tape : Type*}
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (two flag chores : Bool) (w h : ℝ) : Set (Tape × Input n) :=
  Prod.swap ⁻¹' (jointSuccess next (oracle two flag chores w h) [] (inputGood two chores w h))ᶜ

def success {n : ℕ} {Tape : Type*}
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n))) (flag : Bool) (fuel : ℕ) :
    Set (Tape × Input n) := {z | Successful {A | UniformEF A} (baseline next flag fuel z.1)}

def detected {n : ℕ} {Tape : Type*}
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (two flag : Bool) (w : ℝ) (fuel : ℕ) : Set (Tape × Input n) :=
  {z | z.2 ∈ MoatTranscript.detection two w (baselineRequests uniform (baseline next flag fuel z.1))}

def geometricLoss {n : ℕ} {Tape : Type*}
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (flag : Bool) (fuel : ℕ) (h : ℝ) : Set (Tape × Input n) :=
  endpointHit (fun tape => endpointCount uniform (baseline next flag fuel tape))
    (fun tape k => endpoint uniform (baseline next flag fuel tape) k) center h ∪
    Prod.fst ⁻¹' NonnegativeMainEvents.gapLoss next flag fuel h

def capLoss {n : ℕ} {Tape : Type*}
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n))) (flag : Bool) (fuel : ℕ) :
    Set (Tape × Input n) := {z | Exhausted (baseline next flag fuel z.1)}

theorem retained_event_inclusion {n : ℕ} {Tape : Type*} [NeZero n] (hn : 2 ≤ n)
    (next : Protocol Tape (Query (Fin n)) Reply (Allocation (Fin n)))
    (two flag chores : Bool) (fuel : ℕ) (w h : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hh : 0 < h) (hhw : h ≤ w) (hwidth : 1/(n:ℝ) < w) :
    ((success next flag fuel)ᶜ ∪ decoded (baseline next flag fuel) two) \
      (detected next two flag w fuel ∪ (geometricLoss next flag fuel h ∪ capLoss next flag fuel)) ⊆
      failure next two flag chores w h := by
  rintro z ⟨hretain,hnot⟩
  have hdetect : z ∉ detected next two flag w fuel := fun hz => hnot (Or.inl hz)
  have hgeom : z ∉ geometricLoss next flag fuel h := fun hz => hnot (Or.inr (Or.inl hz))
  have hcap : z ∉ capLoss next flag fuel := fun hz => hnot (Or.inr (Or.inr hz))
  have hsafe : CoordinatesSafe uniform (baseline next flag fuel z.1) h (center z.2) (center z.2) := by
    intro k hk
    have hd : h < |center z.2-endpoint uniform (baseline next flag fuel z.1) k| :=
      lt_of_not_ge (fun hdist => hgeom (Or.inl ⟨k,hk,hdist⟩))
    constructor <;> linarith
  have hc : center z.2 ∈ Ioc (0:ℝ) 1 := representative_range _
  obtain ⟨hc0,hc1,_,_⟩ := coordinatesSafe_nonwrapping uniform (baseline next flag fuel z.1)
    h (center z.2) (center z.2) hc hc hsafe
  have hterminal : Terminal (baseline next flag fuel z.1).stop := by
    intro q hq
    exact hcap ⟨q,hq⟩
  have hmiss : ∀ q ∈ determiningRequests (baseline next flag fuel z.1),
      q.agent ∈ selected two z.2.1 →
        (q.left:Circle) ∉ closedBall (center z.2:Circle) (w/2) ∧
        (determiningRight uniform q:Circle) ∉ closedBall (center z.2:Circle) (w/2) := by
    intro q hq hi
    have hreq : determiningRequest uniform q ∈ baselineRequests uniform (baseline next flag fuel z.1) :=
      List.mem_map.mpr ⟨q,hq,rfl⟩
    have hnotreq : z.2 ∉ MoatTranscript.detects two w (determiningRequest uniform q) :=
      fun hd => hdetect ((MoatTranscript.mem_detection_iff _ _ _ _).mpr ⟨_,hreq,hd⟩)
    have hends : z.2.2 ∉ MoatDetection.endpointEvent w q.left ∪
        MoatDetection.endpointEvent w (determiningRight uniform q) := by
      intro hends
      exact hnotreq ((MoatTranscript.detects_iff _ _ _ _).mpr ⟨hi,hends⟩)
    constructor
    · intro he
      apply hends
      left
      simpa only [center, representative_coe, MoatDetection.endpointEvent,
        mem_closedBall, dist_comm] using he
    · intro he
      apply hends
      right
      simpa only [center, representative_coe, MoatDetection.endpointEvent,
        mem_closedBall, dist_comm] using he
  have hreplay := MoatReplay.actual_run_replay next flag chores z.1 fuel []
    (selected two z.2.1) w h (center z.2) hw hh.le hhw (by linarith) (by linarith) hmiss
  have hreplay' : run next (oracle two flag chores w h z.2) z.1 fuel [] = baseline next flag fuel z.1 := by
    simpa only [MoatExperiment.oracle, toFamily, center, representative_coe, baseline, NonnegativeMainEvents.baseline] using hreplay
  change z.1 ∉ eventualSuccess next (oracle two flag chores w h z.2) []
    {A | Fair chores (rows two chores w h z.2) A}
  apply terminal_failure_no_eventual_success next (oracle two flag chores w h z.2) z.1 []
    {A | Fair chores (rows two chores w h z.2) A} fuel
  · simpa only [hreplay'] using hterminal
  · rw [hreplay']
    rintro ⟨A,hreturned,hfair⟩
    change Fair chores (rows two chores w h z.2) A at hfair
    rcases hretain with hold | ⟨B,hB,huniform,hfav⟩
    · have hwrong : ¬ UniformEF A := fun hA => hold ⟨A,hreturned,hA⟩
      have hgap : h < uniformGap A := by
        by_contra hlarge
        apply hgeom
        right
        refine ⟨⟨A,hreturned,hwrong⟩,?_⟩
        change outputGap (baseline next flag fuel z.1) ≤ h
        simpa only [outputGap, returnedValue, hreturned] using le_of_not_gt hlarge
      exact MoatFamily.old_failure chores hw hw1 hh.le hhw (toFamily two z.2) A hgap hfair
    · have hAB : A=B := Stop.returned.inj (hreturned.symm.trans hB)
      subst B
      have houtput := coordinatesSafe_output uniform (baseline next flag fuel z.1)
        h (center z.2) (center z.2) A hreturned hsafe
      have hnonowner : ∃ i ∈ selected two z.2.1, i ≠ ownerAt A (center z.2) := by
        cases two
        · exact ⟨z.2.1,by simp [selected],hfav.resolve_left Bool.false_ne_true⟩
        · exact selected_has_nonowner hn z.2.1 _
      have hbad := MoatReplay.decoded_failure chores A (selected two z.2.1) w h (center z.2)
        hw hh hwidth hc0 hc1 houtput.1 houtput.2.1 huniform hnonowner
      apply hbad
      simpa only [rows, toFamily, center, representative_coe] using hfair

end EnvyFreeResearch.Full.MoatRetention
