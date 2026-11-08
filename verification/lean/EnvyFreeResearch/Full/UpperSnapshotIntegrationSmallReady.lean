import EnvyFreeResearch.Full.UpperSnapshotIntegrationSmallReadyBuffer

/-! A real sampled small-disagreement allocation supplies the complete
checked-Repair contract. No Near, equal-cutter, buffer, or physical gap
certificate is assumed: each follows from the supported interpolation event
and the selected maximal row witness. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotProtocol
open UpperCircular UpperPhysical UpperRecordedDomain UpperCorrectionExecution UpperGridRecords
  UpperDomainDifference UpperCircularStage UpperLogicalPreparation UpperLogicalCells
  UpperAggregateInterpolation UpperGridInterpolation UpperGridSensitivity UpperSnapshotSmall
  UpperStageMeasurable UpperRepairPreparationChecks UpperRepairParameters
variable {n m k : ℕ} {Generated : Type*} [Nonempty (Fin k)]

theorem actual_small_candidate_probability
    (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (policy : Policy n) (hpolicy : Admissible (Chores.measureProfile μ) policy)
    (hmeas : MeasurablePolicy policy) (hk : 2 ≤ k) (chores : Bool)
    (active : Fin k → Fin n) (hinj : Function.Injective active)
    (origin : State n) (hgood : WellFormed μ origin)
    (hpositive : ∀ i, 0 < (μ (active i)).real (domain origin.cells))
    (cutter foreign : Fin k) (cuts : Fin (m+2) → ℝ) (hzero : cuts 0=0)
    (hone : cuts (Fin.last (m+1))=1) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) origin.cells)
    (selected : Finset (Fin (m+1))) (D t : ℝ) (hD : 0<D)
    (hsmall : D < UpperRepair.nearError n/16)
    (htdef : t=(1-(8/UpperRepair.nearError n)*D)/(k:ℝ))
    (first second : UpperSnapshotSmall.Circle) (points : Generated → ℝ)
    (hfirst : ∀ j, ∃ e, points e=(firstRun policy origin (active cutter) cuts selected t first).1 j)
    (hsecond : ∀ j, ∃ e, points e=(secondRun (J:=k) policy origin (active cutter) cuts selected t first second).1 j)
    (eps : ℝ) (heps : eps ≤ 1/2) (hepsgap : eps ≤ 3/(64*(k:ℝ)))
    (htau4 : UpperRepair.nearError n ≤ 4)
    (hinterp : ¬ BadSupportedRecordedUnion (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts points eps)
    (hmax : ∀ i, distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter ≤ D)
    (hforeign : distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) foreign cutter = D)
    (hwitness : D/(8*(k:ℝ)) ≤ candidateContrast hk policy origin (active cutter) cuts selected t
      (signedEstimate (fun e => physicalRows (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts foreign e-
        physicalRows (fun i => μ (active i))
        (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts cutter e)
        (cell (domain origin.cells) cuts)) (first,second)) :
    let packet := actualAllocation (by omega : 0<k) policy origin (active cutter) cuts selected t first second
    31/64 < (UpperRepair.law n k).real
      {p | (execute policy hk chores active (margin n) packet.2.1 packet.1 p).2.2 = false} := by
  let tau := UpperRepair.nearError n
  have htau : 0 < tau := oldError_positive (scale_large n)
    (by exact_mod_cast logarithm_positive (scale_large n))
  have hkreal : (2:ℝ) ≤ k := by exact_mod_cast hk
  have htcheck := small_amount_checks tau D (k:ℝ) htau hD hsmall hkreal
  rw [← htdef] at htcheck
  obtain ⟨ht,_,ht1,hfit,_,hremain⟩ := htcheck
  let packet := actualAllocation (by omega : 0<k) policy origin (active cutter) cuts selected t first second
  have hw := actual_allocation_wellFormed μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
    cuts hzero hmono hsep selected t ht ht1 (by omega : 0<k) first second
  have hd (i : Fin k) : 0 ≤ distance (physicalRows (fun i => μ (active i))
      (fun i => (μ (active i)).real (domain origin.cells)) origin.cells cuts) i cutter :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbudgets (i : Fin k) := small_error_budgets tau D _ eps htau htau4 hD.le (hd i) (hmax i) heps
  have hready (i : Fin k) := actualAllocation_ready μ policy hpolicy active origin hgood hpositive cutter cuts
    hzero hone hmono hsep selected t ht ht1 hfit first second points hfirst hsecond eps tau htau.le hinterp
    (fun j => by rw [hremain]; exact (hbudgets j).1)
    (fun j => by rw [hremain]; exact (hbudgets j).2) (by omega : 0<k) i
  have hpositive' (i : Fin k) : 0 < (μ (active i)).real (domain packet.2.1.cells) := by
    rw [← total_correct μ _ hw.2.1]
    exact (hready i).2.1
  have hnear : Near chores μ active packet.2.1 packet.1 (UpperRepair.nearError n) := by
    intro i j
    have habs : ∀ a b, |(μ (active i)).real (domain (packet.1 a).cells)-
        (μ (active i)).real (domain (packet.1 b).cells)| ≤
        tau*(μ (active i)).real (domain packet.2.1.cells) := by
      intro a b
      rw [← total_correct μ _ (hw.1 a),← total_correct μ _ (hw.1 b),← total_correct μ _ hw.2.1]
      exact (hready i).2.2 a b
    cases chores
    · exact (le_abs_self _).trans (habs j i)
    · exact (le_abs_self _).trans (habs i j)
  have hpair := actual_shares_disjoint μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
    cuts hzero hmono hsep selected t ht ht1 (by omega : 0<k) hfit first second
  have hdis := actual_share_buffer_disjoint μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
    cuts hzero hmono hsep selected t ht ht1 (by omega : 0<k) hfit first second
  have hhistory (j : Fin k) : (packet.1 j).history ⊆ packet.2.1.history := by
    have hh := allocationFrom_history (by omega : 0<k) origin (active cutter) cuts selected t first second
      (firstRun policy origin (active cutter) cuts selected t first)
      (secondRun (J:=k) policy origin (active cutter) cuts selected t first second)
    change ((allocationFrom _ _ _ _ _ _ _ _ _ _).1 j).history ⊆ (allocationFrom _ _ _ _ _ _ _ _ _ _).2.1.history
    rw [hh.1 j,hh.2.1]
  have hupper := actual_small_buffer_upper μ policy hpolicy active origin hgood hpositive cutter cuts
    hzero hone hmono hsep selected t ht ht1 hfit first second points hfirst hsecond eps D (8/tau)
    heps hD.le hremain hinterp (by omega : 0<k) foreign (hmax foreign)
  have hgap := actualAllocation_gap_ready μ policy hpolicy active origin hgood hpositive cutter cuts
    hzero hone hmono hsep selected t ht ht1 hfit first second points hfirst hsecond eps hepsgap hinterp
    hk foreign (by simpa only [hforeign] using hwitness)
  rw [hforeign,← sub_div] at hgap
  have hforeign' := (le_div_iff₀ (hpositive foreign)).mp hgap
  have hequal : (μ (active cutter)).real (domain (packet.1 ⟨0,by omega⟩).cells)=
      (μ (active cutter)).real (domain (packet.1 ⟨1,by omega⟩).cells) := by
    rw [← total_correct μ _ (hw.1 ⟨0,by omega⟩),← total_correct μ _ (hw.1 ⟨1,by omega⟩),
      actual_allocation_cutter_mass μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
        cuts hzero hmono hsep selected t ht ht1 (by omega) hfit first second,
      actual_allocation_cutter_mass μ policy hpolicy origin hgood (active cutter) (hpositive cutter)
        cuts hzero hmono hsep selected t ht ht1 (by omega) hfit first second]
  have hp := small_candidate_repair_probability μ policy hpolicy hmeas hk chores active hinj
    packet.2.1 hw.2.1 hpositive' packet.1 hw.1 hnear hpair hdis hhistory foreign cutter
    ⟨0,by omega⟩ ⟨1,by omega⟩ _ (D/(32*(k:ℝ))) ((8/tau+2)*D) (hpositive foreign)
    (by positivity) (by positivity) hupper hforeign' hequal
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top _ _)
  intro p hp
  apply finish_accepted_mono (by omega) chores active _ _ _ _ _ _ hp
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective active hinj
  have hfitfine := small_endpoints_fit (by omega : 0<k) hkn
  have h8 : 8*k ≤ UpperRepair.fine n := by nlinarith
  exact small_margin_scale tau D (k:ℝ) (UpperRepair.fine n) htau htau4 hD (by positivity) (by exact_mod_cast h8)

end EnvyFreeResearch.Full.UpperSnapshotProtocol
