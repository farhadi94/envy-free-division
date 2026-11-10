import EnvyFreeResearch.Full.MoatFamily
import EnvyFreeResearch.Full.MoatReplayGeometry

/-! Literal adaptive replay and successful-output failure for the concrete
moat family, for any fixed finite set of changed observers. -/
noncomputable section
namespace EnvyFreeResearch.Full.MoatReplay
open Set MeasureTheory Metric IntervalOracle OracleProtocol IntervalAllocation MixedDensity
open NonnegativeOracle NonnegativeProfile NonnegativeReplay NonnegativeAllocation
open NonnegativeRetainedFailure NonnegativeRandomOutput NonnegativeFailure
open MoatFamily MoatDensity MoatPhysical MoatReplayGeometry
open scoped Classical
abbrev Circle := NonnegativeCircle.Circle

/-- Nondetection preserves every determining integral of a changed row. -/
theorem determined {n : ℕ} (chores : Bool) (w h c : ℝ)
    (hw : 0 < w) (hh : 0 ≤ h) (hhw : h ≤ w) (hc0 : 0 < c) (hc1 : c < 1)
    (selected : Finset (Fin n)) (q : Query (Fin n))
    (hmiss : q.agent ∈ selected →
      (q.left:Circle) ∉ closedBall (c:Circle) (w/2) ∧
      (determiningRight uniform q:Circle) ∉ closedBall (c:Circle) (w/2)) :
    Determined uniform (profile chores w h (selected,(c:Circle))) q := by
  intro hs
  have hb := determiningRight_bounds (uniform (Agent := Fin n)) q hs
  have haunit : q.left ∈ Icc (0:ℝ) 1 := ⟨hs.1, hs.2.1.trans hs.2.2⟩
  have hbunit : determiningRight uniform q ∈ Icc (0:ℝ) 1 := ⟨hs.1.trans hb.1, hb.2.trans hs.2.2⟩
  by_cases hi : q.agent ∈ selected
  · change (rows chores w h (selected,(c:Circle)) q.agent).cumulative (determiningRight uniform q)-
      (rows chores w h (selected,(c:Circle)) q.agent).cumulative q.left =
      uniformRow.cumulative (determiningRight uniform q)-uniformRow.cumulative q.left
    simp only [rows, ite_eq_left hi]
    rw [uniform_cumulative _ hbunit, uniform_cumulative _ haunit]
    exact interval_preserved chores w h c q.left (determiningRight uniform q) hw hh hhw hc0 hc1
      hs.1 hb.1 (hb.2.trans hs.2.2) (hmiss hi).1 (hmiss hi).2
  · simp only [profile, rows, uniform, toProfile, ite_eq_right hi]

/-- The full actual Option-oracle execution agrees, including an illegal
terminal request, failure flag, arbitrary output, or query-free divergence. -/
theorem actual_run_replay {Tape Output : Type*} {n : ℕ}
    (next : Protocol Tape (Query (Fin n)) Reply Output) (flag chores : Bool)
    (tape : Tape) (fuel : ℕ) (history : History (Query (Fin n)) Reply)
    (selected : Finset (Fin n)) (w h c : ℝ) (hw : 0 < w) (hh : 0 ≤ h) (hhw : h ≤ w)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hmiss : ∀ q ∈ determiningRequests (run next (flaggedOracle flag uniform) tape fuel history),
      q.agent ∈ selected → (q.left:Circle) ∉ closedBall (c:Circle) (w/2) ∧
        (determiningRight uniform q:Circle) ∉ closedBall (c:Circle) (w/2)) :
    run next (oracle flag chores w h (selected,(c:Circle))) tape fuel history =
      run next (flaggedOracle flag uniform) tape fuel history := by
  apply flagged_run_replay next flag uniform (profile chores w h (selected,(c:Circle)))
    (positive chores hw hh hhw (selected,(c:Circle)))
  intro q hq
  apply determined chores w h c hw hh hhw hc0 hc1 selected q
  apply hmiss q
  rcases hq with ⟨r,hr⟩ | hill
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨(q,r),hr,rfl⟩
  · simp [determiningRequests,hill]

/-- A successful uniform return must give the bump to every changed row. -/
theorem decoded_failure {n : ℕ} (chores : Bool) (A : Allocation (Fin n))
    (selected : Finset (Fin n)) (w h c : ℝ) (hw : 0 < w) (hh : 0 < h)
    (hwidth : 1/(n:ℝ) < w)
    (hc0 : 0 < c-h/2) (hc1 : c+h/2 < 1)
    (hleft : ∀ k, h/2 < |c-A.left k|) (hright : ∀ k, h/2 < |c-A.right k|)
    (huniform : UniformEF A) (hmiss : ∃ i ∈ selected, i ≠ ownerAt A c) :
    ¬ Fair chores (rows chores w h (selected,(c:Circle))) A := by
  obtain ⟨i,hi,hnot⟩ := hmiss
  have hequal : volume.real (A.share i)=volume.real (A.share (ownerAt A c)) :=
    le_antisymm (huniform _ _) (huniform _ _)
  have hlength : volume.real (A.share (ownerAt A c))=1/(n:ℝ) := by
    simpa only [Fintype.card_fin] using equal_lengths_of_uniformEF A huniform (ownerAt A c)
  have henvy := MoatDecoder.strict_envy chores A w h c hw hh hc0 hc1 hleft hright i hnot hequal
    (by rw [hlength]; exact hwidth)
  intro hfair
  cases chores
  · have hcompare := hfair i (ownerAt A c)
    simp only [rows, ite_eq_left hi] at hcompare
    exact (not_lt_of_ge hcompare) henvy
  · have hcompare := hfair i (ownerAt A c)
    simp only [rows, ite_eq_left hi] at hcompare
    exact (not_lt_of_ge hcompare) henvy

end EnvyFreeResearch.Full.MoatReplay
