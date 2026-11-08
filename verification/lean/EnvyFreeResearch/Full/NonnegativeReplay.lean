import EnvyFreeResearch.Full.NonnegativeProfile
import EnvyFreeResearch.Full.NonnegativeEndpointLaw

namespace EnvyFreeResearch.Full.NonnegativeReplay

open Set MeasureTheory IntervalOracle OracleProtocol
open NonnegativeOracle NonnegativeProfile NonnegativeDetection NonnegativeGeometry
open NonnegativeEndpointLaw NonnegativeShift
open scoped Classical

abbrev Circle := NonnegativeCircle.Circle

/-- On the physical interval, circular arc membership agrees with ordinary
interval membership away from endpoints. This discharges the quotient-space
bridge between the sharp detection law and the actual Eval/Cut integrals. -/
theorem coe_mem_arc_iff (a b c : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hca : c ≠ a) :
    (c : Circle) ∈ arc a b ↔ c ∈ Ioc a b := by
  constructor
  · rintro ⟨t, ht, heq⟩
    have htc : t = c := by
      by_cases ht0 : t = 0
      · subst t
        have hz : (0 : ℝ) = c := (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (p := (1 : ℝ)) (a := (0 : ℝ)) (by norm_num)
          (show c ∈ Ico (0 : ℝ) (0 + 1) by exact ⟨hc0.le, by simpa using hc1⟩)).mp heq
        linarith
      · exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
          (p := (1 : ℝ)) (a := (0 : ℝ))
          (show t ∈ Ioc (0 : ℝ) (0 + 1) by
            constructor
            · exact lt_of_le_of_ne (ha.trans ht.1) (Ne.symm ht0)
            · simpa using ht.2.trans hb)
          (show c ∈ Ioc (0 : ℝ) (0 + 1) by exact ⟨hc0, by simpa using hc1.le⟩)).mp heq
    subst t
    exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hca), ht.2⟩
  · intro hc
    exact ⟨c, ⟨hc.1.le, hc.2⟩, rfl⟩

theorem mem_detection_iff {n : ℕ} (requests : List (Request n))
    (z : Fin n × (ℝ × Circle)) :
    z ∈ detection requests ↔ ∃ request ∈ requests, z ∈ detects request := by
  induction requests with
  | nil => simp [detection]
  | cons request requests ih => simp [detection, ih]

def EndpointSafe (h c d : ℝ) (endpoints : List ℝ) : Prop :=
  ∀ e ∈ endpoints, h / 2 < |c - e| ∧ h / 2 < |d - e|

noncomputable def determiningEndpoints {Agent Output : Type*}
    (P : Profile Agent) (execution : Execution (Query Agent) Reply Output) : List ℝ :=
  (determiningRequests execution).flatMap (fun q => [q.left, determiningRight P q])

theorem determiningEndpoints_contains {Agent Output : Type*}
    (P : Profile Agent) (execution : Execution (Query Agent) Reply Output)
    (q : Query Agent) (hq : q ∈ determiningRequests execution) :
    q.left ∈ determiningEndpoints P execution ∧
      determiningRight P q ∈ determiningEndpoints P execution := by
  constructor <;> apply List.mem_flatMap.mpr
  · exact ⟨q, hq, by simp⟩
  · exact ⟨q, hq, by simp⟩

theorem nonwrapping_of_safe_boundary (h c d : ℝ)
    (hc : c ∈ Ioc (0 : ℝ) 1) (hd : d ∈ Ioc (0 : ℝ) 1)
    {endpoints : List ℝ} (h0 : 0 ∈ endpoints) (h1 : 1 ∈ endpoints)
    (hsafe : EndpointSafe h c d endpoints) :
    0 < c - h / 2 ∧ c + h / 2 < 1 ∧
      0 < d - h / 2 ∧ d + h / 2 < 1 := by
  obtain ⟨hc0, hd0⟩ := hsafe 0 h0
  obtain ⟨hc1, hd1⟩ := hsafe 1 h1
  rw [sub_zero, abs_of_pos hc.1] at hc0
  rw [sub_zero, abs_of_pos hd.1] at hd0
  rw [abs_of_nonpos (sub_nonpos.mpr hc.2)] at hc1
  rw [abs_of_nonpos (sub_nonpos.mpr hd.2)] at hd1
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Full concrete adaptive replay: a single fixed baseline execution is
preserved when the actual random perturbation misses its determining arcs
and finite endpoints. Counted unavailable replies and terminal illegal
requests are handled by the same theorem. -/
theorem actual_run_replay {Tape Output : Type*} {n : ℕ}
    (next : Protocol Tape (Query (Fin n)) Reply Output) (flag : Bool)
    (tape : Tape) (fuel : ℕ) (history : History (Query (Fin n)) Reply)
    (observer : Fin n) (z : ℝ × Circle) (h : ℝ) (hh : 0 ≤ h)
    (hc0 : 0 < realFirst z - h / 2) (hc1 : realFirst z + h / 2 < 1)
    (hd0 : 0 < realSecond z - h / 2) (hd1 : realSecond z + h / 2 < 1)
    (hsafe : EndpointSafe h (realFirst z) (realSecond z)
      (determiningEndpoints uniform (run next (flaggedOracle flag uniform) tape fuel history)))
    (hmiss : (observer, z) ∉ detection
      (baselineRequests uniform (run next (flaggedOracle flag uniform) tape fuel history))) :
    run next (flaggedOracle flag (perturbed observer h (first z) (second z))) tape fuel history =
      run next (flaggedOracle flag uniform) tape fuel history := by
  have hc : 0 < realFirst z ∧ realFirst z < 1 := by constructor <;> linarith
  have hd : 0 < realSecond z ∧ realSecond z < 1 := by constructor <;> linarith
  have hcoeC : (realFirst z : Circle) = first z := representative_coe _
  have hcoeD : (realSecond z : Circle) = second z := representative_coe _
  rw [← hcoeC, ← hcoeD]
  apply flagged_run_replay next flag uniform
    (perturbed observer h (realFirst z : Circle) (realSecond z : Circle))
    (perturbed_strictlyPositive _ _ _ _)
  intro q hq
  have hqmem : q ∈ determiningRequests
      (run next (flaggedOracle flag uniform) tape fuel history) := by
    rcases hq with ⟨r, hr⟩ | hill
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨(q, r), hr, rfl⟩
    · simp [determiningRequests, hill]
  have hends := determiningEndpoints_contains uniform
    (run next (flaggedOracle flag uniform) tape fuel history) q hqmem
  have hleft := hsafe _ hends.1
  have hright := hsafe _ hends.2
  intro hs
  apply determined_by_nondetection observer h (realFirst z) (realSecond z) hh
    hc0 hc1 hd0 hd1 q (fun _ => ⟨hleft.1, hright.1, hleft.2, hright.2⟩) _ hs
  intro hi
  have hbound := determiningRight_bounds (uniform (Agent := Fin n)) q hs
  have hrequest : determiningRequest uniform q ∈
      baselineRequests uniform (run next (flaggedOracle flag uniform) tape fuel history) :=
    List.mem_map.mpr ⟨q, hqmem, rfl⟩
  have hnot : (observer, z) ∉ detects (determiningRequest uniform q) := by
    intro hdetect
    exact hmiss ((mem_detection_iff _ _).mpr ⟨_, hrequest, hdetect⟩)
  have hequiv : first z ∈ arc q.left (determiningRight uniform q) ↔
      second z ∈ arc q.left (determiningRight uniform q) := by
    by_contra hn
    apply hnot
    exact ⟨by simpa [determiningRequest] using hi.symm, fun heq => hn (Iff.of_eq heq)⟩
  rw [← hcoeC, ← hcoeD,
    coe_mem_arc_iff _ _ _ hs.1 (hbound.2.trans hs.2.2) hc.1 hc.2
      (by intro he; simp [he] at hleft; linarith [hleft.1]),
    coe_mem_arc_iff _ _ _ hs.1 (hbound.2.trans hs.2.2) hd.1 hd.2
      (by intro he; simp [he] at hleft; linarith [hleft.2])] at hequiv
  exact hequiv

end EnvyFreeResearch.Full.NonnegativeReplay

#print axioms EnvyFreeResearch.Full.NonnegativeReplay.actual_run_replay
