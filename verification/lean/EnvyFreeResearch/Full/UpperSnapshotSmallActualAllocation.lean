import EnvyFreeResearch.Full.UpperSnapshotSmallProgram
import EnvyFreeResearch.Full.UpperSnapshotSmallSecondRestored

/-! Pure output assembly from the two recorded circle outputs. The assembly
uses no response policy and makes no oracle call. -/
noncomputable section
open MeasureTheory Set
open scoped Classical unitInterval
namespace EnvyFreeResearch.Full.UpperSnapshotSmall
open UpperRecordedDomain UpperCorrectionExecution UpperCircularStage UpperStageMeasurable
  UpperDomainDifference UpperGridRecords
variable {n m J : ℕ}

def firstAllocationFrom (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (start : Circle)
    (rawFirst : (Fin 2 → ℝ) × State n) (rawSecond : (Fin J → ℝ) × State n) : State n :=
  ⟨((restoredFrom origin rawFirst).cells.filter (flagFrom origin cutter cuts selected t start rawFirst)),
    rawSecond.2.history⟩

def secondAllocationFrom (hJ : 0 < J) (t : ℝ) (start : Circle)
    (rawSecond : (Fin J → ℝ) × State n) (j : Fin J) : State n :=
  selectState rawSecond.2 (fun c =>
    prefixAtom (remainderTargets J t j.succ) start (rawSecond.1 ⟨0,hJ⟩)
      (boundary hJ rawSecond.1 j.succ) c &&
    !prefixAtom (remainderTargets J t j.castSucc) start (rawSecond.1 ⟨0,hJ⟩)
      (boundary hJ rawSecond.1 j.castSucc) c)

def allocationFrom (hJ : 0 < J) (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle)
    (rawFirst : (Fin 2 → ℝ) × State n) (rawSecond : (Fin J → ℝ) × State n) :
    (Fin J → State n) × State n × State n :=
  (fun j => if hj : j.val = 0 then firstAllocationFrom origin cutter cuts selected t first rawFirst rawSecond
    else secondAllocationFrom hJ t second rawSecond ⟨j.val-1, by omega⟩,
   secondAllocationFrom hJ t second rawSecond ⟨J-1, by omega⟩,
   ⟨refineEndpoints (restoredFrom origin rawFirst).cells (List.ofFn rawSecond.1),rawSecond.2.history⟩)

def actualAllocation (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) :=
  allocationFrom hJ origin cutter cuts selected t first second
    (firstRun policy origin cutter cuts selected t first)
    (secondRun (J:=J) policy origin cutter cuts selected t first second)

theorem firstAllocationFrom_actual (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) :
    firstAllocationFrom origin cutter cuts selected t first
      (firstRun policy origin cutter cuts selected t first)
      (secondRun (J:=J) policy origin cutter cuts selected t first second) =
      ⟨(firstEndowment policy origin cutter cuts selected t first).cells,
       (secondRun (J:=J) policy origin cutter cuts selected t first second).2.history⟩ := rfl

theorem secondAllocationFrom_actual (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle) (j : Fin J) :
    secondAllocationFrom hJ t second (secondRun (J:=J) policy origin cutter cuts selected t first second) j =
      secondPiece hJ policy origin cutter cuts selected t first second j := rfl

theorem allocationFrom_history (hJ : 0 < J) (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (first second : Circle)
    (rawFirst : (Fin 2 → ℝ) × State n) (rawSecond : (Fin J → ℝ) × State n) :
    (∀ j, ((allocationFrom hJ origin cutter cuts selected t first second rawFirst rawSecond).1 j).history = rawSecond.2.history) ∧
    (allocationFrom hJ origin cutter cuts selected t first second rawFirst rawSecond).2.1.history = rawSecond.2.history ∧
    (allocationFrom hJ origin cutter cuts selected t first second rawFirst rawSecond).2.2.history = rawSecond.2.history := by
  refine ⟨?_,rfl,rfl⟩
  intro j
  simp only [allocationFrom]
  split_ifs <;> rfl

end EnvyFreeResearch.Full.UpperSnapshotSmall
