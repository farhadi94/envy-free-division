import EnvyFreeResearch.Full.UpperSnapshotRepetitionSmallProgram
import EnvyFreeResearch.Full.UpperSnapshotSmallActualScore
import EnvyFreeResearch.Full.UpperSnapshotSmallChance

/-! A concrete deterministic acceptance test using only the immutable
interpolation data and the two returned endpoint tables. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
open UpperSnapshotSmall UpperRecordedDomain UpperCorrectionExecution UpperCircularStage
  UpperDomainDifference UpperGridRecords UpperLogicalCells
variable {n m J : ℕ}

def firstFrom (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (selected : Finset (Fin (m+1))) (t : ℝ) (start : Circle)
    (raw : (Fin 2 → ℝ) × State n) : State n :=
  selectState (restoredFrom origin raw) (flagFrom origin cutter cuts selected t start raw)

def secondFrom (hJ : 0 < J) (t : ℝ) (start : Circle)
    (raw : (Fin J → ℝ) × State n) (j : Fin J) : State n :=
  selectState raw.2 (fun c =>
    prefixAtom (remainderTargets J t j.succ) start (raw.1 ⟨0,hJ⟩) (boundary hJ raw.1 j.succ) c &&
      !prefixAtom (remainderTargets J t j.castSucc) start (raw.1 ⟨0,hJ⟩) (boundary hJ raw.1 j.castSucc) c)

def interpolationCheck (hJ : 2 ≤ J) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (score : Fin (m+1) → ℝ) (U : Set ℝ) (t : ℝ)
    (origin : State n) (z : Circle × Circle)
    (first : (Fin 2 → ℝ) × State n) (second : (Fin J → ℝ) × State n) : Bool :=
  decide ((∑ e, |score e|)/(8*(J:ℝ)) ≤
    interpolatedTotal score (cell U cuts)
      (firstFrom origin cutter cuts (positiveIndices score) t z.1 first).cells -
    interpolatedTotal score (cell U cuts)
      (secondFrom (by omega) t z.2 second ⟨0,by omega⟩).cells)

theorem firstFrom_actual (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (start : Circle) :
    firstFrom origin cutter cuts selected t start (firstRun policy origin cutter cuts selected t start)=
      firstEndowment policy origin cutter cuts selected t start := rfl

theorem secondFrom_actual (hJ : 0 < J) (policy : Policy n) (origin : State n) (cutter : Fin n)
    (cuts : Fin (m+2) → ℝ) (selected : Finset (Fin (m+1))) (t : ℝ) (z : Circle × Circle) (j : Fin J) :
    secondFrom hJ t z.2 (secondRun (J:=J) policy origin cutter cuts selected t z.1 z.2) j =
      secondPiece hJ policy origin cutter cuts selected t z.1 z.2 j := rfl

theorem interpolationCheck_actual (hJ : 2 ≤ J) (policy : Policy n)
    (origin : State n) (cutter : Fin n) (cuts : Fin (m+2) → ℝ)
    (score : Fin (m+1) → ℝ) (U : Set ℝ) (t : ℝ) (z : Circle × Circle)
    (hf : DisjointComponents (firstEndowment policy origin cutter cuts (positiveIndices score) t z.1).cells)
    (hg : DisjointComponents (secondPiece (J:=J) (by omega) policy origin cutter cuts
      (positiveIndices score) t z.1 z.2 ⟨0,by omega⟩).cells) :
    interpolationCheck hJ cutter cuts score U t origin z
      (firstRun policy origin cutter cuts (positiveIndices score) t z.1)
      (secondRun (J:=J) policy origin cutter cuts (positiveIndices score) t z.1 z.2) =
    decide ((∑ e, |score e|)/(8*(J:ℝ)) ≤
      candidateContrast hJ policy origin cutter cuts (positiveIndices score) t
        (signedEstimate score (cell U cuts)) z) := by
  unfold interpolationCheck
  rw [firstFrom_actual,secondFrom_actual,interpolatedTotal_correct _ _ _ hf,
    interpolatedTotal_correct _ _ _ hg]
  rfl

end EnvyFreeResearch.Full.UpperSnapshotRepetition
