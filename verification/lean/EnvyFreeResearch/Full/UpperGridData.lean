import EnvyFreeResearch.Full.UpperLogicalPreparationGuard
import EnvyFreeResearch.Full.UpperRecordedGridProgram
import EnvyFreeResearch.Full.UpperOriginalCorrectionProbability

/-! Pure post-query grid computations. The complete returned coarse tuple,
fine tuple and recorded state determine every reserve/representative/guard
operation; these definitions do not call a response policy. -/

noncomputable section

open MeasureTheory
open scoped Classical unitInterval

namespace EnvyFreeResearch.Full.UpperGridData

open UpperRecordedDomain UpperCorrectionExecution UpperGridCells UpperCommonGrid UpperRecordedQuantiles
  UpperLogicalPreparation UpperCircularStage UpperStageMeasurable

abbrev Data (n coarse fine : ℕ) := (Fin coarse → ℝ) × (Fin fine → ℝ) × State n

variable {n coarse fine : ℕ} {Agent : Type*} [Fintype Agent]

def cuts (data : Data n coarse fine) : Fin (coarse + fine + 2) → ℝ :=
  grid (Fin.append data.1 data.2.1)

def coarseCuts (data : Data n coarse fine) : Fin (coarse + 2) → ℝ := grid data.1

def aligned (data : Data n coarse fine) : State n := align data.2.2

def table (active : Agent → Fin n) (origin : State n) (data : Data n coarse fine)
    (a : Agent) (e : Fin (coarse + fine + 1)) : ℝ :=
  cachedMass (aligned data) (cuts data) (active a) e / total origin (active a)

def parent (data : Data n coarse fine) : Fin (coarse + fine + 1) → Fin (coarse + 1) :=
  UpperGridParents.parent (coarseCuts data) (cuts data)

def reserve (data : Data n coarse fine) (theta : I) (labels : Fin (coarse + 1) → I) : State n :=
  retain (aligned data) (cuts data) (reserveCells (parent data) theta labels)

def representatives (active : Agent → Fin n) (origin : State n) (data : Data n coarse fine)
    (jobs : List (Agent × Agent)) :=
  UpperRepresentativeSupply.run (table active origin data) (parent data)
    (List.ofFn (fun i : Fin (coarse + fine + 1) => i)) jobs ∅

def selectedParents (active : Agent → Fin n) (origin : State n) (data : Data n coarse fine)
    (jobs : List (Agent × Agent)) : Finset (Fin (coarse + 1)) :=
  match representatives active origin data jobs with
  | none => ∅
  | some result => result.2

def guard (active : Agent → Fin n) (origin : State n) (data : Data n coarse fine)
    (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ) (labels : Fin (coarse + 1) → I) : Bool :=
  decide ((∀ a, (theta : ℝ) / 2 * total origin (active a) ≤ total (reserve data theta labels) (active a)) ∧
    ((reserveCells (parent data) theta labels).card : ℝ) ≤ cap ∧
    ∀ p ∈ selectedParents active origin data jobs, ¬labels p ≤ theta)

/-- The actual sampler and interpolation theorem use exactly the same
ordered endpoint tuple, not merely grids with the same set of points. -/
theorem cuts_eq_augmented (data : Data n coarse fine) :
    cuts data = UpperSortedGrid.sorted (UpperGridInterpolation.augmented data.1 data.2.1) := by
  unfold cuts grid raw UpperGridInterpolation.augmented
  rw [Fin.cons_snoc_eq_snoc_cons]
  rfl

section Execution

variable (policy : Policy n) (active : Agent → Fin n) (origin : State n) (q m : ℕ)
  (draw : Fin m → Agent × I)

theorem cuts_execute : cuts (UpperGridMerge.prepare policy active origin q m draw) =
    UpperGridMerge.cuts policy active origin q m draw := rfl

theorem coarseCuts_execute : coarseCuts (UpperGridMerge.prepare policy active origin q m draw) =
    UpperRecordedQuantiles.cuts policy active origin q := rfl

theorem aligned_execute : aligned (UpperGridMerge.prepare policy active origin q m draw) =
    UpperGridCache.aligned policy active origin q m draw := rfl

theorem table_execute : table active origin (UpperGridMerge.prepare policy active origin q m draw) =
    UpperGridCache.table policy active origin q m draw := rfl

theorem parent_execute : parent (UpperGridMerge.prepare policy active origin q m draw) =
    UpperRecordedParents.parent policy active origin q m draw := rfl

theorem reserve_execute (theta : I) (labels : Fin (count (Agent := Agent) q + 1) → I) :
    reserve (UpperGridMerge.prepare policy active origin q m draw) theta labels =
      reserveState policy active origin q m draw theta labels := rfl

variable [Nonempty Agent]

theorem representatives_execute (jobs : List (Agent × Agent)) :
    representatives active origin (UpperGridMerge.prepare policy active origin q m draw) jobs =
      representativeRun policy active origin q m draw jobs := rfl

theorem selectedParents_execute (jobs : List (Agent × Agent)) :
    selectedParents active origin (UpperGridMerge.prepare policy active origin q m draw) jobs =
      UpperLogicalPreparationGuard.selectedParents policy active origin q m draw jobs := by
  simp only [selectedParents, UpperLogicalPreparationGuard.selectedParents, representatives_execute]
  cases representativeRun policy active origin q m draw jobs <;> rfl

theorem guard_execute (jobs : List (Agent × Agent)) (theta : I) (cap : ℝ)
    (labels : Fin (count (Agent := Agent) q + 1) → I) :
    guard active origin (UpperGridMerge.prepare policy active origin q m draw) jobs theta cap labels =
      UpperLogicalPreparationGuard.guard policy active origin q m jobs theta cap draw labels := by
  simp only [guard, UpperLogicalPreparationGuard.guard, UpperLogicalPreparationGuard.Passes,
    selectedParents_execute, reserve_execute, parent_execute]
  exact decide_eq_decide.mpr Iff.rfl

end Execution

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem cuts_measurable (data : X → Data n coarse fine) (hdata : Measurable data) :
    Measurable (fun x => cuts (data x)) := by
  apply grid_measurable
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left, Function.comp_def] using (measurable_pi_apply j).comp (measurable_fst.comp hdata)
  · intro j
    simpa only [Fin.append_right, Function.comp_def] using (measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp hdata))

theorem coarseCuts_measurable (data : X → Data n coarse fine) (hdata : Measurable data) :
    Measurable (fun x => coarseCuts (data x)) :=
  grid_measurable (fun x => (data x).1) (fun j => (measurable_pi_apply j).comp (measurable_fst.comp hdata))

theorem aligned_measurable (data : X → Data n coarse fine) (hdata : Measurable data) :
    Measurable (fun x => aligned (data x)) := align_measurable.comp (measurable_snd.comp (measurable_snd.comp hdata))

theorem table_measurable (active : Agent → Fin n) (origin : X → State n) (data : X → Data n coarse fine)
    (horigin : Measurable origin) (hdata : Measurable data) (i : Agent) (e : Fin (coarse + fine + 1)) :
    Measurable (fun x => table active (origin x) (data x) i e) :=
  (cachedMass_measurable _ _ (aligned_measurable data hdata)
    (fun e => (measurable_pi_apply e).comp (cuts_measurable data hdata)) (active i) e).div
    (total_measurable origin (fun _ => active i) horigin measurable_const)

theorem parent_measurable (data : X → Data n coarse fine) (hdata : Measurable data)
    (e : Fin (coarse + fine + 1)) : Measurable (fun x => parent (data x) e) :=
  UpperGridParents.parent_measurable _ _
    (fun e => (measurable_pi_apply e).comp (coarseCuts_measurable data hdata))
    (fun e => (measurable_pi_apply e).comp (cuts_measurable data hdata)) e

theorem reserve_measurable (data : X → Data n coarse fine) (theta : I) (labels : X → Fin (coarse + 1) → I)
    (hdata : Measurable data) (hlabels : ∀ p, Measurable (fun x => labels x p)) :
    Measurable (fun x => reserve (data x) theta (labels x)) :=
  retain_measurable _ _ _ (aligned_measurable data hdata)
    (fun e => (measurable_pi_apply e).comp (cuts_measurable data hdata))
    (reserveCells_measurable (fun x => parent (data x)) theta labels (parent_measurable data hdata) hlabels)

theorem representatives_measurable (active : Agent → Fin n) (origin : X → State n)
    (data : X → Data n coarse fine) (jobs : List (Agent × Agent))
    (horigin : Measurable origin) (hdata : Measurable data) :
    Measurable (fun x => representatives active (origin x) (data x) jobs) :=
  table_run_measurable _ (parent_measurable data hdata) _ jobs _
    (table_measurable active origin data horigin hdata) _ measurable_const

end Measurability

end EnvyFreeResearch.Full.UpperGridData
