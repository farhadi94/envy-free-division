import EnvyFreeResearch.Full.UpperIdealPayments

/-! Borel measurability of the actual finite rejection search and payment
targets, including every optimization tie. -/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace EnvyFreeResearch.Full.UpperIdealMeasurable

open UpperRepresentatives UpperAssignment UpperAssignmentIsolation UpperPotentials
  UpperIdealPayments ProtocolMeasurable

variable {Agent X : Type*} [Fintype Agent] [DecidableEq Agent] [MeasurableSpace X]

theorem assigned_entry_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (i j : Agent) :
    Measurable (fun x => V x i (maximize (V x) j)) := by
  let : MeasurableSpace Agent := ⊤
  let : MeasurableSingletonClass Agent := ⟨fun _ => trivial⟩
  have hlabel : Measurable (fun x => maximize (V x) j) :=
    (measurable_of_countable (fun pi : Equiv.Perm Agent => pi j)).comp (maximize_measurable V hV)
  exact (score_eval_measurable (fun x c => V x i c) (hV i)).comp (measurable_id.prodMk hlabel)

omit [DecidableEq Agent] in
theorem rowMaximum_measurable (V : X → Agent → Agent → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (i : Agent) :
    Measurable (fun x => rowMaximum (V x) i) := by
  let : MeasurableSpace Agent := ⊤
  let : MeasurableSingletonClass Agent := ⟨fun _ => trivial⟩
  have harg := argmax_measurable (Finset.univ.toList : List Agent) (fun x c => V x i c) (hV i)
  have hchoice : Measurable (fun x => rowChoice (V x) i) :=
    measurable_option_cases (present := fun _ c => c) (absent := fun _ => i)
      harg measurable_snd measurable_const
  exact (score_eval_measurable (fun x c => V x i c) (hV i)).comp (measurable_id.prodMk hchoice)

theorem edge_measurable (V A : X → Agent → Agent → ℝ) (lam : X → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j))
    (hA : ∀ i j, Measurable (fun x => A x i j)) (hlam : Measurable lam) (i j : Agent) :
    Measurable (fun x => edge (V x) (A x) (lam x) i j) :=
  ((assigned_entry_measurable V hV i j).sub (assigned_entry_measurable V hV i i)).add
    ((measurable_const.mul hlam).mul (hA i j))

omit [Fintype Agent] [DecidableEq Agent] in
theorem walkWeight_measurable (w : X → Agent → Agent → ℝ)
    (hw : ∀ i j, Measurable (fun x => w x i j)) (i : Agent) (rest : List Agent) :
    Measurable (fun x => walkWeight (w x) i rest) := by
  induction rest generalizing i with
  | nil => exact measurable_const
  | cons j rest ih => exact (hw i j).add (ih j)

/-- Path selection uses the finite discrete path index only; every cached
real coordinate retains its ordinary Borel measurable space. -/
theorem potential_measurable (w : X → Agent → Agent → ℝ)
    (hw : ∀ i j, Measurable (fun x => w x i j)) (i : Agent) :
    Measurable (fun x => potential (w x) i) := by
  let : MeasurableSpace (PathFrom i) := ⊤
  let : MeasurableSingletonClass (PathFrom i) := ⟨fun _ => trivial⟩
  have hscore (p : PathFrom i) : Measurable (fun x => walkWeight (w x) i p.val.val) :=
    walkWeight_measurable w hw i p.val.val
  have harg := argmax_measurable (pathList i) (fun x p => walkWeight (w x) i p.val.val) hscore
  have hbest : Measurable (fun x => bestPath (w x) i) :=
    measurable_option_cases (present := fun _ p => p) (absent := fun _ => emptyPath i)
      harg measurable_snd measurable_const
  exact (score_eval_measurable (fun x p => walkWeight (w x) i p.val.val) hscore).comp
    (measurable_id.prodMk hbest)

theorem allowance_measurable (V : X → Agent → Agent → ℝ) (delta : X → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j)) (hdelta : Measurable delta) :
    Measurable (fun x => allowance (V x) (delta x)) := by
  exact (Finset.measurable_sum _ (fun i _ =>
    (rowMaximum_measurable V hV i).sub (assigned_entry_measurable V hV i i))).add
      (measurable_const.mul hdelta)

theorem cakeTargets_measurable (V A : X → Agent → Agent → ℝ) (lam : X → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j))
    (hA : ∀ i j, Measurable (fun x => A x i j)) (hlam : Measurable lam) (i : Agent) :
    Measurable (fun x => cakeTargets (V x) (A x) (lam x) i) :=
  potential_measurable _ (edge_measurable V A lam hV hA hlam) i

theorem choreTargets_measurable (V A : X → Agent → Agent → ℝ) (lam eta : X → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j))
    (hA : ∀ i j, Measurable (fun x => A x i j)) (hlam : Measurable lam) (heta : Measurable eta)
    (i : Agent) : Measurable (fun x => choreTargets (V x) (A x) (lam x) (eta x) i) :=
  (allowance_measurable (fun x r c => -V x r c) (fun x => 2 * lam x * eta x)
    (fun r c => (hV r c).neg) ((measurable_const.mul hlam).mul heta)).sub
      (cakeTargets_measurable (fun x r c => -V x r c) A lam (fun r c => (hV r c).neg) hA hlam i)

theorem find_first_positive_measurable (candidates : List (Equiv.Perm Agent))
    (scores : X → Equiv.Perm Agent → ℝ) (hscores : ∀ p, Measurable (fun x => scores x p)) :
    Measurable (fun x => candidates.find? (fun p => decide (0 < scores x p))) := by
  induction candidates with
  | nil => exact measurable_const
  | cons p rest ih =>
    have htest : MeasurableSet {x | (0 : ℝ) < scores x p} :=
      measurableSet_lt measurable_const (hscores p)
    have h : Measurable (fun x => if 0 < scores x p then some p else
        rest.find? (fun q => decide (0 < scores x q))) := measurable_const.ite htest ih
    convert h using 1
    funext x
    by_cases hp : 0 < scores x p <;> simp [List.find?_cons, hp]

theorem findPositive_measurable (V A : X → Agent → Agent → ℝ) (lam : X → ℝ)
    (hV : ∀ i j, Measurable (fun x => V x i j))
    (hA : ∀ i j, Measurable (fun x => A x i j)) (hlam : Measurable lam) :
    Measurable (fun x => findPositive (V x) (A x) (lam x)) := by
  apply find_first_positive_measurable
  intro transfer
  exact Finset.measurable_sum _ (fun i _ => edge_measurable V A lam hV hA hlam i (transfer i))

end EnvyFreeResearch.Full.UpperIdealMeasurable
