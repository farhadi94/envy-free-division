import EnvyFreeResearch.Full.RefinedUpperStabilityParents

/-! The actual finite endpoint procedure used by the stability expectation. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open MeasureTheory Set UpperRepresentativeSupply UpperRepresentatives
open scoped Classical

variable {X : Type*} [MeasurableSpace X] {a M : ℕ}

lemma firstIntervalParent_measurable (coarse : Fin (a+2) → ℝ) (l r : X → ℝ)
    (hl : Measurable l) (hr : Measurable r) (js : List (Fin (a+1))) :
    Measurable (fun x => firstIntervalParent coarse (l x,r x) js) := by
  induction js with
  | nil => exact measurable_const
  | cons j js ih =>
    exact measurable_const.ite
      ((measurableSet_le measurable_const hl).inter (measurableSet_le hr measurable_const)) ih

lemma intervalParent_measurable (coarse : Fin (a+2) → ℝ) (l r : X → ℝ)
    (hl : Measurable l) (hr : Measurable r) :
    Measurable (fun x => intervalParent coarse (l x,r x)) :=
  firstIntervalParent_measurable coarse l r hl hr _

lemma optionGetD_measurable {A : Type*} [MeasurableSpace A] (f : X → Option A)
    (hf : Measurable f) (fallback : A) : Measurable (fun x => (f x).getD fallback) := by
  have h := ProtocolMeasurable.measurable_option_cases
    (present := fun (_ : X) a => a) (absent := fun _ : X => fallback)
    hf measurable_snd measurable_const
  convert h using 1
  funext x
  cases f x <;> rfl

variable {Row : Type*}

def pointValues (F : Row → ℝ → ℝ) (points : Fin (M+2) → ℝ) (r : Row) (c : Fin (M+1)) : ℝ :=
  F r (points c.succ)-F r (points c.castSucc)

def pointParents (coarse : Fin (a+2) → ℝ) (points : Fin (M+2) → ℝ) : Fin (M+1) → Fin (a+1) :=
  fun c => intervalParent coarse (intervalLabel points c)

def pointRun (F : Row → ℝ → ℝ) (coarse : Fin (a+2) → ℝ)
    (jobs : List (Row × Row)) (points : Fin (M+2) → ℝ) :
    Option (List (Fin (M+1) × Fin (M+1)) × Finset (Fin (a+1))) :=
  run (pointValues F points) (pointParents coarse points) (List.finRange (M+1)) jobs ∅

def pointResult (F : Row → ℝ → ℝ) (coarse : Fin (a+2) → ℝ)
    (jobs : List (Row × Row)) (points : Fin (M+2) → ℝ) :=
  (pointRun F coarse jobs points).getD ([],∅)

def finalPair (F : Row → ℝ → ℝ) (coarse : Fin (a+2) → ℝ)
    (jobs : List (Row × Row)) (points : Fin (M+2) → ℝ) (job : Row × Row) : Fin (M+1) × Fin (M+1) :=
  (select (pointValues F points job.1) (pointValues F points job.2)
    (available (pointParents coarse points) (pointResult F coarse jobs points).2
      (List.finRange (M+1)))).getD (0,0)

def protectedPairs (F : Row → ℝ → ℝ) (coarse : Fin (a+2) → ℝ)
    (jobs finalJobs : List (Row × Row)) (points : Fin (M+2) → ℝ) : List (Fin (M+1) × Fin (M+1)) :=
  (pointResult F coarse jobs points).1 ++ finalJobs.map (finalPair F coarse jobs points)

/-- Four endpoint slots per peeling job and per final row-pair witness.
The procedure remains total on invalid inputs through deterministic padding. -/
def endpointProcedure (F : Row → ℝ → ℝ) (coarse : Fin (a+2) → ℝ)
    (jobs finalJobs : List (Row × Row)) (points : Fin (M+2) → ℝ)
    (k : Fin (4*(jobs.length+finalJobs.length))) : ℝ :=
  let pair := (protectedPairs F coarse jobs finalJobs points).getD (k.val/4) (0,0)
  let cell := if k.val%4 < 2 then pair.1 else pair.2
  if k.val%2 = 0 then points cell.castSucc else points cell.succ

lemma pointValues_measurable (F : Row → ℝ → ℝ) (hF : ∀ r, Measurable (F r)) (r : Row) (c : Fin (M+1)) :
    Measurable (fun p : Fin (M+2) → ℝ => pointValues F p r c) :=
  ((hF r).comp (measurable_pi_apply c.succ)).sub ((hF r).comp (measurable_pi_apply c.castSucc))

lemma pointParents_measurable (coarse : Fin (a+2) → ℝ) (c : Fin (M+1)) :
    Measurable (fun p : Fin (M+2) → ℝ => pointParents coarse p c) :=
  intervalParent_measurable coarse _ _ (measurable_pi_apply c.castSucc) (measurable_pi_apply c.succ)

lemma pointRun_measurable (F : Row → ℝ → ℝ) (hF : ∀ r, Measurable (F r))
    (coarse : Fin (a+2) → ℝ) (jobs : List (Row × Row)) :
    Measurable (pointRun (M := M) F coarse jobs) :=
  table_run_measurable _ (pointParents_measurable coarse) _ jobs _
    (pointValues_measurable F hF) _ measurable_const

lemma pointResult_measurable (F : Row → ℝ → ℝ) (hF : ∀ r, Measurable (F r))
    (coarse : Fin (a+2) → ℝ) (jobs : List (Row × Row)) :
    Measurable (pointResult (M := M) F coarse jobs) :=
  optionGetD_measurable _ (pointRun_measurable F hF coarse jobs) ([],∅)

lemma finalPair_measurable (F : Row → ℝ → ℝ) (hF : ∀ r, Measurable (F r))
    (coarse : Fin (a+2) → ℝ) (jobs : List (Row × Row)) (job : Row × Row) :
    Measurable (fun points : Fin (M+2) → ℝ => finalPair F coarse jobs points job) := by
  have hparents : Measurable (pointParents (M := M) coarse) := measurable_pi_iff.mpr (pointParents_measurable coarse)
  have hremoved := measurable_snd.comp (pointResult_measurable (M := M) F hF coarse jobs)
  have hfamily : Measurable (fun z : (Fin (M+2) → ℝ) × ((Fin (M+1) → Fin (a+1)) × Finset (Fin (a+1))) =>
      select (pointValues F z.1 job.1) (pointValues F z.1 job.2)
        (available z.2.1 z.2.2 (List.finRange (M+1)))) := by
    apply measurable_from_prod_countable_left
    intro state
    exact select_measurable (available state.1 state.2 (List.finRange (M+1))) _ _
      (pointValues_measurable F hF job.1) (pointValues_measurable F hF job.2)
  have hsel := hfamily.comp (measurable_id.prodMk (hparents.prodMk hremoved))
  exact optionGetD_measurable _ hsel (0,0)

lemma protectedPairs_measurable (F : Row → ℝ → ℝ) (hF : ∀ r, Measurable (F r))
    (coarse : Fin (a+2) → ℝ) (jobs finalJobs : List (Row × Row)) :
    Measurable (protectedPairs (M := M) F coarse jobs finalJobs) := by
  have hfinal : Measurable (fun points : Fin (M+2) → ℝ => finalJobs.map (finalPair F coarse jobs points)) := by
    induction finalJobs with
    | nil => exact measurable_const
    | cons job rest ih =>
      exact ProtocolMeasurable.measurable_list_cons.comp ((finalPair_measurable F hF coarse jobs job).prodMk ih)
  exact ProtocolMeasurable.measurable_list_append.comp
    ((measurable_fst.comp (pointResult_measurable F hF coarse jobs)).prodMk hfinal)

/-- Every protected physical endpoint is Borel in the actual grid endpoints. -/
theorem endpointProcedure_measurable (F : Row → ℝ → ℝ) (hF : ∀ r, Measurable (F r))
    (coarse : Fin (a+2) → ℝ) (jobs finalJobs : List (Row × Row))
    (k : Fin (4*(jobs.length+finalJobs.length))) :
    Measurable (fun points : Fin (M+2) → ℝ => endpointProcedure F coarse jobs finalJobs points k) := by
  have hp : Measurable (fun points : Fin (M+2) → ℝ =>
      (protectedPairs F coarse jobs finalJobs points).getD (k.val/4) (0,0)) := by
    simp only [List.getD_eq_getElem?_getD]
    exact optionGetD_measurable _ ((ProtocolMeasurable.measurable_list_getElem (k.val/4)).comp
      (protectedPairs_measurable F hF coarse jobs finalJobs)) (0,0)
  have hc : Measurable (fun points : Fin (M+2) → ℝ =>
      if k.val%4 < 2 then ((protectedPairs F coarse jobs finalJobs points).getD (k.val/4) (0,0)).1
      else ((protectedPairs F coarse jobs finalJobs points).getD (k.val/4) (0,0)).2) := by
    split_ifs
    · exact measurable_fst.comp hp
    · exact measurable_snd.comp hp
  have hi : Measurable (fun points : Fin (M+2) → ℝ =>
      let pair := (protectedPairs F coarse jobs finalJobs points).getD (k.val/4) (0,0)
      let cell := if k.val%4 < 2 then pair.1 else pair.2
      if k.val%2 = 0 then cell.castSucc else cell.succ) := by
    by_cases h : k.val%2 = 0
    · simpa only [h,ite_true,Function.comp_def] using (measurable_of_countable Fin.castSucc).comp hc
    · simpa only [h,ite_false,Function.comp_def] using (measurable_of_countable Fin.succ).comp hc
  convert (score_eval_measurable id (fun i => measurable_pi_apply i)).comp (measurable_id.prodMk hi) using 1
  funext points
  unfold endpointProcedure
  dsimp only [Function.comp_def,id_eq]
  split_ifs <;> rfl

end EnvyFreeResearch.Full.RefinedUpperPeeling
