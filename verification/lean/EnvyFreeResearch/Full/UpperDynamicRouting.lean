import EnvyFreeResearch.Full.UpperDomainDifferenceHistory

/-!
# Jointly measurable routing on a changing recorded domain

The ordinary-query executor may receive a different finite component list and
cache at every step. The actual cached scan is measurable in all those data;
no countability or discreteness is imposed on real endpoints.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperDynamicRouting

open UpperRecordedDomain UpperDomainDifference ProtocolMeasurable

variable {α X : Type*} [MeasurableSpace α] [MeasurableSpace X]

def routeCode (r : Route α) : List α × α × List α := (r.before, r.cell, r.after)

instance routeMeasurableSpace : MeasurableSpace (Route α) :=
  MeasurableSpace.comap routeCode inferInstance

theorem routeCode_measurable : Measurable (routeCode (α := α)) := comap_measurable _

theorem route_before_measurable : Measurable (Route.before (α := α)) :=
  measurable_fst.comp routeCode_measurable

theorem route_cell_measurable : Measurable (Route.cell (α := α)) :=
  measurable_fst.comp (measurable_snd.comp routeCode_measurable)

theorem route_after_measurable : Measurable (Route.after (α := α)) :=
  measurable_snd.comp (measurable_snd.comp routeCode_measurable)

theorem route_mk_measurable (before : X → List α) (cell : X → α) (after : X → List α)
    (hb : Measurable before) (hc : Measurable cell) (ha : Measurable after) :
    Measurable (fun z => (⟨before z, cell z, after z⟩ : Route α)) :=
  measurable_comap_iff.mpr (hb.prodMk (hc.prodMk ha))

theorem list_tail_measurable : Measurable (List.tail (α := α)) := by
  apply measurable_comap_iff.mpr
  apply Measurable.prodMk
  · simpa only [Function.comp_def, listCode, List.length_tail] using
      (measurable_of_countable (fun n : ℕ => n - 1)).comp measurable_list_length
  · apply Measurable.of_eval
    intro i
    simpa only [Function.comp_def, listCode, List.getElem?_tail] using
      measurable_list_getElem (α := α) (i + 1)

/-- A bounded presentation of the existing recursive scan, used only to
prove measurability under the standard variable-list encoding. -/
def locateFuel (v : α → ℝ) (target : ℝ) (cells : List α) : ℕ → Option (Route α)
  | 0 => none
  | k + 1 => match cells.head? with
    | none => none
    | some c => if target ≤ v c then some ⟨[], c, cells.tail⟩ else
      (locateFuel v (target - v c) cells.tail k).map (fun r => ⟨c :: r.before, r.cell, r.after⟩)

omit [MeasurableSpace α] in
theorem locateFuel_eq (v : α → ℝ) (target : ℝ) (cells : List α) (fuel : ℕ)
    (h : cells.length ≤ fuel) : locateFuel v target cells fuel = locate v target cells := by
  induction fuel generalizing cells target with
  | zero => have hc : cells = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
            subst cells
            rfl
  | succ k ih =>
    cases cells with
    | nil => rfl
    | cons c cs =>
      simp only [locateFuel, List.head?_cons, List.tail_cons, locate]
      split_ifs
      · rfl
      · rw [ih _ _ (by simpa using Nat.le_of_succ_le_succ h)]

theorem locateFuel_measurable (v : X → α → ℝ)
    (hv : Measurable (fun p : X × α => v p.1 p.2)) (fuel : ℕ) :
    Measurable (fun p : X × ℝ × List α => locateFuel (v p.1) p.2.1 p.2.2 fuel) := by
  classical
  induction fuel with
  | zero => exact measurable_const
  | succ k ih =>
    have hx : Measurable (fun p : (X × ℝ × List α) × α => p.1.1) := measurable_fst.comp measurable_fst
    have ht : Measurable (fun p : (X × ℝ × List α) × α => p.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have htail : Measurable (fun p : (X × ℝ × List α) × α => p.1.2.2.tail) :=
      list_tail_measurable.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
    have hval : Measurable (fun p : (X × ℝ × List α) × α => v p.1.1 p.2) := hv.comp (hx.prodMk measurable_snd)
    have hrec : Measurable (fun p : (X × ℝ × List α) × α =>
        locateFuel (v p.1.1) (p.1.2.1 - v p.1.1 p.2) p.1.2.2.tail k) :=
      ih.comp (hx.prodMk ((ht.sub hval).prodMk htail))
    have hprepend : Measurable (fun p : ((X × ℝ × List α) × α) × Route α =>
        some (⟨p.1.2 :: p.2.before, p.2.cell, p.2.after⟩ : Route α)) := by
      apply measurable_some.comp
      apply route_mk_measurable
      · exact measurable_list_cons.comp ((measurable_snd.comp measurable_fst).prodMk
          (route_before_measurable.comp measurable_snd))
      · exact route_cell_measurable.comp measurable_snd
      · exact route_after_measurable.comp measurable_snd
    have hskip := measurable_option_cases
      (present := fun p r => some (⟨p.2 :: r.before, r.cell, r.after⟩ : Route α))
      (absent := fun _ : (X × ℝ × List α) × α => (none : Option (Route α))) hrec hprepend
      (measurable_const : Measurable (fun _ : (X × ℝ × List α) × α => (none : Option (Route α))))
    have hhit : Measurable (fun p : (X × ℝ × List α) × α => some (⟨[], p.2, p.1.2.2.tail⟩ : Route α)) :=
      measurable_some.comp (route_mk_measurable _ _ _ measurable_const measurable_snd htail)
    have hsome : Measurable (fun p : (X × ℝ × List α) × α =>
        if p.1.2.1 ≤ v p.1.1 p.2 then some (⟨[], p.2, p.1.2.2.tail⟩ : Route α) else
        match locateFuel (v p.1.1) (p.1.2.1 - v p.1.1 p.2) p.1.2.2.tail k with
        | some r => some (⟨p.2 :: r.before, r.cell, r.after⟩ : Route α)
        | none => none) := by
      apply hhit.ite (measurableSet_le ht hval)
      convert hskip using 1
      funext p
      cases locateFuel (v p.1.1) (p.1.2.1 - v p.1.1 p.2) p.1.2.2.tail k <;> rfl
    have hhead : Measurable (fun p : (X × ℝ × List α) => p.2.2.head?) := by
      simpa only [List.head?_eq_getElem?, Function.comp_def] using
        (measurable_list_getElem (α := α) 0).comp (measurable_snd.comp measurable_snd)
    have h := measurable_option_cases
      (present := fun p c => if p.2.1 ≤ v p.1 c then some (⟨[], c, p.2.2.tail⟩ : Route α) else
        match locateFuel (v p.1) (p.2.1 - v p.1 c) p.2.2.tail k with
        | some r => some (⟨c :: r.before, r.cell, r.after⟩ : Route α)
        | none => none)
      (absent := fun _ : X × ℝ × List α => (none : Option (Route α))) hhead hsome
      (measurable_const : Measurable (fun _ : (X × ℝ × List α) => (none : Option (Route α))))
    convert h using 1
    funext p
    dsimp only [locateFuel]
    cases p.2.2.head? with
    | none => rfl
    | some c =>
      dsimp only
      split_ifs
      · rfl
      · cases locateFuel (v p.1) (p.2.1 - v p.1 c) p.2.2.tail k <;> rfl

/-- The actual scan is Borel jointly in the variable real-valued cache,
search target, and finite endpoint-owned component list. -/
theorem locate_measurable (v : X → α → ℝ)
    (hv : Measurable (fun p : X × α => v p.1 p.2))
    (target : X → ℝ) (cells : X → List α)
    (htarget : Measurable target) (hcells : Measurable cells) :
    Measurable (fun z => locate (v z) (target z) (cells z)) := by
  have hf : Measurable (fun p : (X × ℝ × List α) × ℕ =>
      locateFuel (v p.1.1) p.1.2.1 p.1.2.2 p.2) :=
    measurable_from_prod_countable_left (locateFuel_measurable v hv)
  have h := hf.comp ((measurable_id.prodMk (htarget.prodMk hcells)).prodMk
    (measurable_list_length.comp hcells))
  convert h using 1
  funext z
  exact (locateFuel_eq (v z) (target z) (cells z) (cells z).length le_rfl).symm

theorem sumValues_measurable (v : X → α → ℝ)
    (hv : Measurable (fun p : X × α => v p.1 p.2))
    (cells : X → List α) (hcells : Measurable cells) :
    Measurable (fun z => sumValues (v z) (cells z)) := by
  have hmap := list_map_measurable v cells hv hcells
  have hsum := list_foldl_measurable (fun (_ : X) (a b : ℝ) => a + b)
    (fun _ => (0 : ℝ)) (fun z => (cells z).map (v z))
    ((measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd))
    measurable_const hmap
  simpa only [sumValues, List.sum_eq_foldl] using hsum

end EnvyFreeResearch.Full.UpperDynamicRouting
