import EnvyFreeResearch.Full.UpperComponentAssembly

/-! Joint Borel assembly under the ordinary endpoint/list coding.
Insertion sorting is proved measurable through finite prefix recursion and
the measurable list length, without a discrete encoding of real endpoints. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperComponentAssembly

open ProtocolMeasurable UpperRecordedDomain UpperDomainDifference UpperDynamicRouting
  UpperCorrectionExecution UpperCircularStage

section Sorting

variable {α : Type} [MeasurableSpace α] (r : α → α → Prop)

def insertFuel : ℕ → α → List α → List α
  | 0, a, _ => [a]
  | fuel + 1, a, xs =>
    match xs[0]? with
    | none => [a]
    | some b => if r a b then a :: xs else b :: insertFuel fuel a xs.tail

theorem insertFuel_eq (fuel : ℕ) (a : α) (xs : List α) (h : xs.length ≤ fuel) :
    insertFuel r fuel a xs = List.orderedInsert r a xs := by
  induction fuel generalizing xs with
  | zero =>
    have : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst xs
    rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      simp only [insertFuel, List.getElem?_cons_zero, List.tail_cons, List.orderedInsert_cons]
      rw [ih xs (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using h)]

theorem insertFuel_measurable (hr : MeasurableSet {p : α × α | r p.1 p.2}) (fuel : ℕ) :
    Measurable (fun p : α × List α => insertFuel r fuel p.1 p.2) := by
  induction fuel with
  | zero => exact measurable_list_singleton.comp measurable_fst
  | succ fuel ih =>
    have hpresent : Measurable (fun z : (α × List α) × α =>
        if r z.1.1 z.2 then z.1.1 :: z.1.2 else z.2 :: insertFuel r fuel z.1.1 z.1.2.tail) := by
      apply (measurable_list_cons.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst))).ite
      · exact hr.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact measurable_list_cons.comp (measurable_snd.prodMk
          (ih.comp ((measurable_fst.comp measurable_fst).prodMk
            (list_tail_measurable.comp (measurable_snd.comp measurable_fst)))))
    have h := measurable_option_cases
      (value := fun p : α × List α => p.2[0]?)
      (present := fun p b => if r p.1 b then p.1 :: p.2 else b :: insertFuel r fuel p.1 p.2.tail)
      (absent := fun p => [p.1]) ((measurable_list_getElem 0).comp measurable_snd) hpresent
      (measurable_list_singleton.comp measurable_fst)
    convert h using 1
    funext p
    simp only [insertFuel]
    cases p.2[0]? <;> rfl

theorem orderedInsert_measurable (hr : MeasurableSet {p : α × α | r p.1 p.2}) :
    Measurable (fun p : α × List α => List.orderedInsert r p.1 p.2) := by
  have h : Measurable (fun p : (α × List α) × ℕ => insertFuel r p.2 p.1.1 p.1.2) :=
    measurable_from_prod_countable_left (insertFuel_measurable r hr)
  have hh := h.comp (measurable_id.prodMk (measurable_list_length.comp measurable_snd))
  convert hh using 1
  funext p
  exact (insertFuel_eq r p.2.length p.1 p.2 le_rfl).symm

def sortFuel : ℕ → List α → List α
  | 0, _ => []
  | fuel + 1, xs =>
    match xs[0]? with
    | none => []
    | some a => List.orderedInsert r a (sortFuel fuel xs.tail)

theorem sortFuel_eq (fuel : ℕ) (xs : List α) (h : xs.length ≤ fuel) :
    sortFuel r fuel xs = List.insertionSort r xs := by
  induction fuel generalizing xs with
  | zero =>
    have : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst xs
    rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      simp only [sortFuel, List.getElem?_cons_zero, List.tail_cons, List.insertionSort_cons]
      rw [ih xs (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using h)]

theorem sortFuel_measurable (hr : MeasurableSet {p : α × α | r p.1 p.2}) (fuel : ℕ) :
    Measurable (sortFuel r fuel) := by
  induction fuel with
  | zero => exact measurable_const
  | succ fuel ih =>
    have hpresent : Measurable (fun z : List α × α => List.orderedInsert r z.2 (sortFuel r fuel z.1.tail)) :=
      (orderedInsert_measurable r hr).comp
        (measurable_snd.prodMk (ih.comp (list_tail_measurable.comp measurable_fst)))
    have h := measurable_option_cases (value := fun xs : List α => xs[0]?)
      (present := fun xs a => List.orderedInsert r a (sortFuel r fuel xs.tail))
      (absent := fun _ => []) (measurable_list_getElem 0) hpresent measurable_const
    convert h using 1
    funext xs
    simp only [sortFuel]
    cases xs[0]? <;> rfl

theorem insertionSort_measurable (hr : MeasurableSet {p : α × α | r p.1 p.2}) :
    Measurable (List.insertionSort r) := by
  have h : Measurable (fun p : List α × ℕ => sortFuel r p.2 p.1) :=
    measurable_from_prod_countable_left (sortFuel_measurable r hr)
  have hh := h.comp (measurable_id.prodMk measurable_list_length)
  convert hh using 1
  funext xs
  exact (sortFuel_eq r xs.length xs le_rfl).symm

end Sorting

theorem live_measurable : Measurable live := by
  apply decide_measurable
  have heq : {c : Component | c.carrier.Nonempty} =
      {c | c.left < c.right} ∪ {c | c.left ∈ c.carrier} := by
    ext c
    exact nonempty_iff c
  rw [heq]
  exact (measurableSet_lt component_left_measurable component_right_measurable).union
    (component_membership_measurable id Component.left measurable_id component_left_measurable)

theorem assemble_measurable : Measurable assemble := by
  have hbefore : MeasurableSet {p : Component × Component | before p.1 p.2} :=
    (measurableSet_lt (component_left_measurable.comp measurable_fst)
      (component_left_measurable.comp measurable_snd)).union
      ((measurableSet_eq_fun (component_left_measurable.comp measurable_fst)
        (component_left_measurable.comp measurable_snd)).inter
      (measurableSet_le (component_right_measurable.comp measurable_fst)
        (component_right_measurable.comp measurable_snd)))
  exact (insertionSort_measurable before hbefore).comp
    (list_filter_measurable (fun _ : List Component => live) id
      (live_measurable.comp measurable_snd) measurable_id)

theorem state_measurable {n : ℕ} : Measurable (fun p : List Component × History n => state p.1 p.2) := by
  apply measurable_comap_iff.mpr
  exact (assemble_measurable.comp measurable_fst).prodMk measurable_snd

end EnvyFreeResearch.Full.UpperComponentAssembly
