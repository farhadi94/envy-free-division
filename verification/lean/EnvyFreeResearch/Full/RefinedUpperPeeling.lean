import EnvyFreeResearch.Full.RefinedUpperWitnessSelectorStability
import EnvyFreeResearch.Full.UpperRepresentativeSupply

/-! Actual maximum-determinant peeling on cached rows. Parent removals,
physical nonemptiness, witness bounds and measurability are proved for this
concrete finite loop. -/
noncomputable section
namespace EnvyFreeResearch.Full.RefinedUpperPeeling
open MeasureTheory Set UpperRecordedDomain UpperRepresentativeSupply UpperRepresentatives
open RefinedUpperDeterminant
open scoped BigOperators Classical
variable {Cell Parent : Type*} [DecidableEq Parent]

def select (x y : Cell → ℝ) (cells : List Cell) : Option (Cell × Cell) :=
  RefinedUpperWitnessSelector.select (fun c => (x c,y c)) cells

theorem select_spec (x y : Cell → ℝ) (cells : List Cell) (hne : cells ≠ [])
    (hx : ∀ c ∈ cells, 0 ≤ x c) (hy : ∀ c ∈ cells, 0 ≤ y c) :
    ∃ F G, select x y cells = some (F,G) ∧ F ∈ cells ∧ G ∈ cells ∧
      ∀ E ∈ cells, ∀ u v, |u*x E-v*y E| ≤
        2*max |u*x F-v*y F| |u*x G-v*y G| := by
  obtain ⟨F,G,hs,hF,hG,_,hbound⟩ := RefinedUpperWitnessSelector.select_spec
    (fun c => (x c,y c)) cells hne (fun c hc => ⟨hx c hc,hy c hc⟩)
  refine ⟨F,G,hs,hF,hG,?_⟩
  intro E hE u v
  have hb := hbound E hE u (-v)
  simp only [value,neg_mul,← sub_eq_add_neg] at hb
  linarith [le_max_left |u*x F-v*y F| |u*x G-v*y G|,
    le_max_right |u*x F-v*y F| |u*x G-v*y G|]

theorem select_measurable [Countable Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    {X : Type*} [MeasurableSpace X] (cells : List Cell) (x y : X → Cell → ℝ)
    (hx : ∀ c, Measurable (fun z => x z c)) (hy : ∀ c, Measurable (fun z => y z c)) :
    Measurable (fun z => select (x z) (y z) cells) :=
  RefinedUpperWitnessSelector.select_measurable cells (fun z c => (x z c,y z c)) hx hy

/-- A finite list of requested row pairs drives all representative rounds.
Each selected coarse parent is excluded before the next round. -/
def run {Row : Type*} (values : Row → Cell → ℝ) (parent : Cell → Parent) (cells : List Cell) :
    List (Row × Row) → Finset Parent → Option (List (Cell × Cell) × Finset Parent)
  | [], removed => some ([], removed)
  | job :: jobs, removed =>
      (select (values job.1) (values job.2) (available parent removed cells)).bind (fun pair =>
        (run values parent cells jobs (addParents parent pair removed)).map
          (fun result => (pair :: result.1, result.2)))

/-- The physical supply bound makes the finite representative loop total.
The only remaining premise is the supplied small-parent budget; no successful
selection or nonemptiness of an intermediate table is assumed. -/
theorem run_completes [Fintype Cell] {Row : Type*}
    (μ : Measure ℝ) [IsFiniteMeasure μ] (fine : Cell → Component)
    (parents : Parent → Component) (parent : Cell → Parent)
    (hparent : ∀ c, (fine c).carrier ⊆ (parents (parent c)).carrier)
    (eta : ℝ) (heta : 0 ≤ eta) (cells : List Cell) (hlisted : ∀ c, c ∈ cells)
    (hnormalized : μ.real (⋃ c, (fine c).carrier) = 1)
    (hsmall : ∀ p, μ.real (parents p).carrier ≤ eta)
    (values : Row → Cell → ℝ) (hnonneg : ∀ r c, 0 ≤ values r c)
    (jobs : List (Row × Row)) (removed : Finset Parent)
    (hbudget : ((removed.card + 2 * jobs.length : ℕ) : ℝ) * eta < 1) :
    ∃ pairs final, run values parent cells jobs removed = some (pairs, final) ∧
      pairs.length = jobs.length ∧ removed ⊆ final ∧ final.card ≤ removed.card + 2 * jobs.length := by
  induction jobs generalizing removed with
  | nil => exact ⟨[], removed, rfl, rfl, Subset.rfl, by simp⟩
  | cons job jobs ih =>
    have hcurrent : (removed.card : ℝ) * eta < 1 := by
      have hle : (removed.card : ℝ) ≤ ((removed.card + 2 * (job :: jobs).length : ℕ) : ℝ) := by
        exact_mod_cast (by omega : removed.card ≤ removed.card + 2 * (job :: jobs).length)
      exact (mul_le_mul_of_nonneg_right hle heta).trans_lt hbudget
    have havailable := available_nonempty μ fine parents parent hparent removed eta cells hlisted
      hnormalized (fun p _ => hsmall p) hcurrent
    obtain ⟨first, last, hselect, _, _, _⟩ := select_spec (values job.1) (values job.2)
      (available parent removed cells) havailable (fun c _ => hnonneg _ c) (fun c _ => hnonneg _ c)
    have hcard := addParents_card_le parent (first, last) removed
    have hnext : (((addParents parent (first, last) removed).card + 2 * jobs.length : ℕ) : ℝ) * eta < 1 := by
      have hle : (((addParents parent (first, last) removed).card + 2 * jobs.length : ℕ) : ℝ) ≤
          ((removed.card + 2 * (job :: jobs).length : ℕ) : ℝ) := by
        exact_mod_cast (by simp only [List.length_cons]; omega :
          (addParents parent (first, last) removed).card + 2 * jobs.length ≤
            removed.card + 2 * (job :: jobs).length)
      exact (mul_le_mul_of_nonneg_right hle heta).trans_lt hbudget
    obtain ⟨pairs, final, hrun, hlength, hsubset, hfinal⟩ := ih _ hnext
    refine ⟨(first, last) :: pairs, final, ?_, ?_, ?_, ?_⟩
    · simp [run, hselect, hrun]
    · simp [hlength]
    · exact (removed_subset_addParents parent (first, last) removed).trans hsubset
    · simp only [List.length_cons]
      omega

def pairParents (parent : Cell → Parent) (pair : Cell × Cell) : Finset Parent :=
  {parent pair.1, parent pair.2}

/-- The final unselected cells include every possible successful reserve cell.
The selected pair controls every linear combination on that entire set. -/
def Represents {Row : Type*} (values : Row → Cell → ℝ) (parent : Cell → Parent)
    (cells : List Cell) (final : Finset Parent) (job : Row × Row) (pair : Cell × Cell) : Prop :=
  pair.1 ∈ cells ∧ pair.2 ∈ cells ∧ parent pair.1 ∈ final ∧ parent pair.2 ∈ final ∧
    ∀ c ∈ cells, parent c ∉ final → ∀ u v : ℝ,
      |u * values job.1 c - v * values job.2 c| ≤
        2 * max |u * values job.1 pair.1 - v * values job.2 pair.1|
          |u * values job.1 pair.2 - v * values job.2 pair.2|

/-- Every successful actual execution has distinct selected parents across
rounds and valid representatives against every cell surviving the whole loop. -/
theorem run_spec {Row : Type*} (values : Row → Cell → ℝ)
    (hnonneg : ∀ r c, 0 ≤ values r c) (parent : Cell → Parent) (cells : List Cell)
    (jobs : List (Row × Row)) (removed : Finset Parent)
    (pairs : List (Cell × Cell)) (final : Finset Parent)
    (hexec : run values parent cells jobs removed = some (pairs, final)) :
    removed ⊆ final ∧
    (∀ pair ∈ pairs, parent pair.1 ∉ removed ∧ parent pair.2 ∉ removed) ∧
    pairs.Pairwise (fun p q => Disjoint (pairParents parent p) (pairParents parent q)) ∧
    List.Forall₂ (Represents values parent cells final) jobs pairs := by
  induction jobs generalizing removed pairs final with
  | nil =>
    have heq : ([], removed) = (pairs, final) := by simpa only [run, Option.some.injEq] using hexec
    cases heq
    exact ⟨Subset.rfl, by simp, by simp, .nil⟩
  | cons job jobs ih =>
    cases hs : select (values job.1) (values job.2) (available parent removed cells) with
    | none => simp [run, hs] at hexec
    | some pair =>
      cases ht : run values parent cells jobs (addParents parent pair removed) with
      | none => simp [run, hs, ht] at hexec
      | some result =>
        rcases result with ⟨tail, final'⟩
        have heq : (pair :: tail, final') = (pairs, final) := by
          simpa only [run, hs, Option.bind_some, ht, Option.map_some, Option.some.injEq] using hexec
        cases heq
        obtain ⟨hsubset, havoid, hdisjoint, hrep⟩ := ih _ _ _ ht
        have holdsubset := (removed_subset_addParents parent pair removed).trans hsubset
        have hnonempty : available parent removed cells ≠ [] := by
          intro hempty
          simp [select, RefinedUpperWitnessSelector.select, hempty] at hs
        obtain ⟨first, last, hchoice, hfirst, hlast, hbound⟩ :=
          select_spec (values job.1) (values job.2) (available parent removed cells) hnonempty
            (fun c _ => hnonneg _ c) (fun c _ => hnonneg _ c)
        have hpair : (first, last) = pair := Option.some.inj (hchoice.symm.trans hs)
        cases hpair
        have hfirst' := (mem_available parent removed cells first).mp hfirst
        have hlast' := (mem_available parent removed cells last).mp hlast
        have hpairs : pairParents parent (first, last) ⊆ addParents parent (first, last) removed := by
          intro p hp
          simpa only [pairParents, addParents, Finset.mem_insert, Finset.mem_singleton] using
            (show p = parent first ∨ p = parent last ∨ p ∈ removed from by
              rcases Finset.mem_insert.mp hp with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl (Finset.mem_singleton.mp h)))
        refine ⟨holdsubset, ?_, ?_, ?_⟩
        · intro candidate hc
          rcases List.mem_cons.mp hc with rfl | htail
          · exact ⟨hfirst'.2, hlast'.2⟩
          · exact ⟨fun h => (havoid candidate htail).1
                (removed_subset_addParents parent (first, last) removed h),
              fun h => (havoid candidate htail).2
                (removed_subset_addParents parent (first, last) removed h)⟩
        · apply List.pairwise_cons.mpr
          refine ⟨?_, hdisjoint⟩
          intro candidate hc
          apply Finset.disjoint_left.mpr
          intro p hp hcandidate
          have hin := hpairs hp
          simp only [pairParents, Finset.mem_insert, Finset.mem_singleton] at hcandidate
          rcases hcandidate with rfl | rfl
          · exact (havoid candidate hc).1 hin
          · exact (havoid candidate hc).2 hin
        · apply List.Forall₂.cons _ hrep
          refine ⟨hfirst'.1, hlast'.1, ?_, ?_, ?_⟩
          · exact hsubset (by simp [addParents])
          · exact hsubset (by simp [addParents])
          · intro c hc hnot u v
            exact hbound c ((mem_available parent removed cells c).mpr
              ⟨hc, fun h => hnot (holdsubset h)⟩) u v

/-- Repeated selection and parent removal remain measurable in the cached
table. The list of row-pair jobs is fixed before reserve labels are sampled. -/
theorem run_measurable [Countable Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    [Countable Parent] {Row X : Type*} [MeasurableSpace X]
    (parent : Cell → Parent) (cells : List Cell) (jobs : List (Row × Row))
    (values : X → Row → Cell → ℝ) (hvalues : ∀ r c, Measurable (fun x => values x r c))
    (removed : X → Finset Parent) (hremoved : Measurable removed) :
    Measurable (fun x => run (values x) parent cells jobs (removed x)) := by
  classical
  induction jobs generalizing removed with
  | nil =>
    exact ProtocolMeasurable.measurable_some.comp (measurable_const.prodMk hremoved)
  | cons job jobs ih =>
    have hchoiceFamily : Measurable (fun p : X × Finset Parent =>
        select (values p.1 job.1) (values p.1 job.2) (available parent p.2 cells)) :=
      measurable_from_prod_countable_left (fun state =>
        select_measurable (available parent state cells) _ _ (hvalues job.1) (hvalues job.2))
    have hchoice := hchoiceFamily.comp (measurable_id.prodMk hremoved)
    have htail : Measurable (fun p : X × (Cell × Cell) =>
        run (values p.1) parent cells jobs (addParents parent p.2 (removed p.1))) := by
      apply measurable_from_prod_countable_left
      intro pair
      exact ih _ ((measurable_of_countable (addParents parent pair)).comp hremoved)
    have hpresent : Measurable (fun p : X × (Cell × Cell) =>
        (run (values p.1) parent cells jobs (addParents parent p.2 (removed p.1))).map
          (fun result => (p.2 :: result.1, result.2))) := by
      apply option_map_measurable
      · exact htail
      · exact (ProtocolMeasurable.measurable_list_cons.comp
          ((measurable_snd.comp measurable_fst).prodMk
            (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_snd)
    have h := ProtocolMeasurable.measurable_option_cases
      (present := fun x pair =>
        (run (values x) parent cells jobs (addParents parent pair (removed x))).map
          (fun result => (pair :: result.1, result.2)))
      (absent := fun _ => none) hchoice hpresent measurable_const
    convert h using 1
    funext x
    rw [run]
    dsimp only [Function.comp_def, id_eq]
    cases select (values x job.1) (values x job.2) (available parent (removed x) cells) <;> rfl


end EnvyFreeResearch.Full.RefinedUpperPeeling
