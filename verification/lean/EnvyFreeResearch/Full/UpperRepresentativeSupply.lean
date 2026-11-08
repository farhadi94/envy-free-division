import EnvyFreeResearch.Full.UpperRepresentatives
import EnvyFreeResearch.Full.UpperRecordedDomain

/-!
# Physical supply for repeated representative selection

Removing a bounded number of small coarse parents leaves positive measured
material, and therefore an available refined cell. This links the finite
selection rule to physical recorded parent/child carriers.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace EnvyFreeResearch.Full.UpperRepresentativeSupply

open UpperRecordedDomain UpperRepresentatives

variable {Cell Parent : Type*} [DecidableEq Parent]

def available (parent : Cell → Parent) (removed : Finset Parent) (cells : List Cell) : List Cell :=
  cells.filter (fun c => parent c ∉ removed)

theorem mem_available (parent : Cell → Parent) (removed : Finset Parent) (cells : List Cell)
    (c : Cell) : c ∈ available parent removed cells ↔ c ∈ cells ∧ parent c ∉ removed := by
  simp [available]

def removedRegion (parents : Parent → Component) (removed : Finset Parent) : Set ℝ :=
  ⋃ p ∈ removed, (parents p).carrier

def remainingRegion [Fintype Cell] (fine : Cell → Component) (parent : Cell → Parent)
    (removed : Finset Parent) : Set ℝ :=
  ⋃ c, if parent c ∈ removed then ∅ else (fine c).carrier

omit [DecidableEq Parent] in
theorem removed_mass_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (parents : Parent → Component) (removed : Finset Parent) (eta : ℝ)
    (hsmall : ∀ p ∈ removed, μ.real (parents p).carrier ≤ eta) :
    μ.real (removedRegion parents removed) ≤ (removed.card : ℝ) * eta := by
  calc
    μ.real (removedRegion parents removed) ≤ ∑ p ∈ removed, μ.real (parents p).carrier :=
      measureReal_biUnion_finset_le removed (fun p => (parents p).carrier)
    _ ≤ ∑ _p ∈ removed, eta := Finset.sum_le_sum hsmall
    _ = _ := by simp

theorem physical_coverage [Fintype Cell] (fine : Cell → Component)
    (parents : Parent → Component) (parent : Cell → Parent)
    (hparent : ∀ c, (fine c).carrier ⊆ (parents (parent c)).carrier)
    (removed : Finset Parent) :
    (⋃ c, (fine c).carrier) ⊆ removedRegion parents removed ∪ remainingRegion fine parent removed := by
  intro x hx
  obtain ⟨c, hc⟩ := mem_iUnion.mp hx
  by_cases hmem : parent c ∈ removed
  · exact Or.inl (mem_iUnion.mpr ⟨parent c, mem_iUnion.mpr ⟨hmem, hparent c hc⟩⟩)
  · apply Or.inr
    exact mem_iUnion.mpr ⟨c, by simpa only [hmem, ite_false] using hc⟩

/-- Every row retains at least `1 - card(removed) * eta` of its original
normalized physical mass, without relying on the representative score table. -/
theorem remaining_mass_lower_bound [Fintype Cell] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (fine : Cell → Component) (parents : Parent → Component) (parent : Cell → Parent)
    (hparent : ∀ c, (fine c).carrier ⊆ (parents (parent c)).carrier)
    (removed : Finset Parent) (eta : ℝ)
    (hnormalized : μ.real (⋃ c, (fine c).carrier) = 1)
    (hsmall : ∀ p ∈ removed, μ.real (parents p).carrier ≤ eta) :
    1 - (removed.card : ℝ) * eta ≤ μ.real (remainingRegion fine parent removed) := by
  have hcoverage := measureReal_mono (μ := μ) (physical_coverage fine parents parent hparent removed)
  have hunion := measureReal_union_le (μ := μ)
    (removedRegion parents removed) (remainingRegion fine parent removed)
  rw [hnormalized] at hcoverage
  have hremoved := removed_mass_le μ parents removed eta hsmall
  linarith

/-- Positive residual physical mass supplies a real listed refined cell whose
coarse parent has not been selected earlier. -/
theorem available_nonempty [Fintype Cell] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (fine : Cell → Component) (parents : Parent → Component) (parent : Cell → Parent)
    (hparent : ∀ c, (fine c).carrier ⊆ (parents (parent c)).carrier)
    (removed : Finset Parent) (eta : ℝ) (cells : List Cell) (hlisted : ∀ c, c ∈ cells)
    (hnormalized : μ.real (⋃ c, (fine c).carrier) = 1)
    (hsmall : ∀ p ∈ removed, μ.real (parents p).carrier ≤ eta)
    (hbudget : (removed.card : ℝ) * eta < 1) :
    available parent removed cells ≠ [] := by
  have hmass := remaining_mass_lower_bound μ fine parents parent hparent removed eta hnormalized hsmall
  have hpositive : 0 < μ.real (remainingRegion fine parent removed) := by linarith
  obtain ⟨x, hx⟩ := nonempty_of_measureReal_ne_zero hpositive.ne'
  obtain ⟨c, hc⟩ := mem_iUnion.mp hx
  have hmem : parent c ∉ removed := by
    intro h
    simp only [h, ite_true, mem_empty_iff_false] at hc
  have hin : c ∈ available parent removed cells :=
    (mem_available parent removed cells c).mpr ⟨hlisted c, hmem⟩
  intro hempty
  simp [hempty] at hin

def addParents (parent : Cell → Parent) (pair : Cell × Cell) (removed : Finset Parent) :
    Finset Parent := insert (parent pair.1) (insert (parent pair.2) removed)

theorem removed_subset_addParents (parent : Cell → Parent) (pair : Cell × Cell)
    (removed : Finset Parent) : removed ⊆ addParents parent pair removed := by
  intro p hp
  simp [addParents, hp]

theorem addParents_card_le (parent : Cell → Parent) (pair : Cell × Cell)
    (removed : Finset Parent) : (addParents parent pair removed).card ≤ removed.card + 2 := by
  have h1 := Finset.card_insert_le (parent pair.1) (insert (parent pair.2) removed)
  have h2 := Finset.card_insert_le (parent pair.2) removed
  unfold addParents
  omega

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
        3 * max |u * values job.1 pair.1 - v * values job.2 pair.1|
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
          simp [select, hempty] at hs
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

end EnvyFreeResearch.Full.UpperRepresentativeSupply
