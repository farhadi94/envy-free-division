import EnvyFreeResearch.Full.IntervalOracle
import EnvyFreeResearch.Full.UpperPhysical

/-!
# A concrete two-cut circular query stage

The stage calls an ordinary interval Cut twice and records both endpoints with
every original observer. Its policy receives the complete preceding answered
history, including the first endpoint's observer records before the second Cut.
The constructed trace, exact cutter mass, endpoint laws, and unconditional
foreign-mass expectation are proved together below.

This module handles a normalized cutter on `[0,1]`. The adapter for a recorded
finite union and the global Repair/Snapshot/Shrink state machine remain open.
Measurability of the two realized response maps is required explicitly; no
independence of the endpoint responses is required.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal unitInterval

namespace EnvyFreeResearch.Full.UpperCircularStage

open IntervalOracle UpperCircular UpperPhysical

abbrev Circle := UpperCircular.Circle
abbrev Query (n : ℕ) := IntervalOracle.Query (Fin n)
abbrev History (n : ℕ) := List (Query n × ℝ)
abbrev Policy (n : ℕ) := History n → Query n → ℝ

/-- Admissibility constrains only oracle answers to legal ordinary queries.
It asserts no sampling, allocation, progress, or cost property. -/
def Admissible {n : ℕ} (P : Profile (Fin n)) (policy : Policy n) : Prop :=
  ∀ history q, Legal P q → ValidReply P q (policy history q)

/-- Execute a finite list of queries sequentially, exposing all previous
answers to the response policy before each new call. -/
def executeQueries {n : ℕ} (policy : Policy n) : List (Query n) → History n → History n
  | [], history => history
  | q :: qs, history =>
      executeQueries policy qs (history ++ [(q, policy history q)])

theorem executeQueries_projection {n : ℕ} (policy : Policy n)
    (queries : List (Query n)) (history : History n) :
    (executeQueries policy queries history).map Prod.fst =
      history.map Prod.fst ++ queries := by
  induction queries generalizing history with
  | nil => simp [executeQueries]
  | cons q qs ih =>
    simp only [executeQueries, ih, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append]

theorem executeQueries_length {n : ℕ} (policy : Policy n)
    (queries : List (Query n)) (history : History n) :
    (executeQueries policy queries history).length = history.length + queries.length := by
  have h := congrArg List.length (executeQueries_projection policy queries history)
  simpa only [List.length_map, List.length_append] using h

def recordings (n : ℕ) (endpoint : ℝ) : List (Query n) :=
  List.ofFn (fun i : Fin n => IntervalOracle.Query.eval i 0 endpoint)

def firstQuery {n : ℕ} (cutter : Fin n) (start : Circle) : Query n :=
  .cut cutter 0 1 (value start : ℝ)

def lastQuery {n : ℕ} (cutter : Fin n) (amount : I) (start : Circle) : Query n :=
  .cut cutter 0 1 (value (start + project amount) : ℝ)

def firstEndpoint {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (start : Circle) : ℝ := policy history (firstQuery cutter start)

def afterFirst {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (start : Circle) : History n :=
  executeQueries policy (recordings n (firstEndpoint policy history cutter start))
    (history ++ [(firstQuery cutter start, firstEndpoint policy history cutter start)])

def lastEndpoint {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) (start : Circle) : ℝ :=
  policy (afterFirst policy history cutter start) (lastQuery cutter amount start)

def finalHistory {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) (start : Circle) : History n :=
  executeQueries policy (recordings n (lastEndpoint policy history cutter amount start))
    (afterFirst policy history cutter start ++
      [(lastQuery cutter amount start, lastEndpoint policy history cutter amount start)])

def output {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) (start : Circle) : Set ℝ :=
  physicalPiece (Icc 0 1) amount start
    (firstEndpoint policy history cutter start) (lastEndpoint policy history cutter amount start)

theorem stage_queries {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) (start : Circle) :
    (finalHistory policy history cutter amount start).map Prod.fst =
      history.map Prod.fst ++ [firstQuery cutter start] ++
      recordings n (firstEndpoint policy history cutter start) ++
      [lastQuery cutter amount start] ++
      recordings n (lastEndpoint policy history cutter amount start) := by
  simp only [finalHistory, afterFirst, executeQueries_projection, List.map_append,
    List.map_cons, List.map_nil]

/-- This counts every Cut and every original observer's endpoint recording. -/
theorem stage_query_count {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) (start : Circle) :
    (finalHistory policy history cutter amount start).length = history.length + 2 * (n + 1) := by
  have h := congrArg List.length (stage_queries policy history cutter amount start)
  simp only [List.length_map, List.length_append, List.length_singleton,
    recordings, List.length_ofFn] at h
  omega

def isCut {n : ℕ} : Query n → Bool
  | .eval _ _ _ => false
  | .cut _ _ _ _ => true

theorem recordings_no_cuts (n : ℕ) (endpoint : ℝ) :
    (recordings n endpoint).countP isCut = 0 := by
  apply List.countP_eq_zero.mpr
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  simp [isCut]

theorem stage_cut_count {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) (start : Circle) :
    ((finalHistory policy history cutter amount start).map Prod.fst).countP isCut =
      (history.map Prod.fst).countP isCut + 2 := by
  rw [stage_queries]
  simp only [List.countP_append, List.countP_cons, List.countP_nil,
    recordings_no_cuts, firstQuery, lastQuery, isCut, ite_true]

theorem normalized_cut_legal {n : ℕ} (P : Profile (Fin n)) (cutter : Fin n)
    (htotal : P.cumulative cutter 1 = 1) (target : I) :
    Legal P (.cut cutter 0 1 (target : ℝ)) := by
  simp only [Legal, P.zero, htotal, ExtremalRoots.LegalTarget]
  norm_num
  exact target.property

theorem first_valid {n : ℕ} (P : Profile (Fin n)) (policy : Policy n)
    (hpolicy : Admissible P policy) (history : History n) (cutter : Fin n)
    (htotal : P.cumulative cutter 1 = 1) (start : Circle) :
    firstEndpoint policy history cutter start ∈ Icc 0 1 ∧
      P.cumulative cutter (firstEndpoint policy history cutter start) = (value start : ℝ) := by
  have h := hpolicy history (firstQuery cutter start)
    (normalized_cut_legal P cutter htotal (value start))
  simpa only [ValidReply, firstQuery, firstEndpoint, P.zero, zero_add] using h

theorem last_valid {n : ℕ} (P : Profile (Fin n)) (policy : Policy n)
    (hpolicy : Admissible P policy) (history : History n) (cutter : Fin n)
    (htotal : P.cumulative cutter 1 = 1) (amount : I) (start : Circle) :
    lastEndpoint policy history cutter amount start ∈ Icc 0 1 ∧
      P.cumulative cutter (lastEndpoint policy history cutter amount start) =
        (value (start + project amount) : ℝ) := by
  have h := hpolicy (afterFirst policy history cutter start) (lastQuery cutter amount start)
    (normalized_cut_legal P cutter htotal (value (start + project amount)))
  simpa only [ValidReply, lastQuery, lastEndpoint, P.zero, zero_add] using h

/-- Every observer recording requested by this stage is an ordinary legal Eval. -/
theorem recordings_legal {n : ℕ} (P : Profile (Fin n)) (endpoint : ℝ)
    (hendpoint : endpoint ∈ Icc (0 : ℝ) 1) :
    ∀ q ∈ recordings n endpoint, Legal P q := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  exact ⟨le_rfl, hendpoint.1, hendpoint.2⟩

/-- The actual query increment is finite on every start, with no restriction to
an acceptance event. Its lower integral is the unconditional expected cost. -/
theorem unconditional_query_cost {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) :
    (∫⁻ start,
      (((finalHistory policy history cutter amount start).length - history.length : ℕ) : ℝ≥0∞)
      ∂(volume : Measure Circle)) = (2 * (n + 1) : ℕ) := by
  simp only [stage_query_count, Nat.add_sub_cancel_left]
  simp

theorem unconditional_cut_cost {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) :
    (∫⁻ start,
      ((((finalHistory policy history cutter amount start).map Prod.fst).countP isCut -
          (history.map Prod.fst).countP isCut : ℕ) : ℝ≥0∞)
      ∂(volume : Measure Circle)) = 2 := by
  simp only [stage_cut_count, Nat.add_sub_cancel_left]
  simp

/-- The returned piece and literal remaining domain partition the resource,
so null fragments are retained exactly. -/
theorem output_partition {n : ℕ} (policy : Policy n) (history : History n)
    (cutter : Fin n) (amount : I) (start : Circle) :
    Disjoint (output policy history cutter amount start)
      (Icc 0 1 \ output policy history cutter amount start) ∧
    output policy history cutter amount start ∪
      (Icc 0 1 \ output policy history cutter amount start) = Icc 0 1 := by
  refine ⟨disjoint_sdiff_right, ?_⟩
  ext x
  constructor
  · rintro (hx | hx)
    · exact physicalPiece_subset (Icc 0 1) amount start _ _ hx
    · exact hx.1
  · intro hx
    by_cases ho : x ∈ output policy history cutter amount start
    · exact Or.inl ho
    · exact Or.inr ⟨hx, ho⟩

theorem output_exact_cutter_mass {n : ℕ} (P : Profile (Fin n)) (policy : Policy n)
    (hpolicy : Admissible P policy) (history : History n) (cutter : Fin n)
    (htotal : P.cumulative cutter 1 = 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hCDF : P.cumulative cutter = cdf μ) (hsupport : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1)
    (amount : I) (start : Circle) :
    μ.real (output policy history cutter amount start) = (amount : ℝ) := by
  apply physicalPiece_own_value μ (Icc 0 1) hsupport
  · simpa only [← hCDF] using (first_valid P policy hpolicy history cutter htotal start).2
  · simpa only [← hCDF] using (last_valid P policy hpolicy history cutter htotal amount start).2

theorem first_endpoint_law {n : ℕ} (P : Profile (Fin n)) (policy : Policy n)
    (hpolicy : Admissible P policy) (history : History n) (cutter : Fin n)
    (htotal : P.cumulative cutter 1 = 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hCDF : P.cumulative cutter = cdf μ)
    (hmeas : Measurable (firstEndpoint policy history cutter)) :
    HasLaw (firstEndpoint policy history cutter) μ (volume : Measure Circle) := by
  apply circular_endpoint_law μ 0 _ hmeas
  exact ae_of_all _ (fun start => by
    simpa only [← hCDF, add_zero] using
      (first_valid P policy hpolicy history cutter htotal start).2)

/-- The second Cut is allowed to use the first Cut response and every first
endpoint Eval. Its law is nevertheless the exact cutter law. -/
theorem last_endpoint_law {n : ℕ} (P : Profile (Fin n)) (policy : Policy n)
    (hpolicy : Admissible P policy) (history : History n) (cutter : Fin n)
    (htotal : P.cumulative cutter 1 = 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hCDF : P.cumulative cutter = cdf μ) (amount : I)
    (hmeas : Measurable (lastEndpoint policy history cutter amount)) :
    HasLaw (lastEndpoint policy history cutter amount) μ (volume : Measure Circle) := by
  apply circular_endpoint_law μ (project amount) _ hmeas
  exact ae_of_all _ (fun start => by
    simpa only [← hCDF] using (last_valid P policy hpolicy history cutter htotal amount start).2)

/-- Unconditional expected foreign mass of the returned physical piece, for a
fixed preceding history and any admissible history-dependent response policy. -/
theorem output_foreign_mass_expectation {n : ℕ} (P : Profile (Fin n)) (policy : Policy n)
    (hpolicy : Admissible P policy) (history : History n) (cutter : Fin n)
    (htotal : P.cumulative cutter 1 = 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hCDF : P.cumulative cutter = cdf μ) (amount : I)
    (hfirstMeas : Measurable (firstEndpoint policy history cutter))
    (hlastMeas : Measurable (lastEndpoint policy history cutter amount))
    (foreign : Measure ℝ) [SFinite foreign] :
    (∫⁻ start, foreign (output policy history cutter amount start)
      ∂(volume : Measure Circle)) = ENNReal.ofReal (amount : ℝ) * foreign (Icc 0 1) := by
  apply physical_foreign_mass_expectation (Icc 0 1) measurableSet_Icc foreign amount
    _ _ hfirstMeas hlastMeas (monotone_cdf μ)
  · intro x _
    exact ⟨cdf_nonneg μ x, cdf_le_one μ x⟩
  · exact ae_of_all _ (fun start => by
      simpa only [← hCDF] using (first_valid P policy hpolicy history cutter htotal start).2)
  · exact ae_of_all _ (fun start => by
      simpa only [← hCDF] using (last_valid P policy hpolicy history cutter htotal amount start).2)

end EnvyFreeResearch.Full.UpperCircularStage
