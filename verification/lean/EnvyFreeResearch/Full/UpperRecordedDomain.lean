import EnvyFreeResearch.Full.ChoresTwoAgent
import EnvyFreeResearch.Full.AdaptiveOracle
import EnvyFreeResearch.Full.UpperCircularStage

/-!
# Recorded-domain routing with ordinary individual Cuts

A component carries its literal endpoint ownership, so complements and domain
unions retain every null fragment. Routing uses only the cached nonnegative
component masses. Its proof identifies one component and one residual target;
no union-cut or sum-measure oracle is postulated.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperRecordedDomain

structure Component where
  left : ℝ
  right : ℝ
  left_nonneg : 0 ≤ left
  left_le_right : left ≤ right
  right_le_one : right ≤ 1
  carrier : Set ℝ
  measurable_carrier : MeasurableSet carrier
  interior_subset : Ioo left right ⊆ carrier
  subset_closed : carrier ⊆ Icc left right

def domain : List Component → Set ℝ
  | [] => ∅
  | c :: cs => c.carrier ∪ domain cs

theorem domain_measurable (cs : List Component) : MeasurableSet (domain cs) := by
  induction cs with
  | nil => exact MeasurableSet.empty
  | cons c cs ih => exact c.measurable_carrier.union ih

theorem mem_domain {x : ℝ} {cs : List Component} :
    x ∈ domain cs ↔ ∃ c ∈ cs, x ∈ c.carrier := by
  induction cs with
  | nil => simp [domain]
  | cons c cs ih => simp [domain, ih]

theorem domain_subset_unit (cs : List Component) : domain cs ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  obtain ⟨c, _, hc⟩ := mem_domain.mp hx
  have h := c.subset_closed hc
  exact ⟨c.left_nonneg.trans h.1, h.2.trans c.right_le_one⟩

def sumValues {α : Type*} (v : α → ℝ) (cs : List α) : ℝ := (cs.map v).sum

@[simp] theorem sumValues_nil {α : Type*} (v : α → ℝ) : sumValues v [] = 0 := rfl

@[simp] theorem sumValues_cons {α : Type*} (v : α → ℝ) (c : α) (cs : List α) :
    sumValues v (c :: cs) = v c + sumValues v cs := rfl

@[simp] theorem sumValues_append {α : Type*} (v : α → ℝ) (as bs : List α) :
    sumValues v (as ++ bs) = sumValues v as + sumValues v bs := by
  simp [sumValues]

structure Route (α : Type*) where
  before : List α
  cell : α
  after : List α

/-- A finite scan of cached masses. Only comparisons and subtraction of
recorded real values are used. -/
def locate {α : Type*} (v : α → ℝ) : ℝ → List α → Option (Route α)
  | _, [] => none
  | target, c :: cs =>
      if target ≤ v c then some ⟨[], c, cs⟩ else
        (locate v (target - v c) cs).map (fun r => ⟨c :: r.before, r.cell, r.after⟩)

theorem locate_spec {α : Type*} (v : α → ℝ) (cs : List α) (target : ℝ)
    (htarget : 0 < target) (hbound : target ≤ sumValues v cs) :
    ∃ r : Route α, locate v target cs = some r ∧
      cs = r.before ++ r.cell :: r.after ∧
      sumValues v r.before < target ∧ target ≤ sumValues v r.before + v r.cell := by
  induction cs generalizing target with
  | nil => simp only [sumValues_nil] at hbound; linarith
  | cons c cs ih =>
    by_cases hhead : target ≤ v c
    · exact ⟨⟨[], c, cs⟩, by simp [locate, hhead], rfl,
        by simpa using htarget, by simpa using hhead⟩
    · have hpos : 0 < target - v c := by linarith
      have htail : target - v c ≤ sumValues v cs := by
        rw [sumValues_cons] at hbound
        linarith
      obtain ⟨r, hroute, hsplit, hlow, hhigh⟩ := ih (target - v c) hpos htail
      refine ⟨⟨c :: r.before, r.cell, r.after⟩, ?_, ?_, ?_, ?_⟩
      · simp only [locate, hhead, ite_false, hroute, Option.map_some]
      · simp only [List.cons_append, ← hsplit]
      · change v c + sumValues v r.before < target
        linarith
      · change target ≤ (v c + sumValues v r.before) + v r.cell
        linarith

def Ordered (cs : List Component) : Prop :=
  cs.Pairwise (fun c d => c.right ≤ d.left)

def DisjointComponents (cs : List Component) : Prop :=
  cs.Pairwise (fun c d => Disjoint c.carrier d.carrier)

variable (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]

def mass (c : Component) : ℝ := μ.real c.carrier

def prefixMass (c : Component) (x : ℝ) : ℝ := μ.real (c.carrier ∩ Iic x)

omit [IsFiniteMeasure μ] in
theorem component_mass_eq_interval (c : Component) :
    mass μ c = μ.real (Ioc c.left c.right) := by
  apply measureReal_congr
  filter_upwards [μ.ae_ne c.left, μ.ae_ne c.right] with x hleft hright
  apply propext
  constructor
  · intro hx
    have h := c.subset_closed hx
    exact ⟨lt_of_le_of_ne h.1 hleft.symm, h.2⟩
  · intro hx
    exact c.interior_subset ⟨hx.1, lt_of_le_of_ne hx.2 hright⟩

omit [IsFiniteMeasure μ] in
theorem component_prefix_eq_interval (c : Component) {x : ℝ}
    (hx : x ∈ Icc c.left c.right) :
    prefixMass μ c x = μ.real (Ioc c.left x) := by
  apply measureReal_congr
  filter_upwards [μ.ae_ne c.left, μ.ae_ne c.right] with y hleft hright
  apply propext
  constructor
  · rintro ⟨hy, hyx⟩
    have h := c.subset_closed hy
    exact ⟨lt_of_le_of_ne h.1 hleft.symm, hyx⟩
  · intro hy
    exact ⟨c.interior_subset ⟨hy.1, lt_of_le_of_ne (hy.2.trans hx.2) hright⟩, hy.2⟩

omit [IsFiniteMeasure μ] in
theorem component_prefix_zero (c : Component) {x : ℝ} (hx : x ≤ c.left) :
    prefixMass μ c x = 0 := by
  have heq : c.carrier ∩ Iic x =ᵐ[μ] ∅ := by
    filter_upwards [μ.ae_ne c.left] with y hy
    apply propext
    simp only [mem_empty_iff_false, iff_false, mem_inter_iff, mem_Iic]
    rintro ⟨hc, hyx⟩
    exact hy (le_antisymm (hyx.trans hx) (c.subset_closed hc).1)
  change μ.real (c.carrier ∩ Iic x) = 0
  rw [measureReal_congr heq]
  simp

omit [IsFiniteMeasure μ] [NullSingletonClass μ] in
theorem component_prefix_full (c : Component) {x : ℝ} (hx : c.right ≤ x) :
    prefixMass μ c x = mass μ c := by
  unfold prefixMass mass
  congr 1
  apply inter_eq_left.mpr
  intro y hy
  exact (c.subset_closed hy).2.trans hx

theorem disjoint_domain (c : Component) (cs : List Component)
    (h : ∀ d ∈ cs, Disjoint c.carrier d.carrier) : Disjoint c.carrier (domain cs) := by
  apply Set.disjoint_left.mpr
  intro x hc hx
  obtain ⟨d, hd, hxd⟩ := mem_domain.mp hx
  exact Set.disjoint_left.mp (h d hd) hc hxd

omit [NullSingletonClass μ] in
theorem domain_prefix_sum (cs : List Component) (hdisjoint : DisjointComponents cs) (x : ℝ) :
    μ.real (domain cs ∩ Iic x) = sumValues (fun c => prefixMass μ c x) cs := by
  induction cs with
  | nil => simp [domain, sumValues]
  | cons c cs ih =>
    have hh := List.pairwise_cons.mp hdisjoint
    have hd := disjoint_domain c cs hh.1
    have hd' : Disjoint (c.carrier ∩ Iic x) (domain cs ∩ Iic x) :=
      hd.mono inter_subset_left inter_subset_left
    rw [domain, union_inter_distrib_right, measureReal_union hd'
      ((domain_measurable cs).inter measurableSet_Iic), ih hh.2, sumValues_cons]
    rfl

omit [NullSingletonClass μ] in
theorem domain_mass_sum (cs : List Component) (hdisjoint : DisjointComponents cs) :
    μ.real (domain cs) = sumValues (mass μ) cs := by
  have hp := domain_prefix_sum μ cs hdisjoint 1
  have hi : domain cs ∩ Iic (1 : ℝ) = domain cs := inter_eq_left.mpr
    (fun _ hx => (domain_subset_unit cs hx).2)
  rw [hi] at hp
  rw [hp]
  unfold sumValues
  congr 1
  apply List.map_congr_left
  intro c _
  exact component_prefix_full μ c c.right_le_one

theorem before_after_order (cs : List Component) (hordered : Ordered cs)
    (r : Route Component) (hsplit : cs = r.before ++ r.cell :: r.after) :
    (∀ c ∈ r.before, c.right ≤ r.cell.left) ∧
      (∀ c ∈ r.after, r.cell.right ≤ c.left) := by
  rw [hsplit] at hordered
  have hh := List.pairwise_append.mp hordered
  exact ⟨fun c hc => hh.2.2 c hc r.cell (by simp),
    (List.pairwise_cons.mp hh.2.1).1⟩

/-- The chosen component's local cut equation implies the full physical-domain
prefix equation; all previous components contribute their cached full masses
and all later components contribute zero. -/
theorem routed_root_prefix (cs : List Component) (hordered : Ordered cs)
    (hdisjoint : DisjointComponents cs) (r : Route Component)
    (hsplit : cs = r.before ++ r.cell :: r.after) {x target : ℝ}
    (hx : x ∈ Icc r.cell.left r.cell.right)
    (hcut : μ.real (Ioc r.cell.left x) = target - sumValues (mass μ) r.before) :
    μ.real (domain cs ∩ Iic x) = target := by
  have horder := before_after_order cs hordered r hsplit
  have hbefore : sumValues (fun c => prefixMass μ c x) r.before =
      sumValues (mass μ) r.before := by
    unfold sumValues
    congr 1
    apply List.map_congr_left
    intro c hc
    exact component_prefix_full μ c ((horder.1 c hc).trans hx.1)
  have hafter : sumValues (fun c => prefixMass μ c x) r.after = 0 := by
    apply List.sum_eq_zero
    intro value hvalue
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hvalue
    exact component_prefix_zero μ c (hx.2.trans (horder.2 c hc))
  rw [domain_prefix_sum μ cs hdisjoint, hsplit, sumValues_append,
    sumValues_cons, hbefore, hafter, component_prefix_eq_interval μ r.cell hx, hcut]
  ring

omit [IsFiniteMeasure μ] [NullSingletonClass μ] in
theorem cached_sum_eq (cs : List Component) (cached : Component → ℝ)
    (hcache : ∀ c ∈ cs, cached c = mass μ c) :
    sumValues cached cs = sumValues (mass μ) cs := by
  unfold sumValues
  congr 1
  exact List.map_congr_left hcache

section Queries

open IntervalOracle Chores

def componentQuery {n : ℕ} (cutter : Fin n) (c : Component) (residual : ℝ) :
    IntervalOracle.Query (Fin n) := .cut cutter c.left c.right residual

/-- A cached boundary uses no query. An interior target uses one ordinary Cut
followed by all original observers' endpoint recordings. -/
def executeRoute {n : ℕ} (policy : UpperCircularStage.Policy n)
    (history : UpperCircularStage.History n) (cutter : Fin n)
    (cached : Component → ℝ) (target : ℝ) (r : Route Component) :
    ℝ × UpperCircularStage.History n :=
  let residual := target - sumValues cached r.before
  if residual = cached r.cell then (r.cell.right, history) else
    let query := componentQuery cutter r.cell residual
    let endpoint := policy history query
    (endpoint, UpperCircularStage.executeQueries policy
      (UpperCircularStage.recordings n endpoint) (history ++ [(query, endpoint)]))

def executeDomain {n : ℕ} (policy : UpperCircularStage.Policy n)
    (history : UpperCircularStage.History n) (cutter : Fin n)
    (cached : Component → ℝ) (target : ℝ) (cs : List Component) :
    Option (ℝ × UpperCircularStage.History n) :=
  (locate cached target cs).map (executeRoute policy history cutter cached target)

theorem componentQuery_legal {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (cutter : Fin n) (c : Component) {residual : ℝ}
    (hres0 : 0 ≤ residual) (hres : residual ≤ mass (cost cutter) c) :
    Legal (measureProfile cost) (componentQuery cutter c residual) := by
  have hdiff : (measureProfile cost).cumulative cutter c.right -
      (measureProfile cost).cumulative cutter c.left = mass (cost cutter) c := by
    exact (prefix_difference_eq_interval (cost cutter) c.left_nonneg c.left_le_right).trans
      (component_mass_eq_interval (cost cutter) c).symm
  have hmass : 0 ≤ mass (cost cutter) c := measureReal_nonneg
  change 0 ≤ c.left ∧ c.left ≤ c.right ∧ c.right ≤ 1 ∧
    min 0 ((measureProfile cost).cumulative cutter c.right -
      (measureProfile cost).cumulative cutter c.left) ≤ residual ∧
    residual ≤ max 0 ((measureProfile cost).cumulative cutter c.right -
      (measureProfile cost).cumulative cutter c.left)
  rw [hdiff, min_eq_left hmass, max_eq_right hmass]
  exact ⟨c.left_nonneg, c.left_le_right, c.right_le_one, hres0, hres⟩

theorem executeRoute_spec {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (policy : UpperCircularStage.Policy n)
    (hpolicy : UpperCircularStage.Admissible (measureProfile cost) policy)
    (history : UpperCircularStage.History n) (cutter : Fin n)
    (cached : Component → ℝ) (target : ℝ) (cs : List Component)
    (hordered : Ordered cs) (hdisjoint : DisjointComponents cs)
    (hcache : ∀ c ∈ cs, cached c = mass (cost cutter) c)
    (r : Route Component) (hsplit : cs = r.before ++ r.cell :: r.after)
    (hlow : sumValues cached r.before < target)
    (hhigh : target ≤ sumValues cached r.before + cached r.cell) :
    let endpoint := (executeRoute policy history cutter cached target r).1
    endpoint ∈ Icc r.cell.left r.cell.right ∧
      (cost cutter).real (domain cs ∩ Iic endpoint) = target := by
  have hcell : cached r.cell = mass (cost cutter) r.cell := hcache r.cell (by rw [hsplit]; simp)
  have hbefore : sumValues cached r.before = sumValues (mass (cost cutter)) r.before := by
    apply cached_sum_eq
    intro c hc
    exact hcache c (by rw [hsplit]; exact List.mem_append_left _ hc)
  have hres0 : 0 < target - sumValues cached r.before := by linarith
  have hres : target - sumValues cached r.before ≤ mass (cost cutter) r.cell := by
    rw [← hcell]
    linarith
  by_cases hboundary : target - sumValues cached r.before = cached r.cell
  · simp only [executeRoute, hboundary, ite_true]
    refine ⟨⟨r.cell.left_le_right, le_rfl⟩,
      routed_root_prefix (cost cutter) cs hordered hdisjoint r hsplit
        ⟨r.cell.left_le_right, le_rfl⟩ ?_⟩
    rw [← component_mass_eq_interval (cost cutter) r.cell, ← hcell, ← hboundary, hbefore]
  · let query := componentQuery cutter r.cell (target - sumValues cached r.before)
    have hvalid := hpolicy history query
      (componentQuery_legal cost cutter r.cell hres0.le hres)
    have hloc : policy history query ∈ Icc r.cell.left r.cell.right := hvalid.1
    have hequation : prefixCost (cost cutter) 0 (policy history query) =
        prefixCost (cost cutter) 0 r.cell.left + (target - sumValues cached r.before) := hvalid.2
    have hinter := prefix_difference_eq_interval (cost cutter) r.cell.left_nonneg hloc.1
    have hcut : (cost cutter).real (Ioc r.cell.left (policy history query)) =
        target - sumValues (mass (cost cutter)) r.before := by
      rw [← hbefore]
      linarith
    simp only [executeRoute, hboundary, ite_false]
    exact ⟨hloc, routed_root_prefix (cost cutter) cs hordered hdisjoint r hsplit hloc hcut⟩

theorem executeRoute_query_bound {n : ℕ} (policy : UpperCircularStage.Policy n)
    (history : UpperCircularStage.History n) (cutter : Fin n)
    (cached : Component → ℝ) (target : ℝ) (r : Route Component) :
    (executeRoute policy history cutter cached target r).2.length ≤ history.length + n + 1 := by
  dsimp only [executeRoute]
  split_ifs
  · change history.length ≤ history.length + n + 1
    omega
  · simp only [UpperCircularStage.executeQueries_length, List.length_append,
      List.length_singleton, UpperCircularStage.recordings, List.length_ofFn]
    omega

theorem executeRoute_cut_bound {n : ℕ} (policy : UpperCircularStage.Policy n)
    (history : UpperCircularStage.History n) (cutter : Fin n)
    (cached : Component → ℝ) (target : ℝ) (r : Route Component) :
    ((executeRoute policy history cutter cached target r).2.map Prod.fst).countP
        UpperCircularStage.isCut ≤ (history.map Prod.fst).countP UpperCircularStage.isCut + 1 := by
  dsimp only [executeRoute]
  split_ifs
  · simp
  · simp only [UpperCircularStage.executeQueries_projection, List.map_append, List.map_cons,
      List.map_nil, List.countP_append, UpperCircularStage.recordings_no_cuts,
      List.countP_cons, List.countP_nil, componentQuery, UpperCircularStage.isCut, ite_true]
    omega

/-- One complete cumulative Cut on a recorded finite union is implemented by
the finite cached-mass scan, at most one ordinary individual Cut, and its `n`
observer records. Every admissible history-dependent response policy satisfies
the physical prefix equation. No union-cut oracle appears in the execution. -/
theorem ordinary_union_cut {n : ℕ} (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (policy : UpperCircularStage.Policy n)
    (hpolicy : UpperCircularStage.Admissible (measureProfile cost) policy)
    (history : UpperCircularStage.History n) (cutter : Fin n)
    (cached : Component → ℝ) (target : ℝ) (cs : List Component)
    (hordered : Ordered cs) (hdisjoint : DisjointComponents cs)
    (hcache : ∀ c ∈ cs, cached c = mass (cost cutter) c)
    (htarget : 0 < target) (hbound : target ≤ (cost cutter).real (domain cs)) :
    ∃ endpoint returnedHistory,
      executeDomain policy history cutter cached target cs = some (endpoint, returnedHistory) ∧
      endpoint ∈ Icc (0 : ℝ) 1 ∧
      (cost cutter).real (domain cs ∩ Iic endpoint) = target ∧
      returnedHistory.length ≤ history.length + n + 1 ∧
      (returnedHistory.map Prod.fst).countP UpperCircularStage.isCut ≤
        (history.map Prod.fst).countP UpperCircularStage.isCut + 1 := by
  have hsum : (cost cutter).real (domain cs) = sumValues cached cs := by
    rw [domain_mass_sum (cost cutter) cs hdisjoint, cached_sum_eq (cost cutter) cs cached hcache]
  obtain ⟨r, hroute, hsplit, hlow, hhigh⟩ := locate_spec cached cs target htarget
    (by rwa [← hsum])
  let result := executeRoute policy history cutter cached target r
  have hspec := executeRoute_spec cost policy hpolicy history cutter cached target cs
    hordered hdisjoint hcache r hsplit hlow hhigh
  refine ⟨result.1, result.2, ?_, ?_, hspec.2, ?_, ?_⟩
  · simp [executeDomain, hroute, result]
  · exact ⟨r.cell.left_nonneg.trans hspec.1.1, hspec.1.2.trans r.cell.right_le_one⟩
  · exact executeRoute_query_bound policy history cutter cached target r
  · exact executeRoute_cut_bound policy history cutter cached target r

end Queries

end EnvyFreeResearch.Full.UpperRecordedDomain
