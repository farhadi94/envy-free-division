import EnvyFreeResearch.R7Chores
import Mathlib.Data.Nat.Choose.Sum

/-!
# Round 8: finite masked-parent, physical-root and merger certificates

Physical atoms in this file are finite, disjoint records.  The file proves
the restriction and accounting statements on those records; it does not
construct continuous suffixes, run SubCore, or infer queue survival from
a bound on exceptional roots.
-/

noncomputable section

namespace EnvyFreeResearch.R8Chores

open scoped BigOperators
open R7Chores

section Masks

variable {Atom Label Agent : Type*} [DecidableEq Label]

def restriction (label : Atom → Label) (p : Label) (D : Finset Atom) : Finset Atom :=
  D.filter (fun x => label x = p)

def maskedValue (cost : Agent → Atom → ℝ) (label : Atom → Label)
    (i : Agent) (p : Label) (D : Finset Atom) : ℝ :=
  ∑ x ∈ restriction label p D, cost i x

def maskedUtility (cost : Agent → Atom → ℝ) (label : Atom → Label)
    (gap : ℝ) (i : Agent) (p : Label) (D : Finset Atom) : ℝ :=
  clipped (maskedValue cost label i p D - gap)

theorem restriction_subset (label : Atom → Label) (p : Label) (D : Finset Atom) :
    restriction label p D ⊆ D := Finset.filter_subset _ _

theorem restriction_idempotent (label : Atom → Label) (p : Label) (D : Finset Atom) :
    restriction label p (restriction label p D) = restriction label p D := by
  ext x
  simp [restriction]

theorem different_blocks_disjoint (label : Atom → Label) (p q : Label)
    (D E : Finset Atom) (hpq : p ≠ q) :
    Disjoint (restriction label p D) (restriction label q E) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  exact hpq (hx'.symm.trans hy')

/-- Restricting a nominal suffix to its own block preserves its actual masked cost. -/
theorem masked_restriction_value (cost : Agent → Atom → ℝ) (label : Atom → Label)
    (i : Agent) (p : Label) (D : Finset Atom) :
    maskedValue cost label i p (restriction label p D) = maskedValue cost label i p D := by
  unfold maskedValue
  rw [restriction_idempotent]

theorem masked_restriction_utility (cost : Agent → Atom → ℝ) (label : Atom → Label)
    (gap : ℝ) (i : Agent) (p : Label) (D : Finset Atom) :
    maskedUtility cost label gap i p (restriction label p D) =
      maskedUtility cost label gap i p D := by
  unfold maskedUtility
  rw [masked_restriction_value]

/-- The observer's label must equal the donor task's label for this transfer. -/
theorem same_label_comparison (cost : Agent → Atom → ℝ) (label : Atom → Label)
    (ownGap rivalGap : ℝ) (i : Agent) (p : Label) (own rival : Finset Atom)
    (hEF : maskedUtility cost label rivalGap i p rival ≤
      maskedUtility cost label ownGap i p own) :
    clipped ((∑ x ∈ restriction label p rival, cost i x)-rivalGap) ≤
      clipped ((∑ x ∈ restriction label p own, cost i x)-ownGap) := hEF

/-- The whole unused physical root supplies the survivor threshold in the observer's block. -/
theorem unused_root_threshold (cost : Agent → Atom → ℝ) (label : Atom → Label)
    (ownGap unusedGap : ℝ) (i : Agent) (p : Label) (own wholeUnused : Finset Atom)
    (hunused : maskedUtility cost label unusedGap i p wholeUnused ≤
      maskedUtility cost label ownGap i p own) :
    clipped ((∑ x ∈ restriction label p wholeUnused, cost i x)-unusedGap) ≤
      maskedUtility cost label ownGap i p (restriction label p own) := by
  rw [masked_restriction_utility]
  exact hunused

/-- Finite record order: an upper suffix remains an upper suffix inside its own block. -/
theorem restriction_is_relative_suffix [Preorder Atom] (label : Atom → Label)
    (p : Label) (parent D : Finset Atom)
    (hupper : ∀ x ∈ D, ∀ y ∈ parent, x ≤ y → y ∈ D) :
    ∀ x ∈ restriction label p D, ∀ y ∈ restriction label p parent,
      x ≤ y → y ∈ restriction label p D := by
  intro x hx y hy hxy
  rcases Finset.mem_filter.mp hx with ⟨hxD, _⟩
  rcases Finset.mem_filter.mp hy with ⟨hyP, hyL⟩
  exact Finset.mem_filter.mpr ⟨hupper x hxD y hyP hxy, hyL⟩

end Masks

section UniqueObservers

variable {Agent Label : Type*} [Fintype Agent] [DecidableEq Agent] [DecidableEq Label]

omit [Fintype Agent] [DecidableEq Agent] in
/-- Disjoint source components prevent one actual observer from becoming two tasks. -/
theorem task_observer_injective (tasks : Finset (Agent × Label))
    (component : Label → Finset Agent)
    (hmember : ∀ t ∈ tasks, t.1 ∈ component t.2)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (component p) (component q)) :
    Function.Injective (fun t : {t // t ∈ tasks} => t.val.1) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext hxy
  by_contra hlabels
  have hd := Finset.disjoint_left.mp (hdisjoint x.val.2 y.val.2 hlabels)
  have hy := hmember y.val y.property
  change x.val.1 = y.val.1 at hxy
  rw [← hxy] at hy
  exact hd (hmember x.val x.property) hy

omit [DecidableEq Agent] in
theorem task_count_le_agents (tasks : Finset (Agent × Label))
    (component : Label → Finset Agent)
    (hmember : ∀ t ∈ tasks, t.1 ∈ component t.2)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (component p) (component q)) :
    tasks.card ≤ Fintype.card Agent := by
  simpa using Fintype.card_le_of_injective _
    (task_observer_injective tasks component hmember hdisjoint)

end UniqueObservers

section SelectedRoots

variable {Task Root : Type*} [DecidableEq Root]

def selectedRoots (tasks : Finset Task) (root : Task → Root) (survivor : Root) : Finset Root :=
  insert survivor (tasks.image root)

/-- All nominal roots are reserved, independently of which own utilities are positive. -/
theorem nominal_reservation (tasks : Finset Task) (root : Task → Root) (survivor : Root)
    (t : Task) (ht : t ∈ tasks) : root t ∈ selectedRoots tasks root survivor := by
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

theorem selected_root_count (tasks : Finset Task) (root : Task → Root) (survivor : Root)
    (hinj : Function.Injective root) (hfresh : survivor ∉ tasks.image root) :
    (selectedRoots tasks root survivor).card = tasks.card + 1 := by
  rw [selectedRoots, Finset.card_insert_of_notMem hfresh,
    Finset.card_image_of_injective _ hinj]

/-- Exact accounting on the selected roots, with no contribution from merely offered roots. -/
theorem selected_root_sum (tasks : Finset Task) (root : Task → Root) (survivor : Root)
    (value : Root → ℝ) (hinj : Function.Injective root)
    (hfresh : survivor ∉ tasks.image root) :
    ∑ s ∈ selectedRoots tasks root survivor, value s =
      value survivor + ∑ t ∈ tasks, value (root t) := by
  rw [selectedRoots, Finset.sum_insert hfresh, Finset.sum_image]
  intro a _ b _ hab
  exact hinj hab

omit [DecidableEq Root] in
theorem selected_root_budget (selected : Finset Root)
    (deficit reserve credit : Root → ℝ)
    (hbudget : ∀ s ∈ selected, deficit s + reserve s ≤ credit s) :
    (∑ s ∈ selected, deficit s) + (∑ s ∈ selected, reserve s) ≤
      ∑ s ∈ selected, credit s := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hbudget

omit [DecidableEq Root] in
/-- A frozen source contributes its own actual cost identity to the package sum. -/
theorem selected_root_own_identity (selected : Finset Root)
    (own baseline credit : Root → ℝ)
    (hown : ∀ s ∈ selected, own s = baseline s-credit s) :
    (∑ s ∈ selected, own s) =
      (∑ s ∈ selected, baseline s) - (∑ s ∈ selected, credit s) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl hown

end SelectedRoots

section PhysicalMaterial

variable {Root Atom : Type*} [DecidableEq Atom]

/-- Disjoint selected packages contribute exactly their selected physical material once. -/
theorem selected_physical_material_sum (selected : Finset Root)
    (material : Root → Finset Atom) (cost : Atom → ℝ)
    (hdisjoint : Set.PairwiseDisjoint (↑selected) material) :
    ∑ x ∈ selected.biUnion material, cost x =
      ∑ s ∈ selected, ∑ x ∈ material s, cost x := by
  exact Finset.sum_biUnion hdisjoint

/-- The physical complementary prefix realizes the affine credit with the original offset. -/
theorem physical_prefix_credit (parent removed : Finset Atom) (cost : Atom → ℝ)
    (baseline : ℝ) (hsubset : removed ⊆ parent) :
    baseline-(∑ x ∈ parent \ removed, cost x) =
      (∑ x ∈ removed, cost x)-((∑ x ∈ parent, cost x)-baseline) := by
  rw [Finset.sum_sdiff_eq_sub hsubset]
  ring

/-- Positive clipped credit equals the actual physical own-cost reduction. -/
theorem positive_physical_credit (parent removed : Finset Atom) (cost : Atom → ℝ)
    (baseline : ℝ) (hsubset : removed ⊆ parent)
    (hpositive : 0 < clipped ((∑ x ∈ removed, cost x)-
      ((∑ x ∈ parent, cost x)-baseline))) :
    baseline-(∑ x ∈ parent \ removed, cost x) =
      clipped ((∑ x ∈ removed, cost x)-((∑ x ∈ parent, cost x)-baseline)) := by
  rw [physical_prefix_credit parent removed cost baseline hsubset,
    positive_clipped_exact _ hpositive]

end PhysicalMaterial

section Queues

variable {Root Class Agent : Type*} [DecidableEq Root] [DecidableEq Agent]

/-- Consuming one physical root removes all of its advertisements simultaneously. -/
theorem queue_union_after_consumption (classes : Finset Class) (queue : Class → Finset Root)
    (consumed : Finset Root) :
    classes.biUnion (fun c => queue c \ consumed) =
      (classes.biUnion queue) \ consumed := by
  ext r
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨c, hc, hr, hn⟩
    exact ⟨⟨c, hc, hr⟩, hn⟩
  · rintro ⟨⟨c, hc, hr⟩, hn⟩
    exact ⟨c, hc, hr, hn⟩

theorem exceptional_root_union_count (classes : Finset Class)
    (exceptional : Class → Finset Root) (bound : Class → ℕ)
    (hbound : ∀ c ∈ classes, (exceptional c).card ≤ bound c) :
    (classes.biUnion exceptional).card ≤ ∑ c ∈ classes, bound c := by
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum hbound)

omit [DecidableEq Agent] in
theorem queue_top_root_count (components : Finset (Finset Agent))
    (top : Finset Agent → Agent → Finset Root) (k : ℕ)
    (hbound : ∀ C ∈ components, ∀ i ∈ C, (top C i).card ≤ k) :
    (components.biUnion (fun C => C.biUnion (top C))).card ≤
      k * ∑ C ∈ components, C.card := by
  calc
    _ ≤ ∑ C ∈ components, (C.biUnion (top C)).card := Finset.card_biUnion_le
    _ ≤ ∑ C ∈ components, C.card * k := by
      apply Finset.sum_le_sum
      intro C hC
      exact Finset.card_biUnion_le_card_mul C (top C) k (hbound C hC)
    _ = k * ∑ C ∈ components, C.card := by rw [← Finset.sum_mul, Nat.mul_comm]

omit [DecidableEq Agent] in
theorem powerset_total_memberships (agents : Finset Agent) :
    ∑ C ∈ agents.powerset, C.card = agents.card * 2^(agents.card-1) := by
  calc
    _ = ∑ k ∈ Finset.range (agents.card+1), agents.card.choose k * k := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_powerset_apply_card (f := fun k : ℕ => k) (x := agents))
    _ = _ := by simpa only [Nat.mul_comm] using Nat.sum_range_mul_choose agents.card

omit [DecidableEq Agent] in
theorem all_component_top_count (agents : Finset Agent)
    (top : Finset Agent → Agent → Finset Root) (k : ℕ)
    (hbound : ∀ C ∈ agents.powerset, ∀ i ∈ C, (top C i).card ≤ k) :
    (agents.powerset.biUnion (fun C => C.biUnion (top C))).card ≤
      k * agents.card * 2^(agents.card-1) := by
  have h := queue_top_root_count agents.powerset top k hbound
  rw [powerset_total_memberships] at h
  simpa [Nat.mul_assoc] using h

/-- Distinct high roots survive removal of previously reserved physical roots. -/
theorem high_roots_after_reservation (high reserved : Finset Root) (n d : ℕ)
    (hhigh : n+1 ≤ high.card) (hreserved : reserved.card+d ≤ n) :
    d+1 ≤ (high \ reserved).card := by
  have hs : high ⊆ (high \ reserved) ∪ reserved := by
    intro x hx
    by_cases hr : x ∈ reserved
    · exact Finset.mem_union_right _ hr
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hr⟩)
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  omega

end Queues

inductive MergeTree where
  | leaf
  | join (left right : MergeTree)
  deriving DecidableEq

def MergeTree.leaves : MergeTree → ℕ
  | .leaf => 1
  | .join left right => left.leaves + right.leaves

def MergeTree.smallSideProduct : MergeTree → ℕ
  | .leaf => 1
  | .join left right =>
      (min left.leaves right.leaves+1) * left.smallSideProduct * right.smallSideProduct

theorem merge_tree_leaves_positive (tree : MergeTree) : 1 ≤ tree.leaves := by
  induction tree with
  | leaf => rfl
  | join left right ihl ihr => simp only [MergeTree.leaves]; omega

/-- This is the actual numerical induction step, not a physical smaller-side-payment claim. -/
theorem smaller_side_step (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (min a b+1)*(a+b) ≤ 4*a*b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    have h1 : a+1 ≤ 2*a := by omega
    have h2 : a+b ≤ 2*b := by omega
    calc
      _ ≤ (2*a)*(2*b) := Nat.mul_le_mul h1 h2
      _ = _ := by ring
  · rw [min_eq_right hba]
    have h1 : b+1 ≤ 2*b := by omega
    have h2 : a+b ≤ 2*a := by omega
    calc
      _ ≤ (2*b)*(2*a) := Nat.mul_le_mul h1 h2
      _ = _ := by ring

/-- Every binary tree satisfies product(min(child sizes)+1) ≤ 4^(n-1)/n. -/
theorem smaller_side_tree_product (tree : MergeTree) :
    tree.smallSideProduct * tree.leaves ≤ 4^(tree.leaves-1) := by
  induction tree with
  | leaf => norm_num [MergeTree.smallSideProduct, MergeTree.leaves]
  | join left right ihl ihr =>
    have hl := merge_tree_leaves_positive left
    have hr := merge_tree_leaves_positive right
    have hstep := smaller_side_step left.leaves right.leaves hl hr
    have hexp : left.leaves+right.leaves-1 = 1+(left.leaves-1)+(right.leaves-1) := by omega
    simp only [MergeTree.smallSideProduct, MergeTree.leaves]
    calc
      _ = ((min left.leaves right.leaves+1)*(left.leaves+right.leaves))*
          (left.smallSideProduct*right.smallSideProduct) := by ring
      _ ≤ (4*left.leaves*right.leaves)*(left.smallSideProduct*right.smallSideProduct) :=
        Nat.mul_le_mul_right _ hstep
      _ = 4*(left.smallSideProduct*left.leaves)*(right.smallSideProduct*right.leaves) := by ring
      _ ≤ 4*4^(left.leaves-1)*4^(right.leaves-1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 ihl) ihr
      _ = 4^(left.leaves+right.leaves-1) := by rw [hexp, pow_add, pow_add]; norm_num

/-! The next tree records only the selected children in a particular queue
architecture: a size-(k+1) package consumes k+1 disjoint size-k packages.
It is not asserted that every chore protocol must have this architecture. -/

inductive CohortTree (Root : Type*) : ℕ → Type _ where
  | base (root : Root) : CohortTree Root 2
  | step {k : ℕ} (children : Fin (k+1) → CohortTree Root k) : CohortTree Root (k+1)

def CohortTree.leafOccurrences {Root : Type*} : {k : ℕ} → CohortTree Root k → ℕ
  | _, .base _ => 1
  | _, .step children => ∑ j, (children j).leafOccurrences

def CohortTree.physicalRoots {Root : Type*} [DecidableEq Root] :
    {k : ℕ} → CohortTree Root k → Finset Root
  | _, .base root => {root}
  | _, .step children => Finset.univ.biUnion (fun j => (children j).physicalRoots)

def CohortTree.DistinctLeaves {Root : Type*} [DecidableEq Root] :
    {k : ℕ} → CohortTree Root k → Prop
  | _, .base _ => True
  | _, .step children =>
      (∀ j, (children j).DistinctLeaves) ∧
      Set.PairwiseDisjoint Set.univ (fun j => (children j).physicalRoots)

/-- The full-arity selected witness tree has exactly k!/2 leaf occurrences. -/
theorem cohort_tree_factorial {Root : Type*} {k : ℕ} (tree : CohortTree Root k) :
    2*tree.leafOccurrences = k.factorial := by
  induction tree with
  | base root => norm_num [CohortTree.leafOccurrences]
  | @step k children ih =>
    simp only [CohortTree.leafOccurrences, Finset.mul_sum]
    calc
      _ = ∑ _j : Fin (k+1), k.factorial := Finset.sum_congr rfl (fun j _ => ih j)
      _ = (k+1)*k.factorial := by simp
      _ = _ := (Nat.factorial_succ k).symm

/-- Recursive disjointness turns occurrences into actual distinct original roots. -/
theorem cohort_distinct_root_count {Root : Type*} [DecidableEq Root] {k : ℕ}
    (tree : CohortTree Root k) (hdistinct : tree.DistinctLeaves) :
    tree.physicalRoots.card = tree.leafOccurrences := by
  induction tree with
  | base root => simp [CohortTree.physicalRoots, CohortTree.leafOccurrences]
  | @step k children ih =>
    rcases hdistinct with ⟨hchildren, hpairwise⟩
    have hp : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (k+1))))
        (fun j => (children j).physicalRoots) := by
      simpa only [Finset.coe_univ] using hpairwise
    simp only [CohortTree.physicalRoots, CohortTree.leafOccurrences]
    rw [Finset.card_biUnion hp]
    exact Finset.sum_congr rfl (fun j _ => ih j (hchildren j))

/-- Extra donors can enlarge a package, but cannot erase its disjoint selected ancestry. -/
theorem selected_cohort_ancestry_lower {Root : Type*} [DecidableEq Root] {k : ℕ}
    (tree : CohortTree Root k) (actualRoots : Finset Root)
    (hdistinct : tree.DistinctLeaves) (hsubset : tree.physicalRoots ⊆ actualRoots) :
    k.factorial ≤ 2*actualRoots.card := by
  have hc := Finset.card_le_card hsubset
  rw [cohort_distinct_root_count tree hdistinct] at hc
  rw [← cohort_tree_factorial tree]
  exact Nat.mul_le_mul_left 2 hc

section ProtectedBases

/-- The permanent secondary label makes the protected base strictly earlier even at zero cost. -/
theorem protected_base_formal_gap (baseCost capCost : ℝ) (hcost : baseCost ≤ capCost) :
    toLex (baseCost, (1:ℝ)/2) < toLex (capCost, (1:ℝ)) := by
  apply Prod.Lex.toLex_lt_toLex'.mpr
  exact ⟨hcost, fun _ => by norm_num⟩

/-- Formal EF of a whole-parent holder forces actual protected-prefix containment. -/
theorem protected_base_containment {Parent Atom : Type*} {Record : Parent → Type*}
    [∀ p, LinearOrder (Record p)]
    (value : (p : Parent) → Record p → ℝ ×ₗ ℝ)
    (piece : (p : Parent) → Record p → Finset Atom)
    (base assigned : (p : Parent) → Record p) (baseCost : Parent → ℝ) (capCost : ℝ)
    (hstrict : ∀ p, StrictMono (value p))
    (hphysical : ∀ p, Monotone (piece p))
    (hbase : ∀ p, value p (base p) = toLex (baseCost p, (1:ℝ)/2))
    (hcap : ∀ p, baseCost p ≤ capCost)
    (hEF : ∀ p, toLex (capCost, (1:ℝ)) ≤ value p (assigned p)) :
    ∀ p, piece p (base p) ⊆ piece p (assigned p) := by
  intro p
  have hv : value p (base p) < value p (assigned p) := by
    rw [hbase p]
    exact (protected_base_formal_gap (baseCost p) capCost (hcap p)).trans_le (hEF p)
  have hr : base p < assigned p := (hstrict p).lt_iff_lt.mp hv
  exact hphysical p hr.le

/-- Two prepared color pieces dominate every protected base, including zero-total rows. -/
theorem balanced_cap_dominates_base (total k first second baseCost : ℝ)
    (htotal : 0 ≤ total) (hk : 0 < k)
    (hfirst : 3*total/(8*k) ≤ first) (hsecond : 3*total/(8*k) ≤ second)
    (hbase : baseCost ≤ 5*total/(8*k)) : baseCost ≤ first+second := by
  have hden : 0 < 8*k := by positivity
  have ha := (div_le_iff₀ hden).mp hfirst
  have hb := (div_le_iff₀ hden).mp hsecond
  have hc := (le_div_iff₀ hden).mp hbase
  apply (mul_le_mul_iff_left₀ hden).mp
  nlinarith

/-- The protected base's quota survives its literal physical inclusion in the assigned prefix. -/
theorem protected_base_cost_quota {Atom : Type*} (cost : Atom → ℝ)
    (hnonnegative : ∀ x, 0 ≤ cost x) (base assigned : Finset Atom) (quota : ℝ)
    (hsubset : base ⊆ assigned) (hquota : quota ≤ ∑ x ∈ base, cost x) :
    quota ≤ ∑ x ∈ assigned, cost x := by
  exact hquota.trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x _ _ => hnonnegative x))

theorem protected_quota_suffices (total k alpha : ℝ)
    (htotal : 0 ≤ total) (hk : 0 < k) (halpha : 0 < alpha)
    (hscale : 8*k ≤ 3*alpha) : total/alpha ≤ 3*total/(8*k) := by
  have hden : 0 < 8*k := by positivity
  apply (div_le_div_iff₀ halpha hden).mpr
  nlinarith [mul_nonneg htotal (sub_nonneg.mpr hscale)]

/-- The preparation uses K=16rk, giving the advertised finite rounding discrepancy. -/
theorem protected_grid_discrepancy (r k : ℝ) (hr : 0 < r) (hk : 0 < k) :
    2*r/(16*r*k) = 1/(8*k) := by
  field_simp [ne_of_gt hr, ne_of_gt hk]
  ring

theorem protected_color_interval (k : ℝ) (hk : 0 < k) :
    1/(2*k)-1/(8*k) = 3/(8*k) ∧ 1/(2*k)+1/(8*k) = 5/(8*k) := by
  constructor <;> field_simp [ne_of_gt hk] <;> ring

end ProtectedBases

end EnvyFreeResearch.R8Chores
