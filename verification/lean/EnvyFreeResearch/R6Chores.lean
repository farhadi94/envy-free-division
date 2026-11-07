import EnvyFreeResearch.R5ChoreMatching
import EnvyFreeResearch.R5ChoreSchedule

/-!
# Round 6 finite chore refresh and scalar window certificates

This module proves finite cost, counting, floor, and signed block algebra.
Physical prefix restoration, the measure-valued package invariant, continuous
window existence, and complete oracle executions are not formalized here.
-/

namespace EnvyFreeResearch.R6Chores

open scoped BigOperators

section Package

variable {Snapshot : Type*}

/-- Exact own-cost accounting converts a package margin into credit plus signed gaps. -/
theorem package_margin_identity (S : Finset Snapshot) (value baseline : Snapshot → ℝ)
    (own credit : ℝ) (hown : own = (∑ s ∈ S, baseline s)-credit) :
    (∑ s ∈ S, value s)-own = credit + ∑ s ∈ S, (value s-baseline s) := by
  rw [Finset.sum_sub_distrib, hown]
  ring

/-- Covering all negative deficits proves the actual package's nonnegative margin. -/
theorem package_nonnegative_margin (S : Finset Snapshot) (value baseline : Snapshot → ℝ)
    (own credit : ℝ) (hown : own = (∑ s ∈ S, baseline s)-credit)
    (hcredit : (∑ s ∈ S, max 0 (baseline s-value s)) ≤ credit) :
    0 ≤ (∑ s ∈ S, value s)-own := by
  rw [package_margin_identity S value baseline own credit hown]
  have hp := R3ChoreAncestry.surplus_bound S value baseline credit hcredit
  have hz : 0 ≤ ∑ s ∈ S, max 0 (value s-baseline s) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  linarith

/-- A current-root positive surplus survives arbitrary other paid snapshot deficits. -/
theorem package_witness_margin (S : Finset Snapshot) (value baseline : Snapshot → ℝ)
    (own credit threshold : ℝ) (hown : own = (∑ s ∈ S, baseline s)-credit)
    (hcredit : (∑ s ∈ S, max 0 (baseline s-value s)) ≤ credit)
    (w : Snapshot) (hw : w ∈ S) (hwitness : threshold ≤ value w-baseline w) :
    threshold ≤ (∑ s ∈ S, value s)-own := by
  rw [package_margin_identity S value baseline own credit hown]
  exact R3ChoreAncestry.witness_surplus S value baseline credit threshold hcredit
    w hw hwitness

/-- All other closed packages add nonnegative margins to a designated witness. -/
theorem aggregate_witness_margin {Root : Type*} (roots : Finset Root)
    (own other : Root → ℝ) (threshold : ℝ)
    (hEF : ∀ s ∈ roots, own s ≤ other s)
    (w : Root) (hw : w ∈ roots) (hwitness : threshold ≤ other w-own w) :
    threshold ≤ (∑ s ∈ roots, other s)-(∑ s ∈ roots, own s) := by
  rw [← Finset.sum_sub_distrib]
  exact hwitness.trans (Finset.single_le_sum (fun s hs => sub_nonneg.mpr (hEF s hs)) hw)

/-- A finite family of actual snapshot costs proves each refreshed recipient's total margin. -/
theorem terminal_refresh_margin {Root Agent : Type*} [DecidableEq Agent]
    (roots : Finset Root) (owners : Finset Agent) (snapshots : Root → Finset Snapshot)
    (value : Root → Snapshot → Agent → Agent → ℝ)
    (baseline : Root → Snapshot → Agent → ℝ) (own credit : Root → Agent → ℝ)
    (threshold : Agent → ℝ) (designated : Agent → Root) (current : Root → Snapshot)
    (hown : ∀ s ∈ roots, ∀ i, own s i =
      (∑ t ∈ snapshots s, baseline s t i)-credit s i)
    (hcredit : ∀ s ∈ roots, ∀ i j,
      (∑ t ∈ snapshots s, max 0 (baseline s t i-value s t i j)) ≤ credit s i)
    (hroot : ∀ j ∈ owners, designated j ∈ roots)
    (hcurrent : ∀ j ∈ owners, current (designated j) ∈ snapshots (designated j))
    (hwitness : ∀ i ∉ owners, ∀ j ∈ owners,
      threshold i ≤ value (designated j) (current (designated j)) i j -
        baseline (designated j) (current (designated j)) i) :
    ∀ i ∉ owners, ∀ j ∈ owners,
      threshold i ≤ (∑ s ∈ roots, ∑ t ∈ snapshots s, value s t i j)-
        (∑ s ∈ roots, own s i) := by
  intro i hi j hj
  apply aggregate_witness_margin roots (fun s => own s i)
    (fun s => ∑ t ∈ snapshots s, value s t i j) (threshold i)
  · intro s hs
    have h := package_nonnegative_margin (snapshots s) (fun t => value s t i j)
      (fun t => baseline s t i) (own s i) (credit s i) (hown s hs i)
      (hcredit s hs i j)
    linarith
  · exact hroot j hj
  · exact package_witness_margin (snapshots (designated j))
      (fun t => value (designated j) t i j) (fun t => baseline (designated j) t i)
      (own (designated j) i) (credit (designated j) i) (threshold i)
      (hown (designated j) (hroot j hj) i)
      (hcredit (designated j) (hroot j hj) i j)
      (current (designated j)) (hcurrent j hj) (hwitness i hi j hj)

/-- Losing at most n small atoms from a large original gap leaves the stated surplus. -/
theorem retained_root_surplus (n H r original removed : ℝ)
    (hlarge : H*r ≤ original) (hsmall : removed ≤ n*r/H) :
    (H-n/H)*r ≤ original-removed := by
  have hid : (H-n/H)*r = H*r-n*r/H := by ring
  rw [hid]
  linarith

/-- The refreshed margin dominates the full residual budget at the chosen scale. -/
theorem refresh_margin_pays_residue (n H J r : ℝ)
    (hr : 0 ≤ r) (hH : 4 ≤ H) (hJn : J*n^2 ≤ H) (hscale : 4*n ≤ H^2) :
    (1+J*n^2/H)*r ≤ (H-n/H)*r := by
  have hHp : 0 < H := by linarith
  have hprod : 0 ≤ H*(H-4) := mul_nonneg hHp.le (by linarith)
  have hscalar : 1+J*n^2/H ≤ H-n/H := by
    apply (le_of_mul_le_mul_right (a := H) ?_ hHp)
    field_simp
    nlinarith
  exact mul_le_mul_of_nonneg_right hscalar hr

/-- The new terminal margin is enough even if the entire residue were added to the observer. -/
theorem terminal_residue_guard (n H J r own other residue : ℝ)
    (hr : 0 ≤ r) (hH : 4 ≤ H) (hJn : J*n^2 ≤ H) (hscale : 4*n ≤ H^2)
    (hmargin : (H-n/H)*r ≤ other-own)
    (hresidue : residue ≤ (1+J*n^2/H)*r) : own+residue ≤ other := by
  have h := refresh_margin_pays_residue n H J r hr hH hJn hscale
  linarith

end Package

section FiniteSelection

variable {Agent Root : Type*}

/-- Cardinality really supplies distinct live roots, not repeated uses of one package. -/
theorem distinct_refresh_roots (owners : Finset Agent) (exhausted : Finset Root)
    (hcard : owners.card ≤ exhausted.card) : Nonempty (owners ↪ exhausted) := by
  classical
  exact Function.Embedding.nonempty_of_card_le (by simpa using hcard)

/-- Distinct roots and complete visited matchings can be selected simultaneously. -/
theorem distinct_visited_resets (owners : Finset Agent) (exhausted : Finset Root)
    (matchings : Finset (Equiv.Perm Agent)) (p : Agent)
    (hcard : owners.card ≤ exhausted.card)
    (hvisited : ∀ j ∈ owners, ∃ π ∈ matchings, π p=j) :
    ∃ _w : owners ↪ exhausted, ∃ reset : owners → Equiv.Perm Agent,
      ∀ j, reset j ∈ matchings ∧ reset j p=j := by
  classical
  obtain ⟨w⟩ := distinct_refresh_roots owners exhausted hcard
  have hchoose : ∀ j : owners, ∃ π : Equiv.Perm Agent, π ∈ matchings ∧ π p=j := by
    intro j
    exact hvisited j j.property
  choose reset hreset using hchoose
  exact ⟨w, reset, hreset⟩

/-- A common omitted cutter keeps every attained pivot prefix proper. -/
theorem omitted_pivot_prefix [Fintype Agent] [DecidableEq Agent]
    (owners eligible : Finset Agent) (c : Agent) (hprefix : owners ⊆ eligible)
    (homit : c ∉ eligible) : c ∉ owners ∧ owners.card ≤ Fintype.card Agent-1 := by
  have hc : c ∉ owners := fun h => homit (hprefix h)
  refine ⟨hc, ?_⟩
  have hs : owners ⊆ (Finset.univ : Finset Agent).erase c := by
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    subst i
    exact hc hi
  have h := Finset.card_le_card hs
  simpa using h

/-- Only noncutter labels are used in the initial pigeonhole extraction. -/
theorem initial_pivot_extraction [Fintype Agent] [Fintype Root] [DecidableEq Agent]
    (c : Agent) (S : ℕ) (pivot : Root → Agent) (homit : ∀ s, pivot s ≠ c)
    (hpool : (S-1)*(Fintype.card Agent-1) < Fintype.card Root) :
    ∃ p : Agent, p ≠ c ∧ S ≤ (Finset.univ.filter fun s => pivot s=p).card := by
  classical
  let code : Root → {p : Agent // p ≠ c} := fun s => ⟨pivot s, homit s⟩
  have hc : Fintype.card {p : Agent // p ≠ c} = Fintype.card Agent-1 := by
    simp [Fintype.card_subtype_compl]
  have hcount : Fintype.card {p : Agent // p ≠ c}*(S-1) < Fintype.card Root := by
    rw [hc]
    simpa [Nat.mul_comm] using hpool
  obtain ⟨p, hp⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card code hcount
  refine ⟨p, p.property, ?_⟩
  have heq : (Finset.univ.filter fun s => code s=p) =
      (Finset.univ.filter fun s => pivot s=(p : Agent)) := by
    ext s
    simp [code, Subtype.ext_iff]
  rw [heq] at hp
  omega

end FiniteSelection

/-- The two scarce populations are closed before the next-owner pigeonhole. -/
def scarceBudget (n : ℕ) : ℕ := n*n*2^n+(n-1)

theorem scarce_exhausted_bound (n K exhausted : ℕ) (hK : K ≤ n)
    (hscarce : exhausted < K) : exhausted ≤ n-1 := by omega

/-- The new exhausted-root loss adds only n-1 to the inherited large-mask count. -/
theorem combined_scarce_bound (n K exhausted large : ℕ) (hK : K ≤ n)
    (hexhausted : exhausted < K) (hlarge : large ≤ n*2^n*K) :
    exhausted+large ≤ scarceBudget n := by
  have he := scarce_exhausted_bound n K exhausted hK hexhausted
  have hl := R5ChoreSchedule.scarce_large_envelope n K large hK hlarge
  unfold scarceBudget
  omega

/-- The actual mask/next-owner coding supplies the large-population term. -/
theorem scarce_population_from_fibers {LargeRoot : Type*} [Fintype LargeRoot]
    (n K exhausted : ℕ) (hK : K ≤ n) (hexhausted : exhausted < K)
    (code : LargeRoot → R5ChoreSchedule.LargeClass n)
    (hfiber : ∀ c, (Finset.univ.filter fun s => code s=c).card ≤ K) :
    exhausted+Fintype.card LargeRoot ≤ scarceBudget n := by
  exact combined_scarce_bound n K exhausted (Fintype.card LargeRoot) hK hexhausted
    (R5ChoreSchedule.scarce_large_roots n K code hfiber)

def choreScale (n J : ℕ) : ℕ := 2^(n+5)*J*n^3

/-- The actual chosen integer scale supplies substantially more than the quadratic payment. -/
theorem chore_scale_lower (n J : ℕ) (hn : 1 ≤ n) :
    4*J*n*n ≤ choreScale n J := by
  have hp : 1 ≤ (2 : ℕ)^n := one_le_pow₀ (by omega)
  have hpow : 4 ≤ (2 : ℕ)^(n+5) := by
    rw [pow_add]
    norm_num
    omega
  have hcube : n*n ≤ n^3 := by
    calc
      n*n = (n*n)*1 := by omega
      _ ≤ (n*n)*n := Nat.mul_le_mul_left _ hn
      _ = n^3 := by ring
  calc
    4*J*n*n = 4*J*(n*n) := by ring
    _ ≤ (2^(n+5)*J)*(n*n) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right J hpow)
    _ ≤ (2^(n+5)*J)*n^3 := Nat.mul_le_mul_left _ hcube
    _ = choreScale n J := rfl

/-- All three terminal-payment side conditions follow from the declared scale. -/
theorem chore_scale_conditions (n J : ℕ) (hn : 1 ≤ n) (hJ : 1 ≤ J) :
    4 ≤ choreScale n J ∧ J*n*n ≤ choreScale n J ∧
      4*n ≤ (choreScale n J)^2 := by
  have h := chore_scale_lower n J hn
  have hnn : n ≤ n*n := by nlinarith
  have hm := Nat.mul_le_mul_right (n*n) hJ
  have hbase : n ≤ J*n*n := by nlinarith
  have hH : 4 ≤ choreScale n J := by nlinarith
  have hquad : choreScale n J ≤ (choreScale n J)^2 := by nlinarith
  exact ⟨hH, by nlinarith, by nlinarith⟩

/-- Substituting the actual scale discharges every numerical terminal-payment premise. -/
theorem actual_chore_scale_pays_residue (n J : ℕ) (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (r : ℝ) (hr : 0 ≤ r) :
    (1+(J : ℝ)*(n : ℝ)^2/(choreScale n J : ℝ))*r ≤
      ((choreScale n J : ℝ)-(n : ℝ)/(choreScale n J : ℝ))*r := by
  have hc := chore_scale_conditions n J hn hJ
  apply refresh_margin_pays_residue (n : ℝ) (choreScale n J : ℝ) (J : ℝ) r hr
  · exact_mod_cast hc.1
  · have h : J*(n*n) ≤ choreScale n J := by simpa only [Nat.mul_assoc] using hc.2.1
    have hR : (J : ℝ)*((n : ℝ)*(n : ℝ)) ≤ (choreScale n J : ℝ) := by exact_mod_cast h
    simpa only [pow_two] using hR
  · exact_mod_cast hc.2.2

def refreshReserve (n t : ℕ) : ℕ := R5ChoreSchedule.reserve n (scarceBudget n) t

/-- The reserve's base still contains enough distinct roots for all recipients. -/
theorem refresh_reserve_base (n t : ℕ) : n+1 ≤ refreshReserve n t := by
  have hp : 1 ≤ (n+1)^t := one_le_pow₀ (by omega)
  unfold refreshReserve R5ChoreSchedule.reserve
  have hn : n ≤ n*n := by nlinarith
  nlinarith [Nat.zero_le (scarceBudget n)]

/-- The actual two subtractions and integer division preserve the next reserve. -/
theorem refreshed_filter_floor (n t pool exhausted large : ℕ) (hn : 0 < n)
    (hbad : exhausted+large ≤ scarceBudget n)
    (hpool : refreshReserve n (t+1) ≤ pool) :
    refreshReserve n t ≤ (pool-exhausted-large)/n := by
  have h := R5ChoreSchedule.reserve_filter_step n (scarceBudget n) t pool hn hpool
  have hs : pool-scarceBudget n ≤ pool-exhausted-large := by
    rw [Nat.sub_sub]
    exact Nat.sub_le_sub_left hbad pool
  exact h.trans (Nat.div_le_div_right hs)

/-- The inherited induction applies to every legal interleaving at the new budget. -/
theorem refreshed_full_pool_budget (n t : ℕ) (hn : 0 < n)
    (ops : List R5ChoreSchedule.PoolOp)
    (hvalid : ∀ op ∈ ops, op.valid n) (pool : ℕ)
    (hpool : refreshReserve n (R5ChoreSchedule.totalCharge ops+t) ≤ pool) :
    refreshReserve n t ≤ R5ChoreSchedule.runPool n (scarceBudget n) ops pool := by
  exact R5ChoreSchedule.full_pool_budget n (scarceBudget n) t hn ops hvalid pool hpool

section Window

/-- Without a zero or a sign-changing adjacent pair, an initial positive sign persists. -/
theorem positive_block_propagation (f : ℕ → ℝ) (h : ℕ)
    (hzero : ∀ k < h, f k ≠ 0)
    (hstep : ∀ k, k+1 < h → 0 ≤ f k*f (k+1))
    (hfirst : 0 < f 0) : ∀ k < h, 0 < f k := by
  intro k hk
  induction k with
  | zero => exact hfirst
  | succ k ih =>
      have hp : 0 < f k := ih (by omega)
      have hn : 0 ≤ f (k+1) := nonneg_of_mul_nonneg_left
        (by simpa [mul_comm] using hstep k hk) hp
      exact lt_of_le_of_ne hn (Ne.symm (hzero (k+1) hk))

/-- A signed block average yields an exact block or two adjacent values bracketing the target. -/
theorem signed_blocks_exact_or_adjacent (f : ℕ → ℝ) (h : ℕ) (alpha : ℝ)
    (hh : 0 < h) (hsum : (∑ k ∈ Finset.range h, f k)=(h : ℝ)*alpha) :
    (∃ k < h, f k=alpha) ∨
      ∃ k, k+1 < h ∧ (f k-alpha)*(f (k+1)-alpha) < 0 := by
  by_contra hnone
  push Not at hnone
  have hz : ∀ k < h, f k-alpha ≠ 0 := by
    intro k hk heq
    exact hnone.1 k hk (by linarith)
  have hs : ∀ k, k+1 < h → 0 ≤ (f k-alpha)*(f (k+1)-alpha) := by
    intro k hk
    exact hnone.2 k hk
  have hcenter : (∑ k ∈ Finset.range h, (f k-alpha))=0 := by
    simp [Finset.sum_sub_distrib, hsum]
  by_cases hp : 0 < f 0-alpha
  · have hall := positive_block_propagation (fun k => f k-alpha) h hz hs hp
    have hpos : 0 < ∑ k ∈ Finset.range h, (f k-alpha) := by
      apply Finset.sum_pos
      · intro k hk
        exact hall k (Finset.mem_range.mp hk)
      · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hh)
    linarith
  · have hn : 0 < -(f 0-alpha) := by
      have hne := hz 0 hh
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · linarith
      · exact False.elim (hp hgt)
    have hall := positive_block_propagation (fun k => -(f k-alpha)) h
      (fun k hk => neg_ne_zero.mpr (hz k hk))
      (fun k hk => by
        simpa only [neg_mul_neg] using hs k hk) hn
    have hpos : 0 < ∑ k ∈ Finset.range h, -(f k-alpha) := by
      apply Finset.sum_pos
      · intro k hk
        exact hall k (Finset.mem_range.mp hk)
      · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hh)
    rw [Finset.sum_neg_distrib, hcenter] at hpos
    linarith

/-- The adjacent strict certificate implies the nonstrict WindowCut legality inequality. -/
theorem strict_window_bracket_is_legal (a b target : ℝ)
    (hbracket : (a-target)*(b-target) < 0) : (a-target)*(b-target) ≤ 0 :=
  hbracket.le

/-- Adjacent block starts obey the geometric bracket constraints of WindowCut. -/
theorem adjacent_window_geometry (h k : ℕ) (length : ℝ) (hlength : 0 ≤ length)
    (hk : k+1 < h) :
    0 ≤ (k : ℝ)*length ∧ (k : ℝ)*length ≤ ((k : ℝ)+1)*length ∧
      ((k : ℝ)+1)*length ≤ (h : ℝ)*length-length := by
  have hindex : (k : ℝ)+2 ≤ (h : ℝ) := by exact_mod_cast (show k+2 ≤ h by omega)
  have hm := mul_le_mul_of_nonneg_right hindex hlength
  exact ⟨by positivity, by nlinarith, by nlinarith⟩

/-- Removing one equal length/value share preserves both signed residual invariants. -/
theorem remove_equal_window (h length alpha totalLength totalValue : ℝ)
    (hL : totalLength=h*length) (hV : totalValue=h*alpha) :
    totalLength-length=(h-1)*length ∧ totalValue-alpha=(h-1)*alpha := by
  constructor <;> nlinarith

/-- Repeated exact removals leave the claimed multiple even when the value is signed. -/
theorem remaining_after_removals (value : ℕ → ℝ) (n k : ℕ) (alpha : ℝ)
    (hstart : value 0=(n : ℝ)*alpha)
    (hstep : ∀ s < k, value (s+1)=value s-alpha) :
    value k=((n : ℝ)-(k : ℝ))*alpha := by
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
      have hbefore := ih (fun s hs => hstep s (by omega))
      rw [hstep k (by omega), hbefore]
      push_cast
      ring

theorem last_window_share (value : ℕ → ℝ) (n : ℕ) (alpha : ℝ) (hn : 0 < n)
    (hstart : value 0=(n : ℝ)*alpha)
    (hstep : ∀ s < n-1, value (s+1)=value s-alpha) : value (n-1)=alpha := by
  rw [remaining_after_removals value n (n-1) alpha hstart hstep]
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

/-- Equality for public length and one signed spanning row equalizes their linear combination. -/
theorem equal_share_linear_combination (a b total n : ℝ) :
    a*(1/n)+b*(total/n)=(a+b*total)/n := by ring

/-- A finite discrepancy annihilates each balanced spanning coordinate. -/
theorem linear_combination_discrepancy (a b lengthWhole lengthPiece
    valueWhole valuePiece n : ℝ) :
    (a*lengthPiece+b*valuePiece)-(a*lengthWhole+b*valueWhole)/n =
      a*(lengthPiece-lengthWhole/n)+b*(valuePiece-valueWhole/n) := by ring

/-- An observed unequal share refutes a proposed two-coordinate representation on those sets. -/
theorem unequal_share_refutes_span (a b total pieceTotal wholeValue pieceValue n : ℝ)
    (hpiece : pieceTotal=total/n) (hwhole : wholeValue=a+b*total)
    (hrow : pieceValue=a*(1/n)+b*pieceTotal)
    (hunequal : pieceValue ≠ wholeValue/n) : False := by
  apply hunequal
  rw [hrow, hpiece, hwhole]
  exact equal_share_linear_combination a b total n

/-- A perfect finite value table is EF for either maximizing values or minimizing costs. -/
theorem perfect_table_ties {Agent : Type*} (value : Agent → Agent → ℝ)
    (target : Agent → ℝ) (hperfect : ∀ i j, value i j=target i) :
    ∀ i j, value i i=value i j := by
  intro i j
  rw [hperfect i i, hperfect i j]

/-- Prefix caching reconstructs a signed concatenation by actual telescoping. -/
theorem prefix_difference_telescope (cumulative : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, (cumulative (j+1)-cumulative j))=cumulative k-cumulative 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring

def windowEvaluationCount (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n-1), (k+3)

/-- The complete finite sum of cached search and returned-endpoint evaluations. -/
theorem window_eval_sum_aux (k : ℕ) :
    2*(∑ j ∈ Finset.range k, (j+3))=k*(k+5) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      nlinarith

theorem window_eval_count_identity (n : ℕ) (hn : 0 < n) :
    2*windowEvaluationCount n+4=n*n+3*n := by
  have h := window_eval_sum_aux (n-1)
  have hp : n-1+1=n := by omega
  unfold windowEvaluationCount
  nlinarith

theorem window_eval_count_closed (n : ℕ) (hn : 0 < n) :
    windowEvaluationCount n=(n*n+3*n-4)/2 := by
  have h := window_eval_count_identity n hn
  omega

def basicWindowEvals (n : ℕ) : ℕ := n+n*(n-1)+windowEvaluationCount n

/-- Discovery, unknown totals, and extraction have the exact stated ordinary-Eval count. -/
theorem basic_window_eval_identity (n : ℕ) (hn : 0 < n) :
    2*basicWindowEvals n+4=3*n*n+3*n := by
  have h := window_eval_count_identity n hn
  have hp : n-1+1=n := by omega
  unfold basicWindowEvals
  nlinarith

theorem basic_window_eval_closed (n : ℕ) (hn : 0 < n) :
    basicWindowEvals n=(3*n*n+3*n-4)/2 := by
  have h := basic_window_eval_identity n hn
  omega

/-- Auditing all nonanchor rows at the retained boundaries gives the strengthened ledger. -/
theorem audited_window_eval_closed (n : ℕ) (hn : 0 < n) :
    basicWindowEvals n+2*(n-1)^2=n*(7*n-5)/2 := by
  have h := basic_window_eval_identity n hn
  have hp : n-1+1=n := by omega
  have hleft : 2*(basicWindowEvals n+2*(n-1)^2)=n*(7*n-5) := by
    have hs : 7*n-5+5=7*n := by omega
    nlinarith
  omega

/-- Discovery marks and extraction marks have a quadratic introduced-coordinate ledger. -/
theorem introduced_window_coordinate_count (n : ℕ) (hn : 0 < n) :
    n-1+windowEvaluationCount n=(n*n+5*n-6)/2 := by
  have h := window_eval_count_identity n hn
  have hp : n-1+1=n := by omega
  omega

/-- Every removal makes at most one stronger scalar query. -/
theorem window_call_count (n : ℕ) (calls : ℕ → ℕ)
    (hcalls : ∀ k < n-1, calls k ≤ 1) :
    (∑ k ∈ Finset.range (n-1), calls k) ≤ n-1 := by
  simpa using Finset.sum_le_sum (s := Finset.range (n-1))
    (fun k hk => hcalls k (Finset.mem_range.mp hk))

/-- Each removal contributes at most two genuinely new output boundaries. -/
theorem retained_window_boundary_count (n : ℕ) (fresh : ℕ → ℕ)
    (hfresh : ∀ k < n-1, fresh k ≤ 2) :
    (∑ k ∈ Finset.range (n-1), fresh k) ≤ 2*(n-1) := by
  calc
    (∑ k ∈ Finset.range (n-1), fresh k) ≤ ∑ _k ∈ Finset.range (n-1), 2 :=
      Finset.sum_le_sum (fun k hk => hfresh k (Finset.mem_range.mp hk))
    _ = 2*(n-1) := by simp [Nat.mul_comm]

end Window

end EnvyFreeResearch.R6Chores

#print axioms EnvyFreeResearch.R6Chores.terminal_refresh_margin
#print axioms EnvyFreeResearch.R6Chores.distinct_visited_resets
#print axioms EnvyFreeResearch.R6Chores.initial_pivot_extraction
#print axioms EnvyFreeResearch.R6Chores.actual_chore_scale_pays_residue
#print axioms EnvyFreeResearch.R6Chores.refreshed_filter_floor
#print axioms EnvyFreeResearch.R6Chores.refreshed_full_pool_budget
#print axioms EnvyFreeResearch.R6Chores.signed_blocks_exact_or_adjacent
#print axioms EnvyFreeResearch.R6Chores.unequal_share_refutes_span
#print axioms EnvyFreeResearch.R6Chores.audited_window_eval_closed
