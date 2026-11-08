import EnvyFreeResearch.Full.ChoresTrackedTable
import Mathlib.Combinatorics.Pigeonhole

/-! The protected noncutter label is extracted from the actual original
snapshots and their final residual domain. The color of a snapshot is
chosen from cached original gaps; no oracle access or valuation-dependent
choice is used by this finite selection. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Snapshot
open Set MeasureTheory OrderedUnion InitialPartition

variable {n : ℕ} {cost : Fin n → Measure ℝ}
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

theorem Chain.member_residue {U : Set ℝ} {c : Fin n} {xs : List (Output n)}
    {cache : List (Parent n)} (chain : Chain cost c U xs cache)
    (out : Output n) (hm : out ∈ xs) :
    ∃ domain, Sound cost domain c out ∧ material cache ⊆ domainResidue domain out.outcome := by
  induction chain with
  | nil _ _ _ => cases hm
  | @cons U first rest cache hfirst hrest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨U,hfirst,hrest.subsets.2⟩
    · exact ih hm

theorem Chain.noncutters_gap (hn : 2 ≤ n) {U R : Set ℝ} {c : Fin n}
    {xs : List (Output n)} {cache : List (Parent n)} (chain : Chain cost c U xs cache)
    (hR : R ⊆ material cache) (hr : 0 < (cost c).real R)
    (out : Output n) (hm : out ∈ xs) :
    ∃ p, p ≠ c ∧ (cost c).real R/(n-1 : ℕ) ≤ Clearance.gap out c p := by
  obtain ⟨domain,hsound,hrest⟩ := chain.member_residue out hm
  obtain ⟨p,hgap⟩ := hsound.core.2.2.2.2.2
  have hden : (0 : ℝ) < (n-1 : ℕ) := by exact_mod_cast (by omega : 0 < n-1)
  have hbound : (cost c).real R/(n-1 : ℕ) ≤ Clearance.gap out c p := by
    rw [Clearance.gap_physical hsound,hsound.piece_eq,hsound.piece_eq]
    exact (div_le_div_of_nonneg_right (measureReal_mono (hR.trans hrest)) hden.le).trans hgap
  refine ⟨p,?_,hbound⟩
  intro hpc
  subst p
  have hz : Clearance.gap out c c = 0 := by simp [Clearance.gap]
  rw [hz] at hbound
  exact (not_le_of_gt (div_pos hr hden)) hbound

end EnvyFreeResearch.Full.Chores.Snapshot

namespace EnvyFreeResearch.Full.Chores.ProtectedPivot
open Set MeasureTheory OrderedUnion InitialPartition Snapshot Clearance
open scoped Classical

def color {n : ℕ} (c : Fin n) (r : ℝ) (out : Snapshot.Output n) : Fin n :=
  ((List.finRange n).find? (fun p => decide (p ≠ c ∧ r/(n-1 : ℕ) ≤ gap out c p))).getD c

theorem color_correct {n : ℕ} (c : Fin n) (r : ℝ) (out : Snapshot.Output n)
    (hwitness : ∃ p, p ≠ c ∧ r/(n-1 : ℕ) ≤ gap out c p) :
    color c r out ≠ c ∧ r/(n-1 : ℕ) ≤ gap out c (color c r out) := by
  cases hf : (List.finRange n).find? (fun p => decide (p ≠ c ∧ r/(n-1 : ℕ) ≤ gap out c p)) with
  | none =>
    obtain ⟨p,hp⟩ := hwitness
    have hnot := List.find?_eq_none.mp hf p (List.mem_finRange p)
    exact (hnot (by simpa only [decide_eq_true_eq] using hp)).elim
  | some p =>
    have hp : p ≠ c ∧ r/(n-1 : ℕ) ≤ gap out c p := by
      simpa only [decide_eq_true_eq] using List.find?_some hf
    simpa only [color,hf,Option.getD_some] using hp

theorem common_omitted_label {n : ℕ} (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    {U R : Set ℝ} (c : Fin n) (xs : List (Snapshot.Output n)) (cache : List (Parent n))
    (chain : Chain cost c U xs cache) (hR : R ⊆ material cache) (hr : 0 < (cost c).real R)
    (H : ℝ) (hH : (n-1 : ℕ) < H) (S : ℕ)
    (hcount : (S-1)*(n-1) < xs.length) :
    ∃ p : Fin n, p ≠ c ∧ ∃ selected : Finset (Fin xs.length), S ≤ selected.card ∧
      ∀ s ∈ selected, (cost c).real R/H < gap (xs.get s) c p := by
  let paint : Fin xs.length → Fin n := fun s => color c ((cost c).real R) (xs.get s)
  have hp (s : Fin xs.length) : paint s ≠ c ∧ (cost c).real R/(n-1 : ℕ) ≤ gap (xs.get s) c (paint s) :=
    color_correct c _ _ (chain.noncutters_gap hn hR hr _ (List.get_mem _ _))
  have hmaps : ∀ s ∈ (Finset.univ : Finset (Fin xs.length)), paint s ∈ Finset.univ.erase c := by
    intro s _
    exact Finset.mem_erase.mpr ⟨(hp s).1,Finset.mem_univ _⟩
  have hcard : (Finset.univ.erase c).card*(S-1) < (Finset.univ : Finset (Fin xs.length)).card := by
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ c),Finset.card_univ,Fintype.card_fin,
      Nat.mul_comm] using hcount
  obtain ⟨p,hpnot,hfiber⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  refine ⟨p,(Finset.mem_erase.mp hpnot).1,Finset.univ.filter (fun s => paint s=p),by omega,?_⟩
  intro s hs
  have heq := (Finset.mem_filter.mp hs).2
  have hden : (0 : ℝ) < (n-1 : ℕ) := by exact_mod_cast (by omega : 0 < n-1)
  have hstrict : (cost c).real R/H < (cost c).real R/(n-1 : ℕ) :=
    div_lt_div_of_pos_left hr hden hH
  exact hstrict.trans_le (heq ▸ (hp s).2)

def eligible {n : ℕ} (out : Snapshot.Output n) (H : ℝ) (r : Fin n → ℝ)
    (p : Fin n) : Finset (Fin n) := Finset.univ.filter (fun i => gap out i p ≤ r i/H)

theorem owner_eligible {n : ℕ} (out : Snapshot.Output n) (H : ℝ) (hH : 0 < H)
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (p : Fin n) : p ∈ eligible out H r p := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ p,?_⟩
  simpa only [gap,sub_self] using div_nonneg (hr p) hH.le

theorem common_omitted_exact {n : ℕ} (hn : 2 ≤ n) (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    {U R : Set ℝ} (c : Fin n) (xs : List (Snapshot.Output n)) (cache : List (Parent n))
    (chain : Chain cost c U xs cache) (hR : R ⊆ material cache) (hr : 0 < (cost c).real R)
    (H : ℝ) (hH : (n-1 : ℕ) < H) (S : ℕ)
    (hcount : (S-1)*(n-1) < xs.length) :
    ∃ p : Fin n, p ≠ c ∧ ∃ selected : Finset (Fin xs.length), selected.card = S ∧
      ∀ s ∈ selected, c ∉ eligible (xs.get s) H (fun i => (cost i).real R) p := by
  obtain ⟨p,hpc,selected,hcard,hgap⟩ := common_omitted_label hn cost c xs cache chain hR hr H hH S hcount
  obtain ⟨chosen,hsub,hsize⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨p,hpc,chosen,hsize,?_⟩
  intro s hs hc
  exact (not_le_of_gt (hgap s (hsub hs))) (Finset.mem_filter.mp hc).2

end EnvyFreeResearch.Full.Chores.ProtectedPivot
