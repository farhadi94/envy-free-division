import EnvyFreeResearch.Full.UpperCorrectionExecution
import Mathlib.Data.List.Sort

/-! Pure assembly of literally disjoint endpoint-owned components.
Only empty carriers are discarded; singleton and zero-value material stay.
Sorting uses both bounds, so singleton ties are placed correctly. -/

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperComponentAssembly

open UpperRecordedDomain UpperDomainDifference UpperCorrectionExecution UpperEndpointCache UpperCircularStage

def before (a b : Component) : Prop :=
  a.left < b.left ∨ (a.left = b.left ∧ a.right ≤ b.right)

instance : Std.Total before := ⟨by
  intro a b
  rcases lt_trichotomy a.left b.left with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total a.right b.right with hr | hr
    · exact Or.inl (Or.inr ⟨h, hr⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hr⟩)
  · exact Or.inr (Or.inl h)⟩

instance : IsTrans Component before := ⟨by
  intro a b c hab hbc
  rcases hab with hab | ⟨hab, habr⟩ <;> rcases hbc with hbc | ⟨hbc, hbcr⟩
  · exact Or.inl (hab.trans hbc)
  · exact Or.inl (hab.trans_eq hbc)
  · exact Or.inl (hab ▸ hbc)
  · exact Or.inr ⟨hab.trans hbc, habr.trans hbcr⟩⟩

def live (c : Component) : Bool := decide c.carrier.Nonempty
def liveComponents (cs : List Component) : List Component := cs.filter live
def assemble (cs : List Component) : List Component := List.insertionSort before (liveComponents cs)

theorem live_iff (c : Component) : live c = true ↔ c.carrier.Nonempty := by simp [live]

theorem nonempty_iff (c : Component) :
    c.carrier.Nonempty ↔ c.left < c.right ∨ c.left ∈ c.carrier := by
  constructor
  · rintro ⟨x, hx⟩
    rcases lt_or_eq_of_le c.left_le_right with h | h
    · exact Or.inl h
    · have hx' : x = c.left := by have hb := c.subset_closed hx; linarith [hb.1, hb.2]
      exact Or.inr (hx' ▸ hx)
  · rintro (h | h)
    · exact ⟨(c.left + c.right) / 2, c.interior_subset (by constructor <;> linarith)⟩
    · exact ⟨c.left, h⟩

theorem domain_perm {cs ds : List Component} (h : cs.Perm ds) : domain cs = domain ds := by
  ext x
  simp only [mem_domain]
  exact exists_congr (fun c => and_congr h.mem_iff Iff.rfl)

theorem live_domain (cs : List Component) : domain (liveComponents cs) = domain cs := by
  ext x
  simp only [mem_domain, liveComponents, List.mem_filter]
  constructor
  · rintro ⟨c, ⟨hc, _⟩, hx⟩
    exact ⟨c, hc, hx⟩
  · rintro ⟨c, hc, hx⟩
    exact ⟨c, ⟨hc, (live_iff c).mpr ⟨x, hx⟩⟩, hx⟩

theorem assemble_domain (cs : List Component) : domain (assemble cs) = domain cs :=
  (domain_perm (List.perm_insertionSort before _)).trans (live_domain cs)

theorem assemble_mem {cs : List Component} {c : Component} (h : c ∈ assemble cs) : c ∈ cs :=
  (List.mem_filter.mp ((List.perm_insertionSort before _).mem_iff.mp h)).1

theorem assemble_live {cs : List Component} {c : Component} (h : c ∈ assemble cs) : c.carrier.Nonempty :=
  (live_iff c).mp (List.mem_filter.mp ((List.perm_insertionSort before _).mem_iff.mp h)).2

theorem before_disjoint_order {a b : Component} (hb : b.carrier.Nonempty)
    (hab : before a b) (hd : Disjoint a.carrier b.carrier) : a.right ≤ b.left := by
  by_contra hn
  have hr : b.left < a.right := lt_of_not_ge hn
  rcases hab with hl | ⟨hl, hright⟩
  · by_cases hdeg : b.left = b.right
    · obtain ⟨x, hx⟩ := hb
      have heq : x = b.left := by have hbnd := b.subset_closed hx; linarith [hbnd.1, hbnd.2]
      exact Set.disjoint_left.mp hd (a.interior_subset (heq ▸ ⟨hl, hr⟩)) hx
    · have hbpos : b.left < b.right := lt_of_le_of_ne b.left_le_right hdeg
      let x := (b.left + min a.right b.right) / 2
      have hxlo : b.left < x := by dsimp only [x]; have := lt_min hr hbpos; linarith
      have hxhi : x < min a.right b.right := by dsimp only [x]; have := lt_min hr hbpos; linarith
      exact Set.disjoint_left.mp hd (a.interior_subset ⟨hl.trans hxlo, hxhi.trans_le (min_le_left _ _)⟩)
        (b.interior_subset ⟨hxlo, hxhi.trans_le (min_le_right _ _)⟩)
  · let x := (b.left + a.right) / 2
    have hlo : b.left < x := by dsimp only [x]; linarith
    have hhi : x < a.right := by dsimp only [x]; linarith
    exact Set.disjoint_left.mp hd (a.interior_subset ⟨hl ▸ hlo, hhi⟩)
      (b.interior_subset ⟨hlo, hhi.trans_le hright⟩)

theorem assemble_disjoint (cs : List Component) (hcs : DisjointComponents cs) :
    DisjointComponents (assemble cs) :=
  (List.perm_insertionSort before (liveComponents cs)).symm.pairwise
    (hcs.filter live) (fun h => h.symm)

theorem assemble_ordered (cs : List Component) (hcs : DisjointComponents cs) : Ordered (assemble cs) := by
  have hs : (assemble cs).Pairwise before := List.pairwise_insertionSort before _
  apply (hs.and (assemble_disjoint cs hcs)).imp_of_mem
  intro a b ha hb hab
  exact before_disjoint_order (assemble_live hb) hab.1 hab.2

theorem domain_append (cs ds : List Component) : domain (cs ++ ds) = domain cs ∪ domain ds := by
  ext x
  simp only [mem_domain, List.mem_append, mem_union]
  aesop

theorem append_disjoint (cs ds : List Component) (hcs : DisjointComponents cs)
    (hds : DisjointComponents ds) (hd : Disjoint (domain cs) (domain ds)) :
    DisjointComponents (cs ++ ds) := by
  apply List.pairwise_append.mpr
  refine ⟨hcs, hds, ?_⟩
  intro c hc d hd'
  exact hd.mono (fun _ hx => mem_domain.mpr ⟨c, hc, hx⟩) (fun _ hx => mem_domain.mpr ⟨d, hd', hx⟩)

theorem assemble_recorded {n : ℕ} (cs : List Component) (history : History n)
    (h : RecordedHistory cs history) : RecordedHistory (assemble cs) history := by
  intro i p hp
  obtain ⟨c, hc, hp⟩ := hp
  exact h i p ⟨c, assemble_mem hc, hp⟩

def state {n : ℕ} (cs : List Component) (history : History n) : State n := ⟨assemble cs, history⟩

theorem state_wellFormed {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, NullSingletonClass (μ i)]
    (cs : List Component) (history : History n) (hd : DisjointComponents cs)
    (ht : Truthful μ history) (hr : RecordedHistory cs history) : WellFormed μ (state cs history) :=
  ⟨assemble_ordered cs hd, assemble_disjoint cs hd, ht, assemble_recorded cs history hr⟩

end EnvyFreeResearch.Full.UpperComponentAssembly
