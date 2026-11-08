import EnvyFreeResearch.Full.UpperInitialState
import EnvyFreeResearch.Full.UpperPendingExclusion
import EnvyFreeResearch.Full.UpperAggregateInterpolationSupported

/-! A literal virtual domain for pending logical-cell exclusion. Its only
boundaries are immutable grid coordinates, independent of all old physical
joins in the reserve. -/

noncomputable section

open Set
open scoped Classical

namespace EnvyFreeResearch.Full.UpperVirtualGrid

open UpperRecordedDomain UpperDomainDifference UpperLogicalCells UpperGridCells UpperGridRecords
  UpperCorrectionExecution UpperWholePaymentsPhysical UpperAggregateInterpolation

variable {m n : ℕ} {Agent : Type*} [Fintype Agent]

def atoms (cuts : Fin (m + 2) → ℝ) : List Component :=
  refineEndpoints [UpperInitialState.unitComponent] (List.ofFn cuts)

theorem atoms_domain (cuts : Fin (m + 2) → ℝ) : domain (atoms cuts) = Icc (0 : ℝ) 1 := by
  rw [atoms, refineEndpoints_domain]
  simp [domain, UpperInitialState.unitComponent]

theorem atoms_disjoint (cuts : Fin (m + 2) → ℝ) : DisjointComponents (atoms cuts) :=
  refineEndpoints_disjoint _ _ (by simp [DisjointComponents])

theorem atoms_ordered (cuts : Fin (m + 2) → ℝ) : Ordered (atoms cuts) :=
  refineEndpoints_ordered _ _ (by simp [Ordered])

theorem atoms_separated (cuts : Fin (m + 2) → ℝ) (e : Fin (m + 2)) :
    SeparatedAt (cuts e) (atoms cuts) :=
  refineEndpoints_separated _ _ (List.mem_ofFn.mpr ⟨e, rfl⟩)

theorem atoms_recorded (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0)
    (hone : cuts (Fin.last (m + 1)) = 1) {p : ℝ} (hp : Recorded (atoms cuts) p) :
    ∃ e, cuts e = p := by
  rcases refineEndpoints_recorded _ _ hp with hp | hp
  · obtain ⟨c, hc, hp⟩ := hp
    have hc' : c = UpperInitialState.unitComponent := List.mem_singleton.mp hc
    subst c
    rcases hp with hp | hp
    · exact ⟨0, hzero.trans hp.symm⟩
    · exact ⟨Fin.last (m + 1), hone.trans hp.symm⟩
  · exact List.mem_ofFn.mp hp

def initial (cuts : Fin (m + 2) → ℝ) (owned : Agent → Finset (Fin (m + 1))) : List Component :=
  (atoms cuts).filter (fun c => !UpperPendingExclusion.selected cuts owned c)

theorem initial_domain (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (owned : Agent → Finset (Fin (m + 1))) :
    domain (initial cuts owned) = Icc (0 : ℝ) 1 \ ⋃ j, piece (cell (Icc 0 1) cuts) owned j := by
  have h := UpperPendingExclusion.remove_domain (⟨atoms cuts, []⟩ : State 0)
    (atoms_disjoint cuts) cuts hzero hmono (atoms_separated cuts) owned
  simpa only [UpperPendingExclusion.remove, atoms_domain, initial] using h

theorem initial_recorded (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0)
    (hone : cuts (Fin.last (m + 1)) = 1) (owned : Agent → Finset (Fin (m + 1)))
    {p : ℝ} (hp : Recorded (initial cuts owned) p) : ∃ e, cuts e = p := by
  obtain ⟨c, hc, hp⟩ := hp
  exact atoms_recorded cuts hzero hone ⟨c, (List.mem_filter.mp hc).1, hp⟩

theorem logicalCell_unit_inter (R : Set ℝ) (hR : R ⊆ Icc 0 1)
    (cuts : Fin (m + 2) → ℝ) (e : Fin (m + 1)) :
    cell R cuts e = R ∩ cell (Icc 0 1) cuts e := by
  rw [logicalCell_inter, logicalCell_inter]
  ext x
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hx, hR hx, he⟩
  · rintro ⟨hx, _, he⟩
    exact ⟨hx, he⟩

theorem piece_unit_inter (R : Set ℝ) (hR : R ⊆ Icc 0 1)
    (cuts : Fin (m + 2) → ℝ) (owned : Agent → Finset (Fin (m + 1))) (j : Agent) :
    piece (cell R cuts) owned j = R ∩ piece (cell (Icc 0 1) cuts) owned j := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, hxe⟩ := (mem_piece _ _ _ _).mp hx
    rw [logicalCell_unit_inter R hR cuts e] at hxe
    exact ⟨hxe.1, (mem_piece _ _ _ _).mpr ⟨e, he, hxe.2⟩⟩
  · rintro ⟨hxR, hx⟩
    obtain ⟨e, he, hxe⟩ := (mem_piece _ _ _ _).mp hx
    apply (mem_piece _ _ _ _).mpr
    refine ⟨e, he, ?_⟩
    rw [logicalCell_unit_inter R hR cuts e]
    exact ⟨hxR, hxe⟩

/-- The physical start state is the reserve intersected with the constructed
virtual start. Endpoint ownership is literal, not an a.e. equivalence. -/
theorem physical_initial_inter (state : State n) (hdis : DisjointComponents state.cells)
    (cuts : Fin (m + 2) → ℝ) (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hsep : ∀ e, SeparatedAt (cuts e) state.cells) (owned : Agent → Finset (Fin (m + 1))) :
    domain (UpperPendingExclusion.remove state cuts owned).cells =
      domain state.cells ∩ domain (initial cuts owned) := by
  rw [UpperPendingExclusion.remove_domain state hdis cuts hzero hmono hsep owned,
    initial_domain cuts hzero hmono owned]
  have hR := domain_subset_unit state.cells
  simp_rw [piece_unit_inter (domain state.cells) hR cuts owned]
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, hR hx, ?_⟩
    intro hxU
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxU
    exact hnot (mem_iUnion.mpr ⟨j, hx, hj⟩)
  · rintro ⟨hx, _, hnot⟩
    refine ⟨hx, ?_⟩
    intro hxU
    obtain ⟨j, _, hj⟩ := mem_iUnion.mp hxU
    exact hnot (mem_iUnion.mpr ⟨j, hj⟩)

end EnvyFreeResearch.Full.UpperVirtualGrid
