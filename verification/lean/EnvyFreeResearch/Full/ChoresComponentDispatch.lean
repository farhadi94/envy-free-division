import EnvyFreeResearch.Full.ChoresComponentAssignment

/-! Finite dispatch from actual injective SubCore assignments back to their
original roots. The unused root follows the supplied survivor operation. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.ComponentAssignment
open SubCore
open scoped Classical

variable {Task Root Coord Value : Type*}

def dispatch (out : Allocation Task Root Coord) (survivor : Root → Value)
    (donor : Task → Value) (s : Root) : Value :=
  if h : ∃ j, out.assigned j = s then donor h.choose else survivor s

theorem dispatch_assigned (out : Allocation Task Root Coord) (survivor : Root → Value)
    (donor : Task → Value) (j : Task) : dispatch out survivor donor (out.assigned j) = donor j := by
  have h : ∃ i, out.assigned i = out.assigned j := ⟨j, rfl⟩
  rw [dispatch, dite_eq_left h, out.assigned.injective h.choose_spec]

theorem dispatch_unassigned (out : Allocation Task Root Coord) (survivor : Root → Value)
    (donor : Task → Value) (s : Root) (h : ∀ j, out.assigned j ≠ s) :
    dispatch out survivor donor s = survivor s := by
  rw [dispatch, dite_eq_right (by simpa only [not_exists] using h)]

theorem dispatch_property (out : Allocation Task Root Coord) (survivor : Root → Value)
    (donor : Task → Value) (property : Root → Value → Prop)
    (hs : ∀ s, property s (survivor s))
    (hd : ∀ j, property (out.assigned j) (donor j)) (s : Root) :
    property s (dispatch out survivor donor s) := by
  unfold dispatch
  split
  next h =>
    have hh := hd h.choose
    simpa only [h.choose_spec] using hh
  next _ => exact hs s

end EnvyFreeResearch.Full.Chores.ComponentAssignment
