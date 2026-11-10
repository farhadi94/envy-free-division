import EnvyFreeResearch.Full.MoatDetection
import EnvyFreeResearch.Full.MoatFamily

/-! A uniform observer and its cyclic successor give the two-row hard
family. No conditioning or random choice among unordered pairs is needed. -/
noncomputable section
namespace EnvyFreeResearch.Full.MoatSelection
open Set MeasureTheory NonnegativeDetection MoatDetection
open scoped Classical ENNReal
abbrev Circle := NonnegativeCircle.Circle
abbrev Input (n : ℕ) := Fin n × Circle

def selected {n : ℕ} (two : Bool) (i : Fin n) : Finset (Fin n) :=
  if two then {i, finRotate n i} else {i}

def toFamily {n : ℕ} (two : Bool) (input : Input n) : MoatFamily.Input n :=
  (selected two input.1,input.2)

theorem toFamily_measurable {n : ℕ} (two : Bool) : Measurable (toFamily (n := n) two) :=
  ((measurable_of_countable (selected two)).comp measurable_fst).prodMk measurable_snd

theorem rotate_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have hrep : n=m+1+1 := by omega
  clear hm
  subst n
  by_cases hi : i = Fin.last (m+1)
  · subst i
    rw [finRotate_last]
    intro heq
    have hval := congrArg Fin.val heq
    simp only [Fin.val_zero, Fin.val_last] at hval
    omega
  · intro heq
    have hval := congrArg Fin.val heq
    rw [coe_finRotate_of_ne_last hi] at hval
    omega

theorem selected_has_nonowner {n : ℕ} (hn : 2 ≤ n) (i a : Fin n) :
    ∃ j ∈ selected true i, j ≠ a := by
  by_cases hi : i = a
  · refine ⟨finRotate n i, ?_, ?_⟩
    · simp [selected]
    · simpa only [← hi] using rotate_ne hn i
  · exact ⟨i, by simp [selected], hi⟩

theorem one_selected_nonowner {n : ℕ} (i a : Fin n) :
    (∃ j ∈ selected false i, j ≠ a) ↔ i ≠ a := by simp [selected]

def twoDetects {n : ℕ} (w : ℝ) (request : Request n) : Set (Input n) :=
  MoatDetection.detects w request ∪
    MoatDetection.detects w {request with observer := (finRotate n).symm request.observer}

theorem two_detects_iff {n : ℕ} (w : ℝ) (r : Request n) (z : Input n) :
    z ∈ twoDetects w r ↔ r.observer ∈ selected true z.1 ∧
      (z.2 ∈ endpointEvent w r.left ∪ endpointEvent w r.right) := by
  simp only [twoDetects, MoatDetection.detects, mem_union, mem_prod,
    mem_singleton_iff, selected, Bool.true_eq, ↓reduceIte, Finset.mem_insert,
    Finset.mem_singleton]
  have heq : z.1 = (finRotate n).symm r.observer ↔ r.observer = finRotate n z.1 := by
    constructor
    · intro h
      rw [h, Equiv.apply_symm_apply]
    · intro h
      rw [h, Equiv.symm_apply_apply]
  rw [heq]
  tauto

theorem two_request_detection_le {n : ℕ} (hn : 0 < n) (w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (request : Request n) :
    law n (twoDetects w request) ≤ 4*ENNReal.ofReal w/(n:ℝ≥0∞) := by
  apply (measure_union_le _ _).trans
  have h1 := MoatDetection.one_request_detection_le w hw1 request
  have h2 := MoatDetection.one_request_detection_le w hw1
    {request with observer := (finRotate n).symm request.observer}
  calc
    _ ≤ 2*ENNReal.ofReal w/(n:ℝ≥0∞) + 2*ENNReal.ofReal w/(n:ℝ≥0∞) := add_le_add h1 h2
    _ = _ := by simp only [div_eq_mul_inv]; ring

end EnvyFreeResearch.Full.MoatSelection
