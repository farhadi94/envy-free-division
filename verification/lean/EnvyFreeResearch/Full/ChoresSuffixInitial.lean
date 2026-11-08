import EnvyFreeResearch.Full.ChoresSuffixClippedStore
import EnvyFreeResearch.Full.ChoresSuffixVirtualStore

/-! Initial physical suffix records and the separately computed common
virtual baseline. Input whole values are explicit cached data. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Suffix
open Set OracleProtocol IntervalOracle QueryProgram Persistent
open scoped Classical

variable {n : ℕ}

def affineEmpty (offset : Fin n → ℝ) : Record n := ⟨0,fun i => (-offset i,0)⟩
def affineWhole (offset total : Fin n → ℝ) : Record n := ⟨1,fun i => (total i-offset i,1)⟩

theorem affine_empty_sound (P : Profile (Fin n)) (offset : Fin n → ℝ) :
    AffineSound P offset (affineEmpty offset) := by
  intro i
  simp [affineEmpty,affineValue]

theorem affine_whole_sound (P : Profile (Fin n)) (offset total : Fin n → ℝ)
    (htotal : ∀ i, total i = P.cumulative i 1) : AffineSound P offset (affineWhole offset total) := by
  intro i
  simp [affineWhole,affineValue,htotal i,P.zero i]

theorem affine_initial_before (offset total : Fin n → ℝ) (htotal : ∀ i, 0 ≤ total i) :
    Before (affineEmpty offset) (affineWhole offset total) := by
  refine ⟨zero_le_one,?_⟩
  intro i
  by_cases hz : total i = 0
  · right
    simp [affineEmpty,affineWhole,hz]
  · left
    change -offset i < total i-offset i
    have hpos : 0 < total i := lt_of_le_of_ne (htotal i) (Ne.symm hz)
    linarith

def clippedEmpty (offset : Fin n → ℝ) : ClippedRecord n :=
  ⟨⟨0,fun i => (max 0 (-offset i),0)⟩,fun i => -offset i⟩
def clippedWhole (offset total : Fin n → ℝ) : ClippedRecord n :=
  ⟨⟨1,fun i => (max 0 (total i-offset i),1)⟩,fun i => total i-offset i⟩

theorem clipped_empty_sound (P : Profile (Fin n)) (offset : Fin n → ℝ) :
    ClippedSound P offset (clippedEmpty offset) := by
  refine ⟨?_,fun _ => rfl⟩
  intro i
  simp [clippedEmpty,affineValue]

theorem clipped_whole_sound (P : Profile (Fin n)) (offset total : Fin n → ℝ)
    (htotal : ∀ i, total i = P.cumulative i 1) : ClippedSound P offset (clippedWhole offset total) := by
  refine ⟨?_,fun _ => rfl⟩
  intro i
  simp [clippedWhole,affineValue,htotal i,P.zero i]

theorem clipped_empty_formal (offset : Fin n → ℝ) (hoffset : ∀ i, 0 ≤ offset i) (i : Fin n) :
    (clippedEmpty offset).record.formal i = (0,0) := by
  simp only [clippedEmpty,max_eq_left (neg_nonpos.mpr (hoffset i))]

theorem clipped_initial_before (offset total : Fin n → ℝ) (hoffset : ∀ i, 0 ≤ offset i) :
    Before (clippedEmpty offset).record (clippedWhole offset total).record := by
  refine ⟨zero_le_one,?_⟩
  intro i
  rw [clipped_empty_formal offset hoffset i]
  by_cases hz : max 0 (total i-offset i) = 0
  · right
    simp [clippedWhole,hz]
  · left
    exact lt_of_le_of_ne (le_max_left _ _) (Ne.symm hz)

theorem affine_primary_lower (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (offset : Fin n → ℝ) (r : Record n) (hsound : AffineSound P offset r) (hpoint : 0 ≤ r.point)
    (i : Fin n) : -offset i ≤ (r.formal i).1 := by
  rw [hsound i]
  have h := hmono i (show 1-r.point ≤ 1 by linarith)
  unfold affineValue
  linarith

variable {Parent : Type*} [Fintype Parent] [Nonempty Parent]

def virtualBaseline (offset : Parent → Fin n → ℝ) (i : Fin n) : ℝ :=
  -1-(Finset.univ.sup' Finset.univ_nonempty (fun p => offset p i))

def virtualBottom (offset : Parent → Fin n → ℝ) : Record n :=
  ⟨0,fun i => (virtualBaseline offset i,0)⟩

theorem virtual_baseline_below_empty (offset : Parent → Fin n → ℝ) (p : Parent) (i : Fin n) :
    virtualBaseline offset i < -offset p i := by
  have h := Finset.le_sup' (fun p => offset p i) (Finset.mem_univ p)
  unfold virtualBaseline
  linarith

theorem virtual_primary_negative (offset : Parent → Fin n → ℝ) (hoffset : ∀ p i, 0 ≤ offset p i)
    (i : Fin n) : ((virtualBottom offset).formal i).1 < 0 := by
  let p : Parent := Classical.choice inferInstance
  exact (virtual_baseline_below_empty offset p i).trans_le (neg_nonpos.mpr (hoffset p i))

theorem virtual_before_physical (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (offset : Parent → Fin n → ℝ) (p : Parent) (r : Record n)
    (hsound : AffineSound P (offset p) r) (hpoint : 0 ≤ r.point) : Before (virtualBottom offset) r := by
  refine ⟨hpoint,?_⟩
  intro i
  left
  exact (virtual_baseline_below_empty offset p i).trans_le
    (affine_primary_lower P hmono (offset p) r hsound hpoint i)

end EnvyFreeResearch.Full.Chores.Suffix
