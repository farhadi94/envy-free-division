import EnvyFreeResearch.Full.UpperSnapshotContrastMargin

/-! The maximizing pair has a deterministic finite first-tie selector,
measurable in the actual cached value matrix. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotContrast
variable {k : ℕ}

def maximizingPair (hk : 0 < k) (chores : Bool) (Z : Fin k → Fin k → ℝ) : Fin k × Fin k :=
  ((Finset.univ : Finset (Fin k × Fin k)).toList.argmax (fun p => signedGap chores Z p.1 p.2)).getD
    (⟨0, hk⟩, ⟨0, hk⟩)

theorem maximizingPair_spec (hk : 0 < k) (chores : Bool) (Z : Fin k → Fin k → ℝ) (i j : Fin k) :
    signedGap chores Z i j ≤ signedGap chores Z (maximizingPair hk chores Z).1 (maximizingPair hk chores Z).2 := by
  let cells := (Finset.univ : Finset (Fin k × Fin k)).toList
  have hmem : (i, j) ∈ cells := by simp [cells]
  have hne : cells ≠ [] := List.ne_nil_of_mem hmem
  obtain ⟨p, hp⟩ := UpperRepresentatives.argmax_exists (fun p : Fin k × Fin k => signedGap chores Z p.1 p.2) cells hne
  have hm := List.le_of_mem_argmax hmem (by simp [hp] : p ∈ cells.argmax (fun p => signedGap chores Z p.1 p.2))
  change (Finset.univ : Finset (Fin k × Fin k)).toList.argmax (fun p => signedGap chores Z p.1 p.2) = some p at hp
  simpa only [maximizingPair, hp, Option.getD_some] using hm

variable {X : Type*} [MeasurableSpace X]

theorem signedGap_measurable (chores : Bool) (Z : X → Fin k → Fin k → ℝ)
    (hZ : ∀ i j, Measurable (fun x => Z x i j)) (i j : Fin k) :
    Measurable (fun x => signedGap chores (Z x) i j) := by
  cases chores
  · exact (hZ i i).sub (hZ i j)
  · exact (hZ i j).sub (hZ i i)

theorem maximizingPair_measurable (hk : 0 < k) (chores : Bool) (Z : X → Fin k → Fin k → ℝ)
    (hZ : ∀ i j, Measurable (fun x => Z x i j)) :
    Measurable (fun x => maximizingPair hk chores (Z x)) := by
  have ha := UpperRepresentatives.argmax_measurable
    ((Finset.univ : Finset (Fin k × Fin k)).toList)
    (fun x p => signedGap chores (Z x) p.1 p.2) (fun p => signedGap_measurable chores Z hZ p.1 p.2)
  exact ProtocolMeasurable.measurable_option_cases (present := fun _ p => p)
    (absent := fun _ => ((⟨0, hk⟩, ⟨0, hk⟩) : Fin k × Fin k)) ha measurable_snd measurable_const

/-- The concrete first maximizing pair satisfies the same positive-gap
certificate as the existential calculation. -/
theorem maximizingPair_large (hk : 0 < k) (chores : Bool) (V Z e : Fin k → Fin k → ℝ)
    (pi : Equiv.Perm (Fin k)) (t : Fin k → ℝ)
    (hvalues : ∀ i j, Z i j = paid V pi t i j + e i j)
    (herr : ∀ i j, |e i j| ≤ signedGap chores Z i j)
    (i h u v : Fin k) (Lambda theta : ℝ) (hLambda : 0 < Lambda) (htheta : 0 < theta)
    (hcontrast : Lambda / theta ≤ contrast V i h u v) :
    (maximizingPair hk chores Z).1 ≠ (maximizingPair hk chores Z).2 ∧
      Lambda / (4 * theta) ≤ signedGap chores Z (maximizingPair hk chores Z).1 (maximizingPair hk chores Z).2 := by
  obtain ⟨a, b, _, hlarge, _⟩ := exists_large_gap hk chores V Z e pi t hvalues herr i h u v Lambda theta hLambda htheta hcontrast
  have hb := hlarge.trans (maximizingPair_spec hk chores Z a b)
  refine ⟨?_, hb⟩
  intro heq
  have hpos : 0 < signedGap chores Z (maximizingPair hk chores Z).1 (maximizingPair hk chores Z).2 :=
    (div_pos hLambda (by positivity)).trans_le hb
  rw [heq, signedGap_self] at hpos
  exact (lt_irrefl 0) hpos

end EnvyFreeResearch.Full.UpperSnapshotContrast
