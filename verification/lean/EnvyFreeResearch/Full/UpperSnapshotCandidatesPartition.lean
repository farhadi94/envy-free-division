import EnvyFreeResearch.Full.UpperSnapshotCandidatesGeometry

/-! Exact partition and value checks for the recorded two-cell large branch. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotCandidates
open UpperRecordedDomain UpperCorrectionExecution UpperLogicalPreparation UpperLogicalCells UpperDomainDifference
variable {n k m : ℕ}

def pairPieces (F G : Set ℝ) (j : Fin k) : Set ℝ := if j.val = 0 then F else if j.val = 1 then G else ∅

theorem pairPieces_disjoint (F G : Set ℝ) (hFG : Disjoint F G) :
    Pairwise (fun i j : Fin k => Disjoint (pairPieces F G i) (pairPieces F G j)) := by
  intro i j hij
  by_cases hi0 : i.val = 0 <;> by_cases hi1 : i.val = 1 <;>
    by_cases hj0 : j.val = 0 <;> by_cases hj1 : j.val = 1 <;>
    simp_all [pairPieces, Fin.ext_iff, disjoint_comm]

theorem pairPieces_union (hk : 2 ≤ k) (F G : Set ℝ) : (⋃ j : Fin k, pairPieces F G j) = F ∪ G := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    unfold pairPieces at hj
    split_ifs at hj with h0 h1
    · exact Or.inl hj
    · exact Or.inr hj
    · exact False.elim hj
  · intro hx
    rcases hx with hf | hg
    · exact mem_iUnion.mpr ⟨⟨0, by omega⟩, by simpa only [pairPieces, ite_true] using hf⟩
    · exact mem_iUnion.mpr ⟨⟨1, by omega⟩, by simpa only [pairPieces, Nat.one_ne_zero, ite_false, ite_true] using hg⟩

theorem large_partition (hk : 2 ≤ k) (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
    (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (F G : Fin (m + 1)) (hFG : F ≠ G) :
    Pairwise (fun i j : Fin k => Disjoint (domain (largeEndowment state cuts F G i).cells)
      (domain (largeEndowment state cuts F G j).cells)) ∧
    (∀ j : Fin k, Disjoint (domain (largeEndowment state cuts F G j).cells) (domain (largeBuffer state cuts F G).cells)) ∧
    (⋃ j : Fin k, domain (largeEndowment state cuts F G j).cells) ∪ domain (largeBuffer state cuts F G).cells = domain state.cells := by
  have hpieces (j : Fin k) : domain (largeEndowment state cuts F G j).cells =
      pairPieces (cell (domain state.cells) cuts F) (cell (domain state.cells) cuts G) j :=
    largeEndowment_domain state cuts hzero hmono hsep F G j
  have hbuffer := largeBuffer_domain state cuts hzero hone hmono hsep F G
  simp_rw [hpieces, hbuffer]
  refine ⟨pairPieces_disjoint _ _ (cells_disjoint _ cuts hmono hFG), ?_, ?_⟩
  · intro j
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hy.2
    have hs : pairPieces (cell (domain state.cells) cuts F) (cell (domain state.cells) cuts G) j ⊆
        cell (domain state.cells) cuts F ∪ cell (domain state.cells) cuts G := by
      unfold pairPieces
      split_ifs
      · exact subset_union_left
      · exact subset_union_right
      · exact empty_subset _
    exact hs hx
  · rw [pairPieces_union hk]
    exact union_sdiff_cancel (union_subset (cell_subset _ _ F) (cell_subset _ _ G))

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

theorem largeBuffer_mass (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
    (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (F G : Fin (m + 1)) (hFG : F ≠ G) :
    μ.real (domain (largeBuffer state cuts F G).cells) = μ.real (domain state.cells) -
      μ.real (cell (domain state.cells) cuts F) - μ.real (cell (domain state.cells) cuts G) := by
  rw [largeBuffer_domain state cuts hzero hone hmono hsep,
    measureReal_sdiff (union_subset (cell_subset _ _ F) (cell_subset _ _ G))
      ((cell_measurable _ (domain_measurable _) _ F).union (cell_measurable _ (domain_measurable _) _ G)),
    measureReal_union (cells_disjoint _ cuts hmono hFG) (cell_measurable _ (domain_measurable _) _ G)]
  ring

omit [IsFiniteMeasure μ] in
theorem largeEndowment_mass_bounds (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (F G : Fin (m + 1)) (eta : ℝ) (heta : 0 ≤ eta)
    (hsmall : ∀ e, μ.real (cell (domain state.cells) cuts e) ≤ eta * μ.real (domain state.cells)) (j : Fin k) :
    0 ≤ μ.real (domain (largeEndowment state cuts F G j).cells) ∧
      μ.real (domain (largeEndowment state cuts F G j).cells) ≤ eta * μ.real (domain state.cells) := by
  refine ⟨measureReal_nonneg, ?_⟩
  rw [largeEndowment_domain state cuts hzero hmono hsep]
  split_ifs
  · exact hsmall F
  · exact hsmall G
  · simpa only [measureReal_empty] using mul_nonneg heta (measureReal_nonneg (μ := μ) (s := domain state.cells))

theorem largeBuffer_lower (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
    (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (F G : Fin (m + 1)) (hFG : F ≠ G) (eta : ℝ)
    (hsmall : ∀ e, μ.real (cell (domain state.cells) cuts e) ≤ eta * μ.real (domain state.cells)) :
    (1 - 2 * eta) * μ.real (domain state.cells) ≤ μ.real (domain (largeBuffer state cuts F G).cells) := by
  rw [largeBuffer_mass μ state cuts hzero hone hmono hsep F G hFG]
  nlinarith [hsmall F, hsmall G]

/-- The large branch is simultaneously a valid near-EF input for both
preference orientations, with a positive buffer for every positive row. -/
theorem large_near_checks (state : State n) (cuts : Fin (m + 2) → ℝ)
    (hzero : cuts 0 = 0) (hone : cuts (Fin.last (m + 1)) = 1)
    (hmono : Monotone cuts) (hsep : ∀ e, SeparatedAt (cuts e) state.cells)
    (F G : Fin (m + 1)) (hFG : F ≠ G) (eta tau : ℝ)
    (heta : 0 ≤ eta) (hetaquarter : eta ≤ 1 / 4) (htau : 0 ≤ tau) (hetatau : eta ≤ tau / 2)
    (hpositive : 0 < μ.real (domain state.cells))
    (hsmall : ∀ e, μ.real (cell (domain state.cells) cuts e) ≤ eta * μ.real (domain state.cells)) :
    μ.real (domain state.cells) / 2 ≤ μ.real (domain (largeBuffer state cuts F G).cells) ∧
      0 < μ.real (domain (largeBuffer state cuts F G).cells) ∧
      ∀ i j : Fin k, |μ.real (domain (largeEndowment state cuts F G i).cells) -
        μ.real (domain (largeEndowment state cuts F G j).cells)| ≤ tau * μ.real (domain (largeBuffer state cuts F G).cells) := by
  have hl := largeBuffer_lower μ state cuts hzero hone hmono hsep F G hFG eta hsmall
  have hhalf : μ.real (domain state.cells) / 2 ≤ μ.real (domain (largeBuffer state cuts F G).cells) := by
    nlinarith
  refine ⟨hhalf, (half_pos hpositive).trans_le hhalf, ?_⟩
  intro i j
  have hi := largeEndowment_mass_bounds μ state cuts hzero hmono hsep F G eta heta hsmall i
  have hj := largeEndowment_mass_bounds μ state cuts hzero hmono hsep F G eta heta hsmall j
  have hrange : |μ.real (domain (largeEndowment state cuts F G i).cells) -
      μ.real (domain (largeEndowment state cuts F G j).cells)| ≤ eta * μ.real (domain state.cells) := by
    apply abs_le.mpr
    constructor <;> linarith
  apply hrange.trans
  nlinarith

end EnvyFreeResearch.Full.UpperSnapshotCandidates
