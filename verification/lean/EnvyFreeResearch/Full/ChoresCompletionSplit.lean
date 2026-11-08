import EnvyFreeResearch.Full.ChoresNearEqualPartition
import EnvyFreeResearch.Full.ChoresAugmentMeasures

/-! The first half of two-group completion: near-equal splitting for one
group followed by whole-piece augmentation for the other. All recorded
observer caches and the exact recursive complement are returned. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Completion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram
open scoped Classical

variable {n : ℕ}

def countPieces (k : ℕ) : ℕ := 2^(k+1)

theorem countPieces_pos (k : ℕ) : 0 < countPieces k := pow_pos (by norm_num) _

structure SplitOutput (n k : ℕ) where
  original : Fin (countPieces k) → List (Parent n)
  allocation : Augment.WholeOutput n k (Fin (countPieces k))

def splitAugment (observers : Finset (Fin n)) (recipient : ℕ → Fin n) (k : ℕ)
    (cache : List (Parent n)) : Program (Query (Fin n)) ℝ (SplitOutput n k) :=
  (NearEqual.program observers (countPieces k) (countPieces_pos k) cache).bind (fun split =>
    (Augment.wholeProgram recipient k split.parts (List.finRange (countPieces k))
      ⟨0,countPieces_pos k⟩).bind (fun allocation => .returned ⟨split.parts,allocation⟩))

def splitBudget (b k : ℕ) : ℕ := b*(4*b*countPieces k-1)+(2^k-1)

theorem split_term_mono (a b m : ℕ) (hab : a ≤ b) : a*(4*a*m-1) ≤ b*(4*b*m-1) := by
  apply Nat.mul_le_mul hab
  apply Nat.sub_le_sub_right
  exact Nat.mul_le_mul_right m (Nat.mul_le_mul_left 4 hab)

theorem split_augment_correct (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (observers : Finset (Fin n)) (recipient : ℕ → Fin n) (k : ℕ)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (splitAugment observers recipient k cache) prior out trace ∧
      trace.length ≤ splitBudget observers.card k*n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ splitBudget observers.card k ∧
      out.allocation.Correct cost recipient U out.original ∧
      ∀ i ∈ observers, ∀ j : Fin k,
        (cost i).real U/(2*(countPieces k : ℝ)) ≤ (cost i).real (material (out.allocation.allocated j)) := by
  obtain ⟨split,t1,hexec1,hQ1,hC1,hphysical,hvalue⟩ :=
    NearEqual.partition_correct cost oracle hpolicy observers (countPieces k) (countPieces_pos k) U cache hc prior
  have hv : Augment.FamilyValid (measureProfile cost) split.parts :=
    ⟨fun j => ⟨(hphysical.1 j).1,(hphysical.1 j).2.1⟩,hphysical.2.1⟩
  obtain ⟨allocated,t2,hexec2,hQ2,hC2,hcorrect⟩ :=
    Augment.whole_physical_correct cost oracle hpolicy recipient k U split.parts hv hphysical.2.2
      (List.finRange (countPieces k)) (List.nodup_finRange _) (by simp [countPieces])
      ⟨0,countPieces_pos k⟩ (prior++t1)
  let out : SplitOutput n k := ⟨split.parts,allocated⟩
  have hr : (NearEqual.positiveObservers observers cache).card ≤ observers.card :=
    Finset.card_filter_le _ _
  have hterm := split_term_mono (NearEqual.positiveObservers observers cache).card observers.card (countPieces k) hr
  refine ⟨out,t1++t2,?_,?_,?_,hcorrect,?_⟩
  · have htail := hexec2.bind (fun allocation => Program.returned (⟨split.parts,allocation⟩ : SplitOutput n k))
      (Executes.returned _ _)
    simpa only [splitAugment,List.append_nil] using hexec1.bind
      (fun split => (Augment.wholeProgram recipient k split.parts (List.finRange (countPieces k))
        ⟨0,countPieces_pos k⟩).bind (fun allocation => Program.returned (⟨split.parts,allocation⟩ : SplitOutput n k))) htail
  · simp only [List.length_append,splitBudget,Nat.add_mul]
    exact (Nat.add_le_add hQ1 hQ2).trans (Nat.add_le_add_right (Nat.mul_le_mul_right n hterm) _)
  · simp only [List.countP_append,splitBudget]
    omega
  · intro i hi j
    exact (hvalue i hi (allocated.originalLabel j)).1.trans
      (measureReal_mono (hcorrect.whole_piece j))

end EnvyFreeResearch.Full.Chores.Completion
