import EnvyFreeResearch.Full.ChoresCompletionPreparation

/-! Completing the prepared groups with their two smaller-population
allocations. The interface keeps the recursive hypotheses explicit; the
outer recursion must instantiate them with its actual recursive calls. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Completion
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition OrderedUnion QueryProgram

variable {n b c : ℕ}

def finishPrepared (out : Prepared n b c) (childB : Allocation n (Fin b)) (childD : Allocation n (Fin c)) :
    Allocation n (Sum (Fin b) (Fin c)) :=
  sumAllocation (attach out.forB.allocation childB) (attach out.forD.allocation childD)

theorem finish_prepared_sound (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agentB : Fin b → Fin n) (agentD : Fin c → Fin n) (hb : 0 < b) (hc : 0 < c)
    (X R : Set ℝ) (hXR : Disjoint X R) (out : Prepared n b c)
    (hp : out.Correct cost agentB agentD hb hc X R)
    (childB : Allocation n (Fin b)) (childD : Allocation n (Fin c))
    (hB : childB.Sound cost agentB (material out.forB.allocation.remainder))
    (hD : childD.Sound cost agentD (material out.forD.allocation.remainder)) :
    (finishPrepared out childB childD).Sound cost (Sum.elim agentB agentD) (X ∪ R) := by
  have hl : (attach out.forB.allocation childB).Sound cost agentB R := by
    simpa only [extendAgent_fin] using attach_sound cost (extendAgent agentB hb) R out.forB.original
      out.forB.allocation hp.forB childB (by simpa only [extendAgent_fin] using hB)
  have hr : (attach out.forD.allocation childD).Sound cost agentD X := by
    simpa only [extendAgent_fin] using attach_sound cost (extendAgent agentD hc) X out.forD.original
      out.forD.allocation hp.forD childD (by simpa only [extendAgent_fin] using hD)
  have h := sum_allocation_sound cost agentB agentD R X hXR.symm _ _ hl hr
    (fun i j => (hp.protectsB i j).trans (measureReal_mono (attach_contains out.forD.allocation childD j)))
    (fun j i => (hp.protectsD j i).trans (measureReal_mono (attach_contains out.forB.allocation childB i)))
  simpa only [finishPrepared,union_comm R X] using h

variable {A B : Type*}

def Allocation.reindex (out : Allocation n A) (f : B → A) : Allocation n B := ⟨out.pieces ∘ f⟩

theorem Allocation.Sound.reindex (cost : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]
    (agent : A → Fin n) (U : Set ℝ) (out : Allocation n A) (h : out.Sound cost agent U)
    (f : B → A) (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    (out.reindex f).Sound cost (agent ∘ f) U := by
  constructor
  · exact fun i => h.cache (f i)
  · exact fun i j hij => h.disjoint (fun heq => hij (hinj heq))
  · change (⋃ i, material (out.pieces (f i)))=U
    have hu : (⋃ i, material (out.pieces (f i)))=(⋃ j, material (out.pieces j)) := by
      ext x
      constructor
      · rintro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨f i,hi⟩
      · intro hx
        obtain ⟨j,hj⟩ := mem_iUnion.mp hx
        obtain ⟨i,rfl⟩ := hsurj j
        exact mem_iUnion.mpr ⟨i,hj⟩
    exact hu.trans h.cover
  · exact fun i j => h.envy_free (f i) (f j)

end EnvyFreeResearch.Full.Chores.Completion
