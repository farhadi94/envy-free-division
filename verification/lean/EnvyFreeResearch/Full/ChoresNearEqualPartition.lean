import EnvyFreeResearch.Full.ChoresNearEqualProgram
import EnvyFreeResearch.Full.ChoresUnionQuery

/-! Complete near-equal physical partition, including zero-total observers.
The program uses only cached inputs and ordinary Eval/Cut replies. Its
bound counts positive designated observers, not all enclosing observers. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.NearEqual
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Quantile
open scoped Classical

def positiveObservers {n : ℕ} (designated : Finset (Fin n)) (cache : List (Parent n)) : Finset (Fin n) :=
  designated.filter (fun i => 0 < cachedValue cache i)

def program {n : ℕ} (designated : Finset (Fin n)) (m : ℕ) (hm : 0 < m)
    (cache : List (Parent n)) : Program (Query (Fin n)) ℝ (Output n m) :=
  let positive := positiveObservers designated cache
  if positive.Nonempty then positiveProgram positive m hm cache
  else .returned ⟨cache,fun _ => ⟨0,hm⟩⟩

variable {n m : ℕ} (cost : Fin n → Measure ℝ)
  [∀ i, IsFiniteMeasure (cost i)] [∀ i, NullSingletonClass (cost i)]

def Output.Physical (U : Set ℝ) (out : Output n m) : Prop :=
  (∀ j, CacheValid (measureProfile cost) (material (out.parts j)) (out.parts j)) ∧
    Pairwise (fun j k => Disjoint (material (out.parts j)) (material (out.parts k))) ∧
    (⋃ j, material (out.parts j))=U

theorem output_physical (U : Set ℝ) (out : Output n m)
    (hv : Valid (measureProfile cost) out.grid) (ho : Ordered out.grid)
    (hU : material out.grid=U) : out.Physical cost U := by
  refine ⟨fun j => ⟨ColorCache.parts_valid _ out.grid hv out.color j,
    ColorCache.parts_ordered out.grid ho out.color j,rfl⟩,
    ColorCache.parts_disjoint out.grid ho out.color,?_⟩
  exact (ColorCache.parts_cover out.grid out.color).trans hU

theorem zero_total_piece (U : Set ℝ) (out : Output n m) (hphysical : out.Physical cost U)
    (i : Fin n) (hz : (cost i).real U=0) (j : Fin m) : (cost i).real (material (out.parts j))=0 := by
  have hsubset : material (out.parts j) ⊆ U := by
    rw [← hphysical.2.2]
    exact subset_iUnion (fun k : Fin m => material (out.parts k)) j
  have hle : (cost i).real (material (out.parts j)) ≤ (cost i).real U := measureReal_mono hsubset
  rw [hz] at hle
  exact le_antisymm hle measureReal_nonneg

theorem partition_correct (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy (measureProfile cost) oracle)
    (designated : Finset (Fin n)) (m : ℕ) (hm : 0 < m)
    (U : Set ℝ) (cache : List (Parent n)) (hc : CacheValid (measureProfile cost) U cache)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (program designated m hm cache) prior out trace ∧
      trace.length ≤ (positiveObservers designated cache).card*
        (4*(positiveObservers designated cache).card*m-1)*n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ (positiveObservers designated cache).card*
        (4*(positiveObservers designated cache).card*m-1) ∧
      out.Physical cost U ∧ ∀ i ∈ designated, ∀ j : Fin m,
        (cost i).real U/(2*(m : ℝ)) ≤ (cost i).real (material (out.parts j)) ∧
        (cost i).real (material (out.parts j)) ≤ 3*(cost i).real U/(2*(m : ℝ)) := by
  let positive := positiveObservers designated cache
  have htotal (i : Fin n) : cachedValue cache i=(cost i).real U := by
    rw [← material_value cost cache hc.1 hc.2.1,hc.2.2]
  have hmono : ∀ i, Monotone ((measureProfile cost).cumulative i) := fun i => prefixCost_monotone (cost i) 0
  by_cases hpos : positive.Nonempty
  · change (positiveObservers designated cache).Nonempty at hpos
    have hpositive : ∀ i ∈ positive, 0 < cachedValue cache i := fun i hi => (Finset.mem_filter.mp hi).2
    obtain ⟨out,trace,hexec,hQ,hC,hv,ho,hmat,hbounds⟩ := positive_program_correct
      (measureProfile cost) hmono oracle hpolicy positive (Finset.card_pos.mpr hpos) m hm
      cache hc.1 hc.2.1 hpositive prior
    have hphysical := output_physical cost U out hv ho (hmat.trans hc.2.2)
    refine ⟨out,trace,?_,hQ,hC,hphysical,?_⟩
    · simpa only [program,positive,ite_eq_left hpos] using hexec
    · intro i hi j
      by_cases hp : 0 < cachedValue cache i
      · have hip : i ∈ positive := Finset.mem_filter.mpr ⟨hi,hp⟩
        have h := hbounds i hip j
        have hvalue : cachedValue (out.parts j) i=(cost i).real (material (out.parts j)) :=
          (material_value cost _ (hphysical.1 j).1 (hphysical.1 j).2.1 i).symm
        simpa only [htotal,hvalue] using h
      · have hz : (cost i).real U=0 := le_antisymm
          (by simpa only [htotal] using le_of_not_gt hp) measureReal_nonneg
        rw [hz,zero_total_piece cost U out hphysical i hz j]
        simp
  · change ¬ (positiveObservers designated cache).Nonempty at hpos
    let out : Output n m := ⟨cache,fun _ => ⟨0,hm⟩⟩
    have hphysical : out.Physical cost U := output_physical cost U out hc.1 hc.2.1 hc.2.2
    refine ⟨out,[],?_,by simp,by simp,hphysical,?_⟩
    · simp only [program,ite_eq_right hpos]
      exact Executes.returned _ _
    · intro i hi j
      have hp : ¬ 0 < cachedValue cache i := fun hp => hpos ⟨i,Finset.mem_filter.mpr ⟨hi,hp⟩⟩
      have hz : (cost i).real U=0 := le_antisymm
        (by simpa only [htotal] using le_of_not_gt hp) measureReal_nonneg
      rw [hz,zero_total_piece cost U out hphysical i hz j]
      simp

end EnvyFreeResearch.Full.Chores.NearEqual
