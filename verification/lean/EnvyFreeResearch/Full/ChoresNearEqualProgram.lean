import EnvyFreeResearch.Full.ChoresNearEqualWeights

/-! The positive-row near-equal splitter is one ordinary-query program:
record the common quantile grid, select a whole-cell coloring from cached
weights, and return the exact component cache for every color. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.NearEqual
open Set MeasureTheory OracleProtocol IntervalOracle InitialPartition QueryProgram OrderedUnion Quantile
open scoped Classical

structure Output (n m : ℕ) where
  grid : List (Parent n)
  color : Fin grid.length → Fin m

def Output.parts {n m : ℕ} (out : Output n m) (j : Fin m) : List (Parent n) :=
  ColorCache.parts out.grid out.color j

def positiveProgram {n : ℕ} (positive : Finset (Fin n)) (m : ℕ) (hm : 0 < m)
    (initial : List (Parent n)) : Program (Query (Fin n)) ℝ (Output n m) :=
  (commonGrid (4*positive.card*m) positive.toList initial).bind (fun fresh =>
    .returned ⟨fresh,Multicolor.select (weights initial fresh positive) (4*positive.card*m : ℕ) ⟨0,hm⟩⟩)

theorem positive_program_correct {n : ℕ} (P : Profile (Fin n))
    (hmono : ∀ i, Monotone (P.cumulative i))
    (oracle : AdaptiveOracle.Policy (Query (Fin n)) ℝ)
    (hpolicy : AdaptiveOracle.IsLegalPolicy P oracle)
    (positive : Finset (Fin n)) (hr : 0 < positive.card) (m : ℕ) (hm : 0 < m)
    (initial : List (Parent n)) (hv : Valid P initial) (ho : Ordered initial)
    (hpositive : ∀ i ∈ positive, 0 < cachedValue initial i)
    (prior : History (Query (Fin n)) ℝ) :
    ∃ out trace, Executes oracle (positiveProgram positive m hm initial) prior out trace ∧
      trace.length ≤ positive.card*(4*positive.card*m-1)*n ∧
      trace.countP (fun qr => isCutQuery qr.1) ≤ positive.card*(4*positive.card*m-1) ∧
      Valid P out.grid ∧ Ordered out.grid ∧ material out.grid=material initial ∧
      ∀ i ∈ positive, ∀ j : Fin m,
        cachedValue initial i/(2*(m : ℝ)) ≤ cachedValue (out.parts j) i ∧
        cachedValue (out.parts j) i ≤ 3*cachedValue initial i/(2*(m : ℝ)) := by
  let K := 4*positive.card*m
  have hK : 0 < K := by dsimp [K]; positivity
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  obtain ⟨fresh,trace,hexec,hQ,hC,hvf,hof,hmat,_,htotal,hsmall,_⟩ :=
    common_grid_correct P hmono oracle hpolicy K hK positive.toList initial hv ho prior
  let color := Multicolor.select (weights initial fresh positive) (K : ℝ) (⟨0,hm⟩ : Fin m)
  let out : Output n m := ⟨fresh,color⟩
  have hsmall' : ∀ i ∈ positive, ∀ p ∈ fresh, p.value i ≤ cachedValue initial i/(K : ℝ) :=
    fun i hi => hsmall i (Finset.mem_toList.mpr hi)
  have hgood := Multicolor.select_good (weights initial fresh positive) (K : ℝ) hKreal
    (⟨0,hm⟩ : Fin m) (weights_small P hmono initial fresh hvf positive hpositive _ hKreal hsmall')
    (weights_normalized initial fresh positive hpositive htotal)
  refine ⟨out,trace,?_,by simpa [K] using hQ,by simpa [K] using hC,hvf,hof,hmat,?_⟩
  · have h := hexec.bind (fun fresh => Program.returned
      (⟨fresh,Multicolor.select (weights initial fresh positive) (K : ℝ) ⟨0,hm⟩⟩ : Output n m))
      (Executes.returned _ (prior++trace))
    simpa only [positiveProgram,K,List.append_nil] using h
  · intro i hi j
    have herror := hgood ⟨i,hi⟩ j
    have hsame : (∑ e, if color e=j then weights initial fresh positive ⟨i,hi⟩ e else 0) =
        ∑ e, @ite ℝ (color e=j) (Classical.propDecidable _) (weights initial fresh positive ⟨i,hi⟩ e) 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : color e=j <;> simp only [h,ite_true,ite_false]
    change |(∑ e, @ite ℝ (color e=j) (Classical.propDecidable _)
      (weights initial fresh positive ⟨i,hi⟩ e) 0)-1/(Fintype.card (Fin m) : ℝ)| ≤
      2*(Fintype.card positive : ℝ)/(K : ℝ) at herror
    rw [← hsame] at herror
    rw [normalized_color_value initial fresh positive color ⟨i,hi⟩ j,
      Fintype.card_fin,Fintype.card_coe] at herror
    rw [rounding_scale positive.card m hr hm] at herror
    exact rescale_near_equal _ _ _ (hpositive i hi) (by exact_mod_cast hm) herror

end EnvyFreeResearch.Full.Chores.NearEqual
