import EnvyFreeResearch.Full.ChoresColorCache
import EnvyFreeResearch.Full.ChoresMulticolorSelector
import EnvyFreeResearch.Full.ChoresQuantileCommon

/-! Normalization and rescaling for the near-equal physical splitter.
The weights are actual cached component values, normalized only for
observers with strictly positive original totals. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.NearEqual
open Set MeasureTheory IntervalOracle InitialPartition OrderedUnion Quantile
open scoped Classical BigOperators

variable {n : ℕ}

theorem sum_component_values (cache : List (Parent n)) (i : Fin n) :
    (∑ e : Fin cache.length, (cache.get e).value i)=cachedValue cache i := by
  have h : List.ofFn (fun e : Fin cache.length => (cache.get e).value i) =
      cache.map (fun p => p.value i) := by
    change List.ofFn ((fun p : Parent n => p.value i) ∘ cache.get) = _
    rw [← List.map_ofFn,List.ofFn_get]
  rw [← List.sum_ofFn,h,← ColorCache.cachedValue_eq_sum]

def weights (initial fresh : List (Parent n)) (positive : Finset (Fin n)) :
    positive → Fin fresh.length → ℝ := fun i e => (fresh.get e).value i.val/cachedValue initial i.val

theorem weights_normalized (initial fresh : List (Parent n)) (positive : Finset (Fin n))
    (hpositive : ∀ i ∈ positive, 0 < cachedValue initial i)
    (htotal : ∀ i, cachedValue fresh i=cachedValue initial i) :
    ∀ i : positive, ∑ e, weights initial fresh positive i e=1 := by
  intro i
  simp only [weights,← Finset.sum_div,sum_component_values,htotal]
  exact div_self (ne_of_gt (hpositive i.val i.property))

theorem weights_small (P : Profile (Fin n)) (hmono : ∀ i, Monotone (P.cumulative i))
    (initial fresh : List (Parent n)) (hfresh : Valid P fresh) (positive : Finset (Fin n))
    (hpositive : ∀ i ∈ positive, 0 < cachedValue initial i) (K : ℝ) (hK : 0 < K)
    (hsmall : ∀ i ∈ positive, ∀ p ∈ fresh, p.value i ≤ cachedValue initial i/K) :
    ∀ (i : positive) e, 0 ≤ weights initial fresh positive i e ∧ weights initial fresh positive i e ≤ 1/K := by
  intro i e
  have ht := hpositive i.val i.property
  have hp := (valid_iff_forall _ _).mp hfresh (fresh.get e) (List.get_mem _ _)
  refine ⟨div_nonneg (validPart_nonnegative P hmono hp i.val) ht.le,?_⟩
  have h := div_le_div_of_nonneg_right
    (hsmall i.val i.property (fresh.get e) (List.get_mem fresh e)) ht.le
  have heq : (cachedValue initial i.val/K)/cachedValue initial i.val=1/K := by field_simp
  exact h.trans_eq heq

theorem normalized_color_value {m : ℕ} (initial fresh : List (Parent n)) (positive : Finset (Fin n))
    (color : Fin fresh.length → Fin m) (i : positive) (j : Fin m) :
    (∑ e, if color e=j then weights initial fresh positive i e else 0) =
      cachedValue (ColorCache.parts fresh color j) i.val/cachedValue initial i.val := by
  rw [ColorCache.parts_value,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : color e=j <;> simp only [weights,h,ite_true,ite_false,zero_div]

theorem rescale_near_equal (value total m : ℝ) (ht : 0 < total) (hm : 0 < m)
    (herror : |value/total-1/m| ≤ 1/(2*m)) :
    total/(2*m) ≤ value ∧ value ≤ 3*total/(2*m) := by
  have heq : 1/m=2*(1/(2*m)) := by field_simp
  have hthree : 3/(2*m)=3*(1/(2*m)) := by ring
  obtain ⟨hlo,hhi⟩ := abs_le.mp herror
  have hlo' : 1/(2*m) ≤ value/total := by rw [heq] at hlo; linarith
  have hhi' : value/total ≤ 3/(2*m) := by rw [heq] at hhi; rw [hthree]; linarith
  constructor
  · have h := (le_div_iff₀ ht).mp hlo'
    convert h using 1 <;> ring
  · have h := (div_le_iff₀ ht).mp hhi'
    convert h using 1 <;> ring

theorem rounding_scale (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    2*(r : ℝ)/(4*r*m : ℕ)=1/(2*(m : ℝ)) := by
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast
  field_simp
  ring

end EnvyFreeResearch.Full.Chores.NearEqual
