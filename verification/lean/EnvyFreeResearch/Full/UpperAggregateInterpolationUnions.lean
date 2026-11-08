import EnvyFreeResearch.Full.UpperAggregateInterpolationTelescope
import EnvyFreeResearch.Full.UpperRecordedDomain

/-!
# Actual finite recorded unions and signed cumulative telescoping

A literal endpoint-owned component union is atomized on its recorded
boundaries. Endpoint ownership is retained by the underlying representation;
only the proved atomless-measure equality ignores finitely many endpoints.
The signed measure calculation then uses the cancellation theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperAggregateInterpolation

open UpperRecordedDomain UpperLogicalCells

def selectedUnion {m : ℕ} (cuts : Fin (m + 1) → ℝ) (selected : Finset (Fin m)) : Set ℝ :=
  ⋃ e ∈ selected, Ioc (cuts e.castSucc) (cuts e.succ)

def componentSelection {m : ℕ} (cs : List Component) (cuts : Fin (m + 1) → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun e => ∃ c ∈ cs, c.left ≤ cuts e.castSucc ∧ cuts e.succ ≤ c.right)

/-- All membership differences between the literal union and its selected
half-open atoms are among the explicitly supplied finite boundary tuple. -/
theorem domain_eq_selectedUnion_off_boundaries {m : ℕ} (cs : List Component)
    (cuts : Fin (m + 1) → ℝ) (hmono : Monotone cuts)
    (hendpoints : ∀ c ∈ cs, (∃ p, cuts p = c.left) ∧ ∃ p, cuts p = c.right)
    (x : ℝ) (hx : ∀ p, x ≠ cuts p) :
    x ∈ domain cs ↔ x ∈ selectedUnion cuts (componentSelection cs cuts) := by
  constructor
  · intro hxcs
    obtain ⟨c, hc, hxc⟩ := mem_domain.mp hxcs
    obtain ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩ := hendpoints c hc
    have hxc' := c.subset_closed hxc
    have hl : cuts 0 < x := lt_of_le_of_ne
      ((hmono (Fin.zero_le left)).trans (hleft.trans_le hxc'.1)) (Ne.symm (hx 0))
    have hr : x ≤ cuts (Fin.last m) := hxc'.2.trans (hright.symm.trans_le (hmono (Fin.le_last right)))
    have hI : x ∈ Ioc (cuts 0) (cuts (Fin.last m)) := ⟨hl, hr⟩
    rw [← consecutive_cover cuts hmono] at hI
    obtain ⟨e, he⟩ := mem_iUnion.mp hI
    have hlower : c.left ≤ cuts e.castSucc := by
      by_contra hn
      have hlt : e.castSucc < left := by
        by_contra hi
        have hh := hmono (le_of_not_gt hi)
        rw [hleft] at hh
        exact (not_le.mpr (lt_of_not_ge hn)) hh
      have hi : e.succ ≤ left := by change e.val + 1 ≤ left.val; exact hlt
      have hh := hmono hi
      rw [hleft] at hh
      exact hx left (by rw [hleft]; linarith [he.2, hxc'.1])
    have hupper : cuts e.succ ≤ c.right := by
      by_contra hn
      have hlt : right < e.succ := by
        by_contra hi
        have hh := hmono (le_of_not_gt hi)
        rw [hright] at hh
        exact (not_le.mpr (lt_of_not_ge hn)) hh
      have hi : right ≤ e.castSucc := by change right.val ≤ e.val; exact Nat.le_of_lt_succ hlt
      have hh := hmono hi
      rw [hright] at hh
      linarith [he.1, hxc'.2]
    exact mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, hlower, hupper⟩, he⟩
  · intro hxsel
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxsel
    obtain ⟨c, hc, hlower, hupper⟩ := (Finset.mem_filter.mp he).2
    apply mem_domain.mpr
    refine ⟨c, hc, c.interior_subset ⟨hlower.trans_lt hxe.1, ?_⟩⟩
    exact (lt_of_le_of_ne hxe.2 (hx e.succ)).trans_le hupper

theorem domain_ae_selectedUnion (μ : Measure ℝ) [NullSingletonClass μ] {m : ℕ}
    (cs : List Component) (cuts : Fin (m + 1) → ℝ) (hmono : Monotone cuts)
    (hendpoints : ∀ c ∈ cs, (∃ p, cuts p = c.left) ∧ ∃ p, cuts p = c.right) :
    domain cs =ᵐ[μ] selectedUnion cuts (componentSelection cs cuts) := by
  have h : ∀ᵐ x ∂μ, ∀ p, x ≠ cuts p := ae_all_iff.mpr (fun p => μ.ae_ne (cuts p))
  filter_upwards [h] with x hx
  exact propext (domain_eq_selectedUnion_off_boundaries cs cuts hmono hendpoints x hx)

/-- A finite real linear combination of actual measures. -/
def signedValue {Term : Type*} [Fintype Term] (coeff : Term → ℝ) (μ : Term → Measure ℝ)
    (E : Set ℝ) : ℝ := ∑ t, coeff t * (μ t).real E

variable {Term : Type*} [Fintype Term] (coeff : Term → ℝ) (μ : Term → Measure ℝ)
  [∀ t, IsFiniteMeasure (μ t)]

theorem signedValue_Ioc (a b : ℝ) (hab : a ≤ b) :
    signedValue coeff μ (Ioc a b) = signedValue coeff μ (Iic b) - signedValue coeff μ (Iic a) := by
  have heq : Ioc a b = Iic b \ Iic a := by ext x; simp
  have hmass (t : Term) : (μ t).real (Ioc a b) = (μ t).real (Iic b) - (μ t).real (Iic a) := by
    rw [heq, measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic]
  simp only [signedValue, hmass, mul_sub, Finset.sum_sub_distrib]

theorem signedValue_selectedUnion {m : ℕ} (cuts : Fin (m + 1) → ℝ) (hmono : Monotone cuts)
    (selected : Finset (Fin m)) :
    signedValue coeff μ (selectedUnion cuts selected) =
      ∑ e, (if e ∈ selected then (1 : ℝ) else 0) *
        (signedValue coeff μ (Iic (cuts e.succ)) - signedValue coeff μ (Iic (cuts e.castSucc))) := by
  have hmass (t : Term) : (μ t).real (selectedUnion cuts selected) =
      ∑ e ∈ selected, (μ t).real (Ioc (cuts e.castSucc) (cuts e.succ)) :=
    measureReal_biUnion_finset (fun i _ j _ hij => consecutive_disjoint cuts hmono hij)
      (fun _ _ => measurableSet_Ioc)
  calc
    _ = ∑ e ∈ selected, signedValue coeff μ (Ioc (cuts e.castSucc) (cuts e.succ)) := by
      simp only [signedValue, hmass, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ e ∈ selected, (signedValue coeff μ (Iic (cuts e.succ)) -
        signedValue coeff μ (Iic (cuts e.castSucc))) := by
      apply Finset.sum_congr rfl
      intro e _
      exact signedValue_Ioc coeff μ _ _ (hmono (by simp [Fin.le_def]))
    _ = _ := by simp [← Finset.sum_filter]

/-- Error of any literal finite component union, with its boundary signs
derived from the actual selected-atom decomposition. -/
theorem recorded_union_error_le [∀ t, NullSingletonClass (μ t)] {m : ℕ}
    {Generated : Type*} [Fintype Generated] (cs : List Component)
    (cuts : Fin (m + 1) → ℝ) (hcuts : StrictMono cuts)
    (hendpoints : ∀ c ∈ cs, (∃ p, cuts p = c.left) ∧ ∃ p, cuts p = c.right)
    (points : Generated → ℝ)
    (hcover : ∀ p, signedValue coeff μ (Iic (cuts p)) = 0 ∨ ∃ j, points j = cuts p) :
    |signedValue coeff μ (domain cs)| ≤ ∑ j, |signedValue coeff μ (Iic (points j))| := by
  have heq : signedValue coeff μ (domain cs) =
      signedValue coeff μ (selectedUnion cuts (componentSelection cs cuts)) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [measureReal_congr (domain_ae_selectedUnion (μ t) cs cuts hcuts.monotone hendpoints)]
  rw [heq, signedValue_selectedUnion coeff μ cuts hcuts.monotone]
  apply selected_union_error_le_generated cuts hcuts.injective points
    (fun z => signedValue coeff μ (Iic z)) hcover
  intro e
  split_ifs <;> norm_num

end EnvyFreeResearch.Full.UpperAggregateInterpolation
