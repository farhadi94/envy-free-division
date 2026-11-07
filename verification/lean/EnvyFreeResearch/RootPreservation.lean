import Mathlib

/-!
Continuous extremal-root preservation under one-sided cumulative perturbations.

This file proves the strict pre/post-root barriers from continuity and the
intermediate value theorem, then proves preservation of first/last roots.
It does not formalize the whole adaptive signed-valuation lower bound.
-/

namespace EnvyFreeResearch.ExtremalRoots

open Set

structure FirstRoot (F : ℝ → ℝ) (a b t r : ℝ) : Prop where
  location : r ∈ Icc a b
  equation : F r = F a + t
  first : ∀ x ∈ Icc a b, F x = F a + t → r ≤ x

structure LastRoot (F : ℝ → ℝ) (a b t r : ℝ) : Prop where
  location : r ∈ Icc a b
  equation : F r = F a + t
  last : ∀ x ∈ Icc a b, F x = F a + t → x ≤ r

def LegalTarget (F : ℝ → ℝ) (a b t : ℝ) : Prop :=
  min 0 (F b - F a) ≤ t ∧ t ≤ max 0 (F b - F a)

variable {F G : ℝ → ℝ} {a b t r x : ℝ}

theorem first_positive_barrier
    (hc : ContinuousOn F (Icc a b)) (hr : FirstRoot F a b t r)
    (ht : 0 < t) (hax : a ≤ x) (hxr : x < r) : F x < F a + t := by
  by_contra h
  have hcx : ContinuousOn F (Icc a x) := hc.mono (by
    intro y hy
    exact ⟨hy.1, le_trans hy.2 (le_trans (le_of_lt hxr) hr.location.2)⟩)
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc hax hcx
    (show F a + t ∈ Icc (F a) (F x) from ⟨by linarith, le_of_not_gt h⟩)
  have hry := hr.first y ⟨hy.1, le_trans hy.2 (le_trans (le_of_lt hxr) hr.location.2)⟩ heq
  linarith [hy.2]

theorem first_negative_barrier
    (hc : ContinuousOn F (Icc a b)) (hr : FirstRoot F a b t r)
    (ht : t < 0) (hax : a ≤ x) (hxr : x < r) : F a + t < F x := by
  by_contra h
  have hcx : ContinuousOn F (Icc a x) := hc.mono (by
    intro y hy
    exact ⟨hy.1, le_trans hy.2 (le_trans (le_of_lt hxr) hr.location.2)⟩)
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc' hax hcx
    (show F a + t ∈ Icc (F x) (F a) from ⟨le_of_not_gt h, by linarith⟩)
  have hry := hr.first y ⟨hy.1, le_trans hy.2 (le_trans (le_of_lt hxr) hr.location.2)⟩ heq
  linarith [hy.2]

theorem last_positive_barrier
    (hc : ContinuousOn F (Icc a b)) (hr : LastRoot F a b t r)
    (htb : t ≤ F b - F a) (hrx : r < x) (hxb : x ≤ b) :
    F a + t < F x := by
  by_contra h
  have hcx : ContinuousOn F (Icc x b) := hc.mono (by
    intro y hy
    exact ⟨le_trans hr.location.1 (le_trans (le_of_lt hrx) hy.1), hy.2⟩)
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc hxb hcx
    (show F a + t ∈ Icc (F x) (F b) from ⟨le_of_not_gt h, by linarith⟩)
  have hyr := hr.last y ⟨le_trans hr.location.1 (le_trans (le_of_lt hrx) hy.1), hy.2⟩ heq
  linarith [hy.1]

theorem last_negative_barrier
    (hc : ContinuousOn F (Icc a b)) (hr : LastRoot F a b t r)
    (hbt : F b - F a ≤ t) (hrx : r < x) (hxb : x ≤ b) :
    F x < F a + t := by
  by_contra h
  have hcx : ContinuousOn F (Icc x b) := hc.mono (by
    intro y hy
    exact ⟨le_trans hr.location.1 (le_trans (le_of_lt hrx) hy.1), hy.2⟩)
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc' hxb hcx
    (show F a + t ∈ Icc (F b) (F x) from ⟨by linarith, le_of_not_gt h⟩)
  have hyr := hr.last y ⟨le_trans hr.location.1 (le_trans (le_of_lt hrx) hy.1), hy.2⟩ heq
  linarith [hy.1]

theorem first_negative_preserved_up
    (hc : ContinuousOn F (Icc a b)) (hr : FirstRoot F a b t r)
    (ht : t < 0) (hG : ∀ x ∈ Icc a b, 0 ≤ G x)
    (ha : G a = 0) (hrr : G r = 0) :
    FirstRoot (fun x => F x + G x) a b t r := by
  refine ⟨hr.location, by simpa [ha, hrr] using hr.equation, ?_⟩
  intro x hx heq
  by_contra h
  have hxr : x < r := lt_of_not_ge h
  have hbar := first_negative_barrier hc hr ht hx.1 hxr
  have hnon := hG x hx
  simp only [ha, add_zero] at heq
  linarith

theorem last_positive_preserved_up
    (hc : ContinuousOn F (Icc a b)) (hr : LastRoot F a b t r)
    (htb : t ≤ F b - F a) (hG : ∀ x ∈ Icc a b, 0 ≤ G x)
    (ha : G a = 0) (hrr : G r = 0) :
    LastRoot (fun x => F x + G x) a b t r := by
  refine ⟨hr.location, by simpa [ha, hrr] using hr.equation, ?_⟩
  intro x hx heq
  by_contra h
  have hrx : r < x := lt_of_not_ge h
  have hbar := last_positive_barrier hc hr htb hrx hx.2
  have hnon := hG x hx
  simp only [ha, add_zero] at heq
  linarith

theorem first_positive_preserved_down
    (hc : ContinuousOn F (Icc a b)) (hr : FirstRoot F a b t r)
    (ht : 0 < t) (hG : ∀ x ∈ Icc a b, G x ≤ 0)
    (ha : G a = 0) (hrr : G r = 0) :
    FirstRoot (fun x => F x + G x) a b t r := by
  refine ⟨hr.location, by simpa [ha, hrr] using hr.equation, ?_⟩
  intro x hx heq
  by_contra h
  have hxr : x < r := lt_of_not_ge h
  have hbar := first_positive_barrier hc hr ht hx.1 hxr
  have hnon := hG x hx
  simp only [ha, add_zero] at heq
  linarith

theorem last_negative_preserved_down
    (hc : ContinuousOn F (Icc a b)) (hr : LastRoot F a b t r)
    (hbt : F b - F a ≤ t) (hG : ∀ x ∈ Icc a b, G x ≤ 0)
    (ha : G a = 0) (hrr : G r = 0) :
    LastRoot (fun x => F x + G x) a b t r := by
  refine ⟨hr.location, by simpa [ha, hrr] using hr.equation, ?_⟩
  intro x hx heq
  by_contra h
  have hrx : r < x := lt_of_not_ge h
  have hbar := last_negative_barrier hc hr hbt hrx hx.2
  have hnon := hG x hx
  simp only [ha, add_zero] at heq
  linarith

theorem legal_target_preserved (ha : G a = 0) (hb : G b = 0) :
    LegalTarget (fun x => F x + G x) a b t ↔ LegalTarget F a b t := by
  simp [LegalTarget, ha, hb]

theorem first_root_zero (hab : a ≤ b) : FirstRoot F a b 0 a := by
  refine ⟨⟨le_rfl, hab⟩, by simp, ?_⟩
  intro x hx _
  exact hx.1

theorem first_zero_eq_left (hr : FirstRoot F a b 0 r) : r = a := by
  apply le_antisymm
  · exact hr.first a ⟨le_rfl, le_trans hr.location.1 hr.location.2⟩ (by simp)
  · exact hr.location.1

theorem first_zero_preserved (hr : FirstRoot F a b 0 r) :
    FirstRoot (fun x => F x + G x) a b 0 r := by
  have hab := le_trans hr.location.1 hr.location.2
  rw [first_zero_eq_left hr]
  exact first_root_zero hab

theorem last_root_total (hab : a ≤ b) : LastRoot F a b (F b - F a) b := by
  refine ⟨⟨hab, le_rfl⟩, by ring, ?_⟩
  intro x hx _
  exact hx.2

theorem last_total_eq_right (hr : LastRoot F a b (F b - F a) r) : r = b := by
  apply le_antisymm hr.location.2
  exact hr.last b ⟨le_trans hr.location.1 hr.location.2, le_rfl⟩ (by ring)

def BracketUpReply (F : ℝ → ℝ) (a b t r : ℝ) : Prop :=
  if 0 ≤ F b - F a then LastRoot F a b t r else FirstRoot F a b t r

def BracketDownReply (F : ℝ → ℝ) (a b t r : ℝ) : Prop :=
  if 0 ≤ F b - F a then FirstRoot F a b t r else LastRoot F a b t r

/-- The rightmost root for a nonnegative bracket total and the leftmost root
for a negative total are preserved by an upward cumulative perturbation.
This includes zero targets, targets equal to the total, and zero totals. -/
theorem bracket_up_reply_preserved
    (hc : ContinuousOn F (Icc a b)) (hl : LegalTarget F a b t)
    (hr : BracketUpReply F a b t r) (hG : ∀ x ∈ Icc a b, 0 ≤ G x)
    (ha : G a = 0) (hb : G b = 0) (hrr : G r = 0) :
    BracketUpReply (fun x => F x + G x) a b t r := by
  by_cases hB : 0 ≤ F b - F a
  · simp only [BracketUpReply, ha, hb, add_zero, hB, ite_true] at hr ⊢
    have htb : t ≤ F b - F a := by
      simpa only [max_eq_right hB] using hl.2
    exact last_positive_preserved_up hc hr htb hG ha hrr
  · simp only [BracketUpReply, ha, hb, add_zero, hB, ite_false] at hr ⊢
    have ht0 : t ≤ 0 := by
      simpa only [max_eq_left (le_of_lt (lt_of_not_ge hB))] using hl.2
    by_cases ht : t < 0
    · exact first_negative_preserved_up hc hr ht hG ha hrr
    · have htz : t = 0 := by linarith
      subst t
      exact first_zero_preserved hr

/-- The mirrored prescribed rule, including all endpoint cases. -/
theorem bracket_down_reply_preserved
    (hc : ContinuousOn F (Icc a b)) (hl : LegalTarget F a b t)
    (hr : BracketDownReply F a b t r) (hG : ∀ x ∈ Icc a b, G x ≤ 0)
    (ha : G a = 0) (hb : G b = 0) (hrr : G r = 0) :
    BracketDownReply (fun x => F x + G x) a b t r := by
  by_cases hB : 0 ≤ F b - F a
  · simp only [BracketDownReply, ha, hb, add_zero, hB, ite_true] at hr ⊢
    have h0t : 0 ≤ t := by
      simpa only [min_eq_left hB] using hl.1
    by_cases ht : 0 < t
    · exact first_positive_preserved_down hc hr ht hG ha hrr
    · have htz : t = 0 := by linarith
      subst t
      exact first_zero_preserved hr
  · simp only [BracketDownReply, ha, hb, add_zero, hB, ite_false] at hr ⊢
    have hbt : F b - F a ≤ t := by
      simpa only [min_eq_right (le_of_lt (lt_of_not_ge hB))] using hl.1
    exact last_negative_preserved_down hc hr hbt hG ha hrr

def UpReply (F : ℝ → ℝ) (a b t r : ℝ) : Prop :=
  if 0 < t then LastRoot F a b t r
  else if t < 0 then FirstRoot F a b t r else r = a

def DownReply (F : ℝ → ℝ) (a b t r : ℝ) : Prop :=
  if 0 < t then FirstRoot F a b t r
  else if t < 0 then LastRoot F a b t r else r = a

theorem up_reply_preserved
    (hc : ContinuousOn F (Icc a b)) (hl : LegalTarget F a b t)
    (hr : UpReply F a b t r) (hG : ∀ x ∈ Icc a b, 0 ≤ G x)
    (ha : G a = 0) (hrr : G r = 0) :
    UpReply (fun x => F x + G x) a b t r := by
  by_cases hp : 0 < t
  · simp only [UpReply, hp, ite_true] at hr ⊢
    have htb : t ≤ F b - F a := by
      rcases le_max_iff.mp hl.2 with h | h
      · linarith
      · exact h
    exact last_positive_preserved_up hc hr htb hG ha hrr
  · by_cases hn : t < 0
    · simp only [UpReply, hp, hn, ite_false, ite_true] at hr ⊢
      exact first_negative_preserved_up hc hr hn hG ha hrr
    · simpa only [UpReply, hp, hn, ite_false] using hr

theorem down_reply_preserved
    (hc : ContinuousOn F (Icc a b)) (hl : LegalTarget F a b t)
    (hr : DownReply F a b t r) (hG : ∀ x ∈ Icc a b, G x ≤ 0)
    (ha : G a = 0) (hrr : G r = 0) :
    DownReply (fun x => F x + G x) a b t r := by
  by_cases hp : 0 < t
  · simp only [DownReply, hp, ite_true] at hr ⊢
    exact first_positive_preserved_down hc hr hp hG ha hrr
  · by_cases hn : t < 0
    · simp only [DownReply, hp, hn, ite_false, ite_true] at hr ⊢
      have hbt : F b - F a ≤ t := by
        rcases min_le_iff.mp hl.1 with h | h
        · linarith
        · exact h
      exact last_negative_preserved_down hc hr hbt hG ha hrr
    · simpa only [DownReply, hp, hn, ite_false] using hr

/-- Equal-mass pulses on ordered disjoint supports have nonnegative cumulative
perturbation when the positive support lies first. `P` and `N` are their
normalized cumulative masses; the hypotheses follow from their supports. -/
theorem ordered_pair_cumulative_nonnegative
    {P N : ℝ → ℝ} {u v M : ℝ} (huv : u ≤ v) (hM : 0 ≤ M)
    (hP : ∀ x, 0 ≤ P x) (hN : ∀ x, N x ≤ 1)
    (hPfull : ∀ x, u ≤ x → P x = 1)
    (hNempty : ∀ x, x ≤ v → N x = 0) :
    ∀ x, 0 ≤ M * (P x - N x) := by
  intro x
  apply mul_nonneg hM
  by_cases hx : x ≤ v
  · rw [hNempty x hx, sub_zero]
    exact hP x
  · rw [hPfull x (le_trans huv (le_of_lt (lt_of_not_ge hx)))]
    linarith [hN x]

theorem cumulative_pair_zero_when_equal {M p q : ℝ} (heq : p = q) :
    M * (p - q) = 0 := by simp [heq]

theorem finite_sum_nonnegative {ι : Type*} (s : Finset ι) (H : ι → ℝ → ℝ)
    (hH : ∀ i ∈ s, ∀ x, 0 ≤ H i x) :
    ∀ x, 0 ≤ ∑ i ∈ s, H i x := by
  intro x
  exact Finset.sum_nonneg (fun i hi => hH i hi x)

theorem reverse_pulses_nonpositive {H : ℝ → ℝ} (hH : ∀ x, 0 ≤ H x) :
    ∀ x, -H x ≤ 0 := by intro x; exact neg_nonpos.mpr (hH x)

def reflected (F : ℝ → ℝ) (x : ℝ) : ℝ := F 1 - F (1 - x)

theorem reflected_query_difference :
    reflected F (1 - x) - reflected F (1 - b) =
      (F b - F a) - (F x - F a) := by
  have hx : 1 - (1 - x) = x := by ring
  have hb : 1 - (1 - b) = b := by ring
  simp only [reflected, hx, hb]
  ring

theorem reflected_bracket_total :
    reflected F (1 - a) - reflected F (1 - b) = F b - F a := by
  have ha : 1 - (1 - a) = a := by ring
  have hb : 1 - (1 - b) = b := by ring
  simp only [reflected, ha, hb]
  ring

theorem reflected_target_legal :
    LegalTarget (reflected F) (1 - b) (1 - a) (F b - F a - t) ↔
      LegalTarget F a b t := by
  simp only [LegalTarget, reflected_bracket_total]
  by_cases hB : 0 ≤ F b - F a
  · simp only [min_eq_left hB, max_eq_right hB]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · have hB' : F b - F a ≤ 0 := le_of_lt (lt_of_not_ge hB)
    simp only [min_eq_right hB', max_eq_left hB']
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem first_reflects_to_last (hr : FirstRoot F a b t r) :
    LastRoot (reflected F) (1 - b) (1 - a) (F b - F a - t) (1 - r) := by
  have hb : 1 - (1 - b) = b := by ring
  have hrr : 1 - (1 - r) = r := by ring
  refine ⟨⟨by linarith [hr.location.2], by linarith [hr.location.1]⟩, ?_, ?_⟩
  · simp only [reflected, hb, hrr]
    linarith [hr.equation]
  · intro y hy heq
    have hloc : 1 - y ∈ Icc a b := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hroot : F (1 - y) = F a + t := by
      simp only [reflected, hb] at heq
      linarith
    have h := hr.first (1 - y) hloc hroot
    linarith

theorem last_reflects_to_first (hr : LastRoot F a b t r) :
    FirstRoot (reflected F) (1 - b) (1 - a) (F b - F a - t) (1 - r) := by
  have hb : 1 - (1 - b) = b := by ring
  have hrr : 1 - (1 - r) = r := by ring
  refine ⟨⟨by linarith [hr.location.2], by linarith [hr.location.1]⟩, ?_, ?_⟩
  · simp only [reflected, hb, hrr]
    linarith [hr.equation]
  · intro y hy heq
    have hloc : 1 - y ∈ Icc a b := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hroot : F (1 - y) = F a + t := by
      simp only [reflected, hb] at heq
      linarith
    have h := hr.last (1 - y) hloc hroot
    linarith

theorem bracket_up_reflects_to_down (hr : BracketUpReply F a b t r) :
    BracketDownReply (reflected F) (1 - b) (1 - a)
      (F b - F a - t) (1 - r) := by
  simp only [BracketUpReply] at hr
  simp only [BracketDownReply, reflected_bracket_total]
  by_cases hB : 0 ≤ F b - F a
  · simp only [hB, ite_true] at hr ⊢
    exact last_reflects_to_first hr
  · simp only [hB, ite_false] at hr ⊢
    exact first_reflects_to_last hr

theorem bracket_down_reflects_to_up (hr : BracketDownReply F a b t r) :
    BracketUpReply (reflected F) (1 - b) (1 - a)
      (F b - F a - t) (1 - r) := by
  simp only [BracketDownReply] at hr
  simp only [BracketUpReply, reflected_bracket_total]
  by_cases hB : 0 ≤ F b - F a
  · simp only [hB, ite_true] at hr ⊢
    exact first_reflects_to_last hr
  · simp only [hB, ite_false] at hr ⊢
    exact last_reflects_to_first hr

end EnvyFreeResearch.ExtremalRoots
