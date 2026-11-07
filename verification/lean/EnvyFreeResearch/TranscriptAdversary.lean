import EnvyFreeResearch.RootPreservation

/-!
Supporting lemmas for a moving-frontier adversary for the always-leftmost
signed Cut oracle. The lemmas cover the exact continuous first-root interface,
legal targets, a continuous affine rebuilding operation, and an independent
three-agent certificate that invalidates weaker transcript invariants.

This file does not formalize an adaptive protocol or a randomized lower bound.
-/

namespace EnvyFreeResearch.TranscriptAdversary

open Set ExtremalRoots

/-- Every recorded coordinate is either in the frozen prefix or the endpoint. -/
def FrozenCoordinate (l x : ℝ) : Prop := x ≤ l ∨ x = 1

/-- Strictly below the normalized total at every proper point of the domain. -/
def TerminalCeiling (F : ℝ → ℝ) : Prop :=
  F 1 = 1 ∧ ∀ x ∈ Ico (0 : ℝ) 1, F x < 1

theorem frozen_coordinate_value {F G : ℝ → ℝ} {l x : ℝ}
    (hp : ∀ y ∈ Icc (0 : ℝ) l, G y = F y)
    (h1 : G 1 = F 1) (hx0 : 0 ≤ x) (hx : FrozenCoordinate l x) :
    G x = F x := by
  rcases hx with hx | hx
  · exact hp x ⟨hx0, hx⟩
  · simpa [hx] using h1

/-- A first-root answer at the terminal point has positive target whenever
the query starts before that point. Negative-target queries cannot acquire
this exceptional kind of reply under the ceiling invariant. -/
theorem terminal_root_target_positive {F : ℝ → ℝ} {a b t : ℝ}
    (hF : TerminalCeiling F) (hr : FirstRoot F a b t 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 < t := by
  have ha := hF.2 a ⟨ha0, ha1⟩
  have he := hr.equation
  rw [hF.1] at he
  linarith

/-- Exact replay of a first-root answer. Roots in the frozen prefix are
protected by pointwise agreement there. A root at 1 is protected by the
strict terminal ceiling. No sign restriction on the target is assumed. -/
theorem first_reply_preserved {F G : ℝ → ℝ} {l a b t r : ℝ}
    (hp : ∀ y ∈ Icc (0 : ℝ) l, G y = F y)
    (hF1 : F 1 = 1) (hG : TerminalCeiling G)
    (ha0 : 0 ≤ a)
    (ha : FrozenCoordinate l a) (hrf : FrozenCoordinate l r)
    (hr : FirstRoot F a b t r) : FirstRoot G a b t r := by
  have h1 : G 1 = F 1 := by rw [hF1, hG.1]
  have haeq := frozen_coordinate_value hp h1 ha0 ha
  have hr0 : 0 ≤ r := le_trans ha0 hr.location.1
  have hreq := frozen_coordinate_value hp h1 hr0 hrf
  refine ⟨hr.location, ?_, ?_⟩
  · simpa only [haeq, hreq] using hr.equation
  · intro x hx heq
    by_contra h
    have hxr : x < r := lt_of_not_ge h
    have hx0 : 0 ≤ x := le_trans ha0 hx.1
    rcases hrf with hrl | hr1
    · have hxl : x ≤ l := le_trans (le_of_lt hxr) hrl
      have hxeq := hp x ⟨hx0, hxl⟩
      rw [hxeq, haeq] at heq
      exact not_lt_of_ge (hr.first x hx heq) hxr
    · have hx1 : x < 1 := by simpa [hr1] using hxr
      have hbar := hG.2 x ⟨hx0, hx1⟩
      have ht : F a + t = 1 := by simpa [hr1, hF1] using hr.equation.symm
      rw [haeq, ht] at heq
      linarith

theorem legal_target_preserved_on_frozen_coordinates
    {F G : ℝ → ℝ} {l a b t : ℝ}
    (hp : ∀ y ∈ Icc (0 : ℝ) l, G y = F y)
    (h1 : G 1 = F 1) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : FrozenCoordinate l a) (hb : FrozenCoordinate l b) :
    LegalTarget G a b t ↔ LegalTarget F a b t := by
  have hae := frozen_coordinate_value hp h1 ha0 ha
  have hbe := frozen_coordinate_value hp h1 hb0 hb
  simp only [LegalTarget, hae, hbe]

theorem frozen_interval_value {F G : ℝ → ℝ} {l a b : ℝ}
    (hp : ∀ y ∈ Icc (0 : ℝ) l, G y = F y)
    (h1 : G 1 = F 1) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : FrozenCoordinate l a) (hb : FrozenCoordinate l b) :
    G b - G a = F b - F a := by
  rw [frozen_coordinate_value hp h1 ha0 ha,
      frozen_coordinate_value hp h1 hb0 hb]

/-- A finite-union bundle is represented by the sum of its interval values.
Disjointness and endpoint conventions are not needed for this algebraic
identity; nonatomicity supplies that representation for actual shares. -/
theorem frozen_bundle_value {ι : Type*} (s : Finset ι)
    (left right : ι → ℝ) {F G : ℝ → ℝ} {l : ℝ}
    (hp : ∀ y ∈ Icc (0 : ℝ) l, G y = F y) (h1 : G 1 = F 1)
    (hleft0 : ∀ k ∈ s, 0 ≤ left k) (hright0 : ∀ k ∈ s, 0 ≤ right k)
    (hleft : ∀ k ∈ s, FrozenCoordinate l (left k))
    (hright : ∀ k ∈ s, FrozenCoordinate l (right k)) :
    (∑ k ∈ s, (G (right k) - G (left k))) =
      ∑ k ∈ s, (F (right k) - F (left k)) := by
  apply Finset.sum_congr rfl
  intro k hk
  exact frozen_interval_value hp h1 (hleft0 k hk) (hright0 k hk)
    (hleft k hk) (hright k hk)

/-- Replace a suffix by a descending affine segment and then an affine
segment ending at total 1. The queried row need not be rebuilt. -/
noncomputable def rebuild (F : ℝ → ℝ) (l h d x : ℝ) : ℝ :=
  if x ≤ l then F x
  else if x ≤ h then F l + d * (x - l)
  else F l + d * (h - l) +
    (1 - (F l + d * (h - l))) * ((x - h) / (1 - h))

theorem rebuild_prefix {F : ℝ → ℝ} {l h d x : ℝ} (hx : x ≤ l) :
    rebuild F l h d x = F x := by
  simp only [rebuild, hx, ite_true]

theorem rebuild_new_cell {F : ℝ → ℝ} {l h d x : ℝ}
    (hlx : l < x) (hxh : x ≤ h) :
    rebuild F l h d x = F l + d * (x - l) := by
  simp only [rebuild, not_le_of_gt hlx, ite_false, hxh, ite_true]

theorem rebuild_endpoint {F : ℝ → ℝ} {l h d : ℝ}
    (hlh : l < h) (hh1 : h < 1) : rebuild F l h d 1 = 1 := by
  have hl1 : l < 1 := lt_trans hlh hh1
  simp only [rebuild, not_le_of_gt hl1, ite_false, not_le_of_gt hh1]
  rw [div_self (by linarith : (1 : ℝ) - h ≠ 0)]
  ring

theorem rebuild_new_level_lt_one {F : ℝ → ℝ} {l h d : ℝ}
    (hFl : F l < 1) (hlh : l ≤ h) (hd : d ≤ 0) :
    F l + d * (h - l) < 1 := by
  have hp : d * (h - l) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd (sub_nonneg.mpr hlh)
  linarith

theorem rebuild_terminal_ceiling {F : ℝ → ℝ} {l h d : ℝ}
    (hF : TerminalCeiling F) (hl0 : 0 ≤ l)
    (hlh : l < h) (hh1 : h < 1) (hd : d ≤ 0) :
    TerminalCeiling (rebuild F l h d) := by
  refine ⟨rebuild_endpoint hlh hh1, ?_⟩
  intro x hx
  have hFl : F l < 1 := hF.2 l ⟨hl0, lt_trans hlh hh1⟩
  by_cases hxl : x ≤ l
  · rw [rebuild_prefix hxl]
    exact hF.2 x hx
  · have hlx : l < x := lt_of_not_ge hxl
    by_cases hxh : x ≤ h
    · rw [rebuild_new_cell hlx hxh]
      exact rebuild_new_level_lt_one hFl (le_of_lt hlx) hd
    · have hhx : h < x := lt_of_not_ge hxh
      have hu : F l + d * (h - l) < 1 :=
        rebuild_new_level_lt_one hFl (le_of_lt hlh) hd
      have hden : 0 < 1 - h := by linarith
      have hratio : (x - h) / (1 - h) < 1 := (div_lt_one hden).2 (by linarith [hx.2])
      have hprod := mul_lt_mul_of_pos_left hratio (by linarith : 0 < 1 - (F l + d * (h - l)))
      simp only [rebuild, hxl, ite_false, hxh]
      nlinarith

theorem rebuild_tail_slope_positive {F : ℝ → ℝ} {l h d : ℝ}
    (hFl : F l < 1) (hlh : l ≤ h) (hh1 : h < 1) (hd : d ≤ 0) :
    0 < (1 - (F l + d * (h - l))) / (1 - h) := by
  have hu := rebuild_new_level_lt_one hFl hlh hd
  exact div_pos (by linarith) (by linarith)

theorem rebuild_continuous {F : ℝ → ℝ} {l h d : ℝ}
    (hF : Continuous F) (hlh : l ≤ h) : Continuous (rebuild F l h d) := by
  have htail : Continuous (fun x : ℝ =>
      if x ≤ h then F l + d * (x - l)
      else F l + d * (h - l) +
        (1 - (F l + d * (h - l))) * ((x - h) / (1 - h))) := by
    apply Continuous.if
    · intro x hx
      have hxh : x = h := by
        change x ∈ frontier (Iic h) at hx
        simpa only [frontier_Iic, mem_singleton_iff] using hx
      subst x
      simp
    · fun_prop
    · fun_prop
  unfold rebuild
  apply Continuous.if
  · intro x hx
    have hxl : x = l := by
      change x ∈ frontier (Iic l) at hx
      simpa only [frontier_Iic, mem_singleton_iff] using hx
    subst x
    simp [hlh]
  · exact hF
  · exact htail

/-- A separate exact-EF certificate used to test proposed adversary
invariants. Columns are the two prefix shares and the remaining tail. -/
noncomputable def tailTable (a b x β y : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![a / 2, a / 2, 1 - a], ![x, b - x, 1 - b], ![y, -β - y, 1 + β]]

def EnvyFreeUnder (V : Fin 3 → Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ i j, V i (σ j) ≤ V i (σ i)

theorem anchored_prefix_cut_and_choose (a b x β y : ℝ)
    (ha : (2 : ℝ) / 3 ≤ a) (hb : (2 : ℝ) / 3 ≤ b)
    (hβ : 0 ≤ β) (hylo : -β ≤ y) (hyhi : y ≤ 1) :
    ∃ σ : Equiv.Perm (Fin 3), EnvyFreeUnder (tailTable a b x β y) σ := by
  by_cases hx : x ≤ b - x
  · refine ⟨Equiv.refl _, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailTable] <;> linarith
  · refine ⟨Equiv.swap 0 1, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [tailTable, Equiv.swap_apply_def] <;> linarith

/-- The scalar certificate follows from the actual signed first-crossing
barriers, rather than from a sign promise on the prefix densities. -/
theorem prefix_certificate_from_first_roots {F : ℝ → ℝ} {u r z β : ℝ}
    (hF : ContinuousOn F (Icc (0 : ℝ) 1)) (hF0 : F 0 = 0)
    (hu : FirstRoot F 0 u (-β) u) (hr : FirstRoot F 0 1 1 r)
    (hβ : 0 < β) (hu1 : u ≤ 1) (hur : u < r)
    (hz0 : 0 ≤ z) (hzu : z < u) : -β < F z ∧ F z < 1 := by
  have hcont : ContinuousOn F (Icc (0 : ℝ) u) := hF.mono (by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 hu1⟩)
  have hlo := first_negative_barrier hcont hu (by linarith : -β < 0) hz0 hzu
  have hhi := first_positive_barrier hF hr (by norm_num : (0 : ℝ) < 1) hz0 (lt_trans hzu hur)
  simpa [hF0] using And.intro hlo hhi

end EnvyFreeResearch.TranscriptAdversary
