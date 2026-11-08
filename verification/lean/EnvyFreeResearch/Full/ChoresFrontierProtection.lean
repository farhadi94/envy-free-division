import EnvyFreeResearch.Full.ChoresFrontierScan

/-! Cached suffix protection follows from the actual separated gap and
atom rows. In particular, an omitted observer's equalizer cannot lie on
the wrong side of a wholly small suffix. -/

noncomputable section
namespace EnvyFreeResearch.Full.Chores.Frontier
open scoped Classical

variable {n : ℕ}

theorem omitted_rank_le (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ)
    (hr : ∀ i, 0 < r i) (hH : 0 < H) (hscale : (n : ℝ) < H*H)
    (hgaps : GapSeparated w rank r H) (t : ℕ)
    (hsmall : ∀ a : Fin n, t < a.val → Small w r H a)
    (i : Fin n) (hi : i ∉ eligible w rank r H) : rank i ≤ t := by
  by_contra h
  have hrank : t < rank i := lt_of_not_ge h
  have hsuffix := tail_small w i (rank i) (r i) H (hr i).le hH
    (fun a ha => hsmall a (hrank.trans_le ha) i)
  exact separated_gap_contradiction (r i) H (hr i) hH hscale _
    (omitted_gap_large w rank r H hgaps i hi) hsuffix

theorem outside_small_protection (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hr : ∀ i, 0 < r i) (hH : 0 < H) (hscale : (n : ℝ) < H*H)
    (hgaps : GapSeparated w rank r H) (C : Finset (Fin n)) (q : Fin n)
    (hstop : (Stop.outside q).Valid rank (eligible w rank r H) C)
    (hsmall : ∀ a : Fin n, rank q ≤ a.val → Small w r H a)
    (i : Fin n) (hi : i ∉ C) : tailCost w i (rank q) ≤ tailCost w i (rank i) := by
  apply tail_antitone w hw i
  by_cases he : i ∈ eligible w rank r H
  · exact hstop.2 i (Finset.mem_sdiff.mpr ⟨he,hi⟩)
  · exact omitted_rank_le w rank r H hr hH hscale hgaps (rank q)
      (fun a ha => hsmall a ha.le) i he

theorem exhausted_participant (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (C : Finset (Fin n)) (q : Fin n)
    (hstop : (Stop.exhausted q).Valid rank (eligible w rank r H) C)
    (i : Fin n) (hi : i ∈ eligible w rank r H) : tailCost w i (rank i) ≤ tailCost w i (rank q) :=
  tail_antitone w hw i (hstop.2.2 i hi)

theorem exhausted_outside_protection (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hr : ∀ i, 0 < r i) (hH : 0 < H) (hscale : (n : ℝ) < H*H)
    (hgaps : GapSeparated w rank r H) (q : Fin n)
    (hsmall : ∀ a : Fin n, rank q ≤ a.val → Small w r H a)
    (i : Fin n) (hi : i ∉ eligible w rank r H) : tailCost w i (rank q) ≤ tailCost w i (rank i) :=
  tail_antitone w hw i (omitted_rank_le w rank r H hr hH hscale hgaps (rank q)
    (fun a ha => hsmall a ha.le) i hi)

theorem exhausted_deviation (w : Fin n → Fin n → ℝ) (rank : Fin n → ℕ) (r : Fin n → ℝ) (H : ℝ)
    (hr : ∀ i, 0 < r i) (hH : 0 < H) (hgaps : GapSeparated w rank r H) (q : Fin n)
    (hsmall : ∀ a : Fin n, rank q ≤ a.val → Small w r H a)
    (i : Fin n) (hi : i ∉ eligible w rank r H) :
    (H-(n : ℝ)/H)*r i ≤ tailCost w i (rank i)-tailCost w i (rank q) := by
  have hl := omitted_gap_large w rank r H hgaps i hi
  have hs := tail_small w i (rank q) (r i) H (hr i).le hH (fun a ha => hsmall a ha i)
  calc
    (H-(n : ℝ)/H)*r i=H*r i-(n : ℝ)*r i/H := by ring
    _ ≤ tailCost w i (rank i)-tailCost w i (rank q) := by linarith

end EnvyFreeResearch.Full.Chores.Frontier
