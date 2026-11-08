import EnvyFreeResearch.Full.UpperGridInterpolationLinear

/-! Joint measurability of the original-grid interpolation error. -/

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperGridSensitivity

variable {X Row : Type*} [MeasurableSpace X] [Fintype Row] [Nonempty Row] {n : ℕ}

theorem cellFraction_measurable (L : ℝ → ℝ) (hL : Measurable L)
    (cuts : X → Fin (n + 1) → ℝ) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (test : X → ℝ) (htest : Measurable test) (e : Fin n) :
    Measurable (fun z => cellFraction L (cuts z) (test z) e) :=
  ((hL.comp ((hcuts e.succ).min htest)).sub (hL.comp ((hcuts e.castSucc).min htest))).div
    ((hL.comp (hcuts e.succ)).sub (hL.comp (hcuts e.castSucc)))

theorem linearEstimate_measurable (F L : ℝ → ℝ) (hF : Measurable F) (hL : Measurable L)
    (cuts : X → Fin (n + 1) → ℝ) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (test : X → ℝ) (htest : Measurable test) :
    Measurable (fun z => linearEstimate F L (cuts z) (test z)) :=
  (hF.comp (hcuts 0)).add (Finset.measurable_sum _ (fun e _ =>
    ((hF.comp (hcuts e.succ)).sub (hF.comp (hcuts e.castSucc))).mul
      (cellFraction_measurable L hL cuts hcuts test htest e)))

theorem linearError_measurable (F : Row → ℝ → ℝ) (hF : ∀ i, Measurable (F i))
    (L : ℝ → ℝ) (hL : Measurable L)
    (cuts : X → Fin (n + 1) → ℝ) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (test : X → ℝ) (htest : Measurable test) (i j : Row) :
    Measurable (fun z => linearError F L (cuts z) (test z) i j) :=
  (((hF i).comp htest).sub ((hF j).comp htest)).sub
    ((linearEstimate_measurable (F i) L (hF i) hL cuts hcuts test htest).sub
      (linearEstimate_measurable (F j) L (hF j) hL cuts hcuts test htest)) |>.abs

theorem linearMaximum_measurable (F : Row → ℝ → ℝ) (hF : ∀ i, Measurable (F i))
    (L : ℝ → ℝ) (hL : Measurable L)
    (cuts : X → Fin (n + 1) → ℝ) (hcuts : ∀ e, Measurable (fun z => cuts z e))
    (test : X → ℝ) (htest : Measurable test) :
    Measurable (fun z => linearMaximum F L (cuts z) (test z)) := by
  have hr (i : Row) (e : Fin n) : Measurable (fun z => linearRows F (cuts z) i e) :=
    ((hF i).comp (hcuts e.succ)).sub ((hF i).comp (hcuts e.castSucc))
  have hd (i j : Row) : Measurable (fun z => distance (linearRows F (cuts z)) i j) :=
    Finset.measurable_sum _ (fun e _ => ((hr i e).sub (hr j e)).abs)
  have he := linearError_measurable F hF L hL cuts hcuts test htest
  have h := Finset.measurable_sup' (s := (Finset.univ : Finset (Row × Row)))
    Finset.univ_nonempty (fun ij _ => (he ij.1 ij.2).div ((hd ij.1 ij.2).add (he ij.1 ij.2)))
  convert h using 1
  funext z
  simp [linearMaximum]

end EnvyFreeResearch.Full.UpperGridInterpolation
