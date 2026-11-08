import EnvyFreeResearch.Full.UpperGridInterpolationAverage
import Mathlib.MeasureTheory.Order.Lattice

/-! Borel measurability of the concrete finite interpolation computations. -/

noncomputable section

open MeasureTheory
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperGridInterpolation

open UpperGridSensitivity UpperSortedGrid

variable {X Row Coord Index : Type*} [MeasurableSpace X]
  [Fintype Coord] [Fintype Row] [Nonempty Row] [Fintype Index]

theorem deletedVariation_measurable (x : X → Row → Coord → ℝ)
    (hx : ∀ i a, Measurable (fun z => x z i a)) (u v : Row) (left right : Coord) :
    Measurable (fun z => deletedVariation (x z) u v left right) :=
  (Finset.measurable_sum _ (fun a _ => ((hx u a).sub (hx v a)).abs)).add
    ((((hx u left).sub (hx v left)).add ((hx u right).sub (hx v right))).abs)

theorem deletionError_measurable (x : X → Row → Coord → ℝ)
    (hx : ∀ i a, Measurable (fun z => x z i a)) (u v : Row) (left right : Coord)
    (theta : X → ℝ) (htheta : Measurable theta) :
    Measurable (fun z => deletionError (x z) u v left right (theta z)) :=
  (((hx u left).sub (hx v left)).sub
    (htheta.mul (((hx u left).sub (hx v left)).add ((hx u right).sub (hx v right))))).abs

theorem normalizedDeletion_measurable (x : X → Row → Coord → ℝ)
    (hx : ∀ i a, Measurable (fun z => x z i a)) (u v : Row) (left right : Coord)
    (theta : X → ℝ) (htheta : Measurable theta) :
    Measurable (fun z => normalizedDeletion (x z) u v left right (theta z)) :=
  (deletionError_measurable x hx u v left right theta htheta).div
    ((deletedVariation_measurable x hx u v left right).add
      (deletionError_measurable x hx u v left right theta htheta))

theorem maxDeletion_measurable (x : X → Row → Coord → ℝ)
    (hx : ∀ i a, Measurable (fun z => x z i a)) (left right : Coord)
    (theta : X → ℝ) (htheta : Measurable theta) :
    Measurable (fun z => maxDeletion (x z) left right (theta z)) := by
  have h := Finset.measurable_sup' (s := (Finset.univ : Finset (Row × Row)))
    Finset.univ_nonempty (fun uv _ => normalizedDeletion_measurable x hx uv.1 uv.2 left right theta htheta)
  convert h using 1
  funext z
  simp [maxDeletion]

theorem fiberCount_measurable (f : X → Index → ℝ) (hf : ∀ i, Measurable (fun z => f z i))
    (v : X → ℝ) (hv : Measurable v) : Measurable (fun z => fiberCount (f z) (v z)) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.ite (measurableSet_eq_fun (hf i) hv) measurable_const

theorem fiberMean_measurable (f : X → Index → ℝ) (hf : ∀ i, Measurable (fun z => f z i))
    (h : X → Index → ℝ) (hh : ∀ i, Measurable (fun z => h z i))
    (v : X → ℝ) (hv : Measurable v) : Measurable (fun z => fiberMean (f z) (h z) (v z)) := by
  apply Finset.measurable_sum
  intro i _
  exact ((hh i).div (fiberCount_measurable f hf v hv)).ite
    (measurableSet_eq_fun (hf i) hv) measurable_const

theorem nodeScores_measurable {m : ℕ} (d : X → Fin m → ℝ)
    (hd : ∀ p, Measurable (fun z => d z p)) (i : Fin (m + 2)) :
    Measurable (fun z => nodeScores (d z) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · refine Fin.lastCases ?_ (fun p => ?_) j
    · simpa [nodeScores] using (show Measurable (fun _ : X => (0 : ℝ)) from measurable_const)
    · simpa [nodeScores] using hd p

theorem gridRows_measurable {m : ℕ} (F : Row → ℝ → ℝ) (hF : ∀ i, Measurable (F i))
    (values : X → Fin (m + 2) → ℝ) (hvalues : ∀ e, Measurable (fun z => values z e))
    (i : Row) (e : Fin (m + 1)) : Measurable (fun z => gridRows F (values z) i e) := by
  have hs := sorted_measurable values hvalues
  exact ((hF i).comp ((measurable_pi_apply e.succ).comp hs)).sub
    ((hF i).comp ((measurable_pi_apply e.castSucc).comp hs))

theorem gridTheta_measurable {m : ℕ} (L : ℝ → ℝ) (hL : Measurable L)
    (values : X → Fin (m + 2) → ℝ) (hvalues : ∀ e, Measurable (fun z => values z e))
    (p : Fin m) : Measurable (fun z => gridTheta L (values z) p) := by
  have hs := sorted_measurable values hvalues
  have hc (e : Fin (m + 2)) := hL.comp ((measurable_pi_apply e).comp hs)
  exact ((hc p.succ.castSucc).sub (hc p.castSucc.castSucc)).div
    ((hc p.succ.succ).sub (hc p.castSucc.castSucc))

theorem gridScore_measurable {m : ℕ} (F : Row → ℝ → ℝ) (hF : ∀ i, Measurable (F i))
    (L : ℝ → ℝ) (hL : Measurable L) (values : X → Fin (m + 2) → ℝ)
    (hvalues : ∀ e, Measurable (fun z => values z e)) (v : X → ℝ) (hv : Measurable v) :
    Measurable (fun z => gridScore F L (values z) (v z)) := by
  have hs := sorted_measurable values hvalues
  apply fiberMean_measurable _ (fun e => (measurable_pi_apply e).comp hs)
  · intro e
    apply nodeScores_measurable
    intro p
    exact maxDeletion_measurable _ (gridRows_measurable F hF values hvalues) _ _ _
      (gridTheta_measurable L hL values hvalues p)
  · exact hv

end EnvyFreeResearch.Full.UpperGridInterpolation
