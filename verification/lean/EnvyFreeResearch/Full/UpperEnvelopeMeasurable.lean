import EnvyFreeResearch.Full.UpperPreparedEnvelope
import EnvyFreeResearch.Full.UpperGridInterpolationPhysical

/-! Joint Borel envelope masses for a varying immutable grid on a fixed
physical reserve. Every real endpoint retains its ordinary Borel encoding. -/

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace EnvyFreeResearch.Full.UpperEnvelopeMeasurable

open UpperRecordedDomain UpperDomainDifference UpperEnvelope UpperPayments UpperLogicalCells
  UpperLogicalPrefix UpperGridInterpolation UpperPreparedEnvelope

variable {Agent Cell : Type*} [Fintype Agent] [Fintype Cell]
  {X : Type*} [MeasurableSpace X]

theorem ratio_measurable (a : X → Agent → Cell → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (i j : Agent) (e : Cell) :
    Measurable (fun z => ratio (a z) i j e) :=
  ((((ha i e).sub (ha j e)).abs.div (cellGap_measurable a ha i j))).ite
    (measurableSet_lt measurable_const (cellGap_measurable a ha i j)) measurable_const

theorem height_measurable (a : X → Agent → Cell → ℝ)
    (ha : ∀ i e, Measurable (fun z => a z i e)) (j : Agent) (e : Cell) :
    Measurable (fun z => height (a z) j e) := by
  have h := Finset.measurable_sup' (s := (Finset.univ : Finset (Option Agent)))
    ⟨none, Finset.mem_univ none⟩ (fun c _ => show Measurable (fun z => c.elim 0 (fun i => ratio (a z) i j e)) from by
      cases c with
      | none => exact measurable_const
      | some i => exact ratio_measurable a ha i j e)
  convert h using 1
  funext z
  exact (Finset.sup'_apply ⟨none, Finset.mem_univ none⟩
    (fun c : Option Agent => fun z : X => c.elim 0 (fun i => ratio (a z) i j e)) z).symm

theorem component_mass_eq_cumulative (ν : Measure ℝ) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (c : Component) : mass ν c = ν.real (Iic c.right) - ν.real (Iic c.left) := by
  have heq : Iic c.right \ Iic c.left = Ioc c.left c.right := by
    ext x
    simp only [mem_sdiff, mem_Iic, mem_Ioc, not_le]
    exact and_comm
  rw [component_mass_eq_interval ν, ← heq,
    measureReal_sdiff (Iic_subset_Iic.mpr c.left_le_right) measurableSet_Iic]

variable {m : ℕ}

def cellCumulative (buffer : List Component) (cuts : Fin (m + 2) → ℝ) (e : Fin (m + 1)) (x : ℝ) : ℝ :=
  (domainCumulative volume buffer (min (cuts e.succ) x) -
    domainCumulative volume buffer (min (cuts e.castSucc) x)) /
      (domainCumulative volume buffer (cuts e.succ) - domainCumulative volume buffer (cuts e.castSucc))

theorem uniformCells_cumulative (buffer : List Component) (cuts : Fin (m + 2) → ℝ)
    (hmono : Monotone cuts) (e : Fin (m + 1)) (x : ℝ) :
    (uniformCells (cell (domain buffer) cuts) e).real (Iic x) = cellCumulative buffer cuts e x := by
  rw [uniformCell_real _ (cell_measurable _ (domain_measurable _) _) e (Iic x),
    cell_volume_prefix buffer cuts hmono, physical_cell_mass volume buffer (domain_volume_finite buffer) cuts hmono]
  rfl

theorem uniformCells_component_mass (buffer : List Component) (cuts : Fin (m + 2) → ℝ)
    (hmono : Monotone cuts) (e : Fin (m + 1)) (c : Component) :
    mass (uniformCells (cell (domain buffer) cuts) e) c =
      cellCumulative buffer cuts e c.right - cellCumulative buffer cuts e c.left := by
  rw [component_mass_eq_cumulative, uniformCells_cumulative buffer cuts hmono,
    uniformCells_cumulative buffer cuts hmono]

theorem cellCumulative_measurable (buffer : List Component) (cuts : X → Fin (m + 2) → ℝ)
    (hcuts : ∀ e, Measurable (fun z => cuts z e)) (e : Fin (m + 1)) (x : X → ℝ) (hx : Measurable x) :
    Measurable (fun z => cellCumulative buffer (cuts z) e (x z)) := by
  have hL := domainCumulative_measurable volume buffer
  exact ((hL.comp ((hcuts e.succ).min hx)).sub (hL.comp ((hcuts e.castSucc).min hx))).div
    ((hL.comp (hcuts e.succ)).sub (hL.comp (hcuts e.castSucc)))

/-- Joint physical component mass for the conditional-volume cells, including
empty cells and atomless endpoint ownership. -/
theorem uniformCells_mass_measurable (buffer : List Component) (cuts : X → Fin (m + 2) → ℝ)
    (hcuts : ∀ e, Measurable (fun z => cuts z e)) (hmono : ∀ z, Monotone (cuts z)) (e : Fin (m + 1)) :
    Measurable (fun p : X × Component => mass (uniformCells (cell (domain buffer) (cuts p.1)) e) p.2) := by
  have hright := cellCumulative_measurable buffer (fun p : X × Component => cuts p.1)
    (fun e => (hcuts e).comp measurable_fst) e (fun p => p.2.right)
    (component_right_measurable.comp measurable_snd)
  have hleft := cellCumulative_measurable buffer (fun p : X × Component => cuts p.1)
    (fun e => (hcuts e).comp measurable_fst) e (fun p => p.2.left)
    (component_left_measurable.comp measurable_snd)
  convert hright.sub hleft using 1
  funext p
  exact uniformCells_component_mass buffer (cuts p.1) (hmono p.1) e p.2

/-- The maximum-cell envelope's actual component mass is jointly measurable
in the full cached table, all grid endpoints, and the selected component. -/
theorem envelope_mass_measurable (buffer : List Component) (cuts : X → Fin (m + 2) → ℝ)
    (hcuts : ∀ e, Measurable (fun z => cuts z e)) (hmono : ∀ z, Monotone (cuts z))
    (a : X → Agent → Fin (m + 1) → ℝ) (ha : ∀ i e, Measurable (fun z => a z i e)) (j : Agent) :
    Measurable (fun p : X × Component => mass
      (envelope (a p.1) (uniformCells (cell (domain buffer) (cuts p.1))) j) p.2) := by
  have hs := Finset.measurable_sum Finset.univ (fun e _ =>
    ((height_measurable a ha j e).comp measurable_fst).mul (uniformCells_mass_measurable buffer cuts hcuts hmono e))
  convert hs using 1
  funext p
  exact envelope_real (a p.1) (uniformCells (cell (domain buffer) (cuts p.1))) j p.2.carrier

end EnvyFreeResearch.Full.UpperEnvelopeMeasurable
