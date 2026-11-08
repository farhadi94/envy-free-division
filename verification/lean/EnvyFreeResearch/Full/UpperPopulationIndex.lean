import EnvyFreeResearch.Full.UpperPopulationZero

/-! Concrete increasing active-population enumeration; physical caches keep
all original observers, so population restriction issues no oracle queries. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace EnvyFreeResearch.Full.UpperZeroRows
open UpperRecordedDomain UpperCorrectionExecution
variable {n : ℕ}

def enumerate (active : Finset (Fin n)) : Fin active.card ↪o Fin n :=
  active.orderEmbOfFin rfl

theorem enumerate_mem (active : Finset (Fin n)) (i : Fin active.card) :
    enumerate active i ∈ active := active.orderEmbOfFin_mem rfl i

theorem enumerate_range (active : Finset (Fin n)) :
    Set.range (enumerate active) = (↑active : Set (Fin n)) :=
  active.range_orderEmbOfFin rfl

theorem enumerate_injective (active : Finset (Fin n)) :
    Function.Injective (enumerate active) := (enumerate active).injective

theorem active_size_bound (active : Finset (Fin n)) : active.card ≤ n := by
  simpa using Finset.card_le_univ active

theorem enumerated_positive (μ : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (origin : State n) (hgood : WellFormed μ origin)
    (active : Finset (Fin n)) :
    ∀ a, 0 < (μ (enumerate (positiveRows origin active) a)).real (domain origin.cells) :=
  active_embedding_positive μ origin hgood active _ (enumerate_mem _)

end EnvyFreeResearch.Full.UpperZeroRows
