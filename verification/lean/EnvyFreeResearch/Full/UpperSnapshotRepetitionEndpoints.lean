import EnvyFreeResearch.Full.UpperSnapshotRepetitionBridge

/-! Fixed-length endpoint collection for every reached candidate. After
acceptance the unused slots are padded with the known grid endpoint zero. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace EnvyFreeResearch.Full.UpperSnapshotRepetition
variable {State Draw : Type} {L : ℕ}

def endpoints (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) : (m : ℕ) → State → Tape Draw m → List ℝ
  | 0, _, _ => []
  | m+1, s, tape => List.ofFn (points s tape.1) ++
    if reject s tape.1 then endpoints next reject points m (next s tape.1) tape.2
    else List.replicate (m*L) 0

theorem endpoints_length (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (m : ℕ) (s : State) (tape : Tape Draw m) :
    (endpoints next reject points m s tape).length=m*L := by
  induction m generalizing s with
  | zero => simp [endpoints]
  | succ m ih =>
    simp only [endpoints,List.length_append,List.length_ofFn]
    split_ifs <;> simp only [ih,List.length_replicate,Nat.add_mul,Nat.one_mul] <;> omega

def endpointCharge (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (u : ℝ → ℝ≥0∞) :
    (m : ℕ) → State → Tape Draw m → ℝ≥0∞
  | 0, _, _ => 0
  | m+1, s, tape => (∑ j, u (points s tape.1 j)) +
    if reject s tape.1 then endpointCharge next reject points u m (next s tape.1) tape.2 else 0

theorem endpoints_charge (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (u : ℝ → ℝ≥0∞) (hu0 : u 0=0)
    (m : ℕ) (s : State) (tape : Tape Draw m) :
    ((endpoints next reject points m s tape).map u).sum=endpointCharge next reject points u m s tape := by
  induction m generalizing s with
  | zero => simp [endpoints,endpointCharge]
  | succ m ih =>
    simp only [endpoints,endpointCharge,List.map_append,List.sum_append,List.map_ofFn,List.sum_ofFn]
    split_ifs <;> simp [ih,hu0]

theorem endpointCharge_measurable [MeasurableSpace State] [MeasurableSpace Draw]
    (next : State → Draw → State) (reject : State → Draw → Bool)
    (points : State → Draw → Fin L → ℝ) (u : ℝ → ℝ≥0∞)
    (hn : Measurable (Function.uncurry next)) (hr : Measurable (Function.uncurry reject))
    (hp : ∀ j, Measurable (fun p : State × Draw => points p.1 p.2 j)) (hu : Measurable u)
    (m : ℕ) : Measurable (fun p : State × Tape Draw m => endpointCharge next reject points u m p.1 p.2) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    have hsd : Measurable (fun p : State × (Draw × Tape Draw m) => (p.1,p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hnext : Measurable (fun p : State × (Draw × Tape Draw m) => (next p.1 p.2.1,p.2.2)) :=
      (hn.comp hsd).prodMk (measurable_snd.comp measurable_snd)
    exact (Finset.measurable_sum _ (fun j _ => hu.comp ((hp j).comp hsd))).add
      ((ih.comp hnext).ite (measurableSet_eq_fun (hr.comp hsd) measurable_const) measurable_const)

end EnvyFreeResearch.Full.UpperSnapshotRepetition
