import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3971_617
    (dropOr : ∀ (n v : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), v < n →
      PEqualNP.MetaComplexity.FanInTwo C →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ v ∈ g.inputs) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size + 1 = C.size ∧
        D.gates.countP (fun g => g.op.eval [false]) = C.gates.countP (fun g => g.op.eval [false]) ∧
        ∀ x : List Bool, x.length = n → x.getD v false = false → D.eval x = C.eval x)
    (oneNot : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      C.gates.countP (fun g => g.op.eval [false]) = 1 →
      ∃ x : Fin 8 → Bool,
        C.eval [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1] ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
           x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false]) x4.gates = (1 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x9 ∈ x4.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x9.inputs) → (∀ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x10) = x3 x10) → ∃ (x11 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x11) ≠ (x3 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ))) := by
  intro reads row F C legal size nots _ reader computes
  obtain ⟨D, dlegal, dsize, dnots, sim⟩ := dropOr 10 6 C (by decide) legal reader
  have dc : D.gates.countP (fun g => g.op.eval [false]) = 1 := dnots.trans nots
  have ds : D.size ≤ 13 := by omega
  obtain ⟨x, hx⟩ := oneNot D dlegal ds dc
  exfalso
  apply hx
  have h := computes x
  dsimp only [row] at h
  simp only [Bool.or_false] at h
  exact (sim _ rfl rfl).trans h
