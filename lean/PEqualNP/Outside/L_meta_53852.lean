import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53852_aux

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [3, 5]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.and, [1, 11]⟩,
  ⟨.not, [12]⟩,
  ⟨.and, [8, 13]⟩
], 14⟩

theorem legal : PEqualNP.MetaComplexity.FanInTwo witness := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_53852_aux

set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.L_meta_53852 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33981 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_53852_aux.witness, PEqualNP.Outside.L_meta_53852_aux.legal, by decide, by decide +kernel⟩
