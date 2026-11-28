import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53825_aux

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.or, [3, 4]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.and, [0, 7]⟩,
  ⟨.and, [1, 6]⟩,
  ⟨.or, [5, 7]⟩,
  ⟨.not, [10]⟩,
  ⟨.and, [2, 11]⟩,
  ⟨.or, [8, 9]⟩,
  ⟨.or, [12, 13]⟩
], 14⟩

theorem legal : PEqualNP.MetaComplexity.FanInTwo witness := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_53825_aux

set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.L_meta_53825 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_53825_aux.witness, PEqualNP.Outside.L_meta_53825_aux.legal, by decide, by decide +kernel⟩
