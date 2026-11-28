import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53926_aux

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.or, [4, 5]⟩,
  ⟨.or, [3, 6]⟩,
  ⟨.and, [0, 7]⟩,
  ⟨.not, [3]⟩,
  ⟨.and, [1, 9]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.not, [11]⟩,
  ⟨.and, [2, 12]⟩,
  ⟨.or, [8, 10]⟩,
  ⟨.or, [14, 13]⟩
], 15⟩

theorem legal : PEqualNP.MetaComplexity.FanInTwo witness := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_53926_aux

set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.L_meta_53926 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52666 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_53926_aux.witness, PEqualNP.Outside.L_meta_53926_aux.legal, by decide, by decide +kernel⟩
