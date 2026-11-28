import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53915_aux

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [6, 7]⟩,
  ⟨.and, [0, 1]⟩,
  ⟨.or, [8, 9]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.not, [11]⟩,
  ⟨.and, [2, 12]⟩,
  ⟨.or, [10, 13]⟩
], 14⟩

theorem legal : PEqualNP.MetaComplexity.FanInTwo witness := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_53915_aux

set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.L_meta_53915 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52274 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_53915_aux.witness, PEqualNP.Outside.L_meta_53915_aux.legal, by decide, by decide +kernel⟩
