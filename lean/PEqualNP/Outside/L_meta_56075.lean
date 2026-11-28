import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56075_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩

private theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_56075_aux

open PEqualNP.Outside.L_meta_56075_aux in
theorem PEqualNP.Outside.L_meta_56075 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843682 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fan, by decide +kernel, by decide +kernel⟩
