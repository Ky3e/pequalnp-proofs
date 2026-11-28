import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54937_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩

private theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_54937_aux

open PEqualNP.Outside.L_meta_54937_aux in
theorem PEqualNP.Outside.L_meta_54937 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50875 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fan, by decide +kernel, by decide +kernel⟩
