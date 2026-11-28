import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53279_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 1]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [10, 9]⟩], 11⟩

private theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_53279_aux

open PEqualNP.Outside.L_meta_53279_aux in
theorem PEqualNP.Outside.L_meta_53279 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (197 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fan, by decide +kernel, by decide +kernel⟩
