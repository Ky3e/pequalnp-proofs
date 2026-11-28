import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55209_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [3, 7]⟩, ⟨.not, [1]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩

private theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_55209_aux

open PEqualNP.Outside.L_meta_55209_aux in
theorem PEqualNP.Outside.L_meta_55209 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2199357 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fan, by decide +kernel, by decide +kernel⟩
