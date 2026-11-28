import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56340_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩], 14⟩

private theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_56340_aux

open PEqualNP.Outside.L_meta_56340_aux in
theorem PEqualNP.Outside.L_meta_56340 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321327 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, fan, by decide +kernel, by decide +kernel⟩
