import PEqualNP.Defs
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4474_617
    (extract : ∀ (n s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < n+n+s →
    (∀ v < n+n, F v = {{v}}) →
    (∀ j < s, ∃ a < n+n+j, ∃ b < n+n+j,
      F (n+n+j) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) ∨
      F (n+n+j) = F a ∨ F (n+n+j) = {∅} ∨
      F (n+n+j) = F a ∪ F b ∧ ∀ u ∈ F a, ∀ v ∈ F b, Disjoint u v) →
    (∀ p : Fin n, ∃ A ∈ F o, p.val ∉ A) →
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outs : Fin n → ℕ),
      C.size ≤ 10*s+2*n ∧
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      ∀ x : Fin n → Bool, (∃ A ∈ F o, ∀ l : Fin n, x l = true → n+l.val ∉ A) →
      ∀ p : Fin n, (C.wires (List.ofFn x)).getD (outs p) false = true ↔
        ∀ A ∈ F o, p.val ∈ A ∨ ∃ l : Fin n, n+l.val ∈ A ∧ x l = true)
    (count : ∀ (n m : ℕ) (k : Fin m → ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), Fintype.card {q : Fin n // x q = true} ≤ k i → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k i) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17 ∧ ∀ x18 ∈ x11 x16, ∀ x20 ∈ x11 x17, Disjoint x18 x20) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  have regular : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
    1 ≤ q → N = q^2+q+1 →
    (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
    (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
    ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q+1 := by
    intro q N I inst hq hN degree unique p
    classical
    let T := Finset.univ.filter (fun l => I p l)
    let S := fun l : Fin N => (Finset.univ.filter (fun r => I r l)).erase p
    have size (l : Fin N) (hl : l ∈ T) : (S l).card = q := by
      have hp : p ∈ Finset.univ.filter (fun r => I r l) := by simpa [T] using hl
      have hd := degree l
      rw [Fintype.card_subtype] at hd
      simp [S, Finset.card_erase_of_mem hp, hd]
    have disj : (T : Set (Fin N)).PairwiseDisjoint S := by
      intro a ha b hb ne
      apply Finset.disjoint_left.mpr
      intro r hra hrb
      have ar := Finset.mem_erase.mp hra
      have br := Finset.mem_erase.mp hrb
      have rp : p ≠ r := Ne.symm ar.1
      obtain ⟨l, _, hu⟩ := unique p r rp
      have ea : a = l := hu a ⟨by simpa [T] using ha, by simpa using ar.2⟩
      have eb : b = l := hu b ⟨by simpa [T] using hb, by simpa using br.2⟩
      exact ne (ea.trans eb.symm)
    have cover : T.biUnion S = Finset.univ.erase p := by
      ext r
      constructor
      · intro hr
        obtain ⟨l, hl, hrl⟩ := Finset.mem_biUnion.mp hr
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hrl).1, Finset.mem_univ r⟩
      · intro hr
        have rp := (Finset.mem_erase.mp hr).1
        obtain ⟨l, hl, _⟩ := unique p r (Ne.symm rp)
        refine Finset.mem_biUnion.mpr ⟨l, by simp [T, hl.1], ?_⟩
        simp [S, rp, hl.2]
    have hc := Finset.card_biUnion disj
    rw [cover] at hc
    have sum : ∑ l ∈ T, (S l).card = T.card*q := by
      calc
        _ = ∑ l ∈ T, q := Finset.sum_congr rfl size
        _ = _ := by simp
    rw [sum] at hc
    have hn : 0 < N := by omega
    simp only [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hc
    have hc2 : N = T.card*q+1 := by omega
    have hp : T.card = q+1 := by nlinarith [Nat.mul_pos (show 0 < q by omega) (show 0 < q by omega)]
    exact hp

  classical
  intro q N I inst hq hN degree unique s o F room inputs gates safe realize
  have absent (p : Fin N) : ∃ A ∈ F o, p.val ∉ A := by
    obtain ⟨A, hA, spec⟩ := realize ∅ (by simp)
    exact ⟨A, hA, by simpa using (spec p).1⟩
  obtain ⟨C, outs, budget, basis, back, values⟩ := extract N s o F room inputs gates absent
  let S : Fin N → Finset (Fin N) := fun p => Finset.univ.filter (I p)
  have memS (p l : Fin N) : l ∈ S p ↔ I p l := by simp [S]
  have cardS (p : Fin N) : (S p).card = q+1 := regular q N I (by omega) hN degree unique p
  have inter (p r : Fin N) (ne : p ≠ r) : (S p ∩ S r).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨l, hl, hu⟩ := unique p r ne
    have ha' := Finset.mem_inter.mp ha
    have hb' := Finset.mem_inter.mp hb
    exact (hu a ⟨(memS p a).mp ha'.1, (memS r a).mp ha'.2⟩).trans
      (hu b ⟨(memS p b).mp hb'.1, (memS r b).mp hb'.2⟩).symm
  have semantics (x : Fin N → Bool)
      (small : (Finset.univ.filter (fun l => x l = true)).card ≤ q) (p : Fin N) :
      (C.wires (List.ofFn x)).getD (outs p) false = true ↔
        ∃ l : Fin N, I p l ∧ x l = true := by
    let T := Finset.univ.filter (fun l => x l = true)
    obtain ⟨A, hA, spec⟩ := realize T small
    have base : ∃ B ∈ F o, ∀ l : Fin N, x l = true → N+l.val ∉ B := by
      refine ⟨A, hA, fun l hl hin => ?_⟩
      exact ((spec l).2.mp hin) (by simp [T, hl])
    rw [values x base p]
    constructor
    · intro h
      rcases h A hA with hp | ⟨l, hl, hx⟩
      · obtain ⟨l, hl, hil⟩ := (spec p).1.mp hp
        exact ⟨l, hil, (Finset.mem_filter.mp hl).2⟩
      · exact False.elim (((spec l).2.mp hl) (by simp [T, hx]))
    · rintro ⟨l, hil, hx⟩ B hB
      rcases safe B hB p l hil with hp | hl
      · exact Or.inl hp
      · exact Or.inr ⟨l, hl, hx⟩
  have singles (p l : Fin N) :
      (C.wires (List.ofFn (fun r : Fin N => decide (r=l)))).getD (outs p) false = true ↔ l ∈ S p := by
    have one : (Finset.univ.filter (fun r : Fin N => decide (r=l) = true)).card = 1 := by
      have eq : Finset.univ.filter (fun r : Fin N => decide (r=l) = true) = {l} := by ext r; simp
      rw [eq]; simp
    rw [semantics _ (by rw [one]; omega)]
    simp [memS]
  have sparse (p : Fin N) (x : Fin N → Bool)
      (small : (Finset.univ.filter (fun l => x l = true)).card ≤ q)
      (off : ∀ l ∈ S p, x l = false) :
      (C.wires (List.ofFn x)).getD (outs p) false = false := by
    cases h : (C.wires (List.ofFn x)).getD (outs p) false with
    | false => rfl
    | true =>
      obtain ⟨l, hil, hx⟩ := (semantics x small p).mp h
      have hf := off l ((memS p l).mpr hil)
      rw [hf] at hx
      cases hx
  have lower := count N N (fun _ => q) S C outs (fun _ => q) inter
    (fun p => by rw [cardS]; omega) basis back singles
    (fun p x small off => sparse p x (by simpa only [Fintype.card_subtype] using small) off)
    (fun _ => le_refl q) (fun p => by rw [cardS])
  have total : N*q ≤ C.size := by simpa using lower
  have large : 4*N ≤ N*q := by
    have := Nat.mul_le_mul_left N (show 4 ≤ q by omega)
    simpa [Nat.mul_comm] using this
  omega
