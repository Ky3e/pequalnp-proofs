import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1413_aux

private theorem card_close_inter {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A \ B).card + (A ∩ B).card = A.card := by
  have h : A ∩ B ⊆ A := Finset.inter_subset_left
  have eq : A \ (A ∩ B) = A \ B := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  simpa only [eq] using Finset.card_sdiff_add_card_eq_card h

private theorem framed_gap [DecidableEq Nat] (s w i j : Nat) (hi : i < j) (A B : Finset Nat)
    (subA : A ⊆ Finset.range s) :
    w ≤ ((B ∪ Finset.Ico s (s+w*j)) \ (A ∪ Finset.Ico s (s+w*i))).card := by
  have inc : s+w*i+w ≤ s+w*j := by
    rw [Nat.add_assoc,←Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left w hi) _
  have sub : Finset.Ico (s+w*i) (s+w*i+w) ⊆
      (B ∪ Finset.Ico s (s+w*j)) \ (A ∪ Finset.Ico s (s+w*i)) := by
    intro x hx
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega,hi.trans_le inc⟩),?_⟩
    intro no
    rcases Finset.mem_union.mp no with h | h
    · have := Finset.mem_range.mp (subA h)
      omega
    · have := (Finset.mem_Ico.mp h).2
      omega
  have cmp := Finset.card_le_card sub
  simpa using cmp

private theorem disjoint_card_union {α : Type*} [DecidableEq α] (A B : Finset α)
    (h : ∀ x ∈ A, x ∉ B) : (A ∪ B).card = A.card + B.card :=
  Finset.card_union_of_disjoint (Finset.disjoint_left.mpr h)

end PEqualNP.Outside.L_lib_1413_aux

open PEqualNP.Outside.L_lib_1413_aux

theorem PEqualNP.Outside.L_lib_1413 :
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let tag := fun (s w j : Nat) => Finset.Ico s (s+w*j)
  let near := fun (a f : Nat) (W Y : Finset Nat) => (W \ Y).card ≤ a ∧ (Y \ W).card ≤ f
  let inc := fun {m : Nat} (Y : Fin m → Finset Nat) => ∀ i j, i ≤ j → Y i ⊆ Y j
  ∀ (n k m : Nat) (E : Fin m → Finset Nat) (d : Fin m → Nat), k ≤ n →
    (∀ j, E j ⊆ Finset.range n ∧ d j ≤ k) →
    let a := n-k
    let s := 2*n+1
    let raw := fun (j : Fin (m+2)) =>
      if j.val=0 then Finset.range n else if h : j.val-1 < m then
        let i : Fin m := ⟨j.val-1,h⟩
        E i ∪ Finset.Ico n (n+(a+d i-(E i).card))
      else ∅
    let W := fun j : Fin (m+2) => raw j ∪ tag s (n+1) j.val
    let good := fun T : Finset Nat => T ⊆ Finset.range n ∧ T.card=k ∧ ∀ i, d i ≤ (T ∩ E i).card
    let fit := fun Y : Fin (m+2) → Finset Nat => inc Y ∧ ∀ j, near a k (W j) (Y j)
    (∀ i j, i < j → n < (W j \ W i).card) ∧
    (∀ Y, fit Y → ∃ T, good T ∧ ∀ j, Y j ∩ Finset.range s = T) ∧
    ∀ T, good T → fit (fun j => T ∪ tag s (n+1) j.val) := by
  intro tag near inc n k m E d kn E_bound a s raw W good fit
  letI : DecidableEq Nat := fun x y => Classical.propDecidable (x=y)
  let last := Fin.last (m+1)
  let frame (j : Fin (m+2)) := Finset.Ico s (s+(n+1)*j.val)
  let middle (i : Fin m) : Fin (m+2) := ⟨i.val+1,by have := i.isLt; omega⟩
  let pad (i : Fin m) := Finset.Ico n (n+(a+d i-(E i).card))
  have rfirst : raw 0 = Finset.range n := by simp [raw]
  have rlast : raw last = ∅ := by
    have no : ¬(m+1-1<m) := by omega
    simp [raw,last,Fin.val_last,no]
  have rmid (i : Fin m) : raw (middle i) = E i ∪ pad i := by
    simp only [raw,middle,Fin.val_mk,Nat.add_one_ne_zero,ite_eq_right,
      Nat.add_sub_cancel_right,dite_eq_left i.isLt,ite_false,pad] <;> rfl
  have wf (j : Fin (m+2)) : W j = raw j ∪ frame j := by simp [W,tag,frame]
  have pad_bound (i : Fin m) : pad i ⊆ Finset.range s := by
    intro v hv
    have high := (Finset.mem_Ico.mp hv).2
    have db := (E_bound i).2
    apply Finset.mem_range.mpr
    dsimp [a,s]
    dsimp [pad,a] at high
    omega
  have first_bound : Finset.range n ⊆ Finset.range s :=
    Finset.range_mono (by dsimp [s]; omega)
  have raw_bound (j : Fin (m+2)) : raw j ⊆ Finset.range s := by
    rcases eq_or_ne j 0 with rfl | ne
    · rw [rfirst]
      exact first_bound
    by_cases h : j.val-1<m
    · let i : Fin m := ⟨j.val-1,h⟩
      have equiv : j=middle i := by
        have nz : j.val≠0 := fun e => ne (Fin.ext e)
        apply Fin.ext
        dsimp [middle,i]
        omega
      rw [equiv,rmid]
      exact Finset.union_subset ((E_bound i).1.trans first_bound) (pad_bound i)
    · have equiv : j=last := by
        have bound:=j.isLt
        have nz : j.val≠0 := fun e => ne (Fin.ext e)
        apply Fin.ext
        dsimp [last]
        omega
      rw [equiv,rlast]
      exact Finset.empty_subset _
  have far (j : Fin (m+2)) {v : Nat} (hv : v ∈ frame j) : v ∉ Finset.range s :=
    fun ht => (not_lt_of_ge (Finset.mem_Ico.mp hv).1) (Finset.mem_range.mp ht)
  have inRaw (j : Fin (m+2)) (T : Finset Nat) (ht : T⊆Finset.range n) :
      raw j \ T = (W j) \ (T ∪ frame j) := by
    ext v
    have a1 : v ∈ raw j → v ∉ frame j := fun rh fh => far j fh (raw_bound j rh)
    rw [wf]
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  have raw_card (i : Fin m) : (raw (middle i)).card = (E i).card+(a+d i-(E i).card) := by
    rw [rmid,disjoint_card_union]
    · simp [pad]
    · intro v vE vpad
      have below := Finset.mem_range.mp ((E_bound i).1 vE)
      have above := (Finset.mem_Ico.mp vpad).1
      omega
  have raw_inter (i : Fin m) (T : Finset Nat) (hT : T⊆Finset.range n) :
      raw (middle i) ∩ T = E i ∩ T := by
    rw [rmid]
    ext v
    have excl : v∈T → v∉pad i := by
      intro h1 h2
      exact (not_lt_of_ge (Finset.mem_Ico.mp h2).1) (Finset.mem_range.mp (hT h1))
    simp only [Finset.mem_inter,Finset.mem_union]
    tauto
  refine ⟨?_,?_,?_⟩
  · intro i j ij
    rw [wf,wf]
    exact (Nat.lt_succ_self n).trans_le (framed_gap s (n+1) i.val j.val ij _ _ (raw_bound i))
  · intro Y hY
    let T := Y 0 ∩ Finset.range n
    have Tsub : T ⊆ Finset.range n := Finset.inter_subset_right
    have T_in (j : Fin (m+2)) : T ⊆ Y j ∩ Finset.range s := by
      intro v hv
      refine Finset.mem_inter.mpr ⟨hY.1 0 j (Fin.zero_le _) (Finset.mem_inter.mp hv).1,
        first_bound (Tsub hv)⟩
    have cap (j : Fin (m+2)) : (Y j ∩ Finset.range s).card ≤ k := by
      have sub : Y j ∩ Finset.range s ⊆ Y last \ W last := by
        intro v hv
        obtain ⟨vy,vs⟩ := Finset.mem_inter.mp hv
        refine Finset.mem_sdiff.mpr ⟨hY.1 j last (Fin.le_last _) vy,?_⟩
        rw [wf,rlast,Finset.empty_union]
        exact fun h => far last h vs
      exact (Finset.card_le_card sub).trans (hY.2 last).2
    have misses : (Finset.range n \ Y 0).card ≤ a := by
      apply (Finset.card_le_card (t := W 0 \ Y 0) ?_).trans (hY.2 0).1
      intro v hv
      rw [Finset.mem_sdiff] at hv ⊢
      rw [wf,rfirst]
      exact ⟨Finset.mem_union_left _ hv.1,hv.2⟩
    have count := card_close_inter (Finset.range n) (Y 0)
    rw [Finset.inter_comm] at count
    rw [Finset.card_range] at count
    change (Finset.range n \ Y 0).card + T.card = n at count
    have enough : k ≤ T.card := by dsimp [a] at misses; omega
    have Tcard : T.card=k := le_antisymm ((Finset.card_le_card (T_in 0)).trans (cap 0)) enough
    have eq (j : Fin (m+2)) : Y j ∩ Finset.range s = T :=
      (Finset.eq_of_subset_of_card_le (T_in j) (by rw [Tcard]; exact cap j)).symm
    refine ⟨T,⟨Tsub,Tcard,?_⟩,eq⟩
    intro i
    have sub : raw (middle i) \ T ⊆ W (middle i) \ Y (middle i) := by
      intro v hv
      obtain ⟨vr,vt⟩ := Finset.mem_sdiff.mp hv
      apply Finset.mem_sdiff.mpr
      rw [wf]
      exact ⟨Finset.mem_union_left _ vr, fun vy =>
        vt (eq (middle i) ▸ Finset.mem_inter.mpr ⟨vy,raw_bound (middle i) vr⟩)⟩
    have bound := (Finset.card_le_card sub).trans (hY.2 (middle i)).1
    have c := card_close_inter (raw (middle i)) T
    rw [raw_inter i T Tsub,raw_card] at c
    rw [Finset.inter_comm] at c
    omega
  · intro T hT
    obtain ⟨Tsub,Tcard,quota⟩ := hT
    constructor
    · intro i j ij
      apply Finset.union_subset_union (le_refl _)
      intro v hv
      obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hv
      exact Finset.mem_Ico.mpr ⟨lo,hi.trans_le
        (Nat.add_le_add_left (Nat.mul_le_mul_left (n+1) ij) _)⟩
    · intro j
      have small : (T \ raw j).card ≤ k := by
        exact (Finset.card_le_card Finset.sdiff_subset).trans_eq Tcard
      have add : ((T ∪ frame j) \ W j) ⊆ T \ raw j := by
        intro v hv
        rw [wf,Finset.mem_sdiff,Finset.mem_union,Finset.mem_union] at hv
        rw [Finset.mem_sdiff]
        tauto
      refine ⟨?_,(Finset.card_le_card add).trans small⟩
      change (W j \ (T ∪ frame j)).card ≤ a
      rw [← inRaw j T Tsub]
      have diff : (Finset.range n \ T).card=a := by
        rw [Finset.card_sdiff_of_subset Tsub,Finset.card_range,Tcard]
      rcases eq_or_ne j 0 with rfl | ne
      · rw [rfirst,diff]
      · by_cases h : j.val-1<m
        · let i : Fin m := ⟨j.val-1,h⟩
          have equiv : j=middle i := by
            have nz : j.val≠0 := fun e => ne (Fin.ext e)
            apply Fin.ext
            dsimp [middle,i]
            omega
          rw [equiv]
          by_cases smallE : (E i).card ≤ a+d i
          · have c := card_close_inter (raw (middle i)) T
            rw [raw_inter i T Tsub,raw_card,Finset.inter_comm] at c
            have qi := quota i
            omega
          · have noPad : pad i=∅ := by
              have eq : a+d i-(E i).card=0 := by omega
              simp [pad,eq]
            rw [rmid,noPad,Finset.union_empty]
            exact (Finset.card_le_card (Finset.sdiff_subset_sdiff (E_bound i).1 (le_refl T))).trans_eq diff
        · have equiv : j=last := by
            have bound:=j.isLt
            have nz : j.val≠0 := fun e => ne (Fin.ext e)
            apply Fin.ext
            dsimp [last]
            omega
          simp [equiv,rlast]
