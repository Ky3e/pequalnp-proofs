import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1411_aux

private theorem close_pair {α : Type*} [DecidableEq α] (A B : Finset α) (a f : Nat)
    (h : (A \ B).card ≤ a+f) :
    ∃ Y Z : Finset α, Y ⊆ Z ∧ (A \ Y).card ≤ a ∧ (Y \ A).card ≤ f ∧
        (B \ Z).card ≤ a ∧ (Z \ B).card ≤ f := by
  let V := A \ B
  obtain ⟨S,sub,card⟩ := Finset.exists_subset_card_eq
    (show min a V.card ≤ V.card from min_le_right _ _)
  have subA : S ⊆ A := sub.trans Finset.sdiff_subset
  let Y := A \ S
  let Z := B ∪ Y
  have rem : A \ Y = S := by
    ext x
    have hs : x ∈ S → x ∈ A := fun hx => subA hx
    simp only [Y, Finset.mem_sdiff]
    tauto
  have add : Z \ B = V \ S := by
    ext x
    simp only [Z,Y,V,Finset.mem_sdiff,Finset.mem_union]
    tauto
  refine ⟨Y,Z,Finset.subset_union_right,?_,?_,?_,?_⟩
  · rw [rem,card]; exact min_le_left _ _
  · have subY : Y ⊆ A := Finset.sdiff_subset
    simp [Finset.sdiff_eq_empty_iff_subset.mpr subY]
  · have subZ : B ⊆ Z := Finset.subset_union_left
    simp [Finset.sdiff_eq_empty_iff_subset.mpr subZ]
  · rw [add,Finset.card_sdiff_of_subset sub,card]
    change V.card ≤ a+f at h
    omega

private theorem count_copies {n r t : Nat} (C : Fin n → Finset (Fin r))
    (large : ∀ i, t ≤ (C i).card) (disj : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    n*t ≤ r := by
  classical
  have cards : (Finset.univ.biUnion C).card = ∑ i : Fin n, (C i).card :=
    Finset.card_biUnion (fun i _ j _ eq => disj i j eq)
  calc
    n*t = ∑ _ : Fin n, t := by simp
    _ ≤ ∑ i : Fin n, (C i).card := Finset.sum_le_sum (fun i _ => large i)
    _ ≤ r := by rw [← cards]; simpa using Finset.card_le_univ (Finset.univ.biUnion C)

private theorem make_copies {n r t : Nat} (room : n*t ≤ r) :
    ∃ C : Fin n → Finset (Fin r), (∀ i, (C i).card = t) ∧
      ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
  classical
  let wire : (Fin n × Fin t) ↪ Fin r := finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb room)
  let C (i : Fin n) := (Finset.univ : Finset (Fin t)).image (fun j => wire (i,j))
  refine ⟨C, fun i => ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun j k e => congrArg Prod.snd (wire.injective e))]
    simp
  · intro i j ne
    apply Finset.disjoint_left.mpr
    intro v vi vj
    obtain ⟨x,_,ex⟩ := Finset.mem_image.mp vi
    obtain ⟨y,_,ey⟩ := Finset.mem_image.mp vj
    exact ne (congrArg Prod.fst (wire.injective (ex.trans ey.symm)))

end PEqualNP.Outside.L_lib_1411_aux

open PEqualNP.Outside.L_lib_1411_aux

theorem PEqualNP.Outside.L_lib_1411 :
  ∀ (n r a f : Nat) (R : Fin n → Fin n → Prop),
    (∀ i, R i i) → (∀ i j k, R i j → R j k → R i k) → (∀ i j, R i j → R j i → i = j) →
    let ideal := fun (A : Finset (Fin n)) => ∀ i j, j ∈ A → R i j → i ∈ A
    let mono := fun (E : Finset (Fin n) → Finset (Fin r)) =>
      ∀ A B, ideal A → ideal B → A ⊆ B → E A ⊆ E B
    let recovers := fun (E : Finset (Fin n) → Finset (Fin r)) =>
      ∃ D : Finset (Fin r) → Finset (Fin n), (∀ X Y, X ⊆ Y → D X ⊆ D Y) ∧
        ∀ A, ideal A → ∀ Y, (E A \ Y).card ≤ a → (Y \ E A).card ≤ f → D Y = A
    let t := a+f+1
    (∀ E, mono E → (recovers E ↔ ∃ C : Fin n → Finset (Fin r),
      (∀ i, t ≤ (C i).card) ∧ (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      ∀ i v, v ∈ C i → ∀ A, ideal A → (v ∈ E A ↔ i ∈ A))) ∧
    ((∃ E, mono E ∧ recovers E) ↔ n*t ≤ r) := by
  classical
  intro n r a f R refl trans antisym ideal mono recovers t
  let down (i : Fin n) := (Finset.univ : Finset (Fin n)).filter (fun j => R j i)
  let avoid (i : Fin n) := (Finset.univ : Finset (Fin n)).filter (fun j => ¬R i j)
  have hd (i : Fin n) : ideal (down i) := by
    intro j k hk hjk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, trans j k i hjk (Finset.mem_filter.mp hk).2⟩
  have hv (i : Fin n) : ideal (avoid i) := by
    intro j k hk hjk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h =>
      (Finset.mem_filter.mp hk).2 (trans i j k h hjk)⟩
  have own (i : Fin n) : i ∈ down i := by simp [down,refl]
  have absent (i : Fin n) : i ∉ avoid i := by simp [avoid,refl]
  let copies (E : Finset (Fin n) → Finset (Fin r)) :=
    ∃ C : Fin n → Finset (Fin r), (∀ i, t ≤ (C i).card) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      ∀ i v, v ∈ C i → ∀ A, ideal A → (v ∈ E A ↔ i ∈ A)
  have detect (E : Finset (Fin n) → Finset (Fin r)) (mon : mono E) :
      recovers E → copies E := by
    rintro ⟨D,monD,right⟩
    let C (i : Fin n) := E (down i) \ E (avoid i)
    have many (i : Fin n) : t ≤ (C i).card := by
      by_contra bad
      have small : (E (down i) \ E (avoid i)).card ≤ a+f := by
        change ¬ a+f+1 ≤ (E (down i) \ E (avoid i)).card at bad
        omega
      obtain ⟨Y,Z,yz,dY,aY,dZ,aZ⟩ := close_pair _ _ a f small
      have inY : i ∈ D Y := by rw [right _ (hd i) _ dY aY]; exact own i
      have inZ := monD Y Z yz inY
      exact absent i ((right _ (hv i) _ dZ aZ) ▸ inZ)
    have exact_copy (i : Fin n) (v : Fin r) (cv : v ∈ C i)
        (A : Finset (Fin n)) (hA : ideal A) : v ∈ E A ↔ i ∈ A := by
      obtain ⟨pos,neg⟩ := Finset.mem_sdiff.mp cv
      constructor
      · intro vt
        by_contra no
        apply neg (mon A (avoid i) hA (hv i) ?_ vt)
        intro j jA
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ij => no (hA i j jA ij)⟩
      · intro it
        apply mon (down i) A (hd i) hA ?_ pos
        intro j jD
        exact hA j i it (Finset.mem_filter.mp jD).2
    refine ⟨C,many,?_,exact_copy⟩
    intro i j distinct
    apply Finset.disjoint_left.mpr
    intro v vi vj
    have compare (k : Fin n) : i ∈ down k ↔ j ∈ down k :=
      ((exact_copy i v vi _ (hd k)).symm.trans (exact_copy j v vj _ (hd k)))
    have ji : R j i := (Finset.mem_filter.mp ((compare i).mp (own i))).2
    have ij : R i j := (Finset.mem_filter.mp ((compare j).mpr (own j))).2
    exact distinct (antisym i j ij ji)
  have decode (E : Finset (Fin n) → Finset (Fin r)) : copies E → recovers E := by
    rintro ⟨C,many,disj,exact_copy⟩
    let D (Y : Finset (Fin r)) := Finset.univ.filter (fun i => f < ((C i) ∩ Y).card)
    refine ⟨D,?_,?_⟩
    · intro X Y xy i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le
        (Finset.card_le_card (Finset.inter_subset_inter_left xy))⟩
    · intro A hA Y gone added
      ext i
      change i ∈ Finset.univ.filter (fun i => f < ((C i) ∩ Y).card) ↔ i ∈ A
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      by_cases it : i ∈ A
      · have sub : C i \ Y ⊆ E A \ Y := by
          intro v hv
          exact Finset.mem_sdiff.mpr ⟨(exact_copy i v (Finset.mem_sdiff.mp hv).1 A hA).mpr it,
            (Finset.mem_sdiff.mp hv).2⟩
        have bound := (Finset.card_le_card sub).trans gone
        have eq : C i \ (C i ∩ Y) = C i \ Y := by
          ext v
          simp only [Finset.mem_sdiff,Finset.mem_inter]
          tauto
        have inter : C i ∩ Y ⊆ C i := Finset.inter_subset_left
        have count := Finset.card_sdiff_add_card_eq_card inter
        rw [eq] at count
        have need := many i
        change a+f+1 ≤ (C i).card at need
        simp only [it,iff_true]
        omega
      · have sub : C i ∩ Y ⊆ Y \ E A := by
          intro v hv
          exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).2, fun hvE =>
            it ((exact_copy i v (Finset.mem_inter.mp hv).1 A hA).mp hvE)⟩
        have bound := (Finset.card_le_card sub).trans added
        simp [it,Nat.not_lt_of_ge bound]
  refine ⟨fun E mon => ⟨detect E mon, decode E⟩, ⟨?_,?_⟩⟩
  · rintro ⟨E,mon,hE⟩
    obtain ⟨C,many,disj,_⟩ := detect E mon hE
    exact count_copies C many disj
  · intro space
    obtain ⟨C,card,disj⟩ := make_copies space
    let E (A : Finset (Fin n)) := A.biUnion C
    have mon : mono E := by
      intro A B _ _ sub v hv
      obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_biUnion.mpr ⟨i,sub hi,hv⟩
    refine ⟨E,mon,decode E ⟨C,fun i => (card i).ge,disj,?_⟩⟩
    intro i v vi A _
    constructor
    · intro hv
      obtain ⟨j,jA,vj⟩ := Finset.mem_biUnion.mp hv
      by_cases same : i=j
      · exact same ▸ jA
      · exact (Finset.disjoint_left.mp (disj i j same) vi vj).elim
    · exact fun hi => Finset.mem_biUnion.mpr ⟨i,hi,vi⟩
