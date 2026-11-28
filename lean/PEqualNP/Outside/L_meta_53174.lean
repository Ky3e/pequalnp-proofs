import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53174

open scoped BigOperators

variable {X : Type} [Preorder X] [Fintype X] {n : Nat}

def pref (S : Finset (Fin (n+1))) (k : Nat) := S.filter (fun i => i.val < k)

def can (cost : Fin (n+1) → X → Nat) (S : Finset (Fin (n+1))) (k : Nat) (x : X) (e : Nat) : Prop :=
  ∃ f : Fin (n+1) → X, Monotone f ∧ (∀ i, f i ≤ x) ∧ (pref S k).sum (fun i => cost i (f i)) ≤ e

theorem pref_le {S T : Finset (Fin (n+1))} {k j : Nat} (sub : S ⊆ T) (le : k ≤ j) :
    pref S k ⊆ pref T j := by
  intro i hi
  obtain ⟨hS,hk⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨sub hS,hk.trans_le le⟩

theorem can_smaller {cost : Fin (n+1) → X → Nat} {S T : Finset (Fin (n+1))} {k j : Nat}
    {x : X} {e : Nat} (sub : S ⊆ T) (le : k ≤ j) : can cost T j x e → can cost S k x e := by
  rintro ⟨f,hm,hx,hc⟩
  exact ⟨f,hm,hx,(Finset.sum_le_sum_of_subset (pref_le sub le)).trans hc⟩

theorem pref_insert (S : Finset (Fin (n+1))) (t : Fin (n+1)) :
    pref S (t.val+1) = if t ∈ S then insert t (pref S t.val) else pref S t.val := by
  ext i
  by_cases ht : t ∈ S <;> simp only [pref,Finset.mem_filter,ht,ite_true,ite_false,Finset.mem_insert]
  · constructor
    · rintro ⟨hi,hle⟩
      by_cases same : i = t
      · exact Or.inl same
      · have hne : i.val ≠ t.val := fun h => same (Fin.ext h)
        exact Or.inr ⟨hi,by omega⟩
    · rintro (rfl|⟨hi,hlt⟩)
      · exact ⟨ht,by omega⟩
      · exact ⟨hi,by omega⟩
  · constructor
    · rintro ⟨hi,hlt⟩
      have hne : i.val ≠ t.val := fun h => ht (Fin.ext h ▸ hi)
      exact ⟨hi,by omega⟩
    · rintro ⟨hi,hlt⟩
      exact ⟨hi,by omega⟩

theorem step_when_present {cost : Fin (n+1) → X → Nat} {S : Finset (Fin (n+1))}
    {t : Fin (n+1)} (ht : t ∈ S) {x : X} {e : Nat} :
    can cost S (t.val+1) x e ↔
      ∃ y ≤ x, ∃ j : Nat, j + cost t y ≤ e ∧ can cost S t.val y j := by
  have hn : t ∉ pref S t.val := by simp [pref]
  constructor
  · rintro ⟨f,hm,hx,hc⟩
    rw [pref_insert,ite_eq_left ht,Finset.sum_insert hn] at hc
    refine ⟨f t,hx t, (pref S t.val).sum (fun i => cost i (f i)), by omega,?_⟩
    let g (i : Fin (n+1)) := if i.val<t.val then f i else f t
    refine ⟨g,?_,?_,?_⟩
    · intro i j hij
      by_cases hj : j.val<t.val
      · have hi : i.val<t.val := by have h : i.val ≤ j.val := hij; omega
        simpa only [g,ite_eq_left hi,ite_eq_left hj] using hm hij
      · by_cases hi : i.val<t.val
        · simpa only [g,ite_eq_left hi,ite_eq_right hj] using hm (show i ≤ t from Nat.le_of_lt hi)
        · simp only [g,ite_eq_right hi,ite_eq_right hj,le_refl]
    · intro i
      by_cases hi : i.val<t.val
      · simpa only [g,ite_eq_left hi] using hm (show i ≤ t from Nat.le_of_lt hi)
      · simp only [g,ite_eq_right hi,le_refl]
    · rw [show (pref S t.val).sum (fun i => cost i (g i)) = (pref S t.val).sum (fun i => cost i (f i)) by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [g,ite_eq_left (Finset.mem_filter.mp hi).2]]
  · rintro ⟨y,hy,j,hj,f,hm,hf,hc⟩
    let g (i : Fin (n+1)) := if i.val<t.val then f i else y
    refine ⟨g,?_,?_,?_⟩
    · intro i j hij
      by_cases hj : j.val<t.val
      · have hi : i.val<t.val := by have hh : i.val ≤ j.val := hij; omega
        simpa only [g,ite_eq_left hi,ite_eq_left hj] using hm hij
      · by_cases hi : i.val<t.val
        · simpa only [g,ite_eq_left hi,ite_eq_right hj] using hf i
        · simp only [g,ite_eq_right hi,ite_eq_right hj,le_refl]
    · intro i
      by_cases hi : i.val<t.val
      · simpa only [g,ite_eq_left hi] using (hf i).trans hy
      · simpa only [g,ite_eq_right hi] using hy
    · rw [pref_insert,ite_eq_left ht,Finset.sum_insert hn]
      have hsum : (pref S t.val).sum (fun i => cost i (g i)) = (pref S t.val).sum (fun i => cost i (f i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [g,ite_eq_left (Finset.mem_filter.mp hi).2]
      rw [hsum]
      simp only [g,lt_irrefl,ite_false]
      omega

theorem main (limit : X → Nat) (anti : Antitone limit) (cost : Fin (n+1) → X → Nat) :
    ∃ S : Finset (Fin (n+1)), S.card ≤ Finset.univ.sum limit ∧
      ∀ (k : Nat) (x : X) (e : Nat), e < limit x →
        (can cost Finset.univ k x e ↔ can cost S k x e) := by
  classical
  let pairs := (Finset.univ : Finset X).sigma (fun x => Finset.range (limit x))
  let changeAt (p : Σ _ : X, Nat) := (Finset.univ : Finset (Fin (n+1))).filter (fun i =>
    can cost Finset.univ i.val p.1 p.2 ∧ ¬can cost Finset.univ (i.val+1) p.1 p.2)
  let S := pairs.biUnion changeAt
  have hsmall (p : Σ _ : X, Nat) : (changeAt p).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro i j hi hj
    obtain ⟨hi,hi'⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hj,hj'⟩ := (Finset.mem_filter.mp hj).2
    rcases Nat.lt_trichotomy i.val j.val with h|h|h
    · exact (hi' (can_smaller (Finset.Subset.refl _) h hj)).elim
    · exact Fin.ext h
    · exact (hj' (can_smaller (Finset.Subset.refl _) h hi)).elim
  refine ⟨S,?_ ,?_⟩
  · calc
      S.card ≤ pairs.sum (fun p => (changeAt p).card) := Finset.card_biUnion_le
      _ ≤ pairs.sum (fun _ => 1) := Finset.sum_le_sum (fun p _ => hsmall p)
      _ = Finset.univ.sum limit := by simp [pairs,Finset.card_sigma]
  · intro k
    induction k with
    | zero => intro x e he; have h (T : Finset (Fin (n+1))) : can cost T 0 x e :=
                  ⟨fun _ => x,fun _ _ _ => le_rfl,fun _ => le_rfl,by simp [pref]⟩
              exact ⟨fun _ => h _,fun _ => h _⟩
    | succ k ih =>
      intro x e he
      refine ⟨can_smaller (Finset.subset_univ _) le_rfl,?_⟩
      intro sampled
      by_cases hk : k<n+1
      · let t : Fin (n+1) := ⟨k,hk⟩
        by_cases ht : t ∈ S
        · obtain ⟨y,hy,j,hj,hpre⟩ := (step_when_present ht).mp sampled
          have good : j < limit y := lt_of_le_of_lt (by omega) (he.trans_le (anti hy))
          exact (step_when_present (Finset.mem_univ t)).mpr ⟨y,hy,j,hj,(ih y j good).mpr hpre⟩
        · have hprev := can_smaller (Finset.Subset.refl _) (Nat.le_succ k) sampled
          have full := (ih x e he).mpr hprev
          by_contra failure
          apply ht
          refine Finset.mem_biUnion.mpr ⟨⟨x,e⟩,?_,?_⟩
          · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr he⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,full,failure⟩
      · have hprev := can_smaller (Finset.Subset.refl _) (Nat.le_succ k) sampled
        obtain ⟨f,hm,hx,hc⟩ := (ih x e he).mpr hprev
        refine ⟨f,hm,hx,?_⟩
        have stable : pref (Finset.univ : Finset (Fin (n+1))) (k+1) = pref Finset.univ k := by
          ext i
          have hi := i.isLt
          simp only [pref,Finset.mem_filter,Finset.mem_univ,true_and]
          omega
        rwa [stable]

end PEqualNP.Outside.L_meta_53174

theorem PEqualNP.Outside.L_meta_53174 :
  ∀ (X : Type) [Preorder X] [Fintype X] (limit : X → Nat), Antitone limit →
    ∀ (n : Nat) (cost : Fin (n+1) → X → Nat),
    let can := fun (S : Finset (Fin (n+1))) (k : Nat) (x : X) (e : Nat) =>
      ∃ f : Fin (n+1) → X, Monotone f ∧ (∀ i, f i ≤ x) ∧
        (S.filter (fun i => i.val < k)).sum (fun i => cost i (f i)) ≤ e
    ∃ S : Finset (Fin (n+1)), S.card ≤ Finset.univ.sum limit ∧
      ∀ (k : Nat) (x : X) (e : Nat), e < limit x →
        (can Finset.univ k x e ↔ can S k x e) := by
  intro X _ _ limit anti n cost
  exact PEqualNP.Outside.L_meta_53174.main limit anti cost
