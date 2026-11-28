import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1393

section Bank

variable {n q : Nat} (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n))

def hit (t : Fin q) (A : Finset (Fin n)) : Prop := ∃ u ∈ A, ∃ v ∈ A, E t u v = true
def nbr (t : Fin q) (v : Fin n) : Finset (Fin n) := S.filter (fun u => E t u v = true)
def same (A A' : Finset (Fin n)) : Prop :=
  ∀ t B, Disjoint S B → (hit E t (A ∪ B) ↔ hit E t (A' ∪ B))
def one : Prop := ∃ (z : Finset (Fin n) → Bool) (read : Fin q → Bool → Finset (Fin n) → Prop),
  ∀ t A, A ⊆ S → ∀ B, Disjoint S B → (hit E t (A ∪ B) ↔ read t (z A) B)

@[simp] theorem empty_hit (t : Fin q) : ¬hit E t ∅ := by simp [hit]

theorem single_hit (diag : ∀ t v, E t v v = false) (t : Fin q) (v : Fin n) : ¬hit E t {v} := by
  simp [hit,diag]

theorem pair_hit (sym : ∀ t u v, E t u v = E t v u) (diag : ∀ t v, E t v v = false)
    (t : Fin q) (u v : Fin n) : hit E t {u,v} ↔ E t u v = true := by
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · simp [diag] at h
    · exact h
    · rwa [sym] at h
    · simp [diag] at h
  · intro he
    exact ⟨u,by simp,v,by simp,he⟩

theorem hit_mono {t : Fin q} {A B : Finset (Fin n)} (hs : A ⊆ B) (h : hit E t A) : hit E t B := by
  obtain ⟨u,hu,v,hv,e⟩ := h
  exact ⟨u,hs hu,v,hs hv,e⟩

theorem hit_union (sym : ∀ t u v, E t u v = E t v u) (t : Fin q) (A B : Finset (Fin n)) (sub : A ⊆ S) :
    hit E t (A ∪ B) ↔ hit E t A ∨ hit E t B ∨ ∃ v ∈ B, (A ∩ nbr E S t v).Nonempty := by
  constructor
  · rintro ⟨u,hu,v,hv,e⟩
    rw [Finset.mem_union] at hu hv
    rcases hu with hu|hu <;> rcases hv with hv|hv
    · exact Or.inl ⟨u,hu,v,hv,e⟩
    · exact Or.inr (Or.inr ⟨v,hv,u,Finset.mem_inter.mpr ⟨hu,Finset.mem_filter.mpr ⟨sub hu,e⟩⟩⟩)
    · exact Or.inr (Or.inr ⟨u,hu,v,Finset.mem_inter.mpr ⟨hv,Finset.mem_filter.mpr ⟨sub hv,(sym t v u).trans e⟩⟩⟩)
    · exact Or.inr (Or.inl ⟨u,hu,v,hv,e⟩)
  · rintro (h|h|⟨v,hv,u,hu⟩)
    · exact hit_mono E Finset.subset_union_left h
    · exact hit_mono E Finset.subset_union_right h
    · obtain ⟨hA,hn⟩ := Finset.mem_inter.mp hu
      exact ⟨u,Finset.mem_union_left _ hA,v,Finset.mem_union_right _ hv,(Finset.mem_filter.mp hn).2⟩

theorem profile (symm : ∀ t u v, E t u v = E t v u) (diag : ∀ t v, E t v v = false)
    (A A' : Finset (Fin n)) (ha : A ⊆ S) (ha' : A' ⊆ S) :
    same E S A A' ↔ ∀ t, (hit E t A ↔ hit E t A') ∧
      (¬hit E t A → ∀ v ∉ S, (A ∩ nbr E S t v).Nonempty ↔ (A' ∩ nbr E S t v).Nonempty) := by
  constructor
  · intro equivalent t
    have top : hit E t A ↔ hit E t A' := by simpa using equivalent t ∅ (by simp)
    refine ⟨top,fun empty v hv => ?_⟩
    have empty' : ¬hit E t A' := fun h => empty (top.mpr h)
    have test := equivalent t {v} (by simpa using hv)
    rw [hit_union E S symm t A {v} ha,hit_union E S symm t A' {v} ha'] at test
    simpa [empty,empty',single_hit E diag] using test
  · intro conditions t B disj
    have ⟨top,cross⟩ := conditions t
    rw [hit_union E S symm t A B ha,hit_union E S symm t A' B ha']
    by_cases h : hit E t A
    · simp [h,top.mp h]
    · have h' : ¬hit E t A' := fun h' => h (top.mpr h')
      simp only [h,h',false_or]
      have eq : (∃ v ∈ B, (A ∩ nbr E S t v).Nonempty) ↔
          ∃ v ∈ B, (A' ∩ nbr E S t v).Nonempty := by
        constructor <;> rintro ⟨v,hv,mem⟩
        · exact ⟨v,hv,(cross h v (fun hs => Finset.disjoint_left.mp disj hs hv)).mp mem⟩
        · exact ⟨v,hv,(cross h v (fun hs => Finset.disjoint_left.mp disj hs hv)).mpr mem⟩
      rw [eq]

theorem same_if_bit {z : Finset (Fin n) → Bool} {read : Fin q → Bool → Finset (Fin n) → Prop}
    (ob : ∀ t A, A ⊆ S → ∀ B, Disjoint S B → (hit E t (A ∪ B) ↔ read t (z A) B))
    {A B : Finset (Fin n)} (ha : A ⊆ S) (hb : B ⊆ S) (eq : z A=z B) : same E S A B := by
  intro t x hx
  exact (ob t A ha x hx).trans (eq ▸ (ob t B hb x hx).symm)

theorem common_other {z : Finset (Fin n) → Bool} {read : Fin q → Bool → Finset (Fin n) → Prop}
    (ob : ∀ t A, A ⊆ S → ∀ B, Disjoint S B → (hit E t (A ∪ B) ↔ read t (z A) B))
    {A B : Finset (Fin n)} (ha : A ⊆ S) (hb : B ⊆ S)
    (na : ¬same E S A ∅) (nb : ¬same E S B ∅) : same E S A B := by
  have e1 : z A ≠ z ∅ := fun e => na (same_if_bit E S ob ha (Finset.empty_subset _) e)
  have e2 : z B ≠ z ∅ := fun e => nb (same_if_bit E S ob hb (Finset.empty_subset _) e)
  have eq : z A=z B := by cases ha' : z A <;> cases hb' : z B <;> cases hc' : z ∅ <;> simp_all
  exact same_if_bit E S ob ha hb eq

theorem internal_other {A : Finset (Fin n)} {t : Fin q} (hitA : hit E t A) : ¬same E S A ∅ := by
  intro equal
  exact empty_hit E t (by simpa using (equal t ∅ (by simp)).mp (by simpa using hitA))

theorem outside_other (diag : ∀ t v, E t v v = false) (t : Fin q) (u v : Fin n)
    (_hu : u ∈ S) (hv : v ∉ S)
    (edge : E t u v = true) : ¬same E S {u} ∅ := by
  intro same0
  have test := same0 t {v} (by simpa using hv)
  have hitPair : hit E t ({u} ∪ {v}) := by
    exact ⟨u,by simp,v,by simp,edge⟩
  have eq := test.mp hitPair
  exact single_hit E diag t v (by simpa using eq)

theorem one_forward (symm : ∀ t u v, E t u v = E t v u) (diag : ∀ t v, E t v v = false)
    (h : one E S) :
    ((∀ t v, v ∉ S → nbr E S t v = ∅) ∧
      ∀ t z, hit E t S → hit E z S → ∀ u ∈ S, ∀ v ∈ S, E t u v = E z u v) ∨
    ((∀ t, ¬hit E t S) ∧ ∀ t z v w, v ∉ S → w ∉ S →
      (nbr E S t v).Nonempty → (nbr E S z w).Nonempty → nbr E S t v = nbr E S z w) := by
  classical
  obtain ⟨bit,read,ob⟩ := h
  by_cases internal : ∃ t, hit E t S
  · obtain ⟨t0,ht0⟩ := internal
    have ns : ¬same E S S ∅ := internal_other E S ht0
    refine Or.inl ⟨?_,?_⟩
    · intro t v hv
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨inS,e⟩ := Finset.mem_filter.mp hu
      have nu := outside_other E S diag t u v inS hv e
      have rel := common_other E S ob (Finset.singleton_subset_iff.mpr inS) (Finset.Subset.refl _) nu ns
      have equal := (profile E S symm diag _ _ (Finset.singleton_subset_iff.mpr inS) (Finset.Subset.refl _)).mp rel t0
      exact single_hit E diag t0 u (equal.1.mpr ht0)
    · intro t z ht hz u hu v hv
      apply Bool.eq_iff_iff.mpr
      have sub : ({u,v} : Finset (Fin n)) ⊆ S := by
        intro w hw
        simp only [Finset.mem_insert,Finset.mem_singleton] at hw
        rcases hw with rfl|rfl <;> assumption
      have forward (r s : Fin q) (hs : hit E s S) (e : E r u v = true) : E s u v = true := by
        have ha := (pair_hit E symm diag r u v).mpr e
        have rel := common_other E S ob sub (Finset.Subset.refl _) (internal_other E S ha) ns
        have equal := (profile E S symm diag _ _ sub (Finset.Subset.refl _)).mp rel s
        exact (pair_hit E symm diag s u v).mp (equal.1.mpr hs)
      exact ⟨forward t z hz,forward z t ht⟩
  · have never : ∀ t, ¬hit E t S := fun t ht => internal ⟨t,ht⟩
    refine Or.inr ⟨never,?_⟩
    intro t z v w hv hw nt nz
    have contained (r s : Fin q) (v w : Fin n) (hv : v ∉ S) (hw : w ∉ S)
        (nons : (nbr E S s w).Nonempty) : nbr E S r v ⊆ nbr E S s w := by
      intro u hu
      obtain ⟨u0,hu0⟩ := nons
      obtain ⟨hs,e⟩ := Finset.mem_filter.mp hu
      obtain ⟨h0,e0⟩ := Finset.mem_filter.mp hu0
      have sub := Finset.singleton_subset_iff.mpr hs
      have sub0 := Finset.singleton_subset_iff.mpr h0
      have rel := common_other E S ob sub sub0 (outside_other E S diag r u v hs hv e)
        (outside_other E S diag s u0 w h0 hw e0)
      have test := ((profile E S symm diag _ _ sub sub0).mp rel s).2 (single_hit E diag s u) w hw
      obtain ⟨u1,hu1⟩ := test.mpr ⟨u0,Finset.mem_inter.mpr ⟨by simp,hu0⟩⟩
      obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hu1
      have e1 : u1=u := Finset.mem_singleton.mp h1
      exact e1 ▸ h2
    exact Finset.Subset.antisymm (contained t z v w hv hw nz) (contained z t w v hw hv nt)

theorem one_backward (symm : ∀ t u v, E t u v = E t v u)
    (h : ((∀ t v, v ∉ S → nbr E S t v = ∅) ∧
      ∀ t z, hit E t S → hit E z S → ∀ u ∈ S, ∀ v ∈ S, E t u v = E z u v) ∨
    ((∀ t, ¬hit E t S) ∧ ∀ t z v w, v ∉ S → w ∉ S →
      (nbr E S t v).Nonempty → (nbr E S z w).Nonempty → nbr E S t v = nbr E S z w)) : one E S := by
  classical
  rcases h with ⟨isolated, common⟩ | ⟨independent, common⟩
  · let bit (A : Finset (Fin n)) := decide (∃ t, hit E t A)
    let read (t : Fin q) (z : Bool) (B : Finset (Fin n)) := hit E t B ∨ hit E t S ∧ z=true
    refine ⟨bit,read,?_⟩
    intro t A sub B disj
    rw [hit_union E S symm t A B sub]
    have never : ¬ ∃ v ∈ B, (A ∩ nbr E S t v).Nonempty := by
      rintro ⟨v,hv,h⟩
      have out : v ∉ S := fun hm => Finset.disjoint_left.mp disj hm hv
      simp [isolated t v out] at h
    simp only [never,or_false,read,bit,decide_eq_true_eq]
    constructor
    · rintro (internal|outsideHit)
      · exact Or.inr ⟨hit_mono E sub internal, t,internal⟩
      · exact Or.inl outsideHit
    · rintro (outsideHit|⟨ht,r,hr⟩)
      · exact Or.inr outsideHit
      · obtain ⟨u,hu,v,hv,e⟩ := hr
        have eq := common r t (hit_mono E sub (show hit E r A from ⟨u,hu,v,hv,e⟩)) ht u (sub hu) v (sub hv)
        exact Or.inl ⟨u,hu,v,hv,eq ▸ e⟩
  · let bit (A : Finset (Fin n)) := decide (∃ t v, v ∉ S ∧ (A ∩ nbr E S t v).Nonempty)
    let read (t : Fin q) (z : Bool) (B : Finset (Fin n)) :=
      hit E t B ∨ ∃ v ∈ B, (nbr E S t v).Nonempty ∧ z=true
    refine ⟨bit,read,?_⟩
    intro t A sub B disj
    rw [hit_union E S symm t A B sub]
    have never : ¬hit E t A := fun h => independent t (hit_mono E sub h)
    simp only [never,false_or,read,bit,decide_eq_true_eq]
    constructor
    · rintro (outsideHit|⟨v,hv,u,hm⟩)
      · exact Or.inl outsideHit
      · exact Or.inr ⟨v,hv,⟨u,(Finset.mem_inter.mp hm).2⟩,t,v,
          fun h => Finset.disjoint_left.mp disj h hv,⟨u,hm⟩⟩
    · rintro (outsideHit|⟨v,hv,nonempty,r,w,out,meet⟩)
      · exact Or.inl outsideHit
      · have neighbor : (nbr E S r w).Nonempty := by
          obtain ⟨u,hu⟩ := meet
          exact ⟨u,(Finset.mem_inter.mp hu).2⟩
        have eq := common r t w v out (fun h => Finset.disjoint_left.mp disj h hv) neighbor nonempty
        exact Or.inr ⟨v,hv,eq ▸ meet⟩

theorem classify (symm : ∀ t u v, E t u v = E t v u) (diag : ∀ t v, E t v v = false) : one E S ↔
    ((∀ t v, v ∉ S → nbr E S t v = ∅) ∧
      ∀ t z, hit E t S → hit E z S → ∀ u ∈ S, ∀ v ∈ S, E t u v = E z u v) ∨
    ((∀ t, ¬hit E t S) ∧ ∀ t z v w, v ∉ S → w ∉ S →
      (nbr E S t v).Nonempty → (nbr E S z w).Nonempty → nbr E S t v = nbr E S z w) :=
  ⟨one_forward E S symm diag,one_backward E S symm⟩

end Bank

end PEqualNP.Outside.L_lib_1393

open PEqualNP.Outside.L_lib_1393 in
theorem PEqualNP.Outside.L_lib_1393 :
  ∀ (n q : Nat) (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n)),
    (∀ t u v, E t u v = E t v u) → (∀ t v, E t v v = false) →
    let hit := fun (t : Fin q) (A : Finset (Fin n)) => ∃ u ∈ A, ∃ v ∈ A, E t u v = true
    let nbr := fun (t : Fin q) (v : Fin n) => S.filter (fun u => E t u v = true)
    let one := ∃ (z : Finset (Fin n) → Bool) (read : Fin q → Bool → Finset (Fin n) → Prop),
      ∀ t A, A ⊆ S → ∀ B, Disjoint S B → (hit t (A ∪ B) ↔ read t (z A) B)
    (∀ A A' : Finset (Fin n), A ⊆ S → A' ⊆ S →
      ((∀ t B, Disjoint S B → (hit t (A ∪ B) ↔ hit t (A' ∪ B))) ↔
        ∀ t, (hit t A ↔ hit t A') ∧
          (¬hit t A → ∀ v ∉ S, ((A ∩ nbr t v).Nonempty ↔ (A' ∩ nbr t v).Nonempty)))) ∧
    (one ↔
      ((∀ t v, v ∉ S → nbr t v = ∅) ∧
        ∀ t z, hit t S → hit z S → ∀ u ∈ S, ∀ v ∈ S, E t u v = E z u v) ∨
      ((∀ t, ¬hit t S) ∧ ∀ t z v w, v ∉ S → w ∉ S →
        (nbr t v).Nonempty → (nbr z w).Nonempty → nbr t v = nbr z w))
  := by
  intro n q E S symm diag
  exact ⟨profile E S symm diag,classify E S symm diag⟩
