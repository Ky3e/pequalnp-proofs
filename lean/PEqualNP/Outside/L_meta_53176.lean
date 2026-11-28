import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53176_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- The circuit rank construction below is from the checked proof of L-meta-53168. -/
private def M_run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

private def M_tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def M_code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := M_tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: M_code gs a
    | _ => M_code gs a

private def M_mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

private theorem M_code_len (gs : List Gate) (w : List Bool) :
    (M_code gs w).length = (gs.filter M_mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [M_code,h,M_mark,List.filter_cons,ih]

private def M_ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

private theorem M_extend_order {x y : List Bool} (w : M_ordered x y) {a b : Bool}
    (ab : a=true → b=true) : M_ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

private theorem M_output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : M_ordered x y) (same : M_code gs x=M_code gs y) :
    M_ordered (M_run gs x) (M_run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change M_ordered (M_run gs (M_tick x g)) (M_run gs (M_tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (M_extend_order w ?_) (by simpa only [M_code,M_tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (M_extend_order w ?_) (by simpa only [M_code,M_tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [M_code,h,List.cons.injEq] at same
      apply ih rest (M_extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

private theorem M_input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    M_ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
private def M_driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + M_driverNumber bs

private theorem M_driver_bound (l : List Bool) : M_driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [M_driverNumber,pow_succ] <;> omega

private theorem M_driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : M_driverNumber a=M_driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := M_driver_bound xs
      have h₂ := M_driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [M_driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

private theorem M_driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : M_ordered a b) :
    M_driverNumber (M_code gs a) ≤ M_driverNumber (M_code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : M_code [g] a=M_code [g] b) : M_ordered (M_tick a g) (M_tick b g) :=
      M_output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [M_code,eq]
      exact ih tailops (growth (by simp [M_code,eq]))
    · simp only [M_code,eq]
      exact ih tailops (growth (by simp [M_code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (M_code gs (M_tick a g)).length=(M_code gs (M_tick b g)).length := by simp [M_code_len]
      change M_driverNumber (M_code (g::gs) a) ≤ M_driverNumber (M_code (g::gs) b)
      simp only [M_code,eq]
      rw [←eq]
      change M_driverNumber (out a :: M_code gs (M_tick a g)) ≤ M_driverNumber (out b :: M_code gs (M_tick b g))
      by_cases same : out a=out b
      · have next : M_ordered (M_tick a g) (M_tick b g) := M_extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [M_driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(M_code gs (M_tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := M_driver_bound (M_code gs (M_tick a g))
        rw [len] at bound
        simp only [M_driverNumber,one,zero,Bool.false_eq_true,if_false,if_true,Nat.zero_add]
        omega

theorem M_circuit_rank {n : Nat} (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) :
    ∃ h : (Fin n → Bool) → Nat, Monotone h ∧ (∀ x, h x < 2^PEqualNP.NotBracket.notCount C) ∧
      ∀ x y, x ≤ y → h x = h y → ∀ w,
        (C.wires (List.ofFn x ++ [false,true])).getD w false=true →
        (C.wires (List.ofFn y ++ [false,true])).getD w false=true := by
  let raw (x : Fin n → Bool) := List.ofFn x ++ [false,true]
  let h (x : Fin n → Bool) := M_driverNumber (M_code C.gates (raw x))
  have ops (g : Gate) (mem : g ∈ C.gates) := (fan g mem).1
  have order {x y : Fin n → Bool} (xy : x ≤ y) : M_ordered (raw x) (raw y) := by
    apply M_input_order
    intro i hi
    have v := xy i
    rw [hi] at v
    exact le_antisymm (by cases y i <;> decide) v
  have size : (C.gates.filter M_mark).length = PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    cases eq : g.op <;> simp [M_mark,eq]
  refine ⟨h,fun x y xy => M_driver_mono _ ops (order xy),?_,?_⟩
  · intro x
    simpa only [h,M_code_len,size] using M_driver_bound (M_code C.gates (raw x))
  · intro x y xy eq w
    have same : M_code C.gates (raw x)=M_code C.gates (raw y) := M_driver_injective (by simp [M_code_len]) eq
    exact (M_output_order ops (order xy) same).2 w

theorem count_le_with_exceptions {T : Type*} [Fintype T] (good before after : T → Prop)
    [DecidablePred good] [DecidablePred before] [DecidablePred after]
    (h : ∀ t, before t → ¬ good t → after t) :
    (Finset.univ.filter before).card ≤
      (Finset.univ.filter after).card + (Finset.univ.filter good).card := by
  classical
  apply Nat.le_trans (Finset.card_le_card (t := (Finset.univ.filter after) ∪ (Finset.univ.filter good)) ?_)
    (Finset.card_union_le _ _)
  intro t ht
  have hb := (Finset.mem_filter.mp ht).2
  by_cases hg : good t
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h t hb hg⟩)

private theorem card_as_indicator {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ a ∈ s, if p a then (1 : Nat) else 0 := by
  rw [← Finset.sum_filter]
  simp

theorem count_bad_windows {R T X : Type*} [Fintype T] [LinearOrder R] [Preorder X]
    (L Q : R → X) (apart : ∀ r s, r < s → Q r ≤ L s)
    (grade : T → X → Nat) (hi : T → Nat)
    (mono : ∀ t, Monotone (grade t)) (bounded : ∀ t x, grade t x ≤ hi t)
    (U : Finset R) :
    ∑ r ∈ U, (Finset.univ.filter (fun t => grade t (L r) < grade t (Q r))).card ≤
      ∑ t : T, min U.card (hi t) := by
  classical
  calc
    _ = ∑ t : T, (U.filter (fun r => grade t (L r) < grade t (Q r))).card := by
      simp only [card_as_indicator]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t _
      apply le_min (Finset.card_le_card (Finset.filter_subset _ _))
      have pred (r : R) : r ∈ U.filter (fun r => grade t (L r) < grade t (Q r)) →
          grade t (L r) ∈ Finset.range (hi t) := by
        intro hr
        apply Finset.mem_range.mpr
        exact ((Finset.mem_filter.mp hr).2).trans_le (bounded t _)
      rw [← Finset.card_range (hi t)]
      apply Finset.card_le_card_of_injOn (fun r => grade t (L r)) pred
      intro r hr s hs eq
      by_contra ne
      rcases lt_or_gt_of_ne ne with h | h
      · exact ((Finset.mem_filter.mp hr).2.trans_le (mono t (apart r s h))).ne eq
      · exact ((Finset.mem_filter.mp hs).2.trans_le (mono t (apart s r h))).ne eq.symm

end PEqualNP.Outside.L_meta_53176_aux

open PEqualNP.Outside.L_meta_53176_aux

theorem PEqualNP.Outside.L_meta_53176 :
  ∀ (n T R a m : Nat) (b : Fin T → Nat)
      (left mid right : Fin R → Fin (n+1))
      (early late : Fin R → Fin m → Fin (n+1))
      (P : Fin R → Fin m → (Fin a → Bool) → Bool)
      (lo hi : Fin R → Fin m → Nat),
    (∀ r s, r < s → right r ≤ left s) →
    (∀ r, left r ≤ mid r ∧ mid r ≤ right r) →
    (∀ r j, left r ≤ early r j ∧ early r j ≤ mid r ∧
      mid r ≤ late r j ∧ late r j ≤ right r) →
    (∀ r j, Monotone (P r j)) →
    (∀ r j, lo r j ≤ hi r j ∧ hi r j ≤ T) →
    ∀ (C : Fin T → PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin T → Fin a → Nat),
    (∀ t, PEqualNP.MetaComplexity.FanInTwo (C t) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) (C t) ∧
      PEqualNP.NotBracket.notCount (C t) ≤ b t ∧ (C t).output < n+2+(C t).size ∧
      ∀ i, tap t i < n+2+(C t).size) →
    let word := fun (t : Fin T) (x : Fin (n+1)) (i : Fin a) =>
      ((C t).wires (List.ofFn (fun j : Fin n => decide (j.val < x.val)) ++ [false,true])).getD (tap t i) false
    let count := fun (r : Fin R) (j : Fin m) (x : Fin (n+1)) =>
      ((Finset.univ : Finset (Fin T)).filter (fun t => P r j (word t x) = true)).card
    (∀ r j, lo r j ≤ count r j (early r j) ∧ count r j (late r j) ≤ hi r j) →
    let err := fun (r : Fin R) => (Finset.univ : Finset (Fin m)).sup (fun j =>
      max (lo r j - count r j (mid r)) (count r j (mid r) - hi r j))
    ∀ U : Finset (Fin R), U.sum err ≤
      (Finset.univ : Finset (Fin T)).sum (fun t => min U.card (2^(b t)-1)) := by
  classical
  intro n T R a m b left mid right early late P lo hi apart between inside monotone limits
  intro C tap gate word count observations err U
  have circuit (t : Fin T) := M_circuit_rank (n := n) (C t) (gate t).1
  choose grade grade_mono grade_lt grade_eq using circuit
  let x (k : Fin (n+1)) (i : Fin n) := decide (i.val < k.val)
  have x_mono : Monotone x := by
    intro j k jk i
    by_cases h : i.val < j.val
    · have h' : i.val < k.val := h.trans_le jk
      simp [x, h, h']
    · simp [x, h]
  let score (t : Fin T) (k : Fin (n+1)) := grade t (x k)
  have score_mono (t : Fin T) : Monotone (score t) := (grade_mono t).comp x_mono
  have score_bounded (t : Fin T) (k : Fin (n+1)) : score t k ≤ 2^(b t)-1 := by
    have h := grade_lt t (x k)
    have h' : 2^PEqualNP.NotBracket.notCount (C t) ≤ 2^(b t) :=
      Nat.pow_le_pow_right (by decide) (gate t).2.2.1
    exact Nat.le_sub_one_of_lt (h.trans_le h')
  let bad (r : Fin R) (t : Fin T) := score t (left r) < score t (right r)
  let charge (r : Fin R) := (Finset.univ.filter (bad r)).card
  have word_le (r : Fin R) (t : Fin T) (k l : Fin (n+1))
      (hk : left r ≤ k) (hkl : k ≤ l) (hl : l ≤ right r) (hn : ¬ bad r t) :
      word t k ≤ word t l := by
    have scores : score t k = score t l := by
      apply le_antisymm (score_mono t hkl)
      exact (score_mono t hl).trans ((Nat.le_of_not_gt hn).trans (score_mono t hk))
    intro i
    cases e : word t k i with
    | false => simp
    | true =>
        have yes : word t l i = true := grade_eq t (x k) (x l) (x_mono hkl) scores (tap t i) e
        simp [yes]
  have bound (r : Fin R) : err r ≤ charge r := by
    apply Finset.sup_le
    intro j _
    have first : count r j (early r j) ≤ count r j (mid r) + charge r := by
      apply count_le_with_exceptions (bad r)
      intro t known hn
      have pass := monotone r j (word_le r t _ _ (inside r j).1 (inside r j).2.1 (between r).2 hn)
      rw [known] at pass
      exact le_antisymm (by cases P r j (word t (mid r)) <;> decide) pass
    have second : count r j (mid r) ≤ count r j (late r j) + charge r := by
      apply count_le_with_exceptions (bad r)
      intro t known hn
      have pass := monotone r j (word_le r t _ _ (between r).1 (inside r j).2.2.1 (inside r j).2.2.2 hn)
      rw [known] at pass
      exact le_antisymm (by cases P r j (word t (late r j)) <;> decide) pass
    have hlo := (observations r j).1
    have hhi := (observations r j).2
    exact max_le (by omega) (by omega)
  exact (Finset.sum_le_sum (fun r _ => bound r)).trans
    (count_bad_windows left right apart score (fun t => 2^(b t)-1) score_mono score_bounded U)
