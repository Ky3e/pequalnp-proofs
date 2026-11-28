import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53181_aux

noncomputable def paidArc {V : Type*} (side : V → Bool) (u v : V) (c : Nat) : Nat :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  if side u=false ∧ side v=true then c else 0

noncomputable def pinned {V : Type*} (side : V → Bool) (pin : Bool → V) (M : Nat) (v : V) (b : Bool) : Nat :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  if b then paidArc side v (pin true) M else paidArc side (pin false) v M

theorem pin_charge {V : Type*} (side : V → Bool) (pin : Bool → V)
    (lo : side (pin false)=false) (hi : side (pin true)=true) (M : Nat) (v : V) (b : Bool) :
    pinned side pin M v b = if side v=b then 0 else M := by
  cases b <;> cases h : side v <;> simp [pinned,paidArc,h,lo,hi]

theorem pin_freedom {V : Type*} (side : V → Bool) (pin : Bool → V)
    (lo : side (pin false)=false) (hi : side (pin true)=true) (B : Nat) (v : V) (b : Bool)
    (cap : pinned side pin (B+1) v b≤B) : side v=b := by
  by_contra ne
  rw [pin_charge side pin lo hi,ite_eq_right ne] at cap
  omega

theorem no_cut {V : Type*} {side : V → Bool} {u v : V} {B : Nat}
    (cap : paidArc side u v (B+1)≤B) : ¬ (side u=false ∧ side v=true) := by
  intro together
  simp [paidArc,together] at cap

theorem boolean_split {α : Type*} (L : Finset α) (q : α → Bool) :
    (∃ l∈L, ∃ r∈L, q l≠q r) ↔ (∃ l∈L, q l=true) ∧ (∃ l∈L, q l=false) := by
  constructor
  · rintro ⟨l,hl,r,hr,ne⟩
    cases lt : q l <;> cases rt : q r
    · exact (ne (lt.trans rt.symm)).elim
    · exact ⟨⟨r,hr,rt⟩,⟨l,hl,lt⟩⟩
    · exact ⟨⟨l,hl,lt⟩,⟨r,hr,rt⟩⟩
    · exact (ne (lt.trans rt.symm)).elim
  · rintro ⟨⟨l,hl,lt⟩,⟨r,hr,rt⟩⟩
    exact ⟨l,hl,r,hr,by simp [lt,rt]⟩

theorem xor_cancel (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> decide

theorem xor_switch (a b c : Bool) : xor (xor a b) c = xor (xor a c) b := by
  cases a <;> cases b <;> cases c <;> decide

theorem xor_rearrange {a b c : Bool} (h : xor a b=c) : a=xor c b := by
  rw [← h,xor_cancel]

def CutV (n g : Nat) := Sum Bool (Sum (Fin (n+1)) (Fin g × Bool))

def cutPin {n g : Nat} (x : Bool) : CutV n g := Sum.inl x
def cutVar {n g : Nat} (v : Fin (n+1)) : CutV n g := Sum.inr (Sum.inl v)
def cutAux {n g : Nat} (i : Fin g) (b : Bool) : CutV n g := Sum.inr (Sum.inr (i,b))

noncomputable def chosen {α : Type*} (P : Finset α) (v : α) : Bool :=
  @decide (v∈P) (Classical.propDecidable _)

theorem chosen_test {α : Type*} (P : Finset α) (v : α) : chosen P v=true ↔ v∈P := by
  simp [chosen]

noncomputable def cutFixed {n g : Nat} (B : Nat) (S P : Finset (Fin (n+1))) (sw : Fin (n+1) → Bool)
    (side : CutV n g → Bool) : Nat :=
  pinned side cutPin (B+1) (cutVar 0) (sw 0) +
    S.sum (fun v => pinned side cutPin (B+1) (cutVar v) (xor (chosen P v) (sw v)))

noncomputable def cutEndpoint {n g : Nat} (S P : Finset (Fin (n+1))) (off : Fin g → Bool)
    (i : Fin g) (l : Fin (n+1) × Bool) : CutV n g :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  if l.1∈S then cutPin (xor (xor (chosen P l.1) l.2) (off i)) else cutVar l.1

noncomputable def groupBill {n g : Nat} (B : Nat) (L : Fin g → Finset (Fin (n+1) × Bool))
    (weight : Fin g → Nat) (S P : Finset (Fin (n+1))) (R : Finset (Fin g))
    (sw : Fin (n+1) → Bool) (off : Fin g → Bool)
    (modes : {i // i∈R} → Option Bool) (side : CutV n g → Bool) (i : Fin g) : Nat :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  if hi : i∈R then
    let setting := modes ⟨i,hi⟩
    if setting.isNone then paidArc side (cutPin false) (cutPin true) (weight i)
    else (L i).sum (fun l =>
      pinned side cutPin (B+1) (cutVar l.1) (xor (setting.getD false) (xor (sw l.1) l.2)))
  else
    paidArc side (cutAux i false) (cutAux i true) (weight i) +
    (L i).sum (fun l =>
      paidArc side (cutEndpoint S P off i l) (cutAux i false) (B+1) +
      paidArc side (cutAux i true) (cutEndpoint S P off i l) (B+1))

theorem outer_endpoint {n g : Nat} (S P : Finset (Fin (n+1))) (off : Fin g → Bool) (sw x : Fin (n+1) → Bool)
    (side : CutV n g → Bool) (pins : ∀ b, side (cutPin b)=b)
    (assignment : ∀ v, side (cutVar v)=xor (x v) (sw v))
    (bound : ∀ v∈S, chosen P v=x v)
    (i : Fin g) (l : Fin (n+1) × Bool)
    (switch : l.1∉S → xor (sw l.1) l.2=off i) :
    side (cutEndpoint S P off i l)=xor (xor (x l.1) l.2) (off i) := by
  by_cases h : l.1∈S
  · simp [cutEndpoint,h,pins,bound _ h]
  · simp only [cutEndpoint,h,ite_false,assignment,← switch h]
    cases (x l.1) <;> cases (sw l.1) <;> cases l.2 <;> decide

theorem literal_pin (x sign sw : Bool) :
    xor (xor x sign) (xor sw sign) = xor x sw := by
  cases x <;> cases sign <;> cases sw <;> decide

theorem decide_uniform {α : Type*} (L : Finset α) (v : α → Bool)
    (same : ¬∃ l∈L, ∃ r∈L, v l≠v r) :
    ∀ l∈L, v l = @decide (∃ r∈L, v r=true) (Classical.propDecidable _) := by
  intro l hl
  by_cases h : ∃ r ∈ L, v r=true
  · obtain ⟨r,hr,known⟩ := h
    have eq : v l=true := by
      by_contra no
      exact same ⟨l,hl,r,hr,fun e => no (e.trans known)⟩
    simp [eq,show ∃ u∈L, v u=true from ⟨r,hr,known⟩]
  · have ne : v l≠true := fun yes => h ⟨l,hl,yes⟩
    have eq : v l=false := by cases e : v l; rfl; exact (ne e).elim
    simp [h,eq]

theorem xor_neq (a b c : Bool) : xor a c≠xor b c ↔ a≠b := by
  cases a <;> cases b <;> cases c <;> decide

theorem sum_part {α : Type*} (A : Finset α) (f : α → Nat) {i : α} (hi : i∈A) :
    f i ≤ A.sum f := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi

end PEqualNP.Outside.L_meta_53181_aux

open PEqualNP.Outside.L_meta_53181_aux

theorem PEqualNP.Outside.L_meta_53181 :
  ∀ (n g B : Nat) (L : Fin g → Finset (Fin (n+1) × Bool)) (weight : Fin g → Nat)
    (S : Finset (Fin (n+1))) (R : Finset (Fin g)) (sw : Fin (n+1) → Bool) (off : Fin g → Bool),
    (∀ i ∉ R, ∀ l ∈ L i, l.1 ∉ S → xor (sw l.1) l.2 = off i) →
    letI : ∀ q : Prop, Decidable q := Classical.propDecidable
    let V := Sum Bool (Sum (Fin (n+1)) (Fin g × Bool))
    let pin := fun (b : Bool) => (Sum.inl b : V)
    let var := fun (v : Fin (n+1)) => (Sum.inr (Sum.inl v) : V)
    let aux := fun (i : Fin g) (b : Bool) => (Sum.inr (Sum.inr (i,b)) : V)
    let M := B+1
    (∃ x : Fin (n+1) → Bool, x 0 = false ∧
      (Finset.univ : Finset (Fin g)).sum (fun i =>
        if ∃ l ∈ L i, ∃ r ∈ L i, xor (x l.1) l.2 ≠ xor (x r.1) r.2 then weight i else 0) ≤ B) ↔
    ∃ P ∈ S.powerset, ∃ modes : {i // i ∈ R} → Option Bool, ∃ side : V → Bool,
      side (pin false) = false ∧ side (pin true) = true ∧
      let arc := fun (u v : V) (c : Nat) => if side u = false ∧ side v = true then c else 0
      let force := fun (v : V) (b : Bool) =>
        if b then arc v (pin true) M else arc (pin false) v M
      let fixed := force (var 0) (sw 0) + S.sum (fun v => force (var v) (xor (decide (v ∈ P)) (sw v)))
      let bill := fun (i : Fin g) =>
        if hi : i ∈ R then
          let setting := modes ⟨i,hi⟩
          if setting.isNone then arc (pin false) (pin true) (weight i)
          else (L i).sum (fun l => force (var l.1) (xor (setting.getD false) (xor (sw l.1) l.2)))
        else
          arc (aux i false) (aux i true) (weight i) +
          (L i).sum (fun l =>
            let endpt := if l.1 ∈ S then pin (xor (xor (decide (l.1 ∈ P)) l.2) (off i)) else var l.1
            arc endpt (aux i false) M + arc (aux i true) endpt M)
      fixed + Finset.univ.sum bill ≤ B := by
  classical
  intro n g B L weight S R sw off switch V pin var aux M
  let source (x : Fin (n+1) → Bool) (l : Fin (n+1) × Bool) := xor (x l.1) l.2
  let bad (x : Fin (n+1) → Bool) (i : Fin g) :=
    ∃ l∈L i, ∃ r∈L i, source x l≠source x r
  let price (x : Fin (n+1) → Bool) (i : Fin g) :=
    @ite Nat (bad x i) (Classical.propDecidable _) (weight i) 0
  constructor
  · rintro ⟨x,x0,good⟩
    let P := S.filter (fun v => x v=true)
    have subset : P⊆S := Finset.filter_subset _ _
    have picked (v : Fin (n+1)) (hv : v∈S) : chosen P v=x v := by
      rw [Bool.eq_iff_iff,chosen_test]
      simp [P,hv]
    let norm (i : Fin g) (l : Fin (n+1) × Bool) := xor (source x l) (off i)
    let allOn (i : Fin g) := @decide (∀ l∈L i, norm i l=true) (Classical.propDecidable _)
    let anyOn (i : Fin g) := @decide (∃ l∈L i, norm i l=true) (Classical.propDecidable _)
    let modes (j : {i // i∈R}) := if bad x j.val then none
      else some (@decide (∃ l∈L j.val, source x l=true) (Classical.propDecidable _))
    let side : CutV n g → Bool := Sum.elim id (Sum.elim
      (fun v => xor (x v) (sw v)) (fun ib => if ib.2 then anyOn ib.1 else allOn ib.1))
    have pins (b : Bool) : side (cutPin b)=b := rfl
    have assignment (v : Fin (n+1)) : side (cutVar v)=xor (x v) (sw v) := rfl
    have lo (i : Fin g) : side (cutAux i false)=allOn i := rfl
    have hi (i : Fin g) : side (cutAux i true)=anyOn i := rfl
    refine ⟨P,Finset.mem_powerset.mpr subset,modes,side,pins false,pins true,?_⟩
    change cutFixed B S P sw side + Finset.univ.sum (groupBill B L weight S P R sw off modes side) ≤ B
    have fixed : cutFixed B S P sw side=0 := by
      unfold cutFixed
      rw [pin_charge side cutPin (pins false) (pins true),assignment,x0]
      simp only [Bool.false_xor,ite_eq_left rfl,ite_true,Nat.zero_add]
      apply Finset.sum_eq_zero
      intro v hv
      rw [pin_charge side cutPin (pins false) (pins true),assignment,picked v hv]
      simp
    have localBill (i : Fin g) : groupBill B L weight S P R sw off modes side i=price x i := by
      by_cases hR : i ∈ R
      · by_cases mixed : bad x i
        · simp [groupBill,hR,modes,mixed,paidArc,pins,price]
        · simp only [groupBill,dite_eq_left hR,modes,ite_eq_right mixed,
            Option.isNone_some, Bool.false_eq_true, ite_false,Option.getD_some,price]
          apply Finset.sum_eq_zero
          intro l hl
          have uniform := decide_uniform (L i) (source x) mixed l hl
          rw [pin_charge side cutPin (pins false) (pins true),assignment,← uniform]
          have eq : xor (source x l) (xor (sw l.1) l.2) = xor (x l.1) (sw l.1) :=
            literal_pin (x l.1) l.2 (sw l.1)
          rw [eq]
          simp
      · simp only [groupBill,dite_eq_right hR]
        have ep (l : Fin (n+1) × Bool) (hl : l∈L i) :
            side (cutEndpoint S P off i l)=norm i l :=
          outer_endpoint S P off sw x side pins assignment picked i l (switch i hR l hl)
        have zeroLoss : (L i).sum (fun l =>
            paidArc side (cutEndpoint S P off i l) (cutAux i false) (B+1) +
            paidArc side (cutAux i true) (cutEndpoint S P off i l) (B+1))=0 := by
          apply Finset.sum_eq_zero
          intro l hl
          rw [paidArc,paidArc,ep l hl,lo,hi]
          cases e : norm i l
          · have noAll : ¬∀ a∈L i, norm i a=true := fun h => Bool.false_ne_true (e.symm.trans (h l hl))
            have eq : allOn i=false := by
              unfold allOn
              rw [decide_eq_false_iff_not]
              exact noAll
            simp [e,eq]
          · have yesAny : ∃ a∈L i, norm i a=true := ⟨l,hl,e⟩
            have eq : anyOn i=true := by
              unfold anyOn
              exact Eq.mpr (@decide_eq_true_eq _ (Classical.propDecidable _)) yesAny
            simp [e,eq]
        rw [zeroLoss,Nat.add_zero,paidArc,lo,hi]
        have same : (allOn i=false ∧ anyOn i=true) ↔ bad x i := by
          have vary : (∃ l∈L i, ∃ r∈L i, norm i l≠norm i r) ↔ bad x i := by
            simp only [norm,bad,xor_neq]
          have absent : (¬∀ l∈L i, norm i l=true) ↔ ∃ l∈L i, norm i l=false := by
            push Not
            simp
          simpa only [allOn,anyOn,decide_eq_false_iff_not,decide_eq_true_eq,absent,and_comm] using
            ((boolean_split (L i) (norm i)).symm.trans vary)
        unfold price
        by_cases cond : bad x i
        · rw [ite_eq_left (same.mpr cond),ite_eq_left cond]
        · rw [ite_eq_right (fun h => cond (same.mp h)),ite_eq_right cond]
    rw [fixed,Nat.zero_add]
    simp_rw [localBill]
    exact good
  · rintro ⟨P,sub,modes,side,lo,hi,good⟩
    change cutFixed B S P sw side + Finset.univ.sum (groupBill B L weight S P R sw off modes side) ≤ B at good
    let x (v : Fin (n+1)) := xor (side (cutVar v)) (sw v)
    have pins (b : Bool) : side (cutPin b)=b := by cases b; exact lo; exact hi
    have assignment (v : Fin (n+1)) : side (cutVar v)=xor (x v) (sw v) := by simp [x,xor_cancel]
    have fx : cutFixed B S P sw side≤B := (Nat.le_add_right _ _).trans good
    have sum_ok : Finset.univ.sum (groupBill B L weight S P R sw off modes side)≤B :=
      (Nat.le_add_left _ _).trans good
    have first : side (cutVar 0)=sw 0 := by
      apply pin_freedom side cutPin lo hi B
      exact (Nat.le_add_right _ _).trans fx
    have x0 : x 0=false := by
      unfold x
      rw [first]
      cases sw 0 <;> decide
    have pick (v : Fin (n+1)) (hv : v∈S) : chosen P v=x v := by
      have fixed_v : side (cutVar v)=xor (chosen P v) (sw v) := by
        apply pin_freedom side cutPin lo hi B
        exact (sum_part S _ hv).trans ((Nat.le_add_left _ _).trans fx)
      exact xor_rearrange fixed_v.symm
    have bills (i : Fin g) : price x i ≤ groupBill B L weight S P R sw off modes side i := by
      by_cases mixed : bad x i
      · have bill_ok := (sum_part Finset.univ (groupBill B L weight S P R sw off modes side)
          (Finset.mem_univ i)).trans sum_ok
        simp only [price,ite_eq_left mixed]
        by_cases hR : i∈R
        · cases setting : modes ⟨i,hR⟩ with
          | none => simp [groupBill,hR,setting,paidArc,pins]
          | some b =>
            exfalso
            simp only [groupBill,dite_eq_left hR,setting,Option.isNone_some,
              Bool.false_eq_true,ite_false,Option.getD_some] at bill_ok
            have uniform (l : Fin (n+1) × Bool) (hl : l∈L i) : source x l=b := by
              have eq := pin_freedom side cutPin lo hi B (cutVar l.1)
                (xor b (xor (sw l.1) l.2)) ((sum_part (L i) _ hl).trans bill_ok)
              rw [assignment,←literal_pin (x l.1) l.2 (sw l.1)] at eq
              have over := congrArg (fun c => xor c (xor (sw l.1) l.2)) eq
              simpa only [xor_cancel,source] using over
            obtain ⟨l,hl,r,hr,ne⟩ := mixed
            exact ne ((uniform l hl).trans (uniform r hr).symm)
        · let norm (l : Fin (n+1) × Bool) := xor (source x l) (off i)
          have ep (l : Fin (n+1) × Bool) (hl : l∈L i) :
              side (cutEndpoint S P off i l)=norm l :=
            outer_endpoint S P off sw x side pins assignment pick i l (switch i hR l hl)
          have disparity : ∃ l∈L i, ∃ r∈L i, norm l≠norm r := by
            obtain ⟨l,hl,r,hr,ne⟩ := mixed
            exact ⟨l,hl,r,hr,(xor_neq _ _ _).mpr ne⟩
          obtain ⟨⟨l,hl,yes⟩,⟨r,hr,no⟩⟩ := (boolean_split (L i) norm).mp disparity
          simp only [groupBill,dite_eq_right hR] at bill_ok ⊢
          have limb (l : Fin (n+1) × Bool) (hl : l∈L i) :
              paidArc side (cutEndpoint S P off i l) (cutAux i false) (B+1) +
                paidArc side (cutAux i true) (cutEndpoint S P off i l) (B+1) ≤ B :=
            (sum_part (L i) _ hl).trans ((Nat.le_add_left _ _).trans bill_ok)
          have lowEnd : side (cutAux i false)=false := by
            have notCut := no_cut ((Nat.le_add_right _ _).trans (limb r hr))
            have eq := (ep r hr).trans no
            cases e : side (cutAux i false)
            · rfl
            · exact (notCut ⟨eq,e⟩).elim
          have highEnd : side (cutAux i true)=true := by
            have notCut := no_cut ((Nat.le_add_left _ _).trans (limb l hl))
            have eq := (ep l hl).trans yes
            cases e : side (cutAux i true)
            · exact (notCut ⟨e,eq⟩).elim
            · rfl
          simpa [paidArc,lowEnd,highEnd] using Nat.le_add_right (weight i)
            ((L i).sum (fun l =>
              paidArc side (cutEndpoint S P off i l) (cutAux i false) (B+1) +
              paidArc side (cutAux i true) (cutEndpoint S P off i l) (B+1)))
      · simp [price,mixed]
    refine ⟨x,x0,?_⟩
    exact (Finset.sum_le_sum (fun i _ => bills i)).trans sum_ok
