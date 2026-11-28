import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53184_aux

-- Grade and circuit primitives adapted from the accepted proof at pin
-- 1adcd7757ae90df113b64e1e1c0794b4eb2fb1b8, lean/PEqualNP/Outside/L_lib_1294.lean.
-- The grade is generalized to direct lists; the circuit operations build a scalar decoder.
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.NotBracket (notCount)

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1],?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD,ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none noneX,List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases h : g.inputs with
  | nil => simp
  | cons i rest => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i,here,rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.any_eq_true] at on ⊢
  obtain ⟨v,hm,active⟩ := on
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact ⟨_,List.mem_map.mpr ⟨i,here,rfl⟩,(bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1],if inverting g then 2*s.2+(firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance,neg,ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance,neg] using strict
    exact ⟨increase.le,fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega,?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit,op,GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gates : List Gate) : ℕ := (gates.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting,h]

private theorem run_consistent (gates : List Gate) (allowed : ∀ g ∈ gates, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gates.foldl advance s) (gates.foldl advance t) := by
  induction gates generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gates : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2^d) :
    (gates.foldl advance s).2 < 2^(d+negCount gates) := by
  induction gates generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2^(d+1) := by
        simp only [advance,neg,ite_true,Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d+1) raises
      simpa [negCount,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2^d := by simpa [advance,neg] using bound
      simpa [negCount,neg] using ih (advance s g) d same

private theorem run_wires (gates : List Gate) (s : List Bool × ℕ) :
    (gates.foldl advance s).1 =
      gates.foldl (fun w g => w ++ [outputBit g w]) s.1 := by
  induction gates generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def value (C : Circuit) (x : List Bool) (i : Nat) : Bool := (C.wires x).getD i false

def nextWire (n : Nat) (C : Circuit) : Nat := n + C.size

def emptyCircuit : Circuit := ⟨[], 0⟩

def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

def appendNot (C : Circuit) (a : Nat) : Circuit := appendGate C ⟨.not, [a]⟩

def withOutput (C : Circuit) (o : Nat) : Circuit := ⟨C.gates, o⟩

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

private theorem fold_length (gates : List Gate) (x : List Bool) :
    (gates.foldl gateStep x).length = x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons,ih]
    simp [gateStep] <;> omega

private theorem fold_value (gates : List Gate) (x : List Bool) {i : Nat} (valid : i < x.length) :
    (gates.foldl gateStep x).getD i false = x.getD i false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g rest ih =>
    have available : i < (gateStep x g).length := by simp [gateStep]; omega
    rw [List.foldl_cons,ih _ available]
    exact List.getD_append _ _ _ _ valid

@[local simp] theorem emptyCircuit_size : emptyCircuit.size = 0 := rfl

@[local simp] theorem emptyCircuit_notCount : notCount emptyCircuit = 0 := rfl

theorem emptyCircuit_fanInTwo : FanInTwo emptyCircuit := by
  simp [FanInTwo,emptyCircuit]

theorem emptyCircuit_readsBack (n : Nat) : ReadsBack n emptyCircuit := by
  simp [ReadsBack,emptyCircuit]

@[local simp] theorem withOutput_size (C : Circuit) (o : Nat) : (withOutput C o).size = C.size := rfl

@[local simp] theorem withOutput_output (C : Circuit) (o : Nat) : (withOutput C o).output = o := rfl

@[local simp] theorem withOutput_notCount (C : Circuit) (o : Nat) :
    notCount (withOutput C o) = notCount C := rfl

@[local simp] theorem withOutput_fanInTwo (C : Circuit) (o : Nat) :
    FanInTwo (withOutput C o) ↔ FanInTwo C := Iff.rfl

@[local simp] theorem withOutput_readsBack (n : Nat) (C : Circuit) (o : Nat) :
    ReadsBack n (withOutput C o) ↔ ReadsBack n C := Iff.rfl

@[local simp] theorem withOutput_value (C : Circuit) (o : Nat) (x : List Bool) (i : Nat) :
    value (withOutput C o) x i = value C x i := rfl

@[local simp] theorem withOutput_eval (C : Circuit) (o : Nat) (x : List Bool) :
    (withOutput C o).eval x = value C x o := rfl

@[local simp] theorem appendGate_size (C : Circuit) (g : Gate) :
    (appendGate C g).size = C.size + 1 := by
  simp [appendGate,Circuit.size]

@[local simp] theorem appendGate_output (C : Circuit) (g : Gate) :
    (appendGate C g).output = C.output := rfl

theorem appendGate_prefix (C : Circuit) (g : Gate) : C.gates <+: (appendGate C g).gates :=
  ⟨[g],rfl⟩

@[local simp] theorem appendGate_notCount (C : Circuit) (g : Gate) :
    notCount (appendGate C g) = notCount C + (@ite ℕ (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not) 1 0) := by
  by_cases inv : g.op = .not <;> simp [notCount,appendGate,inv]

@[local simp] theorem nextWire_appendGate (n : Nat) (C : Circuit) (g : Gate) :
    nextWire n (appendGate C g) = nextWire n C + 1 := by
  simp [nextWire,Nat.add_assoc]

theorem appendGate_fanInTwo {C : Circuit} {g : Gate} (basis : FanInTwo C)
    (op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : g.inputs.length ≤ 2) : FanInTwo (appendGate C g) := by
  intro k hk
  rcases List.mem_append.mp hk with old | new
  · exact basis k old
  · have same : k = g := List.mem_singleton.mp new
    subst k
    exact ⟨op,arity⟩

theorem appendGate_readsBack {n : Nat} {C : Circuit} {g : Gate} (valid : ReadsBack n C)
    (inputs : ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGate C g) := by
  intro j hj i hi
  change i ∈ ((C.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
  by_cases old : j < C.gates.length
  · rw [List.getD_append _ _ _ _ old] at hi
    exact valid j old i hi
  · change j < (C.gates ++ [g]).length at hj
    have same : j = C.gates.length := by simp at hj; omega
    subst j
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    exact inputs i (by simpa using hi)

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = nextWire x.length C := by
  rw [wires_eq]
  exact fold_length C.gates x

theorem value_input (C : Circuit) (x : List Bool) {i : Nat} (valid : i < x.length) :
    value C x i = x.getD i false := by
  rw [value,wires_eq]
  exact fold_value C.gates x valid

theorem nextWire_le_of_prefix {n : Nat} {C D : Circuit} (extension : C.gates <+: D.gates) :
    nextWire n C ≤ nextWire n D := Nat.add_le_add_left extension.length_le n

theorem value_of_prefix {C D : Circuit} (extension : C.gates <+: D.gates) {x : List Bool}
    {i : Nat} (valid : i < nextWire x.length C) : value D x i = value C x i := by
  obtain ⟨rest,appended⟩ := extension
  simp only [value,wires_eq,← appended,List.foldl_append]
  apply fold_value
  rw [fold_length]
  exact valid

theorem appendGate_wires (C : Circuit) (g : Gate) (x : List Bool) :
    (appendGate C g).wires x = C.wires x ++ [g.op.eval (g.inputs.map fun i => value C x i)] := by
  simp [appendGate,wires_eq,gateStep,value]

theorem appendGate_old {C : Circuit} {g : Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGate C g) x i = value C x i :=
  value_of_prefix (appendGate_prefix C g) valid

theorem appendGate_new (C : Circuit) (g : Gate) (x : List Bool) :
    value (appendGate C g) x (nextWire x.length C) =
      g.op.eval (g.inputs.map fun i => value C x i) := by
  rw [value,appendGate_wires,← wires_length]
  simp [List.getD_eq_getElem?_getD]

@[local simp] theorem appendNot_size (C : Circuit) (a : Nat) :
    (appendNot C a).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendNot_notCount (C : Circuit) (a : Nat) :
    notCount (appendNot C a) = notCount C + 1 := by simp [appendNot]

theorem appendNot_fanInTwo {C : Circuit} {a : Nat} (basis : FanInTwo C) :
    FanInTwo (appendNot C a) := appendGate_fanInTwo (g := ⟨.not,[a]⟩) basis (by simp) (by simp)

theorem appendNot_readsBack {n : Nat} {C : Circuit} {a : Nat} (valid : ReadsBack n C)
    (input : a < nextWire n C) : ReadsBack n (appendNot C a) := by
  apply appendGate_readsBack (g := ⟨.not,[a]⟩) valid
  intro i member
  have same : i = a := List.mem_singleton.mp member
  subst i
  exact input

theorem appendNot_new (C : Circuit) (x : List Bool) (a : Nat) :
    value (appendNot C a) x (nextWire x.length C) = !value C x a := by
  exact appendGate_new C ⟨.not,[a]⟩ x
def binaryValue (conjunction x y : Bool) : Bool := if conjunction then x && y else x || y

def appendGates (C : Circuit) (gates : List Gate) : Circuit := ⟨C.gates ++ gates, C.output⟩

def appendFamily {k : Nat} (C : Circuit) (gate : Fin k → Gate) : Circuit :=
  appendGates C (List.ofFn gate)

private theorem appendGates_cons (C : Circuit) (g : Gate) (rest : List Gate) :
    appendGates C (g :: rest) = appendGates (appendGate C g) rest := by
  simp [appendGates,appendGate,List.append_assoc]

theorem appendGates_prefix (C : Circuit) (gates : List Gate) : C.gates <+: (appendGates C gates).gates :=
  ⟨gates,rfl⟩

@[local simp] theorem appendGates_size (C : Circuit) (gates : List Gate) :
    (appendGates C gates).size = C.size + gates.length := by
  simp [appendGates,Circuit.size]

@[local simp] theorem appendGates_nextWire (n : Nat) (C : Circuit) (gates : List Gate) :
    nextWire n (appendGates C gates) = nextWire n C + gates.length := by
  simp [nextWire,Nat.add_assoc]

@[local simp] theorem appendGates_output (C : Circuit) (gates : List Gate) :
    (appendGates C gates).output = C.output := rfl

theorem appendGates_notCount (C : Circuit) (gates : List Gate) :
    notCount (appendGates C gates) =
      notCount C + (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length := by
  simp [notCount,appendGates]

theorem appendGates_notCount_eq {C : Circuit} {gates : List Gate}
    (noNot : ∀ g ∈ gates, g.op ≠ .not) : notCount (appendGates C gates) = notCount C := by
  have empty : (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)) = [] :=
    List.filter_eq_nil_iff.mpr fun g member => by simp [noNot g member]
  simp [appendGates_notCount,empty]

private abbrev GateShape (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem appendGates_fanInTwo {C : Circuit} {gates : List Gate} (basis : FanInTwo C)
    (shape : ∀ g ∈ gates, GateShape g) : FanInTwo (appendGates C gates) := by
  intro g member
  rcases List.mem_append.mp member with old | added
  · exact basis g old
  · exact shape g added

theorem appendGates_readsBack {n : Nat} {C : Circuit} {gates : List Gate} (valid : ReadsBack n C)
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGates C gates) := by
  induction gates generalizing C with
  | nil => simpa [appendGates] using valid
  | cons g rest ih =>
    rw [appendGates_cons]
    have fits : ∀ i ∈ g.inputs, i < nextWire n C := reads g (List.mem_cons_self ..)
    apply ih (appendGate_readsBack valid fits)
    intro h member i input
    exact Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
      (nextWire_le_of_prefix (appendGate_prefix C g))

theorem appendGates_old {C : Circuit} {gates : List Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGates C gates) x i = value C x i :=
  value_of_prefix (appendGates_prefix C gates) valid

private def readGate (C : Circuit) (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (value C x))

private theorem appendGates_wires {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) :
    (appendGates C gates).wires x = C.wires x ++ gates.map (readGate C x) := by
  induction gates generalizing C with
  | nil => simp [appendGates]
  | cons g rest ih =>
    have restReads : ∀ h ∈ rest, ∀ i ∈ h.inputs, i < nextWire x.length (appendGate C g) :=
      fun h member i input => Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
        (nextWire_le_of_prefix (appendGate_prefix C g))
    have tail : rest.map (readGate (appendGate C g) x) = rest.map (readGate C x) := by
      apply List.map_congr_left
      intro h member
      unfold readGate
      apply congrArg h.op.eval
      apply List.map_congr_left
      intro i input
      exact appendGate_old (g := g) (reads h (List.mem_cons_of_mem _ member) i input)
    rw [appendGates_cons,ih restReads,tail,appendGate_wires]
    simp [List.append_assoc,readGate]

theorem appendGates_new {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) (j : Fin gates.length) :
    value (appendGates C gates) x (nextWire x.length C + j.val) =
      gates[j].op.eval (gates[j].inputs.map (value C x)) := by
  change ((appendGates C gates).wires x).getD (nextWire x.length C + j.val) false = _
  rw [appendGates_wires (x := x) reads]
  have within : (C.wires x).length ≤ nextWire x.length C + j.val := by rw [wires_length]; omega
  have index : nextWire x.length C + j.val - nextWire x.length C = j.val := by omega
  rw [List.getD_append_right _ _ _ _ within,wires_length,index]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem j.isLt,readGate]

theorem appendFamily_prefix {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    C.gates <+: (appendFamily C gate).gates := appendGates_prefix C _

@[local simp] theorem appendFamily_size {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).size = C.size + k := by simp [appendFamily]

@[local simp] theorem appendFamily_nextWire {k : Nat} (n : Nat) (C : Circuit) (gate : Fin k → Gate) :
    nextWire n (appendFamily C gate) = nextWire n C + k := by simp [appendFamily]

theorem appendFamily_notCount_eq {k : Nat} {C : Circuit} {gate : Fin k → Gate}
    (noNot : ∀ j, (gate j).op ≠ .not) : notCount (appendFamily C gate) = notCount C := by
  apply appendGates_notCount_eq
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact noNot j

theorem appendFamily_fanInTwo {k : Nat} {C : Circuit} {gate : Fin k → Gate} (basis : FanInTwo C)
    (shape : ∀ j, GateShape (gate j)) : FanInTwo (appendFamily C gate) := by
  apply appendGates_fanInTwo basis
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact shape j

theorem appendFamily_readsBack {k n : Nat} {C : Circuit} {gate : Fin k → Gate}
    (valid : ReadsBack n C) (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C) :
    ReadsBack n (appendFamily C gate) := by
  apply appendGates_readsBack valid
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact reads j

theorem appendFamily_new {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire x.length C) (j : Fin k) :
    value (appendFamily C gate) x (nextWire x.length C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have readsList : ∀ g ∈ List.ofFn gate, ∀ i ∈ g.inputs, i < nextWire x.length C := by
    intro g member
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp member
    exact reads t
  let t : Fin (List.ofFn gate).length := ⟨j.val,by simpa using j.isLt⟩
  simpa [appendFamily,t] using appendGates_new readsList t
private theorem old_value {n : ℕ} {C D : Circuit} (ext : C.gates <+: D.gates)
    {x : List Bool} (length : x.length = n) {w : ℕ} (live : w < nextWire n C) :
    value D x w = value C x w :=
  value_of_prefix ext (by simpa only [length] using live)

private theorem family_value {k n : ℕ} {C : Circuit} {gate : Fin k → Gate}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C)
    (x : List Bool) (length : x.length = n) (j : Fin k) :
    value (appendFamily C gate) x (nextWire n C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have valid : ∀ a b, b ∈ (gate a).inputs → b < nextWire x.length C := by
    rw [length]
    exact reads
  simpa only [length] using appendFamily_new (C := C) (gate := gate) (x := x) valid j


private def Good (P : Nat → Prop) (N : Nat) (C : Circuit) : Prop :=
  FanInTwo C ∧ ReadsBack N C ∧ ∀ g ∈ C.gates, ∀ w ∈ g.inputs, P w

private def Live (P : Nat → Prop) (N : Nat) (C : Circuit) (w : Nat) : Prop :=
  w < nextWire N C ∧ P w

private theorem live_extend {P : Nat → Prop} {N w : Nat} {C D : Circuit}
    (ext : C.gates <+: D.gates) (h : Live P N C w) : Live P N D w :=
  ⟨h.1.trans_le (nextWire_le_of_prefix ext), h.2⟩

private theorem live_new {P : Nat → Prop} {N k : Nat} {C : Circuit} (g : Fin k → Gate)
    (fresh : ∀ w, N ≤ w → P w) (i : Fin k) :
    Live P N (appendFamily C g) (nextWire N C + i.val) := by
  have hi := i.isLt
  constructor
  · rw [appendFamily_nextWire]; omega
  · apply fresh; unfold nextWire; omega

private theorem family_good {P : Nat → Prop} {N k : Nat} {C : Circuit} {g : Fin k → Gate}
    (h : Good P N C) (shape : ∀ i, GateShape (g i))
    (used : ∀ i w, w ∈ (g i).inputs → Live P N C w) : Good P N (appendFamily C g) := by
  refine ⟨appendFamily_fanInTwo h.1 shape, appendFamily_readsBack h.2.1 (fun i w hw => (used i w hw).1), ?_⟩
  intro g' hg w hw
  rcases List.mem_append.mp hg with old | added
  · exact h.2.2 g' old w hw
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp added
    exact (used i w hw).2

private theorem emit_not {X : Type*} {P : Nat → Prop} {N : Nat} {C : Circuit}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (good : Good P N C) {a : Nat} (ha : Live P N C a) :
    ∃ D b, Good P N D ∧ C.gates <+: D.gates ∧ Live P N D b ∧
      D.size = C.size+1 ∧ notCount D = notCount C+1 ∧
      ∀ x, value D (input x) b = !value C (input x) a := by
  let D := appendNot C a
  have ext : C.gates <+: D.gates := appendGate_prefix C _
  refine ⟨D, nextWire N C, ⟨appendNot_fanInTwo good.1, appendNot_readsBack good.2.1 ha.1, ?_⟩,
    ext, ⟨by simp [D, appendNot], fresh _ (by simp [nextWire])⟩,
    appendNot_size .., appendNot_notCount .., ?_⟩
  · intro g hg w hw
    rcases List.mem_append.mp hg with old | added
    · exact good.2.2 g old w hw
    · have eq := List.mem_singleton.mp added
      subst g
      have eq' : w = a := List.mem_singleton.mp hw
      simpa [eq'] using ha.2
  · intro x
    simpa only [len] using appendNot_new C (input x) a

private theorem emit_family {X : Type*} {P : Nat → Prop} {N k : Nat} {C : Circuit}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (good : Good P N C) (conj : Bool)
    (a b : Fin k → Nat) (ha : ∀ i, Live P N C (a i)) (hb : ∀ i, Live P N C (b i)) :
    ∃ D, ∃ w : Fin k → Nat, Good P N D ∧ C.gates <+: D.gates ∧ (∀ i, Live P N D (w i)) ∧
      D.size = C.size+k ∧ notCount D = notCount C ∧
      ∀ x i, value D (input x) (w i) = binaryValue conj (value C (input x) (a i)) (value C (input x) (b i)) := by
  let g (i : Fin k) : Gate := ⟨if conj then .and else .or, [a i,b i]⟩
  have used (i : Fin k) (w : Nat) (hw : w ∈ (g i).inputs) : Live P N C w := by
    change w ∈ [a i,b i] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact ha i
    · exact hb i
  have shape (i : Fin k) : GateShape (g i) := by cases conj <;> simp [GateShape,g]
  refine ⟨appendFamily C g, fun i => nextWire N C + i.val, family_good good shape used,
    appendFamily_prefix .., live_new g fresh, appendFamily_size .., ?_, ?_⟩
  · apply appendFamily_notCount_eq
    intro i
    cases conj <;> simp [g]
  · intro x i
    rw [family_value (fun i w hw => (used i w hw).1) (input x) (len x) i]
    cases conj <;> simp [g,binaryValue,GateOp.eval]

private theorem emit_binary {X : Type*} {P : Nat → Prop} {N : Nat} {C : Circuit}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (good : Good P N C) (conj : Bool)
    {a b : Nat} (ha : Live P N C a) (hb : Live P N C b) :
    ∃ D w, Good P N D ∧ C.gates <+: D.gates ∧ Live P N D w ∧
      D.size = C.size+1 ∧ notCount D = notCount C ∧
      ∀ x, value D (input x) w = binaryValue conj (value C (input x) a) (value C (input x) b) := by
  obtain ⟨D,w,h,e,l,s,c,v⟩ := emit_family input len fresh good (k := 1) conj
    (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
  exact ⟨D,w 0,h,e,l 0,s,c,fun x => v x 0⟩

private theorem mod_half {k j : Nat} (low : k ≤ j) (high : j < 2*k) : j % k = j-k := by
  have e : j = j-k+k := by omega
  calc
    j % k = (j-k+k) % k := congrArg (· % k) e
    _ = j-k := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem fold_level {k j i : Nat} (hk : 0 < k) (hi : i < k-1) (hj : j < 2*k) :
    ((decide (i < j) && !decide (k-1 < j)) || decide (k+i < j)) = decide (i < j % k) := by
  by_cases small : j < k
  · have hp : ¬k-1 < j := by omega
    have hu : ¬k+i < j := by omega
    simp [hp,hu,Nat.mod_eq_of_lt small]
  · have hp : k-1 < j := by omega
    have cmp : (k+i < j) ↔ (i < j-k) := by omega
    simp [hp,mod_half (by omega : k ≤ j) hj,cmp]

private theorem select_level {k j i : Nat} (hk : 0 < k) (hi : i < 2*k) (hj : j < 2*k) :
    (decide (i % k = j % k) &&
      (if i < k then !decide (k-1 < j) else decide (k-1 < j))) = decide (i = j) := by
  by_cases il : i < k <;> by_cases jl : j < k
  · simp [il, Nat.mod_eq_of_lt il, Nat.mod_eq_of_lt jl, show ¬k-1 < j by omega]
  · simp [il, show k-1 < j by omega, show i ≠ j by omega]
  · simp [il, show ¬k-1 < j by omega, show i ≠ j by omega]
  · simp [il, show k-1 < j by omega, mod_half (by omega : k ≤ i) hi,
      mod_half (by omega : k ≤ j) hj, show i-k = j-k ↔ i = j by omega]
 
-- The pulse bank uses one recursive folded thermometer, not two recursive circuits.
set_option maxHeartbeats 700000 in
private theorem oneHot {X : Type*} {P : Nat → Prop} {N : Nat}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (r : Nat) :
    ∀ {C : Circuit} {t : Nat} (good : Good P N C) (ht : Live P N C t)
      (on : ∀ x, value C (input x) t = true)
      (tap : Nat → Nat) (live : ∀ i < 2^r-1, Live P N C (tap i))
      (j : X → Nat) (bound : ∀ x, j x < 2^r)
      (thermo : ∀ x i, i < 2^r-1 → value C (input x) (tap i) = decide (i < j x)),
    ∃ D, ∃ w : Fin (2^r) → Nat, ∃ b v, Good P N D ∧ C.gates <+: D.gates ∧ (∀ i, Live P N D (w i)) ∧
      D.size = C.size+b+v ∧ notCount D = notCount C+v ∧ b ≤ 4*2^r-4 ∧ v ≤ r ∧
      ∀ x (i : Fin (2^r)), value D (input x) (w i) = decide (i.val = j x) := by
  induction r with
  | zero =>
    intro C t good ht on tap live j bound thermo
    refine ⟨C,fun _ => t,0,0,good,List.prefix_refl _,fun _ => ht,by simp,by simp,by decide,le_rfl,?_⟩
    intro x i
    have hi := i.isLt
    have hj := bound x
    rw [on x, decide_eq_true (show i.val = j x by omega)]
  | succ r ih =>
    intro C t good ht on tap live j bound thermo
    let k := 2^r
    have hk : 0 < k := Nat.two_pow_pos _
    have hpow : 2^(r+1) = 2*k := by simp [k,pow_succ,Nat.mul_comm]
    have hp : k-1 < 2^(r+1)-1 := by omega
    obtain ⟨A,np,ga,ea,npl,sa,na,ap⟩ := emit_not input len fresh good (live (k-1) hp)
    have left (i : Fin (k-1)) : Live P N A (tap i.val) :=
      live_extend ea (live _ (by have := i.isLt; omega))
    obtain ⟨B,lo,gb,eb,lol,sb,nb,bp⟩ := emit_family input len fresh ga true
      (fun i : Fin (k-1) => tap i.val) (fun _ => np) left (fun _ => npl)
    have right (i : Fin (k-1)) : Live P N B (tap (k+i.val)) :=
      live_extend (ea.trans eb) (live _ (by have := i.isLt; omega))
    obtain ⟨F,fw,gf,ef,fwl,sf,nf,fp⟩ := emit_family input len fresh gb false lo
      (fun i : Fin (k-1) => tap (k+i.val)) lol right
    have ef0 := ea.trans (eb.trans ef)
    let ft (i : Nat) : Nat := if h : i < k-1 then fw ⟨i,h⟩ else t
    have ftl (i : Nat) (hi : i < k-1) : Live P N F (ft i) := by
      simpa only [ft,dif_pos hi] using fwl ⟨i,hi⟩
    have jbound (x : X) : j x < 2*k := hpow ▸ bound x
    have folded (x : X) (i : Nat) (hi : i < k-1) :
        value F (input x) (ft i) = decide (i < j x % k) := by
      simp only [ft,dite_eq_left hi]
      rw [fp,bp,ap,
        old_value ea (len x) (live i (by omega)).1,
        old_value (ea.trans eb) (len x) (live (k+i) (by omega)).1]
      simp only [thermo x i (by omega), thermo x (k-1) hp, thermo x (k+i) (by omega),binaryValue,ite_true,ite_false,Bool.false_eq_true]
      exact fold_level hk hi (jbound x)
    obtain ⟨R,pulse,b,v,gr,er,pl,sr,nr,br,vr,rp⟩ := ih gf (live_extend ef0 ht)
      (fun x => (old_value ef0 (len x) ht.1).trans (on x)) ft ftl (fun x => j x % k)
      (fun x => Nat.mod_lt _ hk) folded
    have er0 := ef0.trans er
    have ear := eb.trans (ef.trans er)
    let side (i : Fin (2^(r+1))) := if i.val < k then np else tap (k-1)
    let sub (i : Fin (2^(r+1))) : Fin k := ⟨i.val % k, Nat.mod_lt _ hk⟩
    have sideLive (i : Fin (2^(r+1))) : Live P N R (side i) := by
      by_cases hi : i.val < k
      · simpa only [side,if_pos hi] using live_extend ear npl
      · simpa only [side,if_neg hi] using live_extend er0 (live _ hp)
    have sideEval (x : X) (i : Fin (2^(r+1))) :
        value R (input x) (side i) =
          (if i.val < k then !decide (k-1 < j x) else decide (k-1 < j x)) := by
      by_cases hi : i.val < k
      · simp only [side,ite_eq_left hi]
        rw [old_value ear (len x) npl.1,ap,thermo x (k-1) hp]
      · simp only [side,ite_eq_right hi]
        rw [old_value er0 (len x) (live _ hp).1,thermo x (k-1) hp]
    obtain ⟨D,w,gd,ed,wl,sd,nd,dp⟩ := emit_family input len fresh gr true
      (fun i => pulse (sub i)) side (fun i => pl (sub i)) sideLive
    refine ⟨D,w,b+(k-1)+(k-1)+2^(r+1),v+1,gd,er0.trans ed,wl,?_,?_,?_,by omega,?_⟩
    · omega
    · omega
    · change b ≤ 4*k-4 at br
      omega
    · intro x i
      rw [dp,rp,sideEval]
      exact select_level hk (hpow ▸ i.isLt) (jbound x)


private def raw {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool) : List Bool :=
  List.ofFn (fun a : Fin n => decide (a ∈ M)) ++
  List.ofFn (fun g : Fin q => decide (g.val < j.val)) ++ List.ofFn x ++ [false,true]

private theorem raw_len {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool) :
    (raw M j x).length = n+q+(q+1)+2 := by simp [raw,Nat.add_assoc]

private theorem getD_ofFn {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt]

private theorem raw_opt {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool)
    (i : Fin n) : (raw M j x).getD i.val false = decide (i ∈ M) := by
  simp only [raw,List.append_assoc]
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
  exact getD_ofFn _ i

private theorem raw_mark {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool)
    (i : Fin q) : (raw M j x).getD (n+i.val) false = decide (i.val < j.val) := by
  simp only [raw,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn, Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simpa using i.isLt)]
  exact getD_ofFn _ i

private theorem raw_data {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool)
    (i : Fin (q+1)) : (raw M j x).getD (n+q+i.val) false = x i := by
  simp only [raw,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,
    show n+q+i.val-n = q+i.val by omega,
    List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simpa using i.isLt)]
  exact getD_ofFn _ i

private theorem raw_end {n q : Nat} (M : Finset (Fin n)) (j : Fin (q+1)) (x : Fin (q+1) → Bool)
    (i : Nat) : (raw M j x).getD (n+q+(q+1)+i) false = [false,true].getD i false := by
  simp only [raw,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,
    show n+q+(q+1)+i-n = q+(q+1)+i by omega,
    List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,
    show q+(q+1)+i-q = q+1+i by omega,
    List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.add_sub_cancel_left]

private theorem raw_order {n q : Nat} (M : Finset (Fin n)) {j k : Fin (q+1)}
    {x y : Fin (q+1) → Bool} (jk : j.val ≤ k.val) (xy : x ≤ y) :
    bitOrder (raw M j x) (raw M k y) := by
  refine ⟨by simp [raw_len],?_⟩
  intro i
  by_cases h0 : i < n
  · exact le_of_eq ((raw_opt M j x ⟨i,h0⟩).trans (raw_opt M k y ⟨i,h0⟩).symm)
  by_cases h1 : i < n+q
  · let a : Fin q := ⟨i-n,by omega⟩
    have eq : i = n+a.val := by dsimp [a]; omega
    rw [eq,raw_mark,raw_mark,bool_order]
    simpa only [decide_eq_true_eq] using (fun h : a.val < j.val => h.trans_le jk)
  by_cases h2 : i < n+q+(q+1)
  · let a : Fin (q+1) := ⟨i-(n+q),by omega⟩
    have eq : i = n+q+a.val := by dsimp [a]; omega
    rw [eq,raw_data,raw_data]
    exact xy a
  · have eq : i = n+q+(q+1)+(i-(n+q+(q+1))) := by omega
    conv_lhs => rw [eq,raw_end]
    conv_rhs => rw [eq,raw_end]

private theorem fold_agree (gs : List Gate) (w v : List Bool) (o : Nat) (len : w.length = v.length)
    (agree : ∀ i, (i = o ∨ ∃ g ∈ gs, i ∈ g.inputs) → w.getD i false = v.getD i false) :
    (gs.foldl gateStep w).getD o false = (gs.foldl gateStep v).getD o false := by
  induction gs generalizing w v with
  | nil => exact agree o (Or.inl rfl)
  | cons g gs ih =>
    have same : g.op.eval (g.inputs.map (fun i => w.getD i false)) =
        g.op.eval (g.inputs.map (fun i => v.getD i false)) := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      exact fun i hi => agree i (Or.inr ⟨g,List.mem_cons_self ..,hi⟩)
    simp only [List.foldl_cons]
    apply ih _ _ (by simp [gateStep,len])
    intro i hi
    unfold gateStep
    rw [same]
    by_cases h : i < w.length
    · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (len ▸ h)]
      apply agree
      rcases hi with left | ⟨a,ha,ia⟩
      · exact Or.inl left
      · exact Or.inr ⟨a,List.mem_cons_of_mem _ ha,ia⟩
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]

private def Respects {n : Nat} (S : Finset (Fin n)) (C : Circuit) : Prop :=
  ∀ a : Fin n, (C.output = a.val ∨ ∃ g ∈ C.gates, a.val ∈ g.inputs) → a ∈ S

private theorem erase_missed {n q : Nat} {S M : Finset (Fin n)} {C : Circuit}
    (respects : Respects S C) (miss : ¬(M ∩ S).Nonempty) (j : Fin (q+1)) (x : Fin (q+1) → Bool) :
    C.eval (raw M j x) = C.eval (raw (∅ : Finset (Fin n)) j x) := by
  change (C.wires (raw M j x)).getD C.output false = (C.wires (raw ∅ j x)).getD C.output false
  rw [wires_eq,wires_eq]
  apply fold_agree _ _ _ _ (by simp [raw_len])
  intro i hi
  by_cases h : i < n
  · let a : Fin n := ⟨i,h⟩
    have hs : a ∈ S := respects a (hi.imp Eq.symm id)
    have hm : a ∉ M := fun m => miss ⟨a,Finset.mem_inter.mpr ⟨m,hs⟩⟩
    change (raw M j x).getD a.val false = (raw ∅ j x).getD a.val false
    rw [raw_opt,raw_opt]
    simp [hm]
  · have hm : (List.ofFn (fun a : Fin n => decide (a ∈ M))).length ≤ i :=
      by simpa using Nat.le_of_not_gt h
    have he : (List.ofFn (fun a : Fin n => decide (a ∈ (∅ : Finset (Fin n))))).length ≤ i :=
      by simpa using Nat.le_of_not_gt h
    simp only [raw,List.append_assoc,List.getD_append_right _ _ _ _ hm,
      List.getD_append_right _ _ _ _ he,List.length_ofFn]

private def grade (C : Circuit) (x : List Bool) : Nat := (C.gates.foldl advance (x,0)).2

private theorem grade_bound (C : Circuit) (x : List Bool) : grade C x < 2^(notCount C) := by
  simpa [grade,negCount_spec] using run_bounded C.gates (x,0) 0 (by change 0 < (1 : Nat); decide)

private theorem grade_order {C : Circuit} (basis : FanInTwo C) {x y : List Bool} (xy : bitOrder x y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → C.eval x ≤ C.eval y) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by simpa [Allowed] using (basis g mem).1
  have initial : consistent (x,0) (y,0) := ⟨le_rfl,fun _ => xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1,?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires,run_wires] at order
  exact order C.output

private theorem fall {C : Circuit} (basis : FanInTwo C) {x y : List Bool} (xy : bitOrder x y)
    (up : C.eval x = true) (down : C.eval y = false) : grade C x < grade C y := by
  obtain ⟨le,eq⟩ := grade_order basis xy
  refine lt_of_le_of_ne le (fun h => ?_)
  have bad := eq h
  rw [up,down] at bad
  exact (by decide : ¬(true ≤ false)) bad

private def Fits {n q : Nat} (E : Finset (Finset (Fin n))) (S : Finset (Fin n)) (b : Nat)
    (cost : Nat → Prop) : Prop :=
  ∃ C : Circuit,
    FanInTwo C ∧ ReadsBack (n+q+(q+1)+2) C ∧
    C.output < n+q+(q+1)+2+C.size ∧ notCount C ≤ b ∧
    cost (C.size - notCount C) ∧ Respects S C ∧
    (∀ M ∈ E, ∀ x, C.eval (raw (q := q) M 0 x) = x 0) ∧
    ∀ (h : Fin q) x, C.eval (raw (∅ : Finset (Fin n)) h.succ x) = x h.succ

private theorem necessity {n r : Nat} {E : Finset (Finset (Fin n))} {S : Finset (Fin n)}
    (fit : Fits (q := 2^r) E S r (fun _ => True)) : ∀ M ∈ E, (M ∩ S).Nonempty := by
  intro M hM
  by_contra miss
  obtain ⟨C,fan,_,_,budget,_,respects,base,ordinary⟩ := fit
  let q := 2^r
  let bits (j : Nat) (i : Fin (q+1)) : Bool := decide (i.val ≤ j)
  have bits_le {i j : Nat} (ij : i ≤ j) : bits i ≤ bits j := by
    intro a
    rw [bool_order]
    simpa only [bits,decide_eq_true_eq] using (fun h : a.val ≤ i => h.trans ij)
  have correct (j : Fin (q+1)) (x : Fin (q+1) → Bool) :
      C.eval (raw (∅ : Finset (Fin n)) j x) = x j := by
    refine Fin.cases ?_ (fun h => ordinary h x) j
    exact (erase_missed respects miss 0 x).symm.trans (base M hM x)
  let g (j : Fin (q+1)) := grade C (raw (∅ : Finset (Fin n)) j (bits j.val))
  have step (j : Fin q) : g j.castSucc < g j.succ := by
    have up : C.eval (raw (∅ : Finset (Fin n)) j.castSucc (bits j.val)) = true := by
      simp [correct,bits]
    have down : C.eval (raw (∅ : Finset (Fin n)) j.succ (bits j.val)) = false := by
      simp [correct,bits]
    have drop := fall fan (raw_order ∅ (show j.castSucc.val ≤ j.succ.val by simp) le_rfl) up down
    have rise := (grade_order fan (raw_order (∅ : Finset (Fin n)) (j := j.succ) (k := j.succ)
      le_rfl (bits_le (show j.val ≤ j.succ.val by simp)))).1
    exact drop.trans_le rise
  have lower (j : Nat) : ∀ hj : j < q+1, j ≤ g ⟨j,hj⟩ := by
    induction j with
    | zero => intro; omega
    | succ j ih =>
      intro hj
      have a : j < q := by omega
      have old := ih (by omega)
      have inc := step ⟨j,a⟩
      change g ⟨j,by omega⟩ < g ⟨j+1,hj⟩ at inc
      omega
  have hi : q < q+1 := by omega
  have upper := (grade_bound C (raw (∅ : Finset (Fin n)) (⟨q,hi⟩ : Fin (q+1)) (bits q))).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) budget)
  exact (Nat.not_lt_of_ge (lower q hi)) upper

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b :=
  le_antisymm ((bool_order _ _).mpr h.mp) ((bool_order _ _).mpr h.mpr)

private theorem emit_any {X : Type*} {P : Nat → Prop} {N : Nat}
    (input : X → List Bool) (len : ∀ x, (input x).length = N)
    (fresh : ∀ w, N ≤ w → P w) (ws : List Nat) :
    ∀ {C : Circuit} {a : Nat} (good : Good P N C) (ha : Live P N C a)
      (hw : ∀ w ∈ ws, Live P N C w),
      ∃ D b, Good P N D ∧ C.gates <+: D.gates ∧ Live P N D b ∧
        D.size = C.size+ws.length ∧ notCount D = notCount C ∧
        ∀ x, value D (input x) b = (value C (input x) a || ws.any (value C (input x))) := by
  induction ws with
  | nil => intro C a good ha hw; exact ⟨C,a,good,List.prefix_refl _,ha,by simp,rfl,by simp⟩
  | cons w ws ih =>
    intro C a good ha hw
    have h := hw w (List.mem_cons_self ..)
    obtain ⟨A,b,g,e,l,s,c,p⟩ := emit_binary input len fresh good false ha h
    obtain ⟨D,d,gd,ed,dl,sd,nd,dp⟩ := ih g l
      (fun i hi => live_extend e (hw i (List.mem_cons_of_mem _ hi)))
    refine ⟨D,d,gd,e.trans ed,dl,by simp [sd,s,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm],nd.trans c,?_⟩
    intro x
    have eq : ws.any (value A (input x)) = ws.any (value C (input x)) := by
      apply bool_ext
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨i,hi,truth⟩
      · exact ⟨i,hi,(old_value e (len x) (hw i (List.mem_cons_of_mem _ hi)).1).symm.trans truth⟩
      · exact ⟨i,hi,(old_value e (len x) (hw i (List.mem_cons_of_mem _ hi)).1).trans truth⟩
    rw [dp,p,eq]
    simp [binaryValue,Bool.or_assoc]

-- Demultiplex the thermometer into pulses, then route the matching data wire.
set_option maxHeartbeats 700000 in

def C_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def C_run (w : List Bool) (gs : List Gate) : List Bool := gs.foldl C_step w

theorem C_run_append (w : List Bool) (a b : List Gate) : C_run w (a ++ b) = C_run (C_run w a) b :=
  List.foldl_append

theorem C_run_single (w : List Bool) (g : Gate) : C_run w [g] = C_step w g := rfl

theorem C_run_len : ∀ (gs : List Gate) (w : List Bool), (C_run w gs).length = w.length + gs.length
  | [], w => by simp [C_run]
  | g :: gs, w => by
    have := C_run_len gs (C_step w g)
    simp only [C_run, List.foldl_cons] at this ⊢
    rw [this]; simp [C_step]; omega

theorem C_step_pre (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (C_step w g).getD i false = w.getD i false := List.getD_append _ _ _ _ h

theorem C_step_last (w : List Bool) (g : Gate) :
    (C_step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold C_step; rw [List.getD_append_right _ _ _ _ le_rfl]; simp

theorem C_run_pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (C_run w gs).getD i false = w.getD i false
  | [], w, i, _ => rfl
  | g :: gs, w, i, h => by
    have := C_run_pre gs (C_step w g) i (by simp [C_step]; omega)
    simp only [C_run, List.foldl_cons] at this ⊢
    rw [this, C_step_pre w g i h]

def C_RB (s : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < s + j

private def M_mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem inverter_flag (g : Gate) : M_mark g=true ↔ g.op=.not := by
  cases h : g.op <;> simp [M_mark,h]

def inverterCount (gs : List Gate) : Nat := (gs.filter M_mark).length

theorem inverterCount_cons (g : Gate) (gs : List Gate) :
    inverterCount (g::gs)=inverterCount gs+(if M_mark g then 1 else 0) := by
  cases eq : M_mark g <;> simp [inverterCount,List.filter_cons,eq]

theorem inverterCount_eq (C : Circuit) : inverterCount C.gates=notCount C := by
  unfold inverterCount notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases e : g.op <;> simp [M_mark,e]

def certLeaf (gs : List Gate) (n i : Nat) : Prop :=
  i<n ∨ ∃ j<gs.length, i=n+j ∧ (gs.getD j ⟨.or,[]⟩).op=.not

theorem leaf_lift (gs : List Gate) (g : Gate) (n i : Nat) (h : certLeaf gs n i) :
    certLeaf (gs++[g]) n i := by
  rcases h with first | ⟨j,hj,eq,inv⟩
  · exact Or.inl first
  · exact Or.inr ⟨j,by simp;omega,eq,by rwa [List.getD_append _ _ _ _ hj]⟩

theorem binary_clause (g : Gate) (wire : List Bool)
    (op : g.op=.and ∨ g.op=.or) (arity : g.inputs.length≤2)
    (trueGate : g.op.eval (g.inputs.map fun i => wire.getD i false)=true) :
    ∃ S : Finset Nat, (∀ i∈S, i∈g.inputs ∧ wire.getD i false=true) ∧ S.card≤2 ∧
      ∀ w : List Bool, (∀ i∈S, w.getD i false=true) →
        g.op.eval (g.inputs.map fun i => w.getD i false)=true := by
  rcases op with a | o
  · have all : ∀ i∈g.inputs, wire.getD i false=true := by
      simpa [a,GateOp.eval,List.all_eq_true] using trueGate
    refine ⟨g.inputs.toFinset,?_ ,(List.toFinset_card_le _).trans arity,?_⟩
    · intro i hi
      exact ⟨List.mem_toFinset.mp hi,all _ (List.mem_toFinset.mp hi)⟩
    · intro w valid
      simp only [a,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro bit i hi eq
      rw [←eq]
      exact valid _ (List.mem_toFinset.mpr hi)
  · have found : ∃ i∈g.inputs, wire.getD i false=true := by
      simpa [o,GateOp.eval,List.any_eq_true] using trueGate
    obtain ⟨i,hi,t⟩ := found
    refine ⟨{i},fun j hj => by obtain rfl := Finset.mem_singleton.mp hj; exact ⟨hi,t⟩,
      by simp,?_⟩
    intro w valid
    simp only [o,GateOp.eval,List.any_eq_true,List.mem_map]
    exact ⟨_,⟨i,hi,rfl⟩, valid i (Finset.mem_singleton_self _)⟩

theorem certificate {n : Nat} (base : List Bool) (len : base.length=n) (gs : List Gate)
    (back : C_RB n gs) (fan : FanInTwo (⟨gs,0⟩ : Circuit)) (A : Finset Nat)
    (live : ∀ i∈A, i<n+gs.length)
    (on : ∀ i∈A, (C_run base gs).getD i false=true) :
    ∃ S : Finset Nat, S.card≤A.card+(gs.length-inverterCount gs) ∧
      (∀ i∈S, i<n+gs.length ∧ (C_run base gs).getD i false=true ∧ certLeaf gs n i) ∧
      ∀ wire : List Bool, wire.length=n → (∀ i∈S, (C_run wire gs).getD i false=true) →
        ∀ i∈A, (C_run wire gs).getD i false=true := by
  classical
  induction gs using List.reverseRecOn generalizing A with
  | nil =>
    refine ⟨A,by simp [inverterCount],?_,fun w _ => id⟩
    intro i hi
    exact ⟨live i hi,on i hi,Or.inl (by simpa using live i hi)⟩
  | append_singleton gs g ih =>
    let endWire := n+gs.length
    let early := A.erase endWire
    have back0 : C_RB n gs := by
      intro j hj a ha
      apply back j (by simp;omega) a
      rwa [List.getD_append _ _ _ _ hj]
    have fan0 : FanInTwo (⟨gs,0⟩ : Circuit) :=
      fun u hu => fan u (List.mem_append.mpr (Or.inl hu))
    have read : ∀ i∈g.inputs, i<endWire := by
      intro i hi
      have h := back gs.length (by simp) i (by
        rw [List.getD_append_right _ _ _ _ le_rfl]
        simpa using hi)
      exact h
    have count (w : List Bool) (hw : w.length=n) : (C_run w gs).length=endWire := by
      simp [C_run_len,hw,endWire]
    have old (w : List Bool) (hw : w.length=n) (i : Nat) (hi : i<endWire) :
        (C_run w (gs++[g])).getD i false=(C_run w gs).getD i false := by
      rw [C_run_append,C_run_single,C_step_pre _ _ _ (by rwa [count w hw])]
    have last (w : List Bool) (hw : w.length=n) :
        (C_run w (gs++[g])).getD endWire false=
          g.op.eval (g.inputs.map fun i => (C_run w gs).getD i false) := by
      rw [C_run_append,C_run_single,←count w hw,C_step_last]
    have past (i : Nat) (hi : i∈A) (ne : i≠endWire) : i<endWire := by
      have hi := live i hi
      simp only [List.length_append,List.length_singleton] at hi
      dsimp [endWire] at ne ⊢
      omega
    have oldRequirements (i : Nat) (hi : i∈early) : i<endWire :=
      past i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1
    have oldOn (i : Nat) (hi : i∈early) : (C_run base gs).getD i false=true :=
      (old base len i (oldRequirements i hi)).symm.trans (on i (Finset.mem_erase.mp hi).2)
    have pSize : inverterCount gs≤gs.length := List.length_filter_le ..
    have pCount : inverterCount (gs++[g]) = inverterCount gs + (if M_mark g then 1 else 0) := by
      cases e : M_mark g <;> simp [inverterCount,List.filter_append,e]
    have pGrow : gs.length-inverterCount gs≤(gs++[g]).length-inverterCount (gs++[g]) := by
      rw [pCount,List.length_append,List.length_singleton]
      cases M_mark g <;> simp <;> omega
    by_cases need : endWire∈A
    · by_cases marked : M_mark g=true
      · obtain ⟨T,cost,desc,imp⟩ := ih back0 fan0 early oldRequirements oldOn
        have nc : endWire∉T := by
          intro h
          have imp := (desc _ h).1
          exact (Nat.lt_irrefl _) imp
        refine ⟨insert endWire T,?_,?_,?_⟩
        · rw [Finset.card_insert_of_notMem nc]
          have size : early.card+1=A.card := Finset.card_erase_add_one need
          omega
        · intro i hi
          rcases Finset.mem_insert.mp hi with equal | hi
          · subst i
            have marked' : g.op=.not := (inverter_flag g).mp marked
            exact ⟨live _ need,on _ need,Or.inr ⟨gs.length,by simp,rfl,by
              rw [List.getD_append_right _ _ _ _ le_rfl]
              simpa using marked'⟩⟩
          · obtain ⟨inRange,truth,leaf⟩ := desc i hi
            exact ⟨by simp; omega,(old base len i inRange).trans truth,leaf_lift gs g n i leaf⟩
        · intro w hw all i iA
          by_cases e : i=endWire
          · exact all i (Finset.mem_insert.mpr (Or.inl e))
          · have inEarly : i∈early := Finset.mem_erase.mpr ⟨e,iA⟩
            rw [old w hw i (oldRequirements i inEarly)]
            apply imp w hw ?_ i inEarly
            intro t ht
            rw [←old w hw t (desc t ht).1]
            exact all t (Finset.mem_insert_of_mem ht)
      · have shape : g.op=.and ∨ g.op=.or := by
          rcases (fan g (List.mem_append.mpr (Or.inr (by simp)))).1 with a | o | i
          · exact Or.inl a
          · exact Or.inr o
          · exact (marked ((inverter_flag g).mpr i)).elim
        have arity := (fan g (List.mem_append.mpr (Or.inr (by simp)))).2
        have truth := (last base len).symm.trans (on _ need)
        obtain ⟨B,baseB,cardB,imply⟩ := binary_clause g (C_run base gs) shape arity truth
        let prior := early∪B
        have valid (i : Nat) (hi : i∈prior) : i<endWire ∧ (C_run base gs).getD i false=true := by
          rcases Finset.mem_union.mp hi with e | p
          · exact ⟨oldRequirements i e,oldOn i e⟩
          · exact ⟨read i (baseB i p).1,(baseB i p).2⟩
        obtain ⟨T,cost,desc,imp⟩ := ih back0 fan0 prior (fun i hi => (valid i hi).1)
          (fun i hi => (valid i hi).2)
        refine ⟨T,?_ ,?_,?_⟩
        · have cmp := Finset.card_union_le early B
          have size : early.card+1=A.card := Finset.card_erase_add_one need
          rw [pCount,List.length_append,List.length_singleton]
          have flag : M_mark g=false := by cases h : M_mark g; rfl; exact (marked h).elim
          simp only [flag,Bool.false_eq_true,ite_false,Nat.add_zero]
          change prior.card≤early.card+B.card at cmp
          omega
        · intro i hi
          obtain ⟨inRange,truth,leaf⟩ := desc i hi
          exact ⟨by simp; omega,(old base len i inRange).trans truth,leaf_lift gs g n i leaf⟩
        · intro w hw all i iA
          have propagates (j : Nat) (hj : j∈prior) : (C_run w gs).getD j false=true := by
            apply imp w hw ?_ j hj
            intro t ht
            rw [←old w hw t (desc t ht).1]
            exact all t ht
          by_cases e : i=endWire
          · subst i
            rw [last w hw]
            exact imply _ (fun u hu => propagates u (Finset.mem_union_right _ hu))
          · rw [old w hw i (past i iA e)]
            exact propagates i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,iA⟩))
    · have earlyLive (i : Nat) (hi : i∈A) : i<endWire :=
        past i hi (fun same => need (same ▸ hi))
      obtain ⟨T,cost,desc,imp⟩ := ih back0 fan0 A earlyLive (fun i hi =>
        (old base len i (earlyLive i hi)).symm.trans (on i hi))
      refine ⟨T,cost.trans (Nat.add_le_add_left pGrow _),?_,?_⟩
      · intro i hi
        obtain ⟨inRange,truth,leaf⟩ := desc i hi
        exact ⟨by simp; omega,(old base len i inRange).trans truth,leaf_lift gs g n i leaf⟩
      · intro w hw hits i hi
        rw [old w hw i (earlyLive i hi)]
        apply imp w hw ?_ i hi
        intro t ht
        rw [←old w hw t (desc _ ht).1]
        exact hits _ ht

theorem minimum_from (xs : List Nat) (start : Nat) :
    xs.foldl min start=start ∨ xs.foldl min start∈xs := by
  induction xs generalizing start with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    change xs.foldl min (min start x)=start ∨ xs.foldl min (min start x)∈x::xs
    rcases ih (min start x) with h | h
    · by_cases le : start≤x
      · exact Or.inl (h.trans (min_eq_left le))
      · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans (min_eq_right (Nat.le_of_not_ge le)))))
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem minimum_le (xs : List Nat) (start : Nat) :
    xs.foldl min start≤start ∧ ∀ x∈xs, xs.foldl min start≤x := by
  induction xs generalizing start with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨left,right⟩ := ih (min start y)
    refine ⟨left.trans (min_le_left _ _),?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact left.trans (min_le_right _ _)
    · exact right x hx

noncomputable def coverColumn {r d : Nat} (S : Fin d → Finset (Fin r)) (j : Fin d) (z : Option (Fin r)) : Bool :=
  z.elim false (fun e => @decide (e∈S j) (Classical.propDecidable _))

def flipColumn {r : Nat} (u : Option (Fin r) → Bool) (z : Option (Fin r)) : Bool := !u z

noncomputable def feeLine {r d : Nat} (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat) (W : Nat)
    (f : Option (Fin r) → Bool) (j : Fin d) : Nat :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if f=coverColumn S j ∨ f=flipColumn (coverColumn S j) then cost j else W+1

noncomputable def priced {r d : Nat} (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat) (W : Nat)
    (f : Option (Fin r) → Bool) : Nat :=
  (List.ofFn (feeLine S cost W f)).foldl min (W+1)

theorem priced_origin {r d : Nat} (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat) (W : Nat)
    (f : Option (Fin r) → Bool) (small : priced S cost W f≤W) :
    ∃ j, priced S cost W f=cost j ∧ (f=coverColumn S j ∨ f=flipColumn (coverColumn S j)) := by
  rcases minimum_from (List.ofFn (feeLine S cost W f)) (W+1) with deflt | list
  · have eq : priced S cost W f=W+1 := deflt
    omega
  · obtain ⟨j,ex⟩ := List.mem_ofFn.mp list
    have eq : feeLine S cost W f j=priced S cost W f := ex
    by_cases eqColumn : f=coverColumn S j ∨ f=flipColumn (coverColumn S j)
    · exact ⟨j,eq.symm.trans (by simp [feeLine,eqColumn]),eqColumn⟩
    · have impossible : priced S cost W f=W+1 :=
        eq.symm.trans (by simp [feeLine,eqColumn])
      omega

theorem priced_le {r d : Nat} (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat) (W : Nat) (j : Fin d) :
    priced S cost W (flipColumn (coverColumn S j))≤cost j := by
  have row : feeLine S cost W (flipColumn (coverColumn S j)) j=cost j := by simp [feeLine]
  exact ((minimum_le _ _).2 _ (List.mem_ofFn.mpr ⟨j,rfl⟩)).trans_eq row

noncomputable def incidInput {r d : Nat} (S : Fin d → Finset (Fin r)) (z : Option (Fin r)) :=
  List.ofFn (fun j => coverColumn S j z)++[false,true]

theorem incid_len {r d : Nat} (S : Fin d → Finset (Fin r)) (z : Option (Fin r)) :
    (incidInput S z).length=d+2 := by simp [incidInput]

theorem incid_at {r d : Nat} (S : Fin d → Finset (Fin r)) (z : Option (Fin r)) (j : Fin d) :
    (incidInput S z).getD j.val false=coverColumn S j z := by
  unfold incidInput
  rw [List.getD_append _ _ _ _ (by simpa using j.isLt)]
  simp [List.getD_eq_getElem?_getD,j.isLt]

theorem incid_const_true {r d : Nat} (S : Fin d → Finset (Fin r)) (z : Option (Fin r)) :
    (incidInput S z).getD (d+1) false=true := by
  unfold incidInput
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem incid_const_false {r d : Nat} (S : Fin d → Finset (Fin r)) (z : Option (Fin r)) :
    (incidInput S z).getD d false=false := by
  unfold incidInput
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

noncomputable def gatePrice {r d : Nat} (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat)
    (W : Nat) (C : Circuit) (i : Fin C.size) : Nat :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if (C.gates.get i).op=.not then priced S cost W (fun z => value C (incidInput S z) (d+2+i.val)) else 0

theorem index_count (gs : List Gate) :
    ((Finset.univ : Finset (Fin gs.length)).filter (fun i => M_mark (gs.get i)=true)).card =
      inverterCount gs := by
  induction gs with
  | nil => simp [inverterCount]
  | cons g gs ih =>
    rw [Finset.card_filter]
    change (∑ i : Fin (gs.length+1), if M_mark ((g::gs).get i)=true then (1 : Nat) else 0)=_
    rw [Finset.card_filter] at ih
    rw [Fin.sum_univ_succ,inverterCount_cons,←ih]
    simp only [List.get_eq_getElem,Fin.val_zero,Fin.val_succ,List.getElem_cons_zero,List.getElem_cons_succ,
      Nat.add_comm] <;> rfl

theorem true_input_pin {r d : Nat} (S : Fin d → Finset (Fin r)) (i : Nat)
    (hi : i<d+2) (on : (incidInput S none).getD i false=true) :
    ∀ z, (incidInput S z).getD i false=true := by
  by_cases early : i<d
  · have h := incid_at S none ⟨i,early⟩
    simp only [Fin.val_mk,coverColumn,Option.elim] at h
    rw [h] at on
    cases on
  · by_cases atFalse : i=d
    · rw [atFalse,incid_const_false] at on
      cases on
    · have h : i=d+1 := by omega
      intro z
      rw [h,incid_const_true]

theorem extract_cover {r d p b g W : Nat} (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat)
    (C : Circuit) (fan : FanInTwo C) (back : ReadsBack (d+2) C) (live : C.output<d+2+C.size)
    (eval : ∀ z, C.eval (incidInput S z)=z.isNone)
    (ao : C.size-notCount C≤p) (neg : notCount C≤b) (gates : C.size≤g)
    (money : (Finset.univ : Finset (Fin C.size)).sum (gatePrice S cost W C)≤W) :
    ∃ J : Finset (Fin d), (∀ e : Fin r, ∃ j∈J, e∈S j) ∧
      J.card-1≤p ∧ J.card≤b ∧ J.card+(J.card-1)≤g ∧ J.sum cost≤W := by
  classical
  obtain ⟨leaves,sz,leaf,forces⟩ := certificate (incidInput S none) (incid_len S none) C.gates back fan
    ({C.output} : Finset Nat) (fun i hi => (Finset.mem_singleton.mp hi).symm ▸ live)
    (fun i hi => (Finset.mem_singleton.mp hi).symm ▸ eval none)
  let F := (Finset.univ : Finset (Fin C.size)).filter (fun j => d+2+j.val∈leaves)
  have pick_not (j : Fin C.size) (hj : j∈F) : (C.gates.get j).op=.not := by
    have atLeaf := (leaf _ (Finset.mem_filter.mp hj).2).2.2
    rcases atLeaf with h | ⟨m,hm,link,op⟩
    · omega
    · have eq : m=j.val := by omega
      rw [eq] at op
      rwa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem j.isLt] at op
  have sizeF : F.card≤leaves.card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin C.size => d+2+j.val)
    · exact fun j hj => (Finset.mem_filter.mp hj).2
    · intro i _ j _ h
      apply Fin.ext
      exact Nat.add_left_cancel h
  have negF : F.card≤notCount C := by
    rw [←inverterCount_eq C,←index_count]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(inverter_flag _).mpr (pick_not i hi)⟩
  let read (i : Fin C.size) (z : Option (Fin r)) := value C (incidInput S z) (d+2+i.val)
  have pick (i : F) : ∃ j, cost j=gatePrice S cost W C i.val ∧
      read i.val=flipColumn (coverColumn S j) := by
    have fin := (Finset.single_le_sum (fun j _ => Nat.zero_le (gatePrice S cost W C j))
      (Finset.mem_univ i.val)).trans money
    rw [gatePrice,ite_eq_left (pick_not i.val i.property)] at fin
    change priced S cost W (read i.val)≤W at fin
    obtain ⟨j,eq,loc⟩ := priced_origin S cost W (read i.val) fin
    refine ⟨j,?_ ,?_⟩
    · rw [gatePrice,ite_eq_left (pick_not i.val i.property)]
      exact eq.symm
    · refine loc.resolve_left ?_
      intro bad
      have known : read i.val none=true := (leaf _ (Finset.mem_filter.mp i.property).2).2.1
      rw [bad] at known
      simp [coverColumn] at known
  let col (i : F) := Classical.choose (pick i)
  let J := F.attach.image col
  have cardJ : J.card≤F.card := by
    calc
      J.card≤F.attach.card := Finset.card_image_le
      _ = F.card := Finset.card_attach
  have moneyJ : J.sum cost≤W := by
    calc
      J.sum cost ≤ F.attach.sum (fun i => cost (col i)) :=
        Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
      _ = F.attach.sum (fun i => gatePrice S cost W C i.val) :=
        Finset.sum_congr rfl (fun i _ => (Classical.choose_spec (pick i)).1)
      _ = F.sum (gatePrice S cost W C) := Finset.sum_attach F _
      _ ≤ _ := (Finset.sum_le_sum_of_subset (Finset.subset_univ F)).trans money
  have enough : ∀ e : Fin r, ∃ j∈J, e∈S j := by
    intro e
    by_contra! no
    have read_all (i : Nat) (hi : i∈leaves) : (C_run (incidInput S (some e)) C.gates).getD i false=true := by
      obtain ⟨_,onBase,tail⟩ := leaf i hi
      rcases tail with isInput | ⟨j,jC,eq,_⟩
      · rw [C_run_pre _ _ _ (by simpa [incid_len] using isInput)]
        rw [C_run_pre _ _ _ (by simpa [incid_len] using isInput)] at onBase
        exact true_input_pin S i isInput onBase _
      · let t : Fin C.size := ⟨j,jC⟩
        have hF : t∈F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq ▸ hi⟩
        let tagged : F := ⟨t,hF⟩
        have jJ : col tagged∈J := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
        have data := (Classical.choose_spec (pick tagged)).2
        have correct : read t (some e)=true := by
          change read tagged.val (some e)=true
          change read tagged.val=flipColumn (coverColumn S (col tagged)) at data
          rw [data]
          simpa [flipColumn,coverColumn] using no (col tagged) jJ
        rwa [eq]
    have yes : C.eval (incidInput S (some e))=true :=
      forces _ (incid_len S _) read_all _ (Finset.mem_singleton_self _)
    rw [eval] at yes
    cases yes
  simp only [Finset.card_singleton] at sz
  have bound : J.card-1≤C.size-notCount C := by
    have length : C.gates.length=C.size := rfl
    rw [inverterCount_eq,length] at sz
    omega
  have use : J.card≤notCount C := cardJ.trans negF
  refine ⟨J,enough,bound.trans ao,use.trans neg,?_,moneyJ⟩
  have sizeN : notCount C≤C.size := List.length_filter_le ..
  omega

theorem collect_and {X : Type*} {n : Nat} (input : X → List Bool) (len : ∀ x, (input x).length=n)
    (ws : List Nat) : ∀ (C : Circuit) (a : Nat), Good (fun _=>True) n C →
      Live (fun _=>True) n C a → (∀ i∈ws, Live (fun _=>True) n C i) →
      ∃ D o, Good (fun _=>True) n D ∧ C.gates <+: D.gates ∧ Live (fun _=>True) n D o ∧
        D.size=C.size+ws.length ∧ notCount D=notCount C ∧
        ∀ x, value D (input x) o=(value C (input x) a && ws.all (value C (input x))) := by
  induction ws with
  | nil => intro C a good ha _; exact ⟨C,a,good,List.prefix_refl _,ha,by simp,rfl,by simp⟩
  | cons w ws ih =>
    intro C a good ha hw
    obtain ⟨A,b,ag,ca,bl,sa,na,sp⟩ := emit_binary input len (fun _ _ => trivial) good true ha
      (hw w (List.mem_cons_self ..))
    obtain ⟨D,out,dg,ad,ol,sd,nd,dp⟩ := ih A b ag bl (fun i im => live_extend ca
      (hw i (List.mem_cons_of_mem _ im)))
    have tails (x : X) : ws.all (value A (input x))=ws.all (value C (input x)) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      exact forall₂_congr (fun i hi => by rw [old_value ca (len x) (hw i (List.mem_cons_of_mem _ hi)).1])
    refine ⟨D,out,dg,ca.trans ad,ol,by simp [sd,sa];omega,nd.trans na,?_⟩
    intro x
    rw [dp,sp,tails]
    simp [binaryValue,Bool.and_assoc]

theorem realize_cover {r d p b g W : Nat} (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat)
    (J : Finset (Fin d)) (covers : ∀ e : Fin r, ∃ j∈J, e∈S j)
    (pos : J.card-1≤p) (neg : J.card≤b) (size : J.card+(J.card-1)≤g) (levies : J.sum cost≤W) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (d+2) C ∧ C.output<d+2+C.size ∧
      (∀ z, C.eval (incidInput S z)=z.isNone) ∧ C.size-notCount C≤p ∧ notCount C≤b ∧ C.size≤g ∧
      (Finset.univ : Finset (Fin C.size)).sum (gatePrice S cost W C)≤W := by
  classical
  by_cases empty : J=∅
  · let C := withOutput emptyCircuit (d+1)
    refine ⟨C,emptyCircuit_fanInTwo,emptyCircuit_readsBack _,by simp [C,withOutput,emptyCircuit,Circuit.size],
      ?_,by simp [C,withOutput,emptyCircuit,Circuit.size,notCount],
      by simp [C,withOutput,emptyCircuit,notCount],by simp [C,withOutput,emptyCircuit,Circuit.size],?_⟩
    · intro z
      cases z with
      | none => exact incid_const_true S none
      | some e =>
          obtain ⟨j,h,_⟩ := covers e
          rw [empty] at h
          exact (Finset.notMem_empty _ h).elim
    · change (∑ i : Fin 0, gatePrice S cost W C i)≤W
      exact (Finset.sum_eq_zero (fun i _ => Fin.elim0 i)).le.trans (Nat.zero_le _)
  · let k := J.card
    have kpos : 0<k := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    let ord := J.orderIsoOfFin (rfl : J.card=k)
    let col (j : Fin k) := (ord j).val
    have col_inj : Function.Injective col := fun i j eq => ord.injective (Subtype.ext eq)
    have col_all : Finset.univ.image col=J := by
      ext j
      constructor
      · intro h
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
        exact (ord i).property
      · intro h
        exact Finset.mem_image.mpr ⟨ord.symm ⟨j,h⟩,Finset.mem_univ _,
          congrArg Subtype.val (ord.apply_symm_apply ⟨j,h⟩)⟩
    let Z := incidInput S
    let base := d+2
    let bank (i : Fin k) : Gate := ⟨.not,[(col i).val]⟩
    let C := appendFamily emptyCircuit bank
    have csize : C.size=k := by
      have eq := appendFamily_size emptyCircuit bank
      change C.size=0+k at eq
      exact eq.trans (Nat.zero_add _)
    have cgate : C.gates=List.ofFn bank := rfl
    have cneg : notCount C=k := by
      rw [←inverterCount_eq C,cgate]
      unfold inverterCount
      have all : (List.ofFn bank).filter M_mark=List.ofFn bank := by
        apply List.filter_eq_self.mpr
        intro g hg
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
        simp [bank,M_mark]
      rw [all,List.length_ofFn]
    have shape (i : Fin k) : GateShape (bank i) := by simp [bank,GateShape]
    have used (i : Fin k) (u : Nat) (hu : u∈(bank i).inputs) :
        Live (fun _=>True) base emptyCircuit u := by
      have same : u=(col i).val := by simpa [bank] using hu
      rw [same]
      have h := (col i).isLt
      exact ⟨by simp [nextWire,emptyCircuit,Circuit.size,base];omega,trivial⟩
    have pre : Good (fun _=>True) base emptyCircuit :=
      ⟨emptyCircuit_fanInTwo,emptyCircuit_readsBack _,by simp [emptyCircuit]⟩
    have cgood : Good (fun _=>True) base C := family_good pre shape used
    have valid (i : Fin k) : Live (fun _=>True) base C (base+i.val) := by
      simpa [C,nextWire,emptyCircuit,Circuit.size] using
        (live_new (C := emptyCircuit) bank (fun _ _ => trivial) i : Live (fun _=>True) base C _)
    have sem (z : Option (Fin r)) (i : Fin k) :
        value C (Z z) (base+i.val)=flipColumn (coverColumn S (col i)) z := by
      have x := family_value (gate := bank) (C := emptyCircuit) (n := base)
        (fun j u hu => (used j u hu).1) (Z z) (incid_len S z) i
      simp only [bank,GateOp.eval,List.map_cons,List.map_nil,List.headD_cons] at x
      have bounds : (col i).val<(Z z).length := by change _<(incidInput S z).length; rw [incid_len]; have := (col i).isLt;omega
      rw [value_input emptyCircuit (Z z) bounds] at x
      change value C (Z z) (base+i.val) = !(incidInput S z).getD (col i).val false at x
      rwa [incid_at] at x
    let rest := (List.finRange (k-1)).map (fun j => base+j.val+1)
    have restLive (i : Nat) (h : i∈rest) : Live (fun _=>True) base C i := by
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
      have lo : j.val+1<k := by have := j.isLt;omega
      simpa [Nat.add_assoc] using valid ⟨j.val+1,lo⟩
    let first : Fin k := ⟨0,kpos⟩
    obtain ⟨D,out,dgood,extension,dl,ds,dn,finish⟩ :=
      collect_and Z (incid_len S) rest C (base+first.val) cgood (valid first) restLive
    let R := withOutput D out
    have rsize : R.size=k+(k-1) := by
      change D.size=_
      rw [ds,csize]
      simp [rest]
    have rneg : notCount R=k := dn.trans cneg
    have newLive : k≤R.size := rsize ▸ Nat.le_add_right _ _
    let embed (i : Fin k) : Fin R.size := ⟨i.val,i.isLt.trans_le newLive⟩
    let oldg := Finset.univ.image embed
    have embed_inj : Function.Injective embed := fun i j eq =>
      Fin.ext (congrArg (fun t : Fin R.size => t.val) eq)
    have index_op (i : Fin k) : (R.gates.get (embed i)).op=.not := by
      obtain ⟨extra,e⟩ := extension
      have link : (D.gates.getD i.val ⟨.or, []⟩).op=.not := by
        rw [←e,List.getD_append _ _ _ _ (by rw [cgate,List.length_ofFn]; exact i.isLt),cgate]
        simp [List.getD_eq_getElem?_getD,i.isLt,bank]
      have bound : i.val<D.gates.length := (embed i).isLt
      rwa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound] at link
    have no_else (i : Fin R.size) (hi : i∉oldg) : (R.gates.get i).op≠.not := by
      let all := (Finset.univ : Finset (Fin R.size)).filter (fun i => M_mark (R.gates.get i)=true)
      have eq : all.card=k := (index_count R.gates).trans ((inverterCount_eq R).trans rneg)
      have subset : oldg⊆all := by
        intro x hx
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(inverter_flag _).mpr (index_op i)⟩
      have card : oldg.card=k := by
        rw [Finset.card_image_of_injective _ embed_inj]
        simp
      have eq := Finset.eq_of_subset_of_card_le subset (eq.trans card.symm).le
      intro inv
      exact hi (eq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,(inverter_flag _).mpr inv⟩)
    have priced_i (i : Fin k) : gatePrice S cost W R (embed i)≤cost (col i) := by
      rw [gatePrice,ite_eq_left (index_op i)]
      have rewrite : (fun z => value R (incidInput S z) (d+2+(embed i).val)) =
          flipColumn (coverColumn S (col i)) := by
        funext z
        change value D (Z z) (base+i.val)=_
        rw [old_value extension (incid_len S z) (valid i).1]
        exact sem z i
      rw [rewrite]
      exact priced_le S cost W _
    have total : ∑ i : Fin R.size, gatePrice S cost W R i ≤ W := by
      have support : oldg.sum (gatePrice S cost W R)=∑ i : Fin R.size, gatePrice S cost W R i := by
        apply Finset.sum_subset (Finset.subset_univ oldg)
        intro i _ missing
        simp [gatePrice,no_else i missing]
      rw [←support,Finset.sum_image (fun a _ b _ h => embed_inj h)]
      apply (Finset.sum_le_sum (fun i _ => priced_i i)).trans
      rw [←Finset.sum_image (fun a _ b _ h => col_inj h),col_all]
      exact levies
    refine ⟨R,dgood.1,dgood.2.1,dl.1,?_ ,?_ ,?_ ,?_ ,total⟩
    · intro z
      change value D (Z z) out=z.isNone
      rw [finish,sem]
      cases z with
      | none =>
        simp only [Option.isNone,flipColumn,coverColumn,Option.elim,Bool.not_false,Bool.true_and,List.all_eq_true]
        intro t ht
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
        have v : j.val+1<k := by have := j.isLt;omega
        simpa [Nat.add_assoc,flipColumn,coverColumn] using sem none ⟨j.val+1,v⟩
      | some e =>
        obtain ⟨j,inJ,hit⟩ := covers e
        let i := ord.symm ⟨j,inJ⟩
        have ij : col i=j := congrArg Subtype.val (ord.apply_symm_apply ⟨j,inJ⟩)
        have reject : flipColumn (coverColumn S (col i)) (some e)=false := by
          simp [ij,flipColumn,coverColumn,hit]
        by_cases atHead : i.val=0
        · have i0 : i=first := Fin.ext atHead
          rw [i0] at reject
          simp [reject]
        · let index : Fin (k-1) := ⟨i.val-1,by have := i.isLt;omega⟩
          have mem : base+i.val∈rest := by
            apply List.mem_map.mpr
            refine ⟨index,by simp,?_⟩
            dsimp [index]
            omega
          have rejectWire : value C (Z (some e)) (base+i.val)=false := (sem (some e) i).trans reject
          have gone : rest.all (value C (Z (some e)))=false := by
            cases allTrue : rest.all (value C (Z (some e)))
            · rfl
            · have all : ∀ t∈rest, value C (Z (some e)) t=true := by simpa only [List.all_eq_true] using allTrue
              exact (Bool.false_ne_true (rejectWire.symm.trans (all _ mem))).elim
          simp [gone]
    · rw [rsize,rneg]
      omega
    · rw [rneg]
      exact neg
    · rw [rsize]
      exact size

end PEqualNP.Outside.L_meta_53184_aux

open PEqualNP.Outside.L_meta_53184_aux PEqualNP.CircuitLowerBounds PEqualNP.NotBracket

theorem PEqualNP.Outside.L_meta_53184 :
  ∀ (r d p b g W : Nat) (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat),
    letI : ∀ q : Prop, Decidable q := Classical.propDecidable
    let F := Option (Fin r) → Bool
    let col := fun (j : Fin d) (z : Option (Fin r)) => z.elim false (fun e => decide (e ∈ S j))
    let inv := fun (f : F) (z : Option (Fin r)) => !(f z)
    let toll := fun (f : F) => (List.ofFn (fun j =>
      if f = col j ∨ f = inv (col j) then cost j else W+1)).foldl min (W+1)
    let inputs := fun z => List.ofFn (fun j => col j z) ++ [false,true]
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      let wire := fun (n : Nat) (z : Option (Fin r)) => (C.wires (inputs z)).getD n false
      let neg := PEqualNP.NotBracket.notCount C
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
      C.output < d+2+C.size ∧ (∀ z, wire C.output z = z.isNone) ∧
      C.size-neg ≤ p ∧ neg ≤ b ∧ C.size ≤ g ∧
      (Finset.univ : Finset (Fin C.size)).sum (fun i =>
        if (C.gates.get i).op = .not then toll (wire (d+2+i.val)) else 0) ≤ W) ↔
    ∃ J : Finset (Fin d), (∀ e : Fin r, ∃ j ∈ J, e ∈ S j) ∧
      J.card-1 ≤ p ∧ J.card ≤ b ∧ J.card+(J.card-1) ≤ g ∧ J.sum cost ≤ W := by
  classical
  intro r d p b g W S cost F col inv toll inputs
  constructor
  · rintro ⟨C,fan,back,live,eval,ao,neg,size,money⟩
    exact extract_cover S cost C fan back live eval ao neg size money
  · rintro ⟨J,covers,pos,neg,size,money⟩
    exact realize_cover S cost J covers pos neg size money
