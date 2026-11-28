import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53194_aux

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

open PEqualNP.MetaComplexity

theorem monotone2_of_no_not {C : Circuit} (fan : FanInTwo C) (zero : notCount C=0) :
    Monotone2 C := by
  intro g hg
  have facts := fan g hg
  have absent : g.op ≠ .not := by
    intro bad
    have mem : g ∈ C.gates.filter (fun p => @decide (p.op = GateOp.not) (lineDegreeGateOpDecEq _ _)) :=
      List.mem_filter.mpr ⟨hg,by change @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _) = true; exact @decide_eq_true _ (lineDegreeGateOpDecEq _ _) bad⟩
    rw [notCount,List.length_eq_zero_iff] at zero
    rw [zero] at mem
    exact List.not_mem_nil mem
  have allowed : g.op=.and ∨ g.op=.or := by
    have ops : g.op=.and ∨ g.op=.or ∨ g.op=.not := by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using facts.1
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (absent h).elim
  exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using allowed,facts.2⟩



noncomputable def incidence {n : Nat} (s : Finset (Fin n)) (j : Fin n) : Bool :=
  @decide (j∈s) (Classical.propDecidable _)

theorem incidence_true {n : Nat} {s : Finset (Fin n)} {j : Fin n} :
    incidence s j=true ↔ j∈s := by simp [incidence]

theorem incidence_le {n : Nat} {s t : Finset (Fin n)} :
    incidence s ≤ incidence t ↔ s⊆t := by
  constructor
  · intro h j hj
    have h' := h j
    change incidence s j ≤ incidence t j at h'
    rw [incidence_true.mpr hj] at h'
    cases e : incidence t j
    · exact ((by decide : ¬ true ≤ false) (e ▸ h')).elim
    · exact incidence_true.mp e
  · intro h j
    change incidence s j ≤ incidence t j
    cases e : incidence s j
    · simp
    · rw [incidence_true.mpr (h (incidence_true.mp e))]



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



def evalDNF (words : List (List Nat)) (value : Nat → Bool) : Bool :=
  words.any (fun line => line.all value)

theorem evalDNF_congr (terms : List (List Nat)) {f g : Nat → Bool}
    (same : ∀ w∈terms, ∀ i∈w, f i=g i) : evalDNF terms f=evalDNF terms g := by
  rw [Bool.eq_iff_iff]
  simp only [evalDNF,List.any_eq_true,List.all_eq_true]
  constructor <;> rintro ⟨w,hw,on⟩ <;> refine ⟨w,hw,?_⟩
  · intro i hi
    rw [←same w hw i hi]
    exact on i hi
  · intro i hi
    rw [same w hw i hi]
    exact on i hi

theorem compile_dnf_one {X : Type*} {n : Nat} (input : X → List Bool)
    (len : ∀ x, (input x).length=n) (one zero : Nat) :
    ∀ (terms : List (List Nat)) (C : Circuit), Good (fun _=>True) n C →
      Live (fun _=>True) n C one → Live (fun _=>True) n C zero →
      (∀ x, value C (input x) one=true ∧ value C (input x) zero=false) →
      (∀ w∈terms, ∀ i∈w, Live (fun _=>True) n C i) →
      ∃ D out, Good (fun _=>True) n D ∧ C.gates <+: D.gates ∧ Live (fun _=>True) n D out ∧
        notCount D=notCount C ∧ ∀ x, value D (input x) out=evalDNF terms (value C (input x)) := by
  intro terms
  induction terms with
  | nil =>
    intro C gc on off const _
    exact ⟨C,zero,gc,List.prefix_refl _,off,rfl,fun x => (const x).2⟩
  | cons w ws ih =>
    intro C gc on off const valid
    have validW : ∀ i∈w, Live (fun _=>True) n C i := valid w (List.mem_cons_self ..)
    obtain ⟨A,outA,ga,ca,la,_,na,semA⟩ := collect_and input len w C one gc on validW
    have constA (x : X) : value A (input x) one=true ∧ value A (input x) zero=false :=
      ⟨(old_value ca (len x) on.1).trans (const x).1,
        (old_value ca (len x) off.1).trans (const x).2⟩
    obtain ⟨B,outB,gb,ab,lb,nb,semB⟩ := ih A ga (live_extend ca on) (live_extend ca off) constA
      (fun v hv i hi => live_extend ca (valid v (List.mem_cons_of_mem _ hv) i hi))
    obtain ⟨D,out,gd,bd,ld,_,nd,semD⟩ :=
      emit_binary input len (fun _ _ => trivial) gb false (live_extend ab la) lb
    refine ⟨D,out,gd,ca.trans (ab.trans bd),ld,nd.trans (nb.trans na),?_⟩
    intro x
    have tail : evalDNF ws (value A (input x))=evalDNF ws (value C (input x)) :=
      evalDNF_congr ws (fun v hv i hi => old_value ca (len x) (valid v (List.mem_cons_of_mem _ hv) i hi).1)
    rw [semD,old_value ab (len x) la.1,semA,semB,tail,(const x).1]
    rfl

theorem compile_dnf_many {X : Type*} {n : Nat} (input : X → List Bool)
    (len : ∀ x, (input x).length=n) (one zero : Nat) :
    ∀ (a : Nat) (terms : Fin a → List (List Nat)) (C : Circuit), Good (fun _=>True) n C →
      Live (fun _=>True) n C one → Live (fun _=>True) n C zero →
      (∀ x, value C (input x) one=true ∧ value C (input x) zero=false) →
      (∀ j w, w∈terms j → ∀ i∈w, Live (fun _=>True) n C i) →
      ∃ D, ∃ out : Fin a → Nat, Good (fun _=>True) n D ∧ C.gates <+: D.gates ∧
        (∀ j, Live (fun _=>True) n D (out j)) ∧ notCount D=notCount C ∧
        ∀ x j, value D (input x) (out j)=evalDNF (terms j) (value C (input x)) := by
  intro a
  induction a with
  | zero =>
    intro terms C gc on off const valid
    exact ⟨C,Fin.elim0,gc,List.prefix_refl _,fun i => Fin.elim0 i,rfl,fun _ i => Fin.elim0 i⟩
  | succ a ih =>
    intro terms C gc on off const valid
    obtain ⟨A,head,ga,ca,la,na,semA⟩ :=
      compile_dnf_one input len one zero (terms 0) C gc on off const (valid 0)
    have constA (x : X) : value A (input x) one=true ∧ value A (input x) zero=false :=
      ⟨(old_value ca (len x) on.1).trans (const x).1,
        (old_value ca (len x) off.1).trans (const x).2⟩
    obtain ⟨B,rest,gb,ab,lb,nb,semB⟩ := ih (fun i => terms i.succ) A ga
      (live_extend ca on) (live_extend ca off) constA
      (fun j w hw i hi => live_extend ca (valid j.succ w hw i hi))
    refine ⟨B,Fin.cases head rest,gb,ca.trans ab,?_,nb.trans na,?_⟩
    · exact fun j => Fin.cases (live_extend ab la) lb j
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value B (input x) head=_
        rw [old_value ab (len x) la.1]
        exact semA x
      · change value B (input x) (rest j)=_
        rw [semB]
        exact evalDNF_congr _ (fun w hw i hi => old_value ca (len x) (valid j.succ w hw i hi).1)



theorem fit_input_list {X : Type*} [Fintype X] {n a : Nat} (input : X → List Bool)
    (len : ∀ x, (input x).length=n)
    (one zero : Nat) (one_lt : one<n) (zero_lt : zero<n)
    (bits : X → Fin n → Bool) (output : X → Fin a → Bool)
    (read : ∀ x i, (input x).getD i.val false=bits x i)
    (constants : ∀ x, (input x).getD one false=true ∧ (input x).getD zero false=false)
    (mono : ∀ x y, bits x≤bits y → output x≤output y) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack n C ∧ C.output<n+C.size ∧ notCount C=0 ∧
      ∃ tap : Fin a → Nat, (∀ j, tap j<n+C.size) ∧
        ∀ x j, value C (input x) (tap j)=output x j := by
  classical
  let pos (v : X) := ((Finset.univ : Finset (Fin n)).filter (fun j => bits v j=true)).toList.map Fin.val
  let terms (j : Fin a) := ((Finset.univ : Finset X).filter (fun x => output x j=true)).toList.map pos
  have pre : Good (fun _=>True) n emptyCircuit :=
    ⟨emptyCircuit_fanInTwo,emptyCircuit_readsBack _,by simp [emptyCircuit]⟩
  have on : Live (fun _=>True) n emptyCircuit one := ⟨by simpa [nextWire,emptyCircuit,Circuit.size] using one_lt,trivial⟩
  have off : Live (fun _=>True) n emptyCircuit zero := ⟨by simpa [nextWire,emptyCircuit,Circuit.size] using zero_lt,trivial⟩
  have v (x : X) (i : Fin n) : value emptyCircuit (input x) i.val=bits x i := by
    rw [value_input _ _ (by simpa [len] using i.isLt),read]
  have pos_cons (x y : X) :
      (∀ i∈pos x, value emptyCircuit (input y) i=true) ↔ bits x≤bits y := by
    constructor
    · intro ha i
      cases h : bits x i
      · simp
      · have index : i.val∈pos x := List.mem_map.mpr ⟨i,Finset.mem_toList.mpr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩),rfl⟩
        have b := (v y i).symm.trans (ha _ index)
        simp [b]
    · intro ha i hi
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
      have tj := (Finset.mem_filter.mp (Finset.mem_toList.mp hj)).2
      have bt : bits y j=true := by
        have c := ha j
        rw [tj] at c
        cases e : bits y j
        · exact ((by decide : ¬ true ≤ false) (e ▸ c)).elim
        · rfl
      rw [v,bt]
  have semantics (x : X) (j : Fin a) :
      evalDNF (terms j) (value emptyCircuit (input x))=true ↔ output x j=true := by
    simp only [evalDNF,List.any_eq_true,List.all_eq_true]
    constructor
    · rintro ⟨w,hw,run⟩
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
      have declared := (Finset.mem_filter.mp (Finset.mem_toList.mp hy)).2
      have comp := mono y x ((pos_cons y x).mp run) j
      rw [declared] at comp
      cases e : output x j
      · exact ((by decide : ¬ true ≤ false) (e ▸ comp)).elim
      · rfl
    · intro declared
      exact ⟨pos x,List.mem_map.mpr ⟨x,Finset.mem_toList.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,declared⟩),rfl⟩,(pos_cons x x).mpr (le_refl _)⟩
  have reads (j : Fin a) (w : List Nat) (hw : w∈terms j) (i : Nat) (hi : i∈w) :
      Live (fun _=>True) n emptyCircuit i := by
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hw
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hi
    have t := l.isLt
    exact ⟨by simpa [nextWire,emptyCircuit,Circuit.size] using t,trivial⟩
  have const0 (x : X) : value emptyCircuit (input x) one=true ∧ value emptyCircuit (input x) zero=false := by
    rw [value_input _ _ (by rw [len];omega),value_input _ _ (by rw [len];omega)]
    exact constants x
  obtain ⟨D,tap,gd,_,live,nd,run_dnf⟩ := compile_dnf_many input len one zero a terms emptyCircuit pre on off const0 reads
  let C := withOutput D zero
  refine ⟨C,gd.1,gd.2.1,by change zero<n+D.size;omega,nd,tap,fun j => (live j).1,?_⟩
  intro x j
  change value D (input x) (tap j)=output x j
  rw [run_dnf]
  exact Bool.eq_iff_iff.mpr (semantics x j)



theorem quotient_row_bound {Z : Type*} [DecidableEq Z] :
    ∀ (c : Nat) (A : Finset ((Fin c → Bool) × Z)),
      (∀ j : Fin c, ∃ x∈A, ∃ y∈A, x.2=y.2 ∧ x.1 j≠y.1 j ∧
        ∀ i, i≠j → x.1 i=y.1 i) →
      (A.image Prod.snd).card+c ≤ A.card := by
  classical
  intro c
  induction c with
  | zero =>
    intro A _
    simpa using Finset.card_image_le (s := A) (f := Prod.snd)
  | succ c ih =>
    intro A witness
    let cut (z : (Fin (c+1) → Bool) × Z) := ((fun i : Fin c => z.1 i.succ),z.2)
    let B := A.image cut
    have B_cut (j : Fin c) : ∃ x∈B, ∃ y∈B, x.2=y.2 ∧ x.1 j≠y.1 j ∧
        ∀ i, i≠j → x.1 i=y.1 i := by
      obtain ⟨x,hx,y,hy,same,diff,only⟩ := witness j.succ
      refine ⟨cut x,Finset.mem_image_of_mem cut hx,cut y,Finset.mem_image_of_mem cut hy,
        same,diff,?_⟩
      intro i ne
      exact only i.succ (Fin.succ_injective _ |>.ne ne)
    have smaller : B.card<A.card := by
      apply lt_of_le_of_ne Finset.card_image_le
      intro e
      have inj := Finset.injOn_of_card_image_eq e
      obtain ⟨x,hx,y,hy,same,diff,only⟩ := witness 0
      have key : cut x=cut y := by
        refine Prod.ext (funext (fun i => only i.succ (Fin.succ_ne_zero i))) same
      exact diff (congrArg (fun z : (Fin (c+1) → Bool) × Z => z.1 0) (inj hx hy key))
    have count := ih B B_cut
    have features : B.image Prod.snd=A.image Prod.snd := by
      rw [show B=A.image cut from rfl,Finset.image_image]
      rfl
    rw [features] at count
    omega


theorem paired_sign_bound {ι : Type*} [Fintype ι] [Nonempty ι] (t : Nat)
    (support : ι → Finset (Fin t)) (unique : Function.Injective support)
    (mate : ι → ι) (inv : Function.Involutive mate)
    (nonempty : ∀ i, (support i).Nonempty)
    (apart : ∀ i, Disjoint (support i) (support (mate i)))
    (miss : ∀ i, support i ∪ support (mate i) ≠ Finset.univ) :
    Fintype.card ι + Nat.choose t (t/2) + 2 ≤ 2^t := by
  classical
  let p := t-t/2
  have short (i : ι) : (support i).card+(support (mate i)).card<t := by
    rw [←Finset.card_union_of_disjoint (apart i)]
    have sub : support i ∪ support (mate i) ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,miss i⟩
    simpa using Finset.card_lt_card sub
  have t_min : 3≤t := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    have a := Finset.card_pos.mpr (nonempty i)
    have b := Finset.card_pos.mpr (nonempty (mate i))
    have total := short i
    omega
  have ppos : 0<p := by dsimp [p]; omega
  have plt : p<t := by dsimp [p]; omega
  let transform (i : ι) := if (support i).card<p then support i else (support (mate i))ᶜ
  have lo (i : ι) (lt : (support i).card<p) : (transform i).card<p := by
    simp [transform,lt]
  have complement_size (i : ι) : ((support i)ᶜ).card=t-(support i).card := by
    simp [Finset.card_compl]
  have hi (i : ι) (ge : p≤(support i).card) : p<(transform i).card := by
    dsimp only [transform]
    rw [if_neg (not_lt_of_ge ge),complement_size]
    have total := short i
    dsimp [p] at *
    omega
  have transform_inj : Function.Injective transform := by
    intro i j same
    by_cases li : (support i).card<p <;> by_cases lj : (support j).card<p
    · exact unique (by simpa only [transform,if_pos li,if_pos lj] using same)
    · exact ((not_lt_of_ge ((lo i li).le)) (same ▸ hi j (Nat.le_of_not_gt lj))).elim
    · exact ((not_lt_of_ge ((lo j lj).le)) (same ▸ hi i (Nat.le_of_not_gt li))).elim
    · apply inv.injective
      apply unique
      have cc : (support (mate i))ᶜ=(support (mate j))ᶜ := by
        simpa only [transform,if_neg li,if_neg lj] using same
      exact compl_injective cc
  let used : Finset (Finset (Fin t)) := Finset.univ.image transform
  let level : Finset (Finset (Fin t)) := Finset.univ.powersetCard p
  have used_card : used.card=Fintype.card ι := by simp [used,Finset.card_image_of_injective _ transform_inj]
  have level_card : level.card=Nat.choose t (t/2) := by
    simp [level,Finset.card_powersetCard,p,Nat.choose_symm (Nat.div_le_self _ _)]
  have apart_level : Disjoint used level := by
    apply Finset.disjoint_left.mpr
    intro Z hZ hL
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hZ
    have e := (Finset.mem_powersetCard.mp hL).2
    by_cases lt : (support i).card<p
    · exact (lo i lt).ne e
    · exact (hi i (Nat.le_of_not_gt lt)).ne e.symm
  have neither (i : ι) : transform i ≠ ∅ ∧ transform i ≠ Finset.univ := by
    by_cases lt : (support i).card<p
    · have pos := Finset.card_pos.mpr (nonempty i)
      have small := lt.trans plt
      refine ⟨?_,?_⟩ <;> intro he <;> simp [transform,lt] at he
      · simp [he] at pos
      · simp [he] at small
    · have large := hi i (Nat.le_of_not_gt lt)
      have small : (transform i).card<t := by
        dsimp only [transform]
        rw [if_neg lt,complement_size]
        have := Finset.card_pos.mpr (nonempty (mate i))
        omega
      refine ⟨?_,?_⟩ <;> intro he
      · simp [he] at large
      · simp [he] at small
  let extremes : Finset (Finset (Fin t)) := {∅,Finset.univ}
  have two : extremes.card=2 := by
    have neq : (∅ : Finset (Fin t)) ≠ Finset.univ := by
      intro e
      have sz := congrArg Finset.card e
      simp at sz
      omega
    simp [extremes,neq]
  have dis_extremes : Disjoint (used ∪ level) extremes := by
    apply Finset.disjoint_left.mpr
    intro z hZ hz
    change z∈({∅,Finset.univ} : Finset (Finset (Fin t))) at hz
    rcases Finset.mem_insert.mp hz with h0 | h1
    · subst z
      rcases Finset.mem_union.mp hZ with used | mid
      · obtain ⟨i,_,he⟩ := Finset.mem_image.mp used
        exact (neither i).1 he
      · have zero := (Finset.mem_powersetCard.mp mid).2
        simp at zero
        omega
    · have e : z=(Finset.univ : Finset (Fin t)) := Finset.mem_singleton.mp h1
      subst z
      rcases Finset.mem_union.mp hZ with used | mid
      · obtain ⟨i,_,he⟩ := Finset.mem_image.mp used
        exact (neither i).2 he
      · have full := (Finset.mem_powersetCard.mp mid).2
        simp at full
        omega
  have count := Finset.card_le_univ ((used ∪ level) ∪ extremes)
  rw [Finset.card_union_of_disjoint dis_extremes,Finset.card_union_of_disjoint apart_level,
    used_card,level_card,two,Fintype.card_finset,Fintype.card_fin] at count
  exact count



theorem mapped_wire_of_mem {W : Type*} (L : List (W → Bool)) {g : W → Bool} (inL : g∈L) :
    ∃ i : Fin L.length, ∀ x : W, (L.map (fun f => f x)).getD i.val false=g x := by
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp inL
  refine ⟨⟨j,hj⟩,fun x => ?_⟩
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,hj,hget]

theorem fit_on_distinct_rows {W : Type*} (A : Finset W) (L : List (W → Bool))
    (hasTrue : (fun _ : W => true)∈L) (hasFalse : (fun _ : W => false)∈L)
    (distinct : ∀ x∈A, ∀ y∈A, (∀ g∈L, g x=true → g y=true) → x=y)
    (T : Finset (W → Bool)) :
    ∃ C : Circuit, Monotone2 C ∧ ReadsBack L.length C ∧ C.output < L.length+C.size ∧
      ∀ f∈T, ∃ j<L.length+C.size, ∀ x∈A, value C (L.map (fun g => g x)) j=f x := by
  classical
  let Q := {f : W → Bool // f∈T}
  let Z := {x : W // x∈A}
  letI : Fintype Q := by unfold Q; infer_instance
  letI : Fintype Z := by unfold Z; infer_instance
  let e := (Fintype.equivFin Q).symm
  let input (x : Z) := L.map (fun g => g x.val)
  let bits (x : Z) (j : Fin L.length) := (input x).getD j.val false
  let output (x : Z) (j : Fin (Fintype.card Q)) := (e j).val x.val
  have mon (x y : Z) (order : bits x ≤ bits y) : output x ≤ output y := by
    suffices x=y by simp [this]
    apply Subtype.ext
    apply distinct x.val x.property y.val y.property
    intro g hg gx
    obtain ⟨i,ht⟩ := mapped_wire_of_mem L hg
    have h := order i
    change (input x).getD i.val false ≤ (input y).getD i.val false at h
    change (L.map (fun g => g x.val)).getD i.val false ≤ (L.map (fun g => g y.val)).getD i.val false at h
    rw [ht,ht,gx] at h
    cases b : g y.val
    · exact ((by decide : ¬ true ≤ false) (b ▸ h)).elim
    · rfl
  obtain ⟨one,hon⟩ := mapped_wire_of_mem L hasTrue
  obtain ⟨zero,hoff⟩ := mapped_wire_of_mem L hasFalse
  obtain ⟨C,fan,rb,bound,nn,taps,live,correct⟩ :=
    fit_input_list input (fun x => by simp [input]) one.val zero.val one.isLt zero.isLt
      bits output (fun _ _ => rfl) (fun x => ⟨hon x.val,hoff x.val⟩) mon
  refine ⟨C,monotone2_of_no_not fan nn,rb,bound,?_⟩
  intro f hf
  let j := e.symm ⟨f,hf⟩
  refine ⟨taps j,live j,?_⟩
  intro x hx
  have same : e j=⟨f,hf⟩ := e.apply_symm_apply _
  have val := correct ⟨x,hx⟩ j
  change value C (L.map (fun g => g x)) (taps j)=(e j).val x at val
  rw [same] at val
  exact val

section
variable {n c : Nat}

abbrev Word (n : Nat) := Finset (Fin n)
abbrev Signal (n : Nat) := Word n → Bool

noncomputable def seedNeg (i : Fin n) (x : Word n) := !incidence x i

noncomputable def edgeSame (uv : Fin n × Fin n) (x : Word n) :=
  incidence x uv.1 == incidence x uv.2

noncomputable def edgeAtom (uv : Fin n × Fin n) (s : Fin 3) (x : Word n) : Bool :=
  if s=0 then seedNeg uv.1 x && seedNeg uv.2 x
  else if s=1 then incidence x uv.1 && seedNeg uv.2 x
  else seedNeg uv.1 x && incidence x uv.2

noncomputable def seedRaw (E : Finset (Fin n × Fin n)) : Finset (Signal n) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  {fun _ => false,fun _ => true} ∪ Finset.univ.image (fun i x => incidence x i) ∪
    E.image edgeSame ∪ E.image (fun e x => !(edgeSame e x))

noncomputable def seedBank (E : Finset (Fin n × Fin n)) (S : Word n) : Finset (Signal n) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  seedRaw E ∪ S.image seedNeg

noncomputable def seedNeed (E : Finset (Fin n × Fin n)) : Finset (Signal n) :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  Finset.univ.image seedNeg ∪ E.image (fun e => edgeAtom e 0) ∪
    E.image (fun e => edgeAtom e 1) ∪ E.image (fun e => edgeAtom e 2)

noncomputable def classMask (col : Fin n → Fin c) (j : Fin c) : Word n :=
  Finset.univ.filter (fun i => col i=j)

theorem classMask_mem {col : Fin n → Fin c} {j : Fin c} {v : Fin n} :
    v∈classMask col j ↔ col v=j := by simp [classMask]

theorem seedBank_const (E : Finset (Fin n × Fin n)) (S : Word n) :
    (fun _ => true) ∈ (seedBank E S).toList ∧ (fun _ => false) ∈ (seedBank E S).toList := by
  simp [seedBank,seedRaw]

theorem needed_bridge (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hom : ∀ z : Word n, (∀ e∈E, e.1∈z ↔ e.2∈z) ↔
      ∀ i j, color i=color j → (i∈z ↔ j∈z))
    (A : Finset (Word n))
    (blocked : ∀ S : Word n, (∃ j, ∀ i∈S, color i≠j) →
      ¬ ∃ C : Circuit, Monotone2 C ∧ ReadsBack (seedBank E S).toList.length C ∧
        C.output < (seedBank E S).toList.length+C.size ∧
        ∀ f∈seedNeed E, ∃ k<(seedBank E S).toList.length+C.size, ∀ x∈A,
          value C ((seedBank E S).toList.map (fun g => g x)) k=f x) :
    ∀ j, ∃ x∈A, Disjoint x (classMask color j) ∧ x∪classMask color j∈A := by
  classical
  intro j
  by_contra absent
  let B := classMask color j
  let S : Word n := Finset.univ \ B
  let L := (seedBank E S).toList
  have missing : ∃ j, ∀ i∈S, color i≠j := ⟨j,fun i h h' => (Finset.mem_sdiff.mp h).2 (classMask_mem.mpr h')⟩
  apply blocked S missing
  have inputs (g : Signal n) (h : g∈seedRaw E) : g∈L := by
    simp only [L,seedBank,Finset.mem_toList,Finset.mem_union]
    exact Or.inl h
  have rawBit (i : Fin n) : (fun x => incidence x i)∈L := by
    apply inputs
    simp [seedRaw]
  have rawNeg (i : Fin n) (hi : i∈S) : seedNeg i∈L := by
    simp only [L,seedBank,Finset.mem_toList,Finset.mem_union,Finset.mem_image]
    exact Or.inr ⟨i,hi,rfl⟩
  have equalWire (e : Fin n × Fin n) (he : e∈E) : edgeSame e∈L := by
    apply inputs
    simp only [seedRaw,Finset.mem_union,Finset.mem_image]
    exact Or.inl (Or.inr ⟨e,he,rfl⟩)
  have diffWire (e : Fin n × Fin n) (he : e∈E) : (fun x => !edgeSame e x)∈L := by
    apply inputs
    simp only [seedRaw,Finset.mem_union,Finset.mem_image]
    exact Or.inr ⟨e,he,rfl⟩
  have distinct (x : Word n) (hx : x∈A) (y : Word n) (hy : y∈A)
      (run : ∀ g∈L, g x=true → g y=true) : x=y := by
    have xy : x⊆y := fun v hv => incidence_true.mp (run _ (rawBit v) (incidence_true.mpr hv))
    by_contra ne
    let Z := y \ x
    have hz : Z.Nonempty := by
      by_contra! ee
      exact ne (Finset.Subset.antisymm xy (Finset.sdiff_eq_empty_iff_subset.mp ee))
    have no_seed : Z⊆B := by
      intro v hz
      by_contra hv
      have hvS : v∈S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩
      obtain ⟨vy,vx⟩ := Finset.mem_sdiff.mp hz
      have move := run (seedNeg v) (rawNeg v hvS) (by simp [seedNeg,incidence,vx])
      have yy : incidence y v=true := incidence_true.mpr vy
      simp [seedNeg,yy] at move
    have agree (e : Fin n × Fin n) (he : e∈E) : edgeSame e x=edgeSame e y := by
      have same := run _ (equalWire e he)
      have diff := run _ (diffWire e he)
      cases a : edgeSame e x <;> cases b : edgeSame e y <;> simp_all
    have edge_mask (e : Fin n × Fin n) (he : e∈E) : e.1∈Z ↔ e.2∈Z := by
      have eql := agree e he
      have a : incidence x e.1 ≤ incidence y e.1 := incidence_le.mpr xy e.1
      have b : incidence x e.2 ≤ incidence y e.2 := incidence_le.mpr xy e.2
      simp only [edgeSame] at eql
      simp only [Z,Finset.mem_sdiff,←incidence_true]
      cases ax : incidence x e.1 <;> cases ay : incidence y e.1 <;>
        cases bx : incidence x e.2 <;> cases by' : incidence y e.2 <;>
        simp only [ax,ay,bx,by'] at eql a b ⊢ <;> first | contradiction | decide
    obtain ⟨v,hv⟩ := hz
    have vj : color v=j := classMask_mem.mp (no_seed hv)
    have all : B⊆Z := fun i hi =>
      ((hom Z).mp edge_mask i v ((classMask_mem.mp hi).trans vj.symm)).mpr hv
    have eZ : Z=B := Finset.Subset.antisymm no_seed all
    have dis : Disjoint x B := by
      rw [←eZ]
      exact Finset.disjoint_sdiff
    have union : x∪B=y := by
      rw [←eZ]
      exact Finset.union_sdiff_of_subset xy
    exact absent ⟨x,hx,dis,union.symm ▸ hy⟩
  exact fit_on_distinct_rows A L (seedBank_const E S).1 (seedBank_const E S).2 distinct (seedNeed E)

end

theorem compile_pair_ands {X : Type*} {n : Nat} (input : X → List Bool)
    (len : ∀ x, (input x).length=n) :
    ∀ (pairs : List (Fin n × Fin n)) (C : Circuit), Good (fun _=>True) n C →
      ∃ D, Good (fun _=>True) n D ∧ C.gates <+: D.gates ∧
        D.size=C.size+pairs.length ∧ notCount D=notCount C ∧
        ∀ p∈pairs, ∃ t<n+D.size, ∀ x,
          value D (input x) t=((input x).getD p.1.val false && (input x).getD p.2.val false) := by
  intro pairs
  induction pairs with
  | nil =>
    intro C good
    exact ⟨C,good,List.prefix_refl _,by simp,rfl,by simp⟩
  | cons p rest ih =>
    intro C good
    have live (j : Fin n) : Live (fun _=>True) n C j.val :=
      ⟨j.isLt.trans_le (Nat.le_add_right _ _),trivial⟩
    obtain ⟨M,out,gm,cm,lm,sz,nc,sem⟩ := emit_binary input len
      (fun _ _ => trivial) good true (live p.1) (live p.2)
    obtain ⟨D,gd,md,sd,nd,result⟩ := ih M gm
    refine ⟨D,gd,cm.trans md,by simp only [List.length_cons]; omega,nd.trans nc,?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with eq | hr
    · subst v
      refine ⟨out,by have := lm.1; unfold nextWire at this; omega,?_⟩
      intro x
      rw [old_value md (len x) lm.1,sem,value_input C (input x) (i:=p.1.val) (by rw [len]; exact p.1.isLt),
        value_input C (input x) (i:=p.2.val) (by rw [len]; exact p.2.isLt)]
      rfl
    · exact result v hr

set_option maxHeartbeats 1000000 in
theorem compile_distinct_ands {W I : Type*} [Fintype I] (A : Finset W) (L : List (W → Bool))
    (off : (fun _ : W => false)∈L) (l r : I → W → Bool)
    (left : ∀ i, l i∈L) (right : ∀ i, r i∈L) :
    let Q := {x : W // x∈A}
    letI : DecidableEq (W → Bool) := fun a b => Classical.propDecidable (a=b)
    letI : DecidableEq (Q → Bool) := fun a b => Classical.propDecidable (a=b)
    let f := fun (i : I) (x : Q) => l i x && r i x
    let raw := fun (g : W → Bool) (x : Q) => g x
    let new := (Finset.univ.image f) \ (L.toFinset.image raw)
    ∃ C : Circuit, Monotone2 C ∧ ReadsBack L.length C ∧ C.output < L.length+C.size ∧
      C.size ≤ new.card ∧ (∀ g∈L, ∃ t<L.length+C.size, ∀ x∈A,
        value C (L.map (fun p => p x)) t=g x) ∧
      ∀ i, ∃ t<L.length+C.size, ∀ x∈A, value C (L.map (fun p => p x)) t=(l i x && r i x) := by
  classical
  let Q := {x : W // x∈A}
  letI : DecidableEq (W → Bool) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq (Q → Bool) := fun a b => Classical.propDecidable (a=b)
  let f (i : I) (x : Q) := l i x && r i x
  let raw (g : W → Bool) (x : Q) := g x
  let new := (Finset.univ.image f) \ (L.toFinset.image raw)
  dsimp only
  change ∃ C : Circuit, Monotone2 C ∧ ReadsBack L.length C ∧ C.output < L.length+C.size ∧
    C.size ≤ new.card ∧ _
  let input (x : Q) := L.map (fun p => p x.val)
  have len (x : Q) : (input x).length=L.length := by simp [input]
  have choose_pair (g : {g : Q → Bool // g∈new}) : ∃ p : Fin L.length × Fin L.length,
      ∀ x : Q, ((input x).getD p.1.val false && (input x).getD p.2.val false) = g.val x := by
    have mem := (Finset.mem_sdiff.mp g.property).1
    obtain ⟨i,_,same⟩ := Finset.mem_image.mp mem
    obtain ⟨li,hli⟩ := mapped_wire_of_mem L (left i)
    obtain ⟨ri,hri⟩ := mapped_wire_of_mem L (right i)
    refine ⟨(li,ri),fun x => ?_⟩
    change ((L.map (fun p => p x.val)).getD li.val false && (L.map (fun p => p x.val)).getD ri.val false)=g.val x
    rw [hli,hri,←same]
  choose pair match_pair using choose_pair
  let pairs := new.toList.attach.map (fun g => pair ⟨g.val,Finset.mem_toList.mp g.property⟩)
  have empty_good : Good (fun _=>True) L.length emptyCircuit :=
    ⟨emptyCircuit_fanInTwo,emptyCircuit_readsBack _,by simp [emptyCircuit]⟩
  obtain ⟨D,gd,_,size,none,values⟩ := compile_pair_ands input len pairs emptyCircuit empty_good
  obtain ⟨root,_⟩ := mapped_wire_of_mem L off
  let C := withOutput D root.val
  have final_size : C.size=new.card := by
    change D.size=new.card
    rw [size]
    simp [emptyCircuit,Circuit.size,pairs]
  have base (g : W → Bool) (mem : g∈L) : ∃ t<L.length+C.size, ∀ x∈A,
      value C (L.map (fun p => p x)) t=g x := by
    obtain ⟨i,wire⟩ := mapped_wire_of_mem L mem
    refine ⟨i.val,i.isLt.trans_le (Nat.le_add_right _ _),fun x hx => ?_⟩
    have same := value_input C (input ⟨x,hx⟩) (i:=i.val) (by rw [len]; exact i.isLt)
    exact same.trans (wire x)
  refine ⟨C,monotone2_of_no_not gd.1 (by change notCount D=0; exact none),gd.2.1,
    root.isLt.trans_le (Nat.le_add_right _ _),final_size.le,base,?_⟩
  intro i
  by_cases done : f i∈L.toFinset.image raw
  · obtain ⟨g,gin,eq⟩ := Finset.mem_image.mp done
    obtain ⟨t,live,correct⟩ := base g (List.mem_toFinset.mp gin)
    refine ⟨t,live,fun x hx => (correct x hx).trans (congrFun eq ⟨x,hx⟩)⟩
  · have add : f i∈new := Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem f (Finset.mem_univ i),done⟩
    let g : {g : Q → Bool // g∈new} := ⟨f i,add⟩
    have have_pair : pair g∈pairs := by
      apply List.mem_map.mpr
      exact ⟨⟨f i,Finset.mem_toList.mpr add⟩,List.mem_attach _ _,rfl⟩
    obtain ⟨t,live,correct⟩ := values (pair g) have_pair
    refine ⟨t,live,fun x hx => (correct ⟨x,hx⟩).trans (match_pair g ⟨x,hx⟩)⟩

section
variable {n c : Nat}

abbrev Edge {n : Nat} (E : Finset (Fin n × Fin n)) := {e // e∈E}

noncomputable def pairSign {E : Finset (Fin n × Fin n)} (i : Edge E × Bool) (x : Word n) : Bool :=
  if i.2 then seedNeg i.1.val.1 x && incidence x i.1.val.2
  else incidence x i.1.val.1 && seedNeg i.1.val.2 x

theorem count_sign_samples (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hasEdge : E.Nonempty) (onto : Function.Surjective color)
    (hom : ∀ z : Word n, (∀ e∈E, e.1∈z ↔ e.2∈z) ↔
      ∀ i j, color i=color j → (i∈z ↔ j∈z))
    (A : Finset (Word n))
    (bridge : ∀ j, ∃ x∈A, Disjoint x (classMask color j) ∧ x∪classMask color j∈A)
    (distinct : Function.Injective (fun (i : Edge E × Bool) (x : {x : Word n // x∈A}) => pairSign i x.val))
    (witness : ∀ i : Edge E × Bool, ∃ x∈A, pairSign i x=true) :
    c ≤ A.card ∧ 2*E.card + Nat.choose (A.card-c) ((A.card-c)/2) + 2 ≤ 2^(A.card-c) := by
  classical
  choose rep hrep using onto
  have edge_color (e : Edge E) : color e.val.1=color e.val.2 := by
    let B := classMask color (color e.val.1)
    have const (x y : Fin n) (h : color x=color y) : x∈B ↔ y∈B := by
      simp only [B,classMask_mem,h]
    have agree := (hom B).mpr const e.val e.property
    exact (classMask_mem.mp (agree.mp (classMask_mem.mpr rfl))).symm
  let J := Edge E × Bool
  let signals (x : Word n) : J → Bool := fun i => pairSign i x
  let tags (x : Word n) : Fin c → Bool := fun j => incidence x (rep j)
  let packed (x : Word n) := (tags x,signals x)
  let T := A.image packed
  have switches (j : Fin c) : ∃ x∈T, ∃ y∈T, x.2=y.2 ∧ x.1 j≠y.1 j ∧
      ∀ i, i≠j → x.1 i=y.1 i := by
    obtain ⟨x,hx,dis,hy⟩ := bridge j
    let B := classMask color j
    let y := x∪B
    have same_rep (i : Fin c) (ne : i≠j) : tags x i=tags y i := by
      have notB : rep i∉B := fun hit => ne ((hrep i).symm.trans (classMask_mem.mp hit))
      by_cases h : rep i∈x <;> simp [tags,incidence,y,Finset.mem_union,h,notB]
    have inj_rep : tags x j≠tags y j := by
      have b : rep j∈B := classMask_mem.mpr (hrep j)
      have nx : rep j∉x := fun h => Finset.disjoint_left.mp dis h b
      simp [tags,incidence,y,Finset.mem_union,nx,b]
    refine ⟨packed x,Finset.mem_image_of_mem _ hx,packed y,Finset.mem_image_of_mem _ hy,?_,inj_rep,same_rep⟩
    funext i
    obtain ⟨e,b⟩ := i
    by_cases matching : color e.val.1=j
    · have first : e.val.1∈B := classMask_mem.mpr matching
      have second : e.val.2∈B := classMask_mem.mpr ((edge_color e).symm.trans matching)
      have f : e.val.1∉x := fun hit => Finset.disjoint_left.mp dis hit first
      have s : e.val.2∉x := fun hit => Finset.disjoint_left.mp dis hit second
      cases b <;> simp [packed,signals,pairSign,seedNeg,incidence,y,Finset.mem_union,first,second,f,s]
    · have first : e.val.1∉B := fun hit => matching (classMask_mem.mp hit)
      have second : e.val.2∉B := fun hit => matching ((edge_color e).trans (classMask_mem.mp hit))
      cases b <;> by_cases f : e.val.1∈x <;> by_cases s : e.val.2∈x <;>
        simp [packed,signals,pairSign,seedNeg,incidence,y,Finset.mem_union,first,second,f,s]
  have trim := quotient_row_bound c T switches
  have img : T.image Prod.snd=A.image signals := by
    rw [show T=A.image packed from rfl,Finset.image_image]
    rfl
  rw [img] at trim
  have cost : (A.image signals).card+c≤A.card := trim.trans Finset.card_image_le
  have ccap : c≤A.card := by omega
  let t := A.card-c
  let M := A.image signals
  have bound : M.card≤t := by dsimp [M,t]; omega
  let Rows := {x : J → Bool // x∈M}
  letI : Fintype Rows := by unfold Rows; infer_instance
  have rb : Fintype.card Rows≤t := by simpa [Rows] using bound
  let idrow : Rows ↪ Fin t := (Fintype.equivFin Rows).toEmbedding.trans (Fin.castLEEmb rb)
  let asRow (x : Word n) (hx : x∈A) : Rows := ⟨signals x,Finset.mem_image_of_mem _ hx⟩
  let support (i : J) := (Finset.univ.filter (fun row : Rows => row.val i=true)).map idrow
  have observed (i : J) (x : Word n) (hx : x∈A) :
      idrow (asRow x hx)∈support i ↔ pairSign i x=true := by
    simp [support,asRow,signals]
  have unique : Function.Injective support := by
    intro i j e
    apply distinct
    funext x
    have both : pairSign i x.val=true ↔ pairSign j x.val=true :=
      (observed i x.val x.property).symm.trans (e ▸ observed j x.val x.property)
    exact Bool.eq_iff_iff.mpr both
  have visible (i : J) : (support i).Nonempty := by
    obtain ⟨x,hx,p⟩ := witness i
    exact ⟨_,(observed i x hx).mpr p⟩
  let swap (j : J) : J := (j.1,!j.2)
  have inv : Function.Involutive swap := by
    rintro ⟨e,b⟩
    cases b <;> rfl
  have apart (i : J) : Disjoint (support i) (support (swap i)) := by
    apply Finset.disjoint_left.mpr
    intro p ha hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y,hy,ey⟩ := Finset.mem_map.mp hb
    have eq := idrow.injective ey
    subst y
    have a := (Finset.mem_filter.mp hx).2
    have b := (Finset.mem_filter.mp hy).2
    obtain ⟨q,hq,eqv⟩ := Finset.mem_image.mp x.property
    rw [←eqv] at a b
    obtain ⟨edge,bit⟩ := i
    cases bit <;> simp [signals,pairSign,swap,seedNeg,Bool.and_eq_true] at a b <;> simp_all
  have missing_row (i : J) : support i ∪ support (swap i)≠Finset.univ := by
    obtain ⟨e,b⟩ := i
    let j := color e.val.1
    obtain ⟨x,hx,dis,_⟩ := bridge j
    have l : e.val.1∉x := fun h =>
      Finset.disjoint_left.mp dis h (classMask_mem.mpr rfl)
    have r : e.val.2∉x := fun h =>
      Finset.disjoint_left.mp dis h (classMask_mem.mpr (edge_color e).symm)
    intro eq
    have mem : idrow (asRow x hx)∈support (e,b) ∪ support (swap (e,b)) := by simp [eq]
    rcases Finset.mem_union.mp mem with hit | hit <;>
      have p := (observed _ x hx).mp hit <;> cases b <;>
      simp [pairSign,swap,incidence,l,r] at p
  obtain ⟨ed,valid⟩ := hasEdge
  letI : Nonempty J := ⟨⟨⟨ed,valid⟩,false⟩⟩
  have count := paired_sign_bound t support unique swap inv visible apart missing_row
  refine ⟨ccap,?_⟩
  simpa [t,J,Nat.mul_comm,Finset.coe_sort_coe,Fintype.card_coe] using count

end

section
variable {n c : Nat}

def SeedFit (E : Finset (Fin n × Fin n)) (A : Finset (Word n)) (S : Word n) (p : Nat) : Prop :=
  let L := (seedBank E S).toList
  ∃ C : Circuit, Monotone2 C ∧ ReadsBack L.length C ∧
    C.output<L.length+C.size ∧ C.size≤p ∧ ∀ f∈seedNeed E, ∃ j<L.length+C.size,
      ∀ x∈A, value C (L.map (fun g => g x)) j=f x

set_option maxHeartbeats 1000000 in
theorem full_seed_lower (E : Finset (Fin n × Fin n)) (A : Finset (Word n))
    (costly : ∀ p, SeedFit E A Finset.univ p → 3*E.card≤p) :
    Function.Injective (fun (i : Edge E × Bool) (x : {x : Word n // x∈A}) => pairSign i x.val) ∧
    ∀ i : Edge E × Bool, ∃ x∈A, pairSign i x=true := by
  classical
  let J := Edge E × Fin 3
  let L := (seedBank E Finset.univ).toList
  let left (i : J) (x : Word n) :=
    if i.2=1 then incidence x i.1.val.1 else seedNeg i.1.val.1 x
  let right (i : J) (x : Word n) :=
    if i.2=2 then incidence x i.1.val.2 else seedNeg i.1.val.2 x
  have pos_in (v : Fin n) : (fun x => incidence x v)∈L := by
    simp [L,seedBank,seedRaw,Finset.mem_union]
  have neg_in (v : Fin n) : seedNeg v∈L := by
    simp [L,seedBank,Finset.mem_union]
  have left_in (i : J) : left i∈L := by
    by_cases h : i.2=1
    · simpa only [left,if_pos h] using pos_in i.1.val.1
    · simpa only [left,if_neg h] using neg_in i.1.val.1
  have right_in (i : J) : right i∈L := by
    by_cases h : i.2=2
    · simpa only [right,if_pos h] using pos_in i.1.val.2
    · simpa only [right,if_neg h] using neg_in i.1.val.2
  have formula (i : J) (x : Word n) : (left i x && right i x)=edgeAtom i.1.val i.2 x := by
    obtain ⟨e,k⟩ := i
    fin_cases k <;> simp [left,right,edgeAtom]
  have cert := compile_distinct_ands A L (seedBank_const E Finset.univ).2 left right left_in right_in
  dsimp only at cert
  obtain ⟨C,mono,rb,out,size,raw,gate⟩ := cert
  let Q := {x : Word n // x∈A}
  letI : DecidableEq (Word n → Bool) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq (Q → Bool) := fun a b => Classical.propDecidable (a=b)
  let f (i : J) (x : Q) := left i x.val && right i x.val
  let supplied := L.toFinset.image (fun (g : Word n → Bool) (x : Q) => g x.val)
  let pool := Finset.univ.image f
  let fresh := pool \ supplied
  have valid : SeedFit E A Finset.univ fresh.card := by
    refine ⟨C,mono,rb,out,size,?_⟩
    intro g hg
    simp only [seedNeed,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hg
    rcases hg with (((⟨v,rfl⟩ | ⟨e,he,rfl⟩) | ⟨e,he,rfl⟩) | ⟨e,he,rfl⟩)
    · exact raw _ (neg_in v)
    · obtain ⟨tap,bound,sem⟩ := gate (⟨e,he⟩,0)
      exact ⟨tap,bound,fun x hx => (sem x hx).trans (formula (⟨e,he⟩,0) x)⟩
    · obtain ⟨tap,bound,sem⟩ := gate (⟨e,he⟩,1)
      exact ⟨tap,bound,fun x hx => (sem x hx).trans (formula (⟨e,he⟩,1) x)⟩
    · obtain ⟨tap,bound,sem⟩ := gate (⟨e,he⟩,2)
      exact ⟨tap,bound,fun x hx => (sem x hx).trans (formula (⟨e,he⟩,2) x)⟩
  have total : Fintype.card J=3*E.card := by simp [J,Nat.mul_comm]
  have hle := costly _ valid
  have subset : fresh⊆pool := Finset.sdiff_subset
  have pool_card : pool.card≤3*E.card := by
    have fbound := Finset.card_image_le (s := (Finset.univ : Finset J)) (f := f)
    simpa [pool,total] using fbound
  have full : fresh=pool := Finset.eq_of_subset_of_card_le subset (pool_card.trans hle)
  have injective : Function.Injective f := by
    have exact_count : pool.card=(Finset.univ : Finset J).card := by
      rw [Finset.card_univ,total]
      exact le_antisymm pool_card (full ▸ hle)
    have inj := Finset.injOn_of_card_image_eq exact_count
    exact fun i j h => inj (Finset.mem_univ i) (Finset.mem_univ j) h
  let signed (i : Edge E × Bool) : J := (i.1,if i.2 then 2 else 1)
  have signed_inj : Function.Injective signed := by
    rintro ⟨e,u⟩ ⟨e',v⟩ same
    have h := congrArg Prod.fst same
    change e=e' at h
    subst e'
    have h := congrArg Prod.snd same
    cases u <;> cases v <;> simp [signed] at h ⊢
  have signs (i : Edge E × Bool) (x : Q) : f (signed i) x=pairSign i x.val := by
    obtain ⟨e,b⟩ := i
    change (left (signed (e,b)) x.val && right (signed (e,b)) x.val)=_
    rw [formula]
    cases b <;> simp [signed,pairSign,edgeAtom]
  constructor
  · intro i j same
    apply signed_inj
    apply injective
    funext x
    exact (signs i x).trans ((congrFun same x).trans (signs j x).symm)
  · intro i
    by_contra absent
    have zero_out : ∀ x : Q, f (signed i) x=false := by
      intro x
      rw [signs]
      cases e : pairSign i x.val
      · rfl
      · exact (absent ⟨x.val,x.property,e⟩).elim
    have inside : f (signed i)∈pool := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [←full] at inside
    apply (Finset.mem_sdiff.mp inside).2
    apply Finset.mem_image.mpr
    exact ⟨fun _ => false,List.mem_toFinset.mpr (seedBank_const E Finset.univ).2,
      funext (fun x => (zero_out x).symm)⟩

end

section
variable {n c : Nat}

theorem same_edge_color (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (hom : ∀ z : Word n, (∀ e∈E, e.1∈z ↔ e.2∈z) ↔
      ∀ i j, color i=color j → (i∈z ↔ j∈z)) (e : Edge E) :
    color e.val.1=color e.val.2 := by
  let B := classMask color (color e.val.1)
  have const (x y : Fin n) (h : color x=color y) : x∈B ↔ y∈B := by
    simp only [B,classMask_mem,h]
  exact (classMask_mem.mp ((hom B).mpr const e.val e.property |>.mp (classMask_mem.mpr rfl))).symm

theorem incident_sign_degree (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (onto : Function.Surjective color)
    (hom : ∀ z : Word n, (∀ e∈E, e.1∈z ↔ e.2∈z) ↔
      ∀ i j, color i=color j → (i∈z ↔ j∈z))
    (A : Finset (Word n))
    (bridge : ∀ j, ∃ x∈A, Disjoint x (classMask color j) ∧ x∪classMask color j∈A)
    (unique : Function.Injective (fun (i : Edge E × Bool) (x : {x : Word n // x∈A}) => pairSign i x.val))
    (witness : ∀ i : Edge E × Bool, ∃ x∈A, pairSign i x=true)
    (v : Fin n) :
    c+1 ≤ A.card ∧ (E.filter (fun e => e.1=v ∨ e.2=v)).card < 2^((A.card-c-1)/2) := by
  classical
  choose rep hrep using onto
  let vColor := color v
  let Other := {j : Fin c // j≠vColor}
  let t := Fintype.card Other
  let equiv := (Fintype.equivFin Other).symm
  have cards : t+1=c := by
    have div := Fintype.card_subtype_compl (fun j : Fin c => j=vColor)
    have one : Fintype.card {j : Fin c // j=vColor}=1 := by simp
    have pos : 0<c := Nat.zero_lt_of_lt (color v).isLt
    rw [Fintype.card_fin,one] at div
    change t=c-1 at div
    omega
  let J := Edge E × Bool
  let Sigs := Bool × (J → Bool)
  let data (x : Word n) : Sigs := (incidence x v,fun i => pairSign i x)
  let label (x : Word n) (i : Fin t) := incidence x (rep (equiv i).val)
  let pack (x : Word n) := (label x,data x)
  let P := A.image pack
  let M := A.image data
  have edges (e : Edge E) := same_edge_color E color hom e
  have switches (i : Fin t) : ∃ x∈P, ∃ y∈P, x.2=y.2 ∧ x.1 i≠y.1 i ∧
      ∀ j, j≠i → x.1 j=y.1 j := by
    let ci := (equiv i).val
    obtain ⟨x,hx,dis,hy⟩ := bridge ci
    let B := classMask color ci
    let y := x∪B
    have new (w : Fin n) (z : w∈B) : incidence x w=false ∧ incidence y w=true := by
      have no : w∉x := fun h => Finset.disjoint_left.mp dis h z
      simp [incidence,no,y,Finset.mem_union,z]
    have fixed (w : Fin n) (z : w∉B) : incidence x w=incidence y w := by
      by_cases hw : w∈x <;> simp [incidence,y,Finset.mem_union,z,hw]
    have vfixed : v∉B := fun h => (equiv i).property (classMask_mem.mp h).symm
    refine ⟨pack x,Finset.mem_image_of_mem pack hx,pack y,Finset.mem_image_of_mem pack hy,
      Prod.ext (fixed v vfixed) ?_,?_,?_⟩
    · funext ij
      obtain ⟨e,b⟩ := ij
      by_cases l : e.val.1∈B
      · have r : e.val.2∈B := classMask_mem.mpr ((edges e).symm.trans (classMask_mem.mp l))
        have left := new _ l
        have right := new _ r
        change pairSign (e,b) x=pairSign (e,b) y
        cases b <;> simp [pairSign,seedNeg,left.1,left.2,right.1,right.2]
      · have r : e.val.2∉B := fun h => l (classMask_mem.mpr ((edges e).trans (classMask_mem.mp h)))
        change pairSign (e,b) x=pairSign (e,b) y
        cases b <;> simp [pairSign,seedNeg,←fixed _ l,←fixed _ r]
    · have hh := new (rep ci) (classMask_mem.mpr (hrep ci))
      change incidence x (rep ci)≠incidence y (rep ci)
      rw [hh.1,hh.2]
      decide
    · intro j ne
      have h : (equiv j).val≠ci := fun eq => ne (equiv.injective (Subtype.ext eq))
      exact fixed _ (fun hh => h ((hrep _).symm.trans (classMask_mem.mp hh)))
  have mx : P.image Prod.snd=M := by
    rw [show P=A.image pack from rfl,Finset.image_image]
    rfl
  have cs := quotient_row_bound t P switches
  rw [mx] at cs
  have bound : M.card+t≤A.card := cs.trans Finset.card_image_le
  let part (b : Bool) := M.filter (fun z => z.1=b)
  have apart : Disjoint (part false) (part true) := Finset.disjoint_left.mpr (fun z no yes =>
    Bool.false_ne_true ((Finset.mem_filter.mp no).2.symm.trans (Finset.mem_filter.mp yes).2))
  have combine : part false ∪ part true=M := by
    ext z
    cases e : z.1 <;> simp [part,Finset.mem_union,e]
  have part_cards : (part false).card+(part true).card=M.card := by
    rw [←Finset.card_union_of_disjoint apart,combine]
  let D := E.filter (fun e => e.1=v ∨ e.2=v)
  let Inc := {e // e∈D}
  let index (b : Bool) (e : Inc) : J :=
    (⟨e.val,(Finset.mem_filter.mp e.property).1⟩,if e.val.1=v then !b else b)
  have active (b : Bool) (e : Inc) (x : Word n) (out : pairSign (index b e) x=true) :
      incidence x v=b := by
    have incident := (Finset.mem_filter.mp e.property).2
    by_cases l : e.val.1=v
    · cases b <;> simp [index,l,pairSign,seedNeg,Bool.and_eq_true] at out ⊢ <;> tauto
    · have r := incident.resolve_left l
      cases b <;> simp [index,l,r,pairSign,seedNeg,Bool.and_eq_true] at out ⊢ <;> tauto
  have anchors (b : Bool) : ∃ z∈part b, ∀ e : Inc, z.2 (index b e)=false := by
    obtain ⟨x,hx,dis,hy⟩ := bridge vColor
    let B := classMask color vColor
    let y := x∪B
    let w := if b then y else x
    have wmem : w∈A := by cases b <;> simp [w,hx,show y∈A from hy]
    have same (u : Fin n) (col : color u=vColor) : incidence w u=b := by
      have hB := classMask_mem.mpr col
      have absent : u∉x := fun h => Finset.disjoint_left.mp dis h hB
      cases b <;> simp [w,y,incidence,Finset.mem_union,absent,show u∈B from hB]
    refine ⟨data w,Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem data wmem,same v rfl⟩,?_⟩
    intro e
    have h := edges (index b e).1
    have incident := (Finset.mem_filter.mp e.property).2
    change color e.val.1=color e.val.2 at h
    have a : color e.val.1=vColor := by
      rcases incident with ha|hb
      · rw [ha]
      · rw [h,hb]
    have z := h.symm.trans a
    have n1 := same _ a
    have n2 := same _ z
    change pairSign (index b e) w=false
    cases b <;> simp [index,pairSign,seedNeg,n1,n2] <;> split <;> rfl
  have side (b : Bool) : 0<(part b).card ∧ D.card<2^((part b).card-1) := by
    obtain ⟨base,bmem,nofs⟩ := anchors b
    let range := (part b).erase base
    let fn (e : Inc) := range.filter (fun z => z.2 (index b e)=true)
    have mem_iff (e : Inc) (x : Word n) (hx : x∈A) :
        data x∈fn e ↔ pairSign (index b e) x=true := by
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro yes
        have ne : data x≠base := by
          intro eq
          have fs := congrArg (fun z : Sigs => z.2 (index b e)) eq
          change pairSign (index b e) x=base.2 (index b e) at fs
          rw [yes,nofs] at fs
          contradiction
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ne,Finset.mem_filter.mpr
          ⟨Finset.mem_image_of_mem data hx,active b e x yes⟩⟩,yes⟩
    have injective : Function.Injective fn := by
      intro e e' same
      apply Subtype.ext
      have equal : index b e=index b e' := by
        apply unique
        funext x
        apply Bool.eq_iff_iff.mpr
        exact (mem_iff e x.val x.property).symm.trans (same ▸ mem_iff e' x.val x.property)
      exact congrArg (fun j : J => j.1.val) equal
    have sub : Finset.univ.image fn ⊂ range.powerset := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro X hx
        obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
      · intro eq
        have belongs : (∅ : Finset Sigs)∈Finset.univ.image fn := by
          rw [eq]
          exact Finset.mem_powerset.mpr (Finset.empty_subset _)
        obtain ⟨e,_,he⟩ := Finset.mem_image.mp belongs
        obtain ⟨x,hx,yes⟩ := witness (index b e)
        have mem := (mem_iff e x hx).mpr yes
        rw [he] at mem
        exact Finset.notMem_empty _ mem
    have cc := Finset.card_lt_card sub
    rw [Finset.card_image_of_injective _ injective,Finset.card_univ,
      Finset.card_powerset,Finset.card_erase_of_mem bmem] at cc
    exact ⟨Finset.card_pos.mpr ⟨base,bmem⟩,by simpa [Inc] using cc⟩
  have always0 := side false
  have always1 := side true
  refine ⟨by omega,?_⟩
  have choose_side : ∃ b, (part b).card-1≤(A.card-c-1)/2 := by
    by_contra! no
    have l := no false
    have r := no true
    omega
  obtain ⟨b,small⟩ := choose_side
  exact (side b).2.trans_le (Nat.pow_le_pow_right (by decide) small)

end

end PEqualNP.Outside.L_meta_53194_aux


open PEqualNP.Outside.L_meta_53194_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_53194 :
  ∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
    (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
    (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    let W := Finset (Fin n)
    let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
    let neg := fun (i : Fin n) (x : W) => !(bit i x)
    let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
    let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
      E.image same ∪ E.image (fun e x => !(same e x))
    let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
      E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
    let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
      let L := (raw ∪ S.image neg).toList
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
        C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
          ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
      (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
    ∀ A : Finset W, keeps A → ∀ v : Fin n,
      let d := (E.filter (fun e => e.1 = v ∨ e.2 = v)).card
      0 < d → c+1 ≤ A.card ∧ d < 2^((A.card-c-1)/2) := by
  intro n c E color edge_order onto hom
  dsimp only
  intro A keeps
  have eqSame : (edgeSame : (Fin n × Fin n) → Word n → Bool) =
      (fun e x => @BEq.beq Bool (@instBEqOfDecidableEq Bool (fun a b => Classical.propDecidable (a=b))) (@decide (e.1∈x) (Classical.propDecidable _)) (@decide (e.2∈x) (Classical.propDecidable _))) := by
    funext e x
    by_cases left : e.1∈x <;> by_cases right : e.2∈x <;> simp [edgeSame,incidence,left,right]
  have eqNeg : (seedNeg : Fin n → Word n → Bool) =
      (fun i x => !(@decide (i∈x) (Classical.propDecidable _))) := rfl
  have eqZero : (fun e : Fin n × Fin n => edgeAtom e 0) =
      (fun e (x : Word n) => !(@decide (e.1∈x) (Classical.propDecidable _)) && !(@decide (e.2∈x) (Classical.propDecidable _))) := by
    funext e x
    simp [edgeAtom,seedNeg,incidence]
  have eqFirst : (fun e : Fin n × Fin n => edgeAtom e 1) =
      (fun e (x : Word n) => @decide (e.1∈x) (Classical.propDecidable _) && !(@decide (e.2∈x) (Classical.propDecidable _))) := by
    funext e x
    simp [edgeAtom,seedNeg,incidence]
  have eqSecond : (fun e : Fin n × Fin n => edgeAtom e 2) =
      (fun e (x : Word n) => !(@decide (e.1∈x) (Classical.propDecidable _)) && @decide (e.2∈x) (Classical.propDecidable _)) := by
    funext e x
    simp [edgeAtom,seedNeg,incidence]
  have keep (S : Word n) (p : Nat) : SeedFit E A S p ↔
      (∀ j, ∃ i∈S, color i=j) ∧ n+3*E.card-S.card≤p := by
    simpa only [SeedFit,seedBank,seedRaw,seedNeed,eqNeg,eqSame,eqZero,eqFirst,eqSecond,incidence,value] using keeps S p
  have costly (p : Nat) (h : SeedFit E A Finset.univ p) : 3*E.card≤p := by
    have b := ((keep Finset.univ p).mp h).2
    simpa using b
  have bridge := needed_bridge E color hom A (by
    intro S absent fit
    obtain ⟨j,hj⟩ := absent
    obtain ⟨C,mono,rb,out,sem⟩ := fit
    have sat : SeedFit E A S C.size := ⟨C,mono,rb,out,le_refl _,sem⟩
    obtain ⟨i,hi,eq⟩ := ((keep S C.size).mp sat).1 j
    exact hj i hi eq)
  have key := full_seed_lower E A costly
  intro v
  intro positive
  obtain ⟨cap,cut⟩ := incident_sign_degree E color onto hom A bridge key.1 key.2 v
  refine ⟨cap,?_⟩
  convert cut using 1
  congr 1
  ext e
  simp only [Finset.mem_filter]
