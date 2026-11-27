import PEqualNP.Defs
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PEqualNP.Outside.L_lib_790

abbrev Word := BitVec 128

def bit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bit_xor (b c : Bool) : bit (b ^^ c) = bit b + bit c := by
  cases b <;> cases c <;> decide

theorem bit_and (b c : Bool) : bit (b && c) = bit b * bit c := by
  cases b <;> cases c <;> decide

def unpack (w : Word) (j : Fin 128) : ZMod 2 := bit (w.getLsbD j.val)

theorem unpack_xor (a b : Word) : unpack (a ^^^ b) = unpack a + unpack b := by
  funext j
  exact (congrArg bit (BitVec.getLsbD_xor (i := j.val))).trans (bit_xor _ _)

theorem unpack_zero : unpack 0 = 0 := by funext j; simp [unpack, bit]

def reduce (a : Word) : List Word → Word
  | [] => a
  | b :: bs => reduce (if a.getLsbD b.toNat.log2 then a ^^^ b else a) bs

def insertRow (basis : List Word) (a : Word) :=
  let residual := reduce a basis
  if residual = 0 then basis else basis ++ [residual]

theorem reduce_mem (S : Submodule (ZMod 2) (Fin 128 → ZMod 2)) (basis : List Word)
    (h : ∀ b ∈ basis, unpack b ∈ S) (a : Word) :
    unpack (reduce a basis) ∈ S ↔ unpack a ∈ S := by
  induction basis generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [reduce]
    rw [ih (fun v hv => h v (List.mem_cons_of_mem b hv))]
    split
    · rw [unpack_xor]
      exact S.add_mem_iff_left (h b (by simp))
    · rfl

theorem insert_subset (basis : List Word) (a : Word) : ∀ b ∈ basis, b ∈ insertRow basis a := by
  intro b hb
  simp only [insertRow]
  split <;> simp [hb]

theorem insert_spans (S : Submodule (ZMod 2) (Fin 128 → ZMod 2)) (basis : List Word)
    (a : Word) (h : ∀ b ∈ insertRow basis a, unpack b ∈ S) : unpack a ∈ S := by
  apply (reduce_mem S basis (fun b hb => h b (insert_subset _ _ b hb)) a).mp
  by_cases hz : reduce a basis = 0
  · rw [hz, unpack_zero]
    exact S.zero_mem
  · apply h
    unfold insertRow
    dsimp only
    rw [if_neg hz]
    simp

theorem fold_spans (S : Submodule (ZMod 2) (Fin 128 → ZMod 2)) (rows basis : List Word)
    (h : ∀ b ∈ rows.foldl insertRow basis, unpack b ∈ S) :
    ∀ b ∈ basis ++ rows, unpack b ∈ S := by
  induction rows generalizing basis with
  | nil => simpa using h
  | cons a rows ih =>
    intro b hb
    have hs := ih (insertRow basis a) h
    rcases List.mem_append.mp hb with hb | hb
    · exact hs b (List.mem_append_left _ (insert_subset _ _ b hb))
    · rcases List.mem_cons.mp hb with rfl | hb
      · apply insert_spans S basis b
        intro v hv
        exact hs v (List.mem_append_left _ hv)
      · exact hs b (List.mem_append_right _ hb)

def maskOf (flag : Bool) : Word := if flag then BitVec.allOnes 128 else 0

theorem mask_bit (flag : Bool) (j : Fin 128) :
    (maskOf flag).getLsbD j.val = flag := by
  have hj : j.val < 128 := j.isLt
  cases flag
  · change (0#128).getLsbD j.val = false
    exact BitVec.getLsbD_zero
  · change (BitVec.allOnes 128).getLsbD j.val = true
    simp only [BitVec.getLsbD_allOnes, hj, decide_true]

def columns : Fin 7 → Word :=
  ![
    (BitVec.ofNat 128 (0xaaaaaaaaaaaaaaaa <<< 64 ||| 0xaaaaaaaaaaaaaaaa)),
    (BitVec.ofNat 128 (0xcccccccccccccccc <<< 64 ||| 0xcccccccccccccccc)),
    (BitVec.ofNat 128 (0xf0f0f0f0f0f0f0f0 <<< 64 ||| 0xf0f0f0f0f0f0f0f0)),
    (BitVec.ofNat 128 (0xff00ff00ff00ff00 <<< 64 ||| 0xff00ff00ff00ff00)),
    (BitVec.ofNat 128 (0xffff0000ffff0000 <<< 64 ||| 0xffff0000ffff0000)),
    (BitVec.ofNat 128 (0xffffffff00000000 <<< 64 ||| 0xffffffff00000000)),
    (BitVec.ofNat 128 (0xffffffffffffffff <<< 64 ||| 0x0))
  ]

theorem column_bit : ∀ (i : Fin 7) (j : Fin 128),
    (columns i).getLsbD j.val = j.val.testBit i.val := by decide +kernel

def rowWord (schedule : BitVec 8) (x : Fin 128) : Word :=
  let z := fun i : Fin 7 => maskOf (x.val.testBit i.val) ^^^ columns i
  let b := fun i : Nat => maskOf (schedule.getLsbD i)
  let p := z 1 &&& z 2
  let q := (z 3 ^^^ (b 0 &&& p)) &&& (z 4 ^^^ (b 1 &&& p))
  let l := z 5 ^^^ (b 2 &&& p) ^^^ (b 3 &&& q)
  let r := z 6 ^^^ (b 4 &&& p) ^^^ (b 5 &&& q)
  z 0 ^^^ (b 6 &&& p) ^^^ (b 7 &&& q) ^^^ (l &&& r)

def basisFor (schedule : BitVec 8) : List Word :=
  (List.ofFn (rowWord schedule)).foldl insertRow []

def pack {n : Nat} (f : Fin n → ZMod 2) : BitVec n :=
  BitVec.cast (List.length_ofFn (f := fun i => decide (f i = 1)))
    (BitVec.ofBoolListLE (List.ofFn (fun i => decide (f i = 1))))

theorem read_pack {n : Nat} (f : Fin n → ZMod 2) (i : Fin n) :
    bit ((pack f).getLsbD i.val) = f i := by
  simp only [pack, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dif_pos, Option.getD_some]
  have hb : ∀ a : ZMod 2, bit (decide (a = 1)) = a := by decide
  exact hb (f i)

def code (i : Fin 128) (j : Fin 7) : ZMod 2 := bit (i.val.testBit j.val)

theorem code_pack (z : Fin 7 → ZMod 2) : code (pack z).toFin = z := by
  funext j
  exact read_pack z j

theorem row_entry (s : BitVec 8) (x y : Fin 128) :
    let z := code x + code y
    let b := fun i : Nat => bit (s.getLsbD i)
    let p := z 1 * z 2
    let q := (z 3 + b 0 * p) * (z 4 + b 1 * p)
    let l := z 5 + b 2 * p + b 3 * q
    let r := z 6 + b 4 * p + b 5 * q
    unpack (rowWord s x) y = z 0 + b 6 * p + b 7 * q + l * r := by
  simp only [rowWord, unpack, BitVec.getLsbD_xor, BitVec.getLsbD_and, code, mask_bit, column_bit, bit_xor, bit_and, Pi.add_apply]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block0 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 0 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block1 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 1 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block2 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 2 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block3 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 3 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block4 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 4 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block5 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 5 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block6 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 6 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block7 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 7 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block8 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 8 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block9 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 9 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block10 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 10 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block11 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 11 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block12 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 12 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block13 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 13 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block14 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 14 + j.val))).length ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block15 : ∀ j : Fin 16, (basisFor (BitVec.ofNat 8 (16 * 15 + j.val))).length ≤ 16 := by
  decide +kernel

theorem bounded (s : BitVec 8) : (basisFor s).length ≤ 16 := by
  have hb : s.toNat < 256 := s.isLt
  let hi : Fin 16 := ⟨s.toNat / 16, by omega⟩
  let lo : Fin 16 := ⟨s.toNat % 16, by omega⟩
  have chunks : ∀ i j : Fin 16,
      (basisFor (BitVec.ofNat 8 (16 * i.val + j.val))).length ≤ 16 := by
    intro i
    fin_cases i
    · exact block0
    · exact block1
    · exact block2
    · exact block3
    · exact block4
    · exact block5
    · exact block6
    · exact block7
    · exact block8
    · exact block9
    · exact block10
    · exact block11
    · exact block12
    · exact block13
    · exact block14
    · exact block15
  have he : BitVec.ofNat 8 (16 * hi.val + lo.val) = s := by
    apply BitVec.eq_of_toNat_eq
    have he' : 16 * hi.val + lo.val = s.toNat := by dsimp [hi, lo]; omega
    rw [he']
    simp
  rw [← he]
  exact chunks hi lo

theorem rank_rows (s : BitVec 8) :
    (Matrix.of fun i j : Fin 128 => unpack (rowWord s i) j).rank ≤ 16 := by
  classical
  let B := ((basisFor s).map unpack).toFinset
  let S := Submodule.span (ZMod 2) (B : Set (Fin 128 → ZMod 2))
  rw [Matrix.rank_eq_finrank_span_row]
  have hle : Submodule.span (ZMod 2) (Set.range
      (Matrix.of fun i j : Fin 128 => unpack (rowWord s i) j).row) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change unpack (rowWord s i) ∈ S
    apply fold_spans S (List.ofFn (rowWord s)) []
    · intro b hb
      apply Submodule.subset_span
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)
    · simp only [List.nil_append, List.mem_ofFn]
      exact ⟨i, rfl⟩
  exact (Submodule.finrank_mono hle).trans ((finrank_span_finset_le_card B).trans
    ((List.toFinset_card_le _).trans (by simpa using bounded s)))

noncomputable def indexEquiv : Fin 128 ≃ (Fin 7 → ZMod 2) :=
  Equiv.ofBijective code ((Fintype.bijective_iff_surjective_and_card code).2
    ⟨fun z => ⟨(pack z).toFin, code_pack z⟩, by simp [Fintype.card_fun, ZMod.card]⟩)

end PEqualNP.Outside.L_lib_790



theorem PEqualNP.Outside.L_lib_790 : (∀ bits : Fin 8 → ZMod 2,
  let output := fun (z : Fin 7 → ZMod 2) =>
    let p := z 1 * z 2
    let q := (z 3 + bits 0 * p) * (z 4 + bits 1 * p)
    let left := z 5 + bits 2 * p + bits 3 * q
    let right := z 6 + bits 4 * p + bits 5 * q
    z 0 + bits 6 * p + bits 7 * q + left * right
  (Matrix.of (fun x y : Fin 7 → ZMod 2 => output (x + y))).rank ≤ 16) := by
  intro bits
  dsimp only
  let s := PEqualNP.Outside.L_lib_790.pack bits
  let e := PEqualNP.Outside.L_lib_790.indexEquiv
  let M : Matrix (Fin 7 → ZMod 2) (Fin 7 → ZMod 2) (ZMod 2) :=
    Matrix.of fun x y =>
      let z := x + y
      let p := z 1 * z 2
      let q := (z 3 + bits 0 * p) * (z 4 + bits 1 * p)
      let l := z 5 + bits 2 * p + bits 3 * q
      let r := z 6 + bits 4 * p + bits 5 * q
      z 0 + bits 6 * p + bits 7 * q + l * r
  change M.rank ≤ 16
  rw [← Matrix.rank_reindex e.symm e.symm M]
  have hm : Matrix.reindex e.symm e.symm M =
      Matrix.of fun i j : Fin 128 => PEqualNP.Outside.L_lib_790.unpack
        (PEqualNP.Outside.L_lib_790.rowWord s i) j := by
    ext i j
    have hbits (k : Fin 8) : PEqualNP.Outside.L_lib_790.bit (s.getLsbD k.val) = bits k :=
      PEqualNP.Outside.L_lib_790.read_pack bits k
    have h := PEqualNP.Outside.L_lib_790.row_entry s i j
    dsimp only at h ⊢
    change M (PEqualNP.Outside.L_lib_790.code i) (PEqualNP.Outside.L_lib_790.code j) = _
    unfold M
    change _ = PEqualNP.Outside.L_lib_790.unpack (PEqualNP.Outside.L_lib_790.rowWord s i) j
    rw [h]
    simp only [← hbits 0, ← hbits 1, ← hbits 2, ← hbits 3, ← hbits 4, ← hbits 5, ← hbits 6, ← hbits 7]
    rfl
  rw [hm]
  exact PEqualNP.Outside.L_lib_790.rank_rows s

