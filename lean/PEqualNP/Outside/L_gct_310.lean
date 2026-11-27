import Mathlib
import PEqualNP.Defs

-- The classification and coefficient lemmas below are adapted from these Apache-2.0
-- proofs in pequalnp-proofs: L-gct-309 (p6h6i6l, 151562bf8), L-gct-312
-- (bowerofbliss, a68da9306), L-gct-306 (Bili Dong, 3177f56d5), L-gct-303
-- (Nico Habets, 5d43eb310), and L-gct-142 (Flambé, c70e339e5).

namespace PEqualNP.Outside.L_gct_310

section Reuse309

/-! Rank-two block reduction and the bilinear Witt bound on the centred row and column factors. -/

namespace RankTwo.PivotCore

variable {K S W : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S]

structure Pivot (K S W : Type*) [Field K] [AddCommGroup S] [Module K S] where
  p : S →ₗ[K] K
  q : S →ₗ[K] K
  a : S →ₗ[K] K
  b : S →ₗ[K] K
  c : S →ₗ[K] K
  d : S →ₗ[K] K
  u : W → S →ₗ[K] K
  v : W → S →ₗ[K] K
  quad : ∀ s w, p s * u w s + q s * v w s = 0
  cubic : ∀ s w, p s * (a s * u w s + b s * v w s) +
    q s * (c s * u w s + d s * v w s) = 0

namespace Pivot

def det3 (a b u c d v p q z : K) : K :=
  a * (d*z-v*q) - b * (c*z-v*p) + u * (c*q-d*p)

theorem detData (a b u c d v p q z : K)
    (h : det3 a b u c d v p q z = 0)
    (hp : det3 (1+a) b u c (1+d) v p q z = 0)
    (hm : det3 (1-a) (-b) (-u) (-c) (1-d) (-v) (-p) (-q) (-z) = 0) :
    z = 0 ∧ p*u+q*v = 0 ∧
      p*(a*u+b*v)+q*(c*u+d*v) = 0 := by
  simp only [det3] at h hp hm
  have h₂ : (2:K) ≠ 0 := (OfNat.ofNat_ne_zero 2)
  have e : (2:K)*z = 0 := by
    linear_combination hp - hm - 2*h
  have hz : z = 0 := (mul_eq_zero.mp e).resolve_left h₂
  rw [hz] at h hp hm
  have e' : (2:K)*(p*u+q*v) = 0 := by
    linear_combination -hp - hm
  have hq : p*u+q*v = 0 := (mul_eq_zero.mp e').resolve_left h₂
  refine ⟨hz,hq,?_⟩
  linear_combination h + (a+d)*hq

variable (P : Pivot K S W)

theorem polar (x y : S) (w : W) :
    P.p x * P.u w y + P.q x * P.v w y +
      (P.p y * P.u w x + P.q y * P.v w x) = 0 := by
  have hh := P.quad (x+y) w
  simp only [map_add] at hh
  linear_combination hh - P.quad x w - P.quad y w

theorem inLine {p q x y : K} (hn : p ≠ 0 ∨ q ≠ 0) (hh : p*y=q*x) :
    ∃ t : K, x=t*p ∧ y=t*q := by
  by_cases hp : p=0
  · have hq : q≠0 := hn.resolve_left (fun e => e hp)
    have hqx : q*x=0 := by simpa [hp] using hh.symm
    have hx : x=0 := (mul_eq_zero.mp hqx).resolve_left hq
    refine ⟨y/q, by simp [hx,hp], ?_⟩
    exact (div_mul_cancel₀ y hq).symm
  · refine ⟨x/p, (div_mul_cancel₀ x hp).symm, ?_⟩
    have h₀ : (x/p*q-y)*p = 0 := by
      linear_combination q * (div_mul_cancel₀ x hp) - hh
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h₀).resolve_right hp)).symm

private theorem hasBoth (F G : S →ₗ[K] K)
    (hf : ∃ x, F x ≠ 0) (hg : ∃ x, G x ≠ 0) :
    ∃ x, F x ≠ 0 ∧ G x ≠ 0 := by
  obtain ⟨x,hx⟩ := hf
  obtain ⟨y,hy⟩ := hg
  by_cases hGx : G x = 0
  · by_cases hFy : F y = 0
    · exact ⟨x+y, by simpa [map_add,hFy] using hx, by simpa [map_add,hGx] using hy⟩
    · exact ⟨y,hFy,hy⟩
  · exact ⟨x,hx,hGx⟩

theorem vanishesOffTwo (F G H : S →ₗ[K] K)
    (hf : ∃ x, F x ≠ 0) (hg : ∃ x, G x ≠ 0)
    (h : ∀ x, F x ≠ 0 → G x ≠ 0 → H x = 0) :
    ∀ x, H x = 0 := by
  obtain ⟨y,hfY,hgY⟩ := hasBoth F G hf hg
  have hy : H y = 0 := h y hfY hgY
  have prod : ∀ x, H x ≠ 0 → F x * G x = 0 := by
    intro x hx
    by_cases hxF : F x = 0
    · simp [hxF]
    by_cases hxG : G x = 0
    · simp [hxG]
    exact (hx (h x hxF hxG)).elim
  intro x
  by_contra hx
  have hx0 := prod x hx
  have hxp := prod (x+y) (by simpa [map_add,hy] using hx)
  have hxm := prod (x-y) (by simpa [map_sub,hy] using hx)
  simp only [map_add,map_sub] at hxp hxm
  have hz : (2:K) * (F y * G y) = 0 := by
    linear_combination hxp + hxm - 2 * hx0
  exact (mul_ne_zero ((OfNat.ofNat_ne_zero 2)) (mul_ne_zero hfY hgY)) hz

def PureImage : Prop := ∀ x, P.p x = 0 ∧ P.q x = 0
def PureKernel : Prop := ∀ x w, P.u w x = 0 ∧ P.v w x = 0

def form (z : S) : S →ₗ[K] K :=
  P.p z • (P.q z • P.a - P.p z • P.b) +
    P.q z • (P.q z • P.c - P.p z • P.d)

theorem form_apply (z x : S) :
    P.form z x = P.p z * (P.a x * P.q z - P.b x * P.p z) +
      P.q z * (P.c x * P.q z - P.d x * P.p z) := by
  simp only [form,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  ring1

def Mixed : Prop := ∃ z, (P.p z ≠ 0 ∨ P.q z ≠ 0) ∧
    (∀ x, P.p z * P.q x = P.q z * P.p x) ∧
    (∀ x w, P.p z * P.u w x + P.q z * P.v w x = 0) ∧
    (∀ x, P.form z x = 0)

private theorem oneDirection (z : S) (hz : P.p z ≠ 0 ∨ P.q z ≠ 0)
    (line : ∀ x, P.p z * P.q x = P.q z * P.p x)
    (hC : ¬ P.PureKernel) : P.Mixed := by
  classical
  have bline : ∀ x, ∃ t : K, P.p x=t*P.p z ∧ P.q x=t*P.q z :=
    fun x => inLine hz (line x)
  have orth : ∀ x w, P.p z * P.u w x + P.q z * P.v w x = 0 := by
    intro x w
    obtain ⟨t,hp,hq⟩ := bline x
    have hh := P.polar z x w
    rw [hp,hq] at hh
    linear_combination hh - t * P.quad z w
  have cline : ∀ x w, ∃ t : K, P.u w x=t*P.q z ∧ P.v w x=t*(-P.p z) := by
    intro x w
    apply inLine
    · rcases hz with hz|hz
      · exact Or.inr (neg_ne_zero.mpr hz)
      · exact Or.inl hz
    · linear_combination orth x w
  have hc : ∃ w, (∃ x, P.u w x ≠ 0) ∨ (∃ x, P.v w x ≠ 0) := by
    classical
    by_contra h
    apply hC
    intro x w
    exact ⟨by by_contra e; exact h ⟨w, Or.inl ⟨x,e⟩⟩,
      by by_contra e; exact h ⟨w, Or.inr ⟨x,e⟩⟩⟩
  obtain ⟨w,hw⟩ := hc
  let F : S →ₗ[K] K := if P.p z = 0 then P.q else P.p
  let G : S →ₗ[K] K := if ∃ x, P.u w x ≠ 0 then P.u w else P.v w
  have hf : ∃ x, F x ≠ 0 := by
    refine ⟨z,?_⟩
    rcases eq_or_ne (P.p z) 0 with h|h
    · simpa [F,h] using hz.resolve_left (fun e => e h)
    · simpa [F,h] using h
  have hg : ∃ x, G x ≠ 0 := by
    by_cases h : ∃ x, P.u w x ≠ 0
    · simpa [G,h] using h
    · simpa [G,h] using hw.resolve_left h
  refine ⟨z,hz,line,orth,vanishesOffTwo F G (P.form z) hf hg ?_⟩
  intro x hFx hGx
  obtain ⟨r,hp,hq⟩ := bline x
  obtain ⟨t,hu,hv⟩ := cline x w
  have hr : r ≠ 0 := by
    intro h
    have e₀ : P.p x = 0 := by simp [hp,h]
    have e₁ : P.q x = 0 := by simp [hq,h]
    apply hFx
    by_cases hF : P.p z = 0 <;> simp [F,hF,e₀,e₁]
  have ht : t ≠ 0 := by
    intro h
    have e₀ : P.u w x = 0 := by simp [hu,h]
    have e₁ : P.v w x = 0 := by simp [hv,h]
    apply hGx
    by_cases hG : ∃ u, P.u w u ≠ 0 <;> simp [G,hG,e₀,e₁]
  have hpv := P.cubic x w
  rw [hp,hq,hu,hv] at hpv
  have hz' : (r*t)*P.form z x = 0 := by
    rw [P.form_apply]
    linear_combination hpv
  exact (mul_eq_zero.mp hz').resolve_left (mul_ne_zero hr ht)

def Faithful : Prop := ∀ x, P.p x = 0 → P.q x = 0 →
    P.a x = 0 → P.b x = 0 → P.c x = 0 → P.d x = 0 →
    (∀ w, P.u w x = 0 ∧ P.v w x = 0) → x = 0

def Small : Prop := ∀ x, P.p x = 0 → P.q x = 0 → P.a x = 0 → x = 0

private theorem twoDirections (x₀ x₁ : S)
    (hp₀ : P.p x₀ = 1) (hq₀ : P.q x₀ = 0)
    (hp₁ : P.p x₁ = 0) (hq₁ : P.q x₁ = 1)
    (hf : P.Faithful) (hC : ¬ P.PureKernel) :
    P.Small := by
  have onKernel : ∀ x, P.p x=0 → P.q x=0 → ∀ w, P.u w x=0 ∧ P.v w x=0 := by
    intro x hp hq w
    constructor
    · simpa [hp,hq,hp₀,hq₀] using P.polar x x₀ w
    · simpa [hp,hq,hp₁,hq₁] using P.polar x x₁ w
  have sy : ∀ w, P.u w x₁ = -(P.v w x₀) := by
    intro w
    have h := P.polar x₀ x₁ w
    simp only [hp₀,hq₀,hp₁,hq₁, one_mul,zero_mul,add_zero,zero_add] at h
    linear_combination h
  have xu : ∀ w, P.u w x₀ = 0 := by
    intro w
    simpa [hp₀,hq₀] using P.quad x₀ w
  have xv : ∀ w, P.v w x₁ = 0 := by
    intro w
    simpa [hp₁,hq₁] using P.quad x₁ w
  have express : ∀ x w, P.u w x = -P.q x * P.v w x₀ ∧ P.v w x = P.p x * P.v w x₀ := by
    intro x w
    have h := P.polar x x₀ w
    have h' := P.polar x x₁ w
    simp only [hp₀,hq₀,xu w, one_mul,zero_mul,add_zero,zero_add] at h
    simp only [hp₁,hq₁,xv w,sy w,one_mul,zero_mul,add_zero,zero_add] at h'
    refine ⟨?_,?_⟩
    · linear_combination h
    · linear_combination h'
  have hn : ∃ w, P.v w x₀ ≠ 0 := by
    classical
    by_contra hh
    apply hC
    intro x w
    have hz : P.v w x₀ = 0 := by
      by_contra hz'
      exact hh ⟨w,hz'⟩
    have h := express x w
    simpa [hz] using h
  obtain ⟨w,hw⟩ := hn
  have reduced : ∀ x, P.p x * (-P.a x * P.q x + P.b x * P.p x) +
      P.q x * (-P.c x * P.q x + P.d x * P.p x) = 0 := by
    intro x
    have h := P.cubic x w
    rw [(express x w).1,(express x w).2] at h
    have hz : (P.p x * (-P.a x * P.q x + P.b x * P.p x) +
      P.q x * (-P.c x * P.q x + P.d x * P.p x)) * P.v w x₀ = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hz).resolve_right hw
  intro x hp hq ha
  have hx₀ := reduced (x₀+x)
  have hx₁ := reduced (x₁+x)
  have h₀ := reduced x₀
  have h₁ := reduced x₁
  simp only [map_add,hp,hq,hp₀,hq₀,hp₁,hq₁, add_zero, mul_one,zero_mul,mul_zero,
    one_mul,zero_add,neg_zero] at hx₀ hx₁ h₀ h₁
  have hb : P.b x = 0 := by linear_combination hx₀ - h₀
  have hc : P.c x = 0 := by linear_combination h₁ - hx₁
  have hxy := reduced (x₀+x₁+x)
  have hy := reduced (x₀+x₁)
  simp only [map_add,hp,hq,hp₀,hq₀,hp₁,hq₁,ha,hb,hc, add_zero,zero_add,
    mul_one,zero_mul,mul_zero,one_mul,neg_zero] at hxy hy
  have hd : P.d x = 0 := by linear_combination hxy - hy
  exact hf x hp hq ha hb hc hd (onKernel x hp hq)

theorem classify (hf : P.Faithful) :
    P.PureImage ∨ P.PureKernel ∨ P.Mixed ∨ P.Small := by
  classical
  by_cases hB : P.PureImage
  · exact Or.inl hB
  by_cases hC : P.PureKernel
  · exact Or.inr (Or.inl hC)
  have hZ : ∃ z, P.p z ≠ 0 ∨ P.q z ≠ 0 := by
    by_contra h
    apply hB
    intro z
    exact ⟨by by_contra h'; exact h ⟨z,Or.inl h'⟩,
      by by_contra h'; exact h ⟨z,Or.inr h'⟩⟩
  obtain ⟨z,hz⟩ := hZ
  by_cases hLine : ∀ x, P.p z * P.q x = P.q z * P.p x
  · exact Or.inr (Or.inr (Or.inl (P.oneDirection z hz hLine hC)))
  obtain ⟨y,hy⟩ := not_forall.mp hLine
  let Δ := P.p z * P.q y - P.q z * P.p y
  have hΔ : Δ ≠ 0 := sub_ne_zero.mpr hy
  let x₀ := Δ⁻¹ • (P.q y • z - P.q z • y)
  let x₁ := Δ⁻¹ • (P.p z • y - P.p y • z)
  have hp₀ : P.p x₀ = 1 := by
    simp only [x₀,map_sub,map_smul,smul_eq_mul]
    rw [show P.q y * P.p z - P.q z * P.p y = Δ by unfold Δ; ring1]
    exact inv_mul_cancel₀ hΔ
  have hq₀ : P.q x₀ = 0 := by
    simp only [x₀,map_sub,map_smul,smul_eq_mul]
    ring1
  have hp₁ : P.p x₁ = 0 := by
    simp only [x₁,map_sub,map_smul,smul_eq_mul]
    ring1
  have hq₁ : P.q x₁ = 1 := by
    simp only [x₁,map_sub,map_smul,smul_eq_mul]
    rw [show P.p z * P.q y - P.p y * P.q z = Δ by unfold Δ; ring1]
    exact inv_mul_cancel₀ hΔ
  exact Or.inr (Or.inr (Or.inr (P.twoDirections x₀ x₁ hp₀ hq₀ hp₁ hq₁ hf hC)))

end Pivot
end RankTwo.PivotCore

open Module
open scoped BigOperators

namespace RankTwo.PivotCore

variable {K S D : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S] [AddCommGroup D] [Module K D]

abbrev Target (K : Type*) := Fin 3 → K

def evalSlot (T : S →ₗ[K] D →ₗ[K] Target K) (i : Fin 3) (x : D) : S →ₗ[K] K where
  toFun s := T s x i
  map_add' s t := by simp only [map_add,LinearMap.add_apply,Pi.add_apply]
  map_smul' r s := by simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]

@[simp] theorem evalSlot_apply (T : S →ₗ[K] D →ₗ[K] Target K)
    (i : Fin 3) (x : D) (s : S) : evalSlot T i x s = T s x i := rfl

def coord (T : D →ₗ[K] Target K) (i : Fin 3) : D →ₗ[K] K :=
  (LinearMap.proj i).comp T

@[simp] theorem coord_apply (T : D →ₗ[K] Target K) (i : Fin 3) (x : D) :
    coord T i x = T x i := rfl

theorem cutDet (A : D →ₗ[K] Target K) (hA : finrank K (LinearMap.range A) ≤ 2)
    (cols : Fin 3 → D) : (Matrix.of fun (i j : Fin 3) => A (cols j) i).det = 0 := by
  classical
  let M : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => A (cols j) i
  change M.det = 0
  have hle : LinearMap.range M.mulVecLin ≤ LinearMap.range A := by
    rintro _ ⟨x,rfl⟩
    refine ⟨∑ j, x j • cols j, ?_⟩
    ext i
    simp only [map_sum,map_smul,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul,M,Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hr : M.rank ≤ 2 := (Submodule.finrank_mono hle).trans hA
  by_contra hd
  have h3 := Matrix.rank_of_det_ne_zero hd
  rw [Fintype.card_fin] at h3
  omega

structure Normalized (K S D : Type*) [Field K] [AddCommGroup S] [Module K S]
    [AddCommGroup D] [Module K D] where
  T : S →ₗ[K] D →ₗ[K] Target K
  faithful : Function.Injective T
  rank : ∀ s, finrank K (LinearMap.range (T s)) ≤ 2
  center : D
  vanishes : ∀ s, T s center = 0
  chosen : S
  x0 : D
  x1 : D
  at0 : T chosen x0 = ![1,0,0]
  at1 : T chosen x1 = ![0,1,0]
  at2 : ∀ x, T chosen x 2 = 0

variable {V : Type*} [AddCommGroup V] [Module K V]

def FixedImage (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ a b : V, LinearIndependent K ![a,b] ∧
    ∀ s, ∃ f g : D →ₗ[K] K, f center = 0 ∧ g center = 0 ∧
      ∀ x, T s x = f x • a + g x • b

def FixedKernel (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ f g : D →ₗ[K] K, f center = 0 ∧ g center = 0 ∧ LinearIndependent K ![f,g] ∧
    ∀ s, ∃ a b : V, ∀ x, T s x = f x • a + g x • b

def FixedLine (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ (a : V) (b : D →ₗ[K] K), a ≠ 0 ∧ b ≠ 0 ∧ b center = 0 ∧
    ∀ s, ∃ (f : D →ₗ[K] K) (y : V), f center = 0 ∧
      ∀ x, T s x = f x • a + b x • y

def ThreeShapes (T : S →ₗ[K] D →ₗ[K] V) (center : D) :=
  FixedImage T center ∨ FixedKernel T center ∨ FixedLine T center

theorem fixedLine_of_restrict (T : S →ₗ[K] D →ₗ[K] V) {center : D}
    (hCenter : ∀ s, T s center = 0)
    (a : V) (b : D →ₗ[K] K) (e : V →ₗ[K] K) (v : D)
    (ha : e a = 1) (hb : b v = 1) (hzero : b center = 0)
    (h : ∀ s x, b x = 0 → ∃ t : K, T s x = t • a) :
    FixedLine T center := by
  have hane : a ≠ 0 := by intro hz; simp [hz] at ha
  have hbne : b ≠ 0 := by intro hz; simp [hz] at hb
  refine ⟨a,b,hane,hbne,hzero,?_⟩
  intro s
  let M : D →ₗ[K] V := T s - b.smulRight (T s v)
  refine ⟨e.comp M, T s v, ?_, ?_⟩
  · simp [M,hCenter s,hzero,LinearMap.smulRight_apply]
  intro x
  let w := x - b x • v
  have hw : b w = 0 := by simp [w,hb,map_sub,map_smul,smul_eq_mul]
  obtain ⟨t,ht⟩ := h s w hw
  have hM : M x = t • a := by
    simpa [M,w,map_sub,map_smul,LinearMap.smulRight_apply] using ht
  change T s x = e (M x) • a + b x • T s v
  rw [hM, map_smul, ha, smul_eq_mul, mul_one, ← hM]
  simp [M,LinearMap.smulRight_apply]

namespace Normalized

variable (N : Normalized K S D)

abbrev Tail := LinearMap.ker (N.T N.chosen)
abbrev r0 := coord (N.T N.chosen) 0
abbrev r1 := coord (N.T N.chosen) 1

def tailPart (x : D) : N.Tail := ⟨x - N.r0 x • N.x0 - N.r1 x • N.x1, by
  rw [LinearMap.mem_ker]
  ext i
  fin_cases i <;>
    simp [r0,r1,map_sub,map_smul,Pi.sub_apply,smul_eq_mul,N.at0,N.at1,N.at2,
      Matrix.vecHead,Matrix.vecTail,Fin.succ_zero_eq_one]⟩

theorem split (x : D) : x = N.r0 x • N.x0 + N.r1 x • N.x1 + (N.tailPart x : D) := by
  change x = _ + _ + (x - _ - _)
  abel

theorem cutStencil (s : S) (w : N.Tail) :
    N.T s (w : D) 2 = 0 ∧
    N.T s N.x0 2 * N.T s (w : D) 0 + N.T s N.x1 2 * N.T s (w : D) 1 = 0 ∧
    N.T s N.x0 2 * (N.T s N.x0 0 * N.T s (w : D) 0 + N.T s N.x1 0 * N.T s (w : D) 1) +
    N.T s N.x1 2 * (N.T s N.x0 1 * N.T s (w : D) 0 + N.T s N.x1 1 * N.T s (w : D) 1) = 0 := by
  let cols : Fin 3 → D := ![N.x0,N.x1,(w : D)]
  let a := N.T s N.x0 0
  let b := N.T s N.x1 0
  let u := N.T s (w : D) 0
  let c := N.T s N.x0 1
  let d := N.T s N.x1 1
  let v := N.T s (w : D) 1
  let p := N.T s N.x0 2
  let q := N.T s N.x1 2
  let z := N.T s (w : D) 2
  have unfoldDet (t : S) :
      (Matrix.of fun (i j : Fin 3) => N.T t (cols j) i).det =
      Pivot.det3 (N.T t N.x0 0) (N.T t N.x1 0) (N.T t (w : D) 0)
        (N.T t N.x0 1) (N.T t N.x1 1) (N.T t (w : D) 1)
        (N.T t N.x0 2) (N.T t N.x1 2) (N.T t (w : D) 2) := by
    rw [Matrix.det_fin_three]
    simp only [cols,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      Pivot.det3]
    ring1
  have h (t : S) := (unfoldDet t).symm.trans (cutDet (N.T t) (N.rank t) cols)
  have hw : N.T N.chosen (w : D) = 0 := w.property
  have hp := h (N.chosen+s)
  have hm := h (N.chosen-s)
  simp only [map_add,LinearMap.add_apply,Pi.add_apply,N.at0,N.at1,hw,Pi.zero_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,zero_add] at hp
  simp only [map_sub,LinearMap.sub_apply,Pi.sub_apply,N.at0,N.at1,hw,Pi.zero_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,zero_sub] at hm
  exact Pivot.detData a b u c d v p q z (h s) hp hm

def pivot : Pivot K S N.Tail where
  p := evalSlot N.T 2 N.x0
  q := evalSlot N.T 2 N.x1
  a := evalSlot N.T 0 N.x0
  b := evalSlot N.T 0 N.x1
  c := evalSlot N.T 1 N.x0
  d := evalSlot N.T 1 N.x1
  u w := evalSlot N.T 0 w
  v w := evalSlot N.T 1 w
  quad s w := (N.cutStencil s w).2.1
  cubic s w := (N.cutStencil s w).2.2

theorem pivot_faithful : N.pivot.Faithful := by
  intro s hp hq ha hb hc hd ht
  apply N.faithful
  rw [map_zero]
  ext x i
  have h0 : N.T s N.x0 = 0 := by
    ext i
    fin_cases i
    · exact ha
    · exact hc
    · exact hp
  have h1 : N.T s N.x1 = 0 := by
    ext i
    fin_cases i
    · exact hb
    · exact hd
    · exact hq
  have hTail (w : N.Tail) : N.T s w = 0 := by
    ext i
    fin_cases i
    · exact (ht w).1
    · exact (ht w).2
    · exact (N.cutStencil s w).1
  rw [N.split x]
  simp only [map_add,map_smul,h0,h1,hTail,smul_zero,add_zero,LinearMap.zero_apply]

theorem splitValues (s : S) (x : D) :
    N.T s x = N.r0 x • N.T s N.x0 + N.r1 x • N.T s N.x1 + N.T s (N.tailPart x : D) := by
  conv_lhs => rw [N.split x]
  simp only [map_add,map_smul]

theorem r00 : N.r0 N.x0 = 1 := by simp [r0,N.at0]
theorem r01 : N.r0 N.x1 = 0 := by simp [r0,N.at1]
theorem r10 : N.r1 N.x0 = 0 := by simp [r1,N.at0]
theorem r11 : N.r1 N.x1 = 1 := by simp [r1,N.at1]

theorem pImage (hh : N.pivot.PureImage) : FixedImage N.T N.center := by
  let a : Target K := ![1,0,0]
  let b : Target K := ![0,1,0]
  refine ⟨a,b,?_,?_⟩
  · rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    constructor
    · intro h; have e := congrFun h 1
      simp [b] at e
    · intro c h; have e := congrFun h 0
      simp [a,b,Pi.smul_apply] at e
  intro s
  refine ⟨coord (N.T s) 0,coord (N.T s) 1, by simp [N.vanishes],by simp [N.vanishes],?_⟩
  intro x
  have hx : N.T s x 2 = 0 := by
    have h₀ : N.T s N.x0 2 = 0 := (hh s).1
    have h₁ : N.T s N.x1 2 = 0 := (hh s).2
    rw [N.splitValues s x]
    simp [h₀,h₁,(N.cutStencil s (N.tailPart x)).1]
  ext i
  fin_cases i <;> simp [a,b,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hx,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem pKernel (hh : N.pivot.PureKernel) : FixedKernel N.T N.center := by
  refine ⟨N.r0,N.r1,by simp [r0,N.vanishes],by simp [r1,N.vanishes],?_,?_⟩
  · rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    constructor
    · intro h; have e := DFunLike.congr_fun h N.x1; simp [N.r11] at e
    · intro c h; have e := DFunLike.congr_fun h N.x0
      simp [N.r10,N.r00,LinearMap.smul_apply] at e
  intro s
  refine ⟨N.T s N.x0,N.T s N.x1,?_⟩
  intro x
  rw [N.splitValues s x]
  have ht : N.T s (N.tailPart x : D) = 0 := by
    ext i
    fin_cases i
    · exact (hh s (N.tailPart x)).1
    · exact (hh s (N.tailPart x)).2
    · exact (N.cutStencil s (N.tailPart x)).1
  rw [ht,add_zero]

theorem pMixed (hh : N.pivot.Mixed) : FixedLine N.T N.center := by
  obtain ⟨z,hz,hline,horth,hform⟩ := hh
  let p := N.pivot.p z
  let q := N.pivot.q z
  let a : Target K := ![q,-p,0]
  let b : D →ₗ[K] K := p • N.r0 + q • N.r1
  have hb (x : D) : b x = p*N.r0 x+q*N.r1 x := by
    simp only [b,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  have center : b N.center = 0 := by simp [hb,r0,r1,N.vanishes]
  have hR : ∀ s x, b x = 0 → ∃ t : K, N.T s x = t • a := by
    intro s x hx
    have hne : q ≠ 0 ∨ -p ≠ 0 := by
      rcases hz with h|h
      · exact Or.inr (neg_ne_zero.mpr h)
      · exact Or.inl h
    obtain ⟨v,hv₀,hv₁⟩ := Pivot.inLine hne (show q*N.r1 x=(-p)*N.r0 x by
      rw [hb] at hx
      linear_combination hx)
    have h02 : N.T s x 2 = 0 := by
      rw [N.splitValues s x]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,(N.cutStencil s (N.tailPart x)).1,
        hv₀,hv₁,add_zero]
      have e : p * N.T s N.x1 2 = q * N.T s N.x0 2 := hline s
      linear_combination -v*e
    have ho : p*N.T s x 0+q*N.T s x 1=0 := by
      rw [N.splitValues s x]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hv₀,hv₁]
      have h₁ : p*N.T s (N.tailPart x : D) 0+q*N.T s (N.tailPart x : D) 1=0 :=
        horth s (N.tailPart x)
      have h₂ := hform s
      rw [Pivot.form_apply] at h₂
      change p*(N.T s N.x0 0*q - N.T s N.x1 0*p) +
        q*(N.T s N.x0 1*q - N.T s N.x1 1*p) = 0 at h₂
      linear_combination h₁ + v*h₂
    obtain ⟨t,h₀,h₁⟩ := Pivot.inLine hne (show q*N.T s x 1=(-p)*N.T s x 0 by
      linear_combination ho)
    refine ⟨t,?_⟩
    ext i
    fin_cases i <;> simp [a,h₀,h₁,h02,Pi.smul_apply,smul_eq_mul,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  obtain ⟨e,he⟩ : ∃ e : Target K →ₗ[K] K, e a = 1 := by
    rcases hz with h|h
    · refine ⟨(-p)⁻¹ • LinearMap.proj 1,?_⟩
      change (-p)⁻¹ * (-p) = 1
      exact inv_mul_cancel₀ (neg_ne_zero.mpr (show p ≠ 0 from h))
    · refine ⟨q⁻¹ • LinearMap.proj 0,?_⟩
      change q⁻¹ * q = 1
      exact inv_mul_cancel₀ (show q ≠ 0 from h)
  obtain ⟨v,hv⟩ : ∃ v : D, b v = 1 := by
    rcases hz with h|h
    · refine ⟨p⁻¹ • N.x0,?_⟩
      have h0 : b N.x0 = p := by simp [hb,N.r00,N.r10]
      rw [map_smul,h0,smul_eq_mul,inv_mul_cancel₀ h]
    · refine ⟨q⁻¹ • N.x1,?_⟩
      have h1 : b N.x1 = q := by simp [hb,N.r01,N.r11]
      rw [map_smul,h1,smul_eq_mul,inv_mul_cancel₀ h]
  exact fixedLine_of_restrict N.T N.vanishes a b e v he hv center hR

theorem classification (hLarge : 3 < finrank K S) : ThreeShapes N.T N.center := by
  rcases N.pivot.classify N.pivot_faithful with hi|hk|hm|hs
  · exact Or.inl (N.pImage hi)
  · exact Or.inr (Or.inl (N.pKernel hk))
  · exact Or.inr (Or.inr (N.pMixed hm))
  let f := N.pivot.p.prod (N.pivot.q.prod N.pivot.a)
  have h : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun s h => ?_
    exact hs s (congrArg Prod.fst h) (congrArg (fun p => p.2.1) h)
      (congrArg (fun p => p.2.2) h)
  have hf : finrank K S ≤ 3 := by simpa using f.finrank_le_finrank_of_injective h
  omega

end Normalized
end RankTwo.PivotCore

open Module
open scoped BigOperators

namespace RankTwo.PivotCore

variable {K S D V : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S] [AddCommGroup D] [Module K D]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem rankOneLaw (T : D →ₗ[K] V) (h : finrank K (LinearMap.range T) ≤ 1)
    (e : V →ₗ[K] K) (x v : D) : e (T x) • T v = e (T v) • T x := by
  obtain ⟨a,ha⟩ := finrank_le_one_iff.mp h
  obtain ⟨p,hp⟩ := ha ⟨T x,⟨x,rfl⟩⟩
  obtain ⟨q,hq⟩ := ha ⟨T v,⟨v,rfl⟩⟩
  have ep : p • (a : V) = T x := congrArg Subtype.val hp
  have eq : q • (a : V) = T v := congrArg Subtype.val hq
  simp only [← ep,← eq,map_smul,smul_eq_mul,smul_smul]
  congr 1 <;> ring1

theorem rankOneLine (T : S →ₗ[K] D →ₗ[K] V) (hT : Function.Injective T) (center : D)
    (hcenter : ∀ s, T s center = 0) (hsmall : ∀ s, finrank K (LinearMap.range (T s)) ≤ 1)
    (hLarge : 3 < finrank K S) :
    FixedLine T center := by
  classical
  have hex : ∃ (s : S) (v : D), T s v ≠ 0 := by
    by_contra h
    have hz : ∀ s, T s = 0 := by
      intro s
      ext v
      by_contra hv
      exact h ⟨s,v,hv⟩
    letI : Subsingleton S := ⟨fun a b => hT ((hz a).trans (hz b).symm)⟩
    have hz : finrank K S = 0 := Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨m,v,hv⟩ := hex
  let a := T m v
  obtain ⟨e,he⟩ := Module.Projective.exists_dual_eq_one K hv
  change e a = 1 at he
  let b := e.comp (T m)
  have hBV : b v = 1 := he
  have hBZ : b center = 0 := by simp [b,hcenter]
  refine fixedLine_of_restrict T hcenter a b e v he hBV hBZ ?_
  intro s x hx
  have hMx : T m x = 0 := by
    have h := rankOneLaw (T m) (hsmall m) e x v
    change b x • a = e a • T m x at h
    simpa [hx,he] using h.symm
  have h := rankOneLaw (T (m+s)) (hsmall (m+s)) e x v
  have he' : e (T m v) = 1 := he
  simp only [map_add,LinearMap.add_apply,hMx,zero_add,he',add_smul,smul_add,one_smul] at h
  have hr := rankOneLaw (T s) (hsmall s) e x v
  rw [hr] at h
  exact ⟨e (T s x),(add_right_cancel h).symm⟩

def post (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V) :
    S →ₗ[K] D →ₗ[K] Target K where
  toFun s := E.toLinearMap.comp (T s)
  map_add' s t := by ext x i; simp only [map_add,LinearMap.add_apply,LinearMap.comp_apply,
    LinearEquiv.coe_coe,Pi.add_apply]
  map_smul' c s := by ext x i; simp only [map_smul,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearEquiv.coe_coe,Pi.smul_apply,RingHom.id_apply]

@[simp] theorem post_eval (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V)
    (s : S) (x : D) : post E T s x = E (T s x) := rfl

theorem ofPost (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V) (center : D)
    (h : ThreeShapes (post E T) center) : ThreeShapes T center := by
  rcases h with h|h|h
  · obtain ⟨a,b,hi,h⟩ := h
    refine Or.inl ⟨E.symm a,E.symm b,?_,?_⟩
    · have h' := hi.map' E.symm.toLinearMap (LinearMap.ker_eq_bot.mpr E.symm.injective)
      convert h' using 1
      ext i
      fin_cases i <;> rfl
    intro s
    obtain ⟨f,g,hf,hg,h⟩ := h s
    refine ⟨f,g,hf,hg,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)
  · obtain ⟨f,g,hf,hg,hi,h⟩ := h
    refine Or.inr (Or.inl ⟨f,g,hf,hg,hi,?_⟩)
    intro s
    obtain ⟨a,b,h⟩ := h s
    refine ⟨E.symm a,E.symm b,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)
  · obtain ⟨a,b,ha,hb,hb0,h⟩ := h
    refine Or.inr (Or.inr ⟨E.symm a,b,?_,hb,hb0,?_⟩)
    · intro hz
      exact ha (E.symm.injective (hz.trans (map_zero E.symm).symm))
    intro s
    obtain ⟨f,y,hf,h⟩ := h s
    refine ⟨f,E.symm y,hf,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)

theorem classifySpace (T : S →ₗ[K] D →ₗ[K] V) (hT : Function.Injective T)
    (center : D) (hcenter : ∀ s, T s center = 0)
    (hrank : ∀ s, finrank K (LinearMap.range (T s)) ≤ 2)
    (hV : finrank K V = 3) (hS : 3 < finrank K S) : ThreeShapes T center := by
  classical
  by_cases hm : ∃ m, finrank K (LinearMap.range (T m)) = 2
  · obtain ⟨m,hm⟩ := hm
    let R := LinearMap.range (T m)
    have hR : finrank K R = 2 := hm
    obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := R) (n := 2) hR.ge
    let f' : Fin 2 → V := fun i => (f i : V)
    have hf' : LinearIndependent K f' := hf.map' R.subtype R.ker_subtype
    obtain ⟨b,hb⟩ := exists_linearIndependent_snoc_of_lt_finrank hf' (by omega : 2 < finrank K V)
    let B : Basis (Fin 3) K V := basisOfLinearIndependentOfCardEqFinrank hb (by simp [hV])
    have hB (i : Fin 2) : B (Fin.castSucc i) = f' i := by
      simp [B,basisOfLinearIndependentOfCardEqFinrank,Fin.snoc_castSucc]
    have hspan : Submodule.span K (Set.range f') = R := by
      apply Submodule.eq_of_le_of_finrank_eq
      · apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        exact (f i).property
      · rw [finrank_span_eq_card hf',hR,Fintype.card_fin]
    obtain ⟨v0,hv0⟩ := (f 0).property
    obtain ⟨v1,hv1⟩ := (f 1).property
    have hb0 : T m v0 = B 0 := hv0.trans (hB 0).symm
    have hb1 : T m v1 = B 1 := hv1.trans (hB 1).symm
    let E : V ≃ₗ[K] Target K := B.equivFun
    let U := post E T
    have hU : Function.Injective U := by
      intro x y hxy
      apply hT
      ext z
      apply E.injective
      exact congrArg (fun F : D →ₗ[K] Target K => F z) hxy
    have hUr (s : S) : finrank K (LinearMap.range (U s)) ≤ 2 := by
      change finrank K (LinearMap.range (E.toLinearMap.comp (T s))) ≤ 2
      rw [LinearMap.range_comp,LinearEquiv.finrank_map_eq]
      exact hrank s
    have hU0 : U m v0 = ![1,0,0] := by
      rw [show U m v0 = B.equivFun (T m v0) from rfl,hb0]
      ext i
      fin_cases i <;> exact B.equivFun_self _ _
    have hU1 : U m v1 = ![0,1,0] := by
      rw [show U m v1 = B.equivFun (T m v1) from rfl,hb1]
      ext i
      fin_cases i <;> exact B.equivFun_self _ _
    have hU2 (x : D) : U m x 2 = 0 := by
      have hle : Submodule.span K (Set.range f') ≤ LinearMap.ker (B.coord 2) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change B.coord 2 (f' i) = 0
        rw [← hB i, Basis.coord_apply, Basis.repr_self_apply]
        fin_cases i <;> simp
      have hm' : T m x ∈ Submodule.span K (Set.range f') := by
        rw [hspan]
        exact ⟨x,rfl⟩
      exact hle hm'
    let N : Normalized K S D :=
      ⟨U,hU,hUr,center,by intro s; simp [U,hcenter],m,v0,v1,hU0,hU1,hU2⟩
    exact ofPost E T center (N.classification hS)
  · have hr : ∀ s, finrank K (LinearMap.range (T s)) ≤ 1 := by
      intro s
      have h := hrank s
      have hs : finrank K (LinearMap.range (T s)) ≠ 2 := fun e => hm ⟨s,e⟩
      omega
    exact Or.inr (Or.inr (rankOneLine T hT center hcenter hr hS))

end RankTwo.PivotCore

/- Post-compression finite-dimensional arguments for L-gct-309.
The row and column forms are bilinear, not Hermitian. -/
namespace RankTwo.Form
open scoped BigOperators
open LinearMap Module

abbrev Pairing (E : Type*) [AddCommGroup E] [Module ℂ E] :=
  E →ₗ[ℂ] E →ₗ[ℂ] ℂ

def Symmetric {E : Type*} [AddCommGroup E] [Module ℂ E] (B : Pairing E) : Prop :=
  ∀ x y, B x y = B y x

def Regular {E : Type*} [AddCommGroup E] [Module ℂ E] (B : Pairing E) : Prop :=
  ∀ x, (∀ y, B x y = 0) → x = 0

section General
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

theorem polar_zero (B : Pairing E) (symm : Symmetric B)
    (W : Submodule ℂ E) (hq : ∀ x ∈ W, B x x = 0)
    (x y : E) (hx : x ∈ W) (hy : y ∈ W) : B x y = 0 := by
  have h := hq (x+y) (W.add_mem hx hy)
  simp only [map_add,LinearMap.add_apply,hq x hx,hq y hy,symm y x,zero_add,add_zero] at h
  have e : (2 : ℂ)*B x y = 0 := by simpa only [two_mul] using h
  exact (mul_eq_zero.mp e).resolve_left two_ne_zero

theorem isotropic_bound (B : Pairing E) (symm : Symmetric B)
    (W : Submodule ℂ E) (hq : ∀ x ∈ W, B x x = 0) :
    2 * finrank ℂ W ≤ finrank ℂ E + finrank ℂ B.ker := by
  let f := B.comp W.subtype
  have into : f.range ≤ W.dualAnnihilator := by
    rintro _ ⟨x,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro y hy
    exact polar_zero B symm W hq x.val y x.prop hy
  have ann := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have rel := Submodule.finrank_mono into
  have dim := f.finrank_range_add_finrank_ker
  have eq : f.ker.map W.subtype = W ⊓ B.ker := by
    dsimp only [f]
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype]
  have le := Submodule.finrank_mono (inf_le_right : W ⊓ B.ker ≤ B.ker)
  rw [←eq,Submodule.finrank_map_subtype_eq] at le
  calc
    2 * finrank ℂ W = finrank ℂ W + finrank ℂ W := by rw [two_mul]
    _ = finrank ℂ W + (finrank ℂ f.range + finrank ℂ f.ker) :=
      congrArg (fun d : Nat => finrank ℂ W + d) dim.symm
    _ ≤ finrank ℂ W + (finrank ℂ W.dualAnnihilator + finrank ℂ B.ker) :=
      Nat.add_le_add_left (Nat.add_le_add rel le) _
    _ = finrank ℂ E + finrank ℂ B.ker :=
      (Nat.add_assoc _ _ _).symm.trans (congrArg (fun d : Nat => d + finrank ℂ B.ker) ann)

theorem regular_ker (B : Pairing E) (nd : Regular B) : B.ker = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply nd
  intro y
  exact LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y

theorem isotropic_bound_nd (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (W : Submodule ℂ E)
    (hq : ∀ x ∈ W, B x x = 0) : 2 * finrank ℂ W ≤ finrank ℂ E := by
  have q := isotropic_bound B symm W hq
  rwa [regular_ker B nd,finrank_bot,add_zero] at q

noncomputable def diag (B : Pairing E) (a b : ℂ) :
    Pairing (E × E) :=
  a • B.compl₁₂ (LinearMap.fst ℂ E E) (LinearMap.fst ℂ E E) +
    b • B.compl₁₂ (LinearMap.snd ℂ E E) (LinearMap.snd ℂ E E)

theorem diag_apply (B : Pairing E) (a b : ℂ) (x y : E × E) :
    diag B a b x y = a * B x.1 y.1 + b * B x.2 y.2 := rfl

theorem diag_symm (B : Pairing E) (hs : Symmetric B) (a b : ℂ) :
    Symmetric (diag B a b) := by
  intro x y
  rw [diag_apply,diag_apply,hs x.1 y.1,hs x.2 y.2]

theorem fst_zero_of_ker (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (ha : a ≠ 0) (z : E × E) (hz : z ∈ (diag B a b).ker) : z.1 = 0 := by
  change diag B a b z = 0 at hz
  apply nd
  intro y
  have h := LinearMap.congr_fun hz (y,0)
  rw [diag_apply] at h
  simpa [ha] using h

theorem snd_zero_of_ker (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (hb : b ≠ 0) (z : E × E) (hz : z ∈ (diag B a b).ker) : z.2 = 0 := by
  change diag B a b z = 0 at hz
  apply nd
  intro y
  have h := LinearMap.congr_fun hz (0,y)
  rw [diag_apply] at h
  simpa [hb] using h

theorem diag_ker_bound (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (ha : a ≠ 0) :
    finrank ℂ (diag B a b).ker ≤ finrank ℂ E := by
  let K := (diag B a b).ker
  let pr : K →ₗ[ℂ] E := (LinearMap.snd ℂ E E).comp K.subtype
  have inj : Function.Injective pr := by
    intro u v e
    apply Subtype.ext
    apply Prod.ext
    · exact (fst_zero_of_ker B nd a b ha u.val u.prop).trans
        (fst_zero_of_ker B nd a b ha v.val v.prop).symm
    · exact e
  exact LinearMap.finrank_le_finrank_of_injective inj

theorem diag_isotropic_bound (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (a b : ℂ) (ha : a ≠ 0)
    (L : Submodule ℂ (E × E))
    (hq : ∀ z ∈ L, a * B z.1 z.1 + b * B z.2 z.2 = 0) :
    2 * finrank ℂ L ≤ 3 * finrank ℂ E := by
  have h := isotropic_bound (diag B a b) (diag_symm B symm a b) L (by
    intro z hz
    rw [diag_apply]
    exact hq z hz)
  have r := diag_ker_bound B nd a b ha
  rw [Module.finrank_prod] at h
  omega

theorem diag_isotropic_bound_regular (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (L : Submodule ℂ (E × E))
    (hq : ∀ z ∈ L, a * B z.1 z.1 + b * B z.2 z.2 = 0) :
    finrank ℂ L ≤ finrank ℂ E := by
  have ker : (diag B a b).ker = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    exact Prod.ext (fst_zero_of_ker B nd a b ha z hz) (snd_zero_of_ker B nd a b hb z hz)
  have h := isotropic_bound (diag B a b) (diag_symm B symm a b) L (by
    intro z hz
    rw [diag_apply]
    exact hq z hz)
  rw [ker,finrank_bot,add_zero,Module.finrank_prod] at h
  omega
end General

noncomputable def dots (n : Nat) : Pairing (Fin n → ℂ) :=
  dotProductBilin ℂ ℂ

theorem dots_eval (n : Nat) (x y : Fin n → ℂ) :
    dots n x y = ∑ i, x i * y i := rfl

theorem dots_symm (n : Nat) : Symmetric (dots n) := by
  intro x y
  change dotProduct x y = dotProduct y x
  exact dotProduct_comm x y

theorem dots_regular (n : Nat) : Regular (dots n) := by
  intro x h
  funext i
  have z := h (Pi.single i (1 : ℂ))
  change dotProduct x (Pi.single i 1) = 0 at z
  rwa [dotProduct_single_one] at z

def ones (n : Nat) : Fin n → ℂ := fun _ => 1

noncomputable def sumLin (n : Nat) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i : Fin n, LinearMap.proj i

theorem sumLin_eval (n : Nat) (x : Fin n → ℂ) : sumLin n x = ∑ i, x i := by
  simp [sumLin]

noncomputable def centered (n : Nat) : Submodule ℂ (Fin n → ℂ) := (sumLin n).ker

theorem centered_mem (n : Nat) (x : Fin n → ℂ) :
    x ∈ centered n ↔ ∑ i, x i = 0 := by
  rw [centered,LinearMap.mem_ker,sumLin_eval]

theorem sum_ones (n : Nat) : sumLin n (ones n) = (n : ℂ) := by
  simp [sumLin_eval,ones]

theorem centered_rank (n : Nat) (h : 0 < n) : finrank ℂ (centered n) = n - 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)
  have onto : Function.Surjective (sumLin n) := by
    intro x
    refine ⟨(x/(n : ℂ)) • ones n,?_⟩
    rw [map_smul,sum_ones,smul_eq_mul]
    exact div_mul_cancel₀ x hn
  have d := (sumLin n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto,finrank_top,finrank_self,Module.finrank_pi,Fintype.card_fin] at d
  change 1 + finrank ℂ (centered n) = n at d
  omega

noncomputable def centerDot (n : Nat) : Pairing (centered n) :=
  (dots n).compl₁₂ (centered n).subtype (centered n).subtype

theorem centerDot_symm (n : Nat) : Symmetric (centerDot n) :=
  fun x y => dots_symm n x.val y.val

theorem centerDot_regular (n : Nat) (h : 0 < n) : Regular (centerDot n) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)
  intro x orth
  apply Subtype.ext
  apply dots_regular n
  intro y
  let a := sumLin n y/(n : ℂ)
  let y' := y-a • ones n
  have ok : y' ∈ centered n := by
    change sumLin n (y-a • ones n) = 0
    rw [map_sub,map_smul,sum_ones,smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (sumLin n y) hn).symm
  have base : dots n x.val y' = 0 := orth ⟨y',ok⟩
  have ref : dots n x.val (ones n) = 0 := by
    simpa [dots_eval,ones] using (centered_mem n x.val).mp x.prop
  have e : y = y' + a • ones n := (sub_add_cancel y (a • ones n)).symm
  calc
    dots n x.val y = dots n x.val (y' + a • ones n) := congrArg (dots n x.val) e
    _ = 0 := by rw [map_add,map_smul,base,ref,smul_zero,zero_add]

end RankTwo.Form

namespace RankTwo.Form
open LinearMap Module

abbrev Mat (m n : Nat) := Matrix (Fin m) (Fin n) ℂ
abbrev Vec (n : Nat) := Fin n → ℂ

noncomputable def outer (a : Vec m) (x : Vec n) : Mat m n :=
  Matrix.vecMulVec a x

noncomputable def alongColumn (a : Vec m) : Vec n →ₗ[ℂ] Mat m n :=
  (vecMulVecBilin ℂ ℂ : Vec m →ₗ[ℂ] Vec n →ₗ[ℂ] Mat m n) a

noncomputable def alongRow (b : Vec n) : Vec m →ₗ[ℂ] Mat m n :=
  (vecMulVecBilin ℂ ℂ : Vec m →ₗ[ℂ] Vec n →ₗ[ℂ] Mat m n).flip b

theorem alongColumn_eval (a : Vec m) (x : Vec n) : alongColumn a x = outer a x := rfl
theorem alongRow_eval (b : Vec n) (y : Vec m) : alongRow b y = outer y b := rfl
theorem outer_apply (a : Vec m) (x : Vec n) (i : Fin m) (j : Fin n) :
    outer a x i j = a i * x j := rfl

theorem column_injective (a : Vec m) (ha : a ≠ 0) :
    Function.Injective (alongColumn (n := n) a) := by
  classical
  have useful : ∃ i, a i ≠ 0 := by
    by_contra z
    apply ha
    funext i
    exact Classical.byContradiction (fun fi => z ⟨i,fi⟩)
  obtain ⟨i,hi⟩ := useful
  intro x y h
  funext j
  have e := congrArg (fun A : Mat m n => A i j) h
  change a i * x j = a i * y j at e
  exact mul_left_cancel₀ hi e

noncomputable def fiber (L : Submodule ℂ (Mat m n)) (a : Vec m) :
    Submodule ℂ (Vec n) := L.comap (alongColumn a)

theorem fiber_exact (L : Submodule ℂ (Mat m n)) (a : Vec m) :
    (fiber L a).map (alongColumn a) = L ⊓ (alongColumn a).range := by
  ext A
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx,⟨x,rfl⟩⟩
  · rintro ⟨hh,⟨x,he⟩⟩
    exact ⟨x,by change alongColumn a x ∈ L; rw [he]; exact hh,he⟩

theorem fiber_dimension (L : Submodule ℂ (Mat m n)) (a : Vec m) (ha : a ≠ 0) :
    finrank ℂ (fiber L a) = finrank ℂ (L ⊓ (alongColumn a).range : Submodule ℂ (Mat m n)) := by
  rw [← fiber_exact L a]
  exact (Submodule.equivMapOfInjective _ (column_injective a ha) _).finrank_eq

/-- Abstract dimension consequence of a rank-(1,1) compression. -/
theorem dim_compressed {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (L C R : Submodule ℂ E) (ls : L ≤ C ⊔ R)
    (r : finrank ℂ R ≤ 3) (h : 1 ≤ finrank ℂ (C ⊓ R : Submodule ℂ E)) :
    finrank ℂ L ≤ finrank ℂ (L ⊓ C : Submodule ℂ E) + 2 := by
  have t : L ⊔ C ≤ C ⊔ R := sup_le ls le_sup_left
  have f := Submodule.finrank_mono t
  have s := Submodule.finrank_sup_add_finrank_inf_eq L C
  have q := Submodule.finrank_sup_add_finrank_inf_eq C R
  omega

theorem mixed_first {n : Nat} (n5 : 5 ≤ n) (L : Submodule ℂ (Mat 4 n))
    (a : centered 4) (ha : (a : Vec 4) ≠ 0) (b : Vec n)
    (contains : ∀ X ∈ L, ∃ x : Vec n, ∃ y : centered 4,
      X = outer a.val x + outer y.val b) :
    ∃ (u : Vec 4) (K : Submodule ℂ (Vec n)), u ≠ 0 ∧
      2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
      ∀ x ∈ K, (fun i j => u i * x j) ∈ L := by
  let C : Submodule ℂ (Mat 4 n) := (alongColumn a.val).range
  let R : Submodule ℂ (Mat 4 n) := ((alongRow b).comp (centered 4).subtype).range
  let K := fiber L a.val
  have clear : finrank ℂ K = finrank ℂ (L ⊓ C : Submodule ℂ (Mat 4 n)) :=
    fiber_dimension L a.val ha
  refine ⟨a.val,K,ha,?_,?_⟩
  · by_cases bz : b = 0
    · have good : L ≤ C := by
        intro X hx
        obtain ⟨x,y,h⟩ := contains X hx
        refine ⟨x,?_⟩
        rw [alongColumn_eval,h,bz]
        simp [outer]
      have e : L ⊓ C = L := inf_eq_left.mpr good
      rw [e] at clear
      omega
    · have range_dim : finrank ℂ R ≤ 3 := by
        let f : centered 4 →ₗ[ℂ] Mat 4 n := (alongRow b).comp (centered 4).subtype
        calc
          finrank ℂ R ≤ finrank ℂ R + finrank ℂ f.ker := Nat.le_add_right _ _
          _ = finrank ℂ (centered 4) :=
            LinearMap.finrank_range_add_finrank_ker (K := ℂ)
              (V := ↥(centered 4)) (V₂ := Mat 4 n) f
          _ = 3 := centered_rank 4 (by decide)
      have cap : L ≤ C ⊔ R := by
        intro X hx
        obtain ⟨x,y,h⟩ := contains X hx
        rw [h]
        exact Submodule.add_mem_sup (show outer a.val x ∈ C from ⟨x,rfl⟩)
          (show outer y.val b ∈ R from ⟨y,rfl⟩)
      have joint : outer a.val b ∈ C ⊓ R := ⟨⟨b,rfl⟩,⟨a,rfl⟩⟩
      have nz : outer a.val b ≠ 0 := by
        intro eq
        apply bz
        apply column_injective a.val ha
        change outer a.val b = alongColumn a.val 0
        rw [map_zero,eq]
      have line : ℂ ∙ outer a.val b ≤ C ⊓ R :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr joint
      have bound := Submodule.finrank_mono line
      rw [finrank_span_singleton nz] at bound
      have d := dim_compressed L C R cap range_dim bound
      omega
  · intro x hx
    exact hx

end RankTwo.Form

namespace RankTwo.Form
open LinearMap Module
open scoped BigOperators

noncomputable def qMat (X : Mat m n) : ℂ := ∑ i, ∑ j, (X i j)^2

theorem q_two_columns (a b : Vec m) (x y : Vec n) (ort : dots m a b = 0) :
    qMat (outer a x + outer b y) =
      dots m a a * dots n x x + dots m b b * dots n y y := by
  calc
    _ = ∑ i, ((a i*a i)*dots n x x + (b i*b i)*dots n y y +
        (a i*b i)*(2*dots n x y)) := by
      unfold qMat
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ j, ((a i*a i)*(x j*x j) + (b i*b i)*(y j*y j) +
            (a i*b i)*(2*(x j*y j))) := by
          apply Finset.sum_congr rfl
          intro j _
          change (a i*x j + b i*y j)^2 = _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib,dots_eval,← Finset.mul_sum]
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_mul,← dots_eval,ort,zero_mul,add_zero]

theorem q_transpose (X : Mat m n) : qMat X.transpose = qMat X := by
  unfold qMat
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

theorem q_two_rows (a b : Vec n) (x y : Vec m) (ort : dots n a b = 0) :
    qMat (outer x a + outer y b) = dots n a a * dots m x x + dots n b b * dots m y y := by
  have flip : (outer x a + outer y b).transpose = outer a x + outer b y := by
    ext i j
    change x j*a i + y j*b i = a i*x j + b i*y j
    rw [mul_comm (x j),mul_comm (y j)]
  rw [← q_transpose (outer x a + outer y b),flip]
  exact q_two_columns a b x y ort

noncomputable def cols (a b : Vec m) : centered n × centered n →ₗ[ℂ] Mat m n :=
  ((alongColumn a).comp (centered n).subtype).comp (LinearMap.fst ℂ _ _) +
    ((alongColumn b).comp (centered n).subtype).comp (LinearMap.snd ℂ _ _)

noncomputable def rows (a b : Vec n) : centered m × centered m →ₗ[ℂ] Mat m n :=
  ((alongRow a).comp (centered m).subtype).comp (LinearMap.fst ℂ _ _) +
    ((alongRow b).comp (centered m).subtype).comp (LinearMap.snd ℂ _ _)

theorem cols_eval (a b : Vec m) (x y : centered n) :
    cols a b (x,y) = outer a x.val + outer b y.val := rfl

theorem rows_eval (a b : Vec n) (x y : centered m) :
    rows a b (x,y) = outer x.val a + outer y.val b := rfl

theorem comap_bound {E V : Type*} [AddCommGroup E] [AddCommGroup V]
    [Module ℂ E] [Module ℂ V] [FiniteDimensional ℂ E]
    (f : E →ₗ[ℂ] V) (L : Submodule ℂ V)
    (onto : ∀ x ∈ L, ∃ z, f z = x) :
    finrank ℂ L ≤ finrank ℂ (L.comap f) := by
  have e : (L.comap f).map f = L := by
    ext x; constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hx
      obtain ⟨z,hz⟩ := onto x hx
      exact ⟨z,by change f z ∈ L; rw [hz]; exact hx,hz⟩
  have d := Submodule.finrank_map_le f (L.comap f)
  rwa [e] at d

theorem q_cols_comap (L : Submodule ℂ (Mat m n)) (a b : Vec m)
    (ort : dots m a b = 0) (hq : ∀ X ∈ L, qMat X = 0) :
    ∀ z ∈ L.comap (cols a b), dots m a a * centerDot n z.1 z.1 +
      dots m b b * centerDot n z.2 z.2 = 0 := by
  rintro ⟨x,y⟩ hz
  have h := hq _ (show cols a b (x,y) ∈ L from hz)
  rw [cols_eval,q_two_columns a b _ _ ort] at h
  exact h

theorem q_rows_comap (L : Submodule ℂ (Mat m n)) (a b : Vec n)
    (ort : dots n a b = 0) (hq : ∀ X ∈ L, qMat X = 0) :
    ∀ z ∈ L.comap (rows a b), dots n a a * centerDot m z.1 z.1 +
      dots n b b * centerDot m z.2 z.2 = 0 := by
  rintro ⟨x,y⟩ hz
  have h := hq _ (show rows a b (x,y) ∈ L from hz)
  rw [rows_eval,q_two_rows a b _ _ ort] at h
  exact h

theorem regular_columns_impossible {n : Nat} (n0 : 0 < n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L) (a b : Vec 4)
    (ort : dots 4 a b = 0) (ap : dots 4 a a ≠ 0) (bp : dots 4 b b ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered n, X = outer a x.val + outer b y.val)
    (hq : ∀ X ∈ L, qMat X = 0) : False := by
  have big := comap_bound (cols a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have d := diag_isotropic_bound_regular (centerDot n) (centerDot_symm n)
    (centerDot_regular n n0) _ _ ap bp _ (q_cols_comap L a b ort hq)
  rw [centered_rank n n0] at d
  omega

theorem nonisotropic_rows_impossible {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L) (a b : Vec n)
    (ort : dots n a b = 0) (ap : dots n a a ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered 4, X = outer x.val a + outer y.val b)
    (hq : ∀ X ∈ L, qMat X = 0) : False := by
  have big := comap_bound (rows a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have d := diag_isotropic_bound (centerDot 4) (centerDot_symm 4)
    (centerDot_regular 4 (by decide)) _ _ ap _ (q_rows_comap L a b ort hq)
  rw [centered_rank 4 (by decide)] at d
  omega

theorem radical_columns_first {n : Nat} (n0 : 0 < n)
    (L : Submodule ℂ (Mat 4 n)) (a b : Vec 4) (anz : a ≠ 0)
    (ort : dots 4 a b = 0) (null : dots 4 a a = 0) (bp : dots 4 b b ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered n, X = outer a x.val + outer b y.val)
    (hq : ∀ X ∈ L, qMat X = 0) :
    ∃ (u : Vec 4) (K : Submodule ℂ (Vec n)), u ≠ 0 ∧
      2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
      ∀ x ∈ K, (fun i j => u i * x j) ∈ L := by
  let S := L.comap (cols a b)
  let f : S →ₗ[ℂ] centered n := (LinearMap.snd ℂ _ _).comp S.subtype
  let K := fiber L a
  have big : finrank ℂ L ≤ finrank ℂ S := comap_bound (cols a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have fit : ∀ z ∈ f.range, centerDot n z z = 0 := by
    rintro y ⟨z,rfl⟩
    have h := q_cols_comap L a b ort hq z.val z.prop
    rw [null,zero_mul,zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left bp
  have d := isotropic_bound_nd (centerDot n) (centerDot_symm n)
    (centerDot_regular n n0) f.range fit
  rw [centered_rank n n0] at d
  have ker_second (z : f.ker) : z.val.val.2 = 0 := LinearMap.mem_ker.mp z.prop
  let first : f.ker →ₗ[ℂ] Vec n :=
    (centered n).subtype.comp ((LinearMap.fst ℂ _ _).comp (S.subtype.comp f.ker.subtype))
  have hfirst (z : f.ker) : first z ∈ K := by
    have hs : cols a b z.val.val ∈ L := z.val.prop
    have eq : z.val.val = (z.val.val.1,0) := Prod.ext rfl (ker_second z)
    rw [eq,cols_eval] at hs
    change outer a z.val.val.1.val ∈ L
    have hs' : outer a z.val.val.1.val + outer b (0 : Vec n) ∈ L := hs
    simpa [outer] using hs'
  let g : f.ker →ₗ[ℂ] K := first.codRestrict K hfirst
  have gi : Function.Injective g := by
    intro z t ge
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have e := congrArg (fun x : K => x.val) ge
      change z.val.val.1.val = t.val.val.1.val at e
      exact e
    · rw [ker_second z,ker_second t]
  have kcap := LinearMap.finrank_le_finrank_of_injective gi
  have rn := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
    (V := ↥S) (V₂ := ↥(centered n)) f
  refine ⟨a,K,anz,by omega,?_⟩
  intro x hx
  exact hx

end RankTwo.Form

namespace RankTwo.Form
open scoped BigOperators
open LinearMap Module

/-- A subspace of dimension at most two containing a nonisotropic
direction is generated by it and a single orthogonal direction. -/
theorem orthogonal_span_two {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (B : Pairing E) (A : Submodule ℂ E)
    (sm : finrank ℂ A ≤ 2) (b : E) (hb : b ∈ A) (nb : B b b ≠ 0) :
    ∃ a ∈ A, B b a = 0 ∧
      ∀ x ∈ A, ∃ c d : ℂ, x = c • a + d • b := by
  let b' : A := ⟨b,hb⟩
  let f : A →ₗ[ℂ] ℂ := (B b).domRestrict A
  let D := f.ker
  have t : f b' = B b b := rfl
  have surj : Function.Surjective f := by
    intro y
    refine ⟨(y / B b b) • b',?_⟩
    rw [map_smul,t,smul_eq_mul]
    exact div_mul_cancel₀ y nb
  have dim := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj,finrank_top,finrank_self] at dim
  have small : finrank ℂ D ≤ 1 := by change finrank ℂ f.ker ≤ 1; omega
  obtain ⟨a',aSpan⟩ := finrank_le_one_iff.mp small
  let a : E := a'.val.val
  have porth : B b a = 0 := LinearMap.mem_ker.mp a'.prop
  refine ⟨a,a'.val.prop,porth,?_⟩
  intro x hx
  let x' : A := ⟨x,hx⟩
  let d := f x' / B b b
  have kh : x' - d • b' ∈ D := by
    change f (x' - d • b') = 0
    rw [map_sub,map_smul,t,smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (f x') nb).symm
  obtain ⟨c,cv⟩ := aSpan ⟨x' - d • b',kh⟩
  have cve : c • a'.val = x' - d • b' := congrArg Subtype.val cv
  refine ⟨c,d,?_⟩
  have xy : c • a'.val + d • b' = x' := by rw [cve,sub_add_cancel]
  exact (congrArg Subtype.val xy).symm

end RankTwo.Form

namespace RankTwo.Form
open scoped BigOperators
open LinearMap Module

def First {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ (a : Vec 4) (K : Submodule ℂ (Vec n)), a ≠ 0 ∧
    2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
    (∀ x ∈ K, (fun i j => a i * x j) ∈ L)

def Second {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ U : Submodule ℂ (Vec n), finrank ℂ U = 2 ∧
    (∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^2) = 0) ∧
    (∀ X ∈ L, ∀ i, X i ∈ U)

def ColCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ a b : centered 4, LinearIndependent ℂ ![a,b] ∧
    ∀ X ∈ L, ∃ x y : centered n, X = outer a.val x.val + outer b.val y.val

def RowCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ a b : centered n, LinearIndependent ℂ ![a,b] ∧
    ∀ X ∈ L, ∃ x y : centered 4, X = outer x.val a.val + outer y.val b.val

def MixedCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ (a : centered 4) (b : centered n), a.val ≠ 0 ∧
    ∀ X ∈ L, ∃ x : centered n, ∃ y : centered 4, X = outer a.val x.val + outer y.val b.val

theorem spanTwo_finrank {E : Type*} [AddCommGroup E] [Module ℂ E] {a b : E}
    (lin : LinearIndependent ℂ ![a,b]) :
    finrank ℂ (Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E))) = 2 := by
  rw [finrank_span_eq_card lin,Fintype.card_fin]

theorem spanTwo_left {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E) :
    a ∈ Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E)) :=
  Submodule.subset_span ⟨0,rfl⟩

theorem spanTwo_right {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E) :
    b ∈ Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E)) :=
  Submodule.subset_span ⟨1,rfl⟩

theorem change_columns {m n : Nat} (a b p q : centered m)
    (c d e f : ℂ) (ha : a = c • p + d • q) (hb : b = e • p + f • q)
    (x y : centered n) :
    outer a.val x.val + outer b.val y.val =
      outer p.val (c • x + e • y : centered n).val +
      outer q.val (d • x + f • y : centered n).val := by
  apply Matrix.ext
  intro i j
  have ai := congrArg (fun z : centered m => z.val i) ha
  have bi := congrArg (fun z : centered m => z.val i) hb
  change a.val i = c*p.val i + d*q.val i at ai
  change b.val i = e*p.val i + f*q.val i at bi
  change a.val i*x.val j + b.val i*y.val j =
    p.val i*(c*x.val j + e*y.val j) + q.val i*(d*x.val j + f*y.val j)
  rw [ai,bi]
  ring

theorem change_rows {m n : Nat} (a b p q : centered n)
    (c d e f : ℂ) (ha : a = c • p + d • q) (hb : b = e • p + f • q)
    (x y : centered m) :
    outer x.val a.val + outer y.val b.val =
      outer (c • x + e • y : centered m).val p.val +
      outer (d • x + f • y : centered m).val q.val := by
  apply Matrix.ext
  intro i j
  have aj := congrArg (fun z : centered n => z.val j) ha
  have bj := congrArg (fun z : centered n => z.val j) hb
  change a.val j = c*p.val j + d*q.val j at aj
  change b.val j = e*p.val j + f*q.val j at bj
  change x.val i*a.val j + y.val i*b.val j =
    (c*x.val i + e*y.val i)*p.val j + (d*x.val i + f*y.val i)*q.val j
  rw [aj,bj]
  ring

theorem generators_independent_direction {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (A : Submodule ℂ E) (dim : finrank ℂ A = 2)
    (p q : E) (qq : q ≠ 0) (sp : ∀ x ∈ A, ∃ c d : ℂ, x = c • p + d • q) :
    p ≠ 0 := by
  intro p0
  have small : A ≤ ℂ ∙ q := by
    intro x hx
    obtain ⟨_c,d,ex⟩ := sp x hx
    apply Submodule.mem_span_singleton.mpr
    exact ⟨d,by simpa [p0] using ex.symm⟩
  have nu := Submodule.finrank_mono small
  rw [dim,finrank_span_singleton qq] at nu
  omega

theorem column_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, qMat X = 0) (covered : ColCompression L) :
    First L := by
  obtain ⟨a,b,li,coords⟩ := covered
  let A := Submodule.span ℂ (Set.range (![a,b] : Fin 2 → centered 4))
  have dim : finrank ℂ A = 2 := spanTwo_finrank li
  have qExists : ∃ q ∈ A, centerDot 4 q q ≠ 0 := by
    classical
    by_contra no
    have zero : ∀ q ∈ A, centerDot 4 q q = 0 := by
      intro q hn
      exact Classical.byContradiction (fun hz => no ⟨q,hn,hz⟩)
    have cap := isotropic_bound_nd (centerDot 4) (centerDot_symm 4)
      (centerDot_regular 4 (by decide)) A zero
    rw [dim,centered_rank 4 (by decide)] at cap
    omega
  obtain ⟨q,qA,qN⟩ := qExists
  obtain ⟨p,_,ort,sp⟩ := orthogonal_span_two (centerDot 4) A (by omega) q qA qN
  obtain ⟨c,d,ha⟩ := sp a (spanTwo_left a b)
  obtain ⟨e,f,hb⟩ := sp b (spanTwo_right a b)
  have qnz : q ≠ 0 := by intro bz; apply qN; simp [bz]
  have pnz := generators_independent_direction A dim p q qnz sp
  have pv : p.val ≠ 0 := fun z => pnz (Subtype.ext z)
  have ort' : dots 4 p.val q.val = 0 := (dots_symm 4 p.val q.val).trans ort
  have newCoords (X : Mat 4 n) (inL : X ∈ L) :
      ∃ x y : centered n, X = outer p.val x.val + outer q.val y.val := by
    obtain ⟨x,y,h⟩ := coords X inL
    exact ⟨c • x + e • y,d • x + f • y,h.trans (change_columns a b p q c d e f ha hb x y)⟩
  by_cases hz : dots 4 p.val p.val = 0
  · exact radical_columns_first (by omega) L p.val q.val pv ort' hz qN newCoords hq
  · exact False.elim (regular_columns_impossible (by omega) L large p.val q.val ort' hz qN newCoords hq)

theorem row_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, qMat X = 0) (covered : RowCompression L) :
    Second L := by
  classical
  obtain ⟨a,b,li,coords⟩ := covered
  let A := Submodule.span ℂ (Set.range (![a,b] : Fin 2 → centered n))
  have dim : finrank ℂ A = 2 := spanTwo_finrank li
  let U := A.map (centered n).subtype
  by_cases qExists : ∃ q ∈ A, centerDot n q q ≠ 0
  · obtain ⟨q,qA,qN⟩ := qExists
    obtain ⟨p,_,ort,sp⟩ := orthogonal_span_two (centerDot n) A (by omega) q qA qN
    obtain ⟨c,d,ha⟩ := sp a (spanTwo_left a b)
    obtain ⟨e,f,hb⟩ := sp b (spanTwo_right a b)
    have newCoords (X : Mat 4 n) (inL : X ∈ L) :
        ∃ x y : centered 4, X = outer x.val q.val + outer y.val p.val := by
      obtain ⟨x,y,h⟩ := coords X inL
      refine ⟨d • x + f • y,c • x + e • y,?_⟩
      exact h.trans ((change_rows a b p q c d e f ha hb x y).trans (add_comm _ _))
    exact False.elim (nonisotropic_rows_impossible n5 L large q.val p.val ort qN newCoords hq)
  · have zero : ∀ q ∈ A, centerDot n q q = 0 := by
      intro q hn
      exact Classical.byContradiction (fun hz => qExists ⟨q,hn,hz⟩)
    have size : finrank ℂ U = 2 := by
      simpa only [U,Submodule.finrank_map_subtype_eq] using dim
    refine ⟨U,size,?_,?_⟩
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨(centered_mem n x.val).mp x.prop,?_⟩
      have d := zero x hx
      change dots n x.val x.val = 0 at d
      change (∑ j, (x.val j)^2) = 0
      simpa only [dots_eval,pow_two] using d
    · intro X inL i
      obtain ⟨x,y,showX⟩ := coords X inL
      let z : centered n := x.val i • a + y.val i • b
      have zA : z ∈ A := A.add_mem (A.smul_mem _ (spanTwo_left a b)) (A.smul_mem _ (spanTwo_right a b))
      refine ⟨z,zA,?_⟩
      funext j
      rw [showX]
      rfl

theorem mixed_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (covered : MixedCompression L) : First L := by
  obtain ⟨a,b,az,coords⟩ := covered
  apply mixed_first n5 L a az b.val
  intro X inL
  obtain ⟨x,y,h⟩ := coords X inL
  exact ⟨x.val,y,h⟩

theorem postcompression {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, (∑ i, ∑ j, (X i j)^2) = 0)
    (shape : ColCompression L ∨ RowCompression L ∨ MixedCompression L) :
    First L ∨ Second L := by
  rcases shape with cols|rows|mixed
  · exact Or.inl (column_finish n5 L large hq cols)
  · exact Or.inr (row_finish n5 L large hq rows)
  · exact Or.inl (mixed_finish n5 L mixed)

end RankTwo.Form

open Module
open scoped BigOperators

namespace RankTwo.Bridge
open RankTwo.PivotCore
open RankTwo.Form


abbrev Domain (n : Nat) := Fin n → ℂ

noncomputable def act {n : Nat} (L : Submodule ℂ (Mat 4 n))
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) :
    L →ₗ[ℂ] Domain n →ₗ[ℂ] centered 4 where
  toFun X := LinearMap.codRestrict (centered 4) X.val.mulVecLin (by
    intro v
    rw [centered_mem]
    simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hcols X.val X.prop,zero_mul]
    simp)
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (X.val+Y.val).mulVecLin v = X.val.mulVecLin v+Y.val.mulVecLin v
    rw [Matrix.mulVecLin_add,LinearMap.add_apply]
  map_smul' r X := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (r • X.val).mulVecLin v = r • X.val.mulVecLin v
    exact Matrix.smul_mulVec r X.val v

theorem act_coe {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    {hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0} (X : L) (v : Domain n) :
    (act L hcols X v).val = X.val.mulVecLin v := rfl

theorem act_single {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    {hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0} (X : L) (i : Fin 4) (j : Fin n) :
    (act L hcols X (Pi.single j 1)).val i = X.val i j := by
  rw [act_coe,Matrix.mulVecLin_apply,Matrix.mulVec_single_one]
  rfl

theorem act_inj {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) : Function.Injective (act L hcols) := by
  intro X Y h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  simpa only [act_single] using
    congrArg (fun F : Domain n →ₗ[ℂ] centered 4 => (F (Pi.single j 1)).val i) h

theorem act_center {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hrows : ∀ X ∈ L, ∀ i, (∑ j, X i j) = 0)
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) (X : L) :
    act L hcols X (ones n) = 0 := by
  apply Subtype.ext
  funext i
  simp [act_coe,ones,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,hrows X.val X.prop i]

theorem act_rank {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) (X : L) :
    Module.finrank ℂ (LinearMap.range (act L hcols X)) = X.val.rank := by
  change _ = finrank ℂ (LinearMap.range X.val.mulVecLin)
  have h : (centered 4).subtype.comp (act L hcols X) = X.val.mulVecLin := rfl
  rw [← h,LinearMap.range_comp,Submodule.finrank_map_subtype_eq]

noncomputable def asProfile {n : Nat} (f : Domain n →ₗ[ℂ] ℂ) (hf : f (ones n) = 0) : centered n := by
  let e := dotProductEquiv ℂ (Fin n)
  refine ⟨e.symm f,?_⟩
  rw [centered_mem]
  have h : e (e.symm f) (ones n) = 0 := by rw [e.apply_symm_apply,hf]
  change dotProduct (e.symm f) (ones n) = 0 at h
  simpa [dotProduct,ones] using h

theorem asProfile_single {n : Nat} (f : Domain n →ₗ[ℂ] ℂ) (hf : f (ones n) = 0)
    (j : Fin n) :
    (asProfile f hf).val j = f (Pi.single j 1) := by
  have h := LinearEquiv.apply_symm_apply (dotProductEquiv ℂ (Fin n)) f
  have hx := LinearMap.congr_fun h (Pi.single j 1)
  change dotProduct (asProfile f hf).val (Pi.single j 1) = _ at hx
  rwa [dotProduct_single_one] at hx

theorem independentProfiles {n : Nat} {f g : Domain n →ₗ[ℂ] ℂ}
    (hf : f (ones n) = 0) (hg : g (ones n) = 0)
    (h : LinearIndependent ℂ ![f,g]) :
    LinearIndependent ℂ ![asProfile f hf,asProfile g hg] := by
  let e := (dotProductEquiv ℂ (Fin n)).symm
  have h' := h.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  apply LinearIndependent.of_comp (centered n).subtype
  convert h' using 1
  funext i
  fin_cases i <;> rfl

theorem shapes {n : Nat} (L : Submodule ℂ (Mat 4 n))
    (hc : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0)
    (h : ThreeShapes (act L hc) (ones n)) :
    ColCompression L ∨ RowCompression L ∨ MixedCompression L := by
  rcases h with h|h|h
  · obtain ⟨a,b,hab,h⟩ := h
    refine Or.inl ⟨a,b,hab,?_⟩
    intro X hX
    obtain ⟨f,g,hf,hg,h⟩ := h ⟨X,hX⟩
    refine ⟨asProfile f hf,asProfile g hg,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e
  · obtain ⟨f,g,hf,hg,hi,h⟩ := h
    refine Or.inr (Or.inl ⟨asProfile f hf,asProfile g hg,independentProfiles hf hg hi,?_⟩)
    intro X hX
    obtain ⟨a,b,h⟩ := h ⟨X,hX⟩
    refine ⟨a,b,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e
  · obtain ⟨a,b,ha,_,hb,h⟩ := h
    refine Or.inr (Or.inr ⟨a,asProfile b hb,?_,?_⟩)
    · intro hz
      exact ha (Subtype.ext hz)
    intro X hX
    obtain ⟨f,y,hf,h⟩ := h ⟨X,hX⟩
    refine ⟨asProfile f hf,y,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e

theorem bridge {n : Nat} (n5 : 5 ≤ n) (L : Submodule ℂ (Mat 4 n))
    (large : n ≤ finrank ℂ L)
    (hrows : ∀ X ∈ L, ∀ i, (∑ j, X i j) = 0)
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0)
    (hquad : ∀ X ∈ L, (∑ i, ∑ j, (X i j)^2) = 0)
    (hr : ∀ X ∈ L, X.rank ≤ 2) : First L ∨ Second L := by
  apply postcompression n5 L large hquad
  apply shapes L hcols
  apply classifySpace (act L hcols) (act_inj hcols) (ones n) (act_center hrows hcols)
  · intro X
    rw [act_rank hcols X]
    exact hr X.val X.prop
  · simpa using centered_rank 4 (by decide)
  · omega

end RankTwo.Bridge

theorem RankTwo : ∀ (n : ℕ), 5 ≤ n → ∀ L : Submodule ℂ (Matrix (Fin 4) (Fin n) ℂ),
  n ≤ Module.finrank ℂ L →
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ i, ∑ j, (X i j)^2) = 0 ∧ X.rank ≤ 2) →
  (∃ (a : Fin 4 → ℂ) (K : Submodule ℂ (Fin n → ℂ)), a ≠ 0 ∧
    2 * Module.finrank ℂ L + 1 ≤ 2 * Module.finrank ℂ K + n ∧
    (∀ x ∈ K, (fun i j => a i * x j) ∈ L)) ∨
  (∃ U : Submodule ℂ (Fin n → ℂ), Module.finrank ℂ U = 2 ∧
    (∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^2) = 0) ∧
    (∀ X ∈ L, ∀ i, X i ∈ U)) := by
  intro n n5 L large hypotheses
  exact RankTwo.Bridge.bridge n5 L large
    (fun X hX => (hypotheses X hX).1)
    (fun X hX => (hypotheses X hX).2.1)
    (fun X hX => (hypotheses X hX).2.2.1)
    (fun X hX => (hypotheses X hX).2.2.2)

end Reuse309

section Reuse312

namespace RankOne

open Finset

noncomputable def D (n m : ℕ) (g : Fin m → Fin n → ℂ) : ℂ :=
  ∑ f : Fin m ↪ Fin n, ∏ k, g k (f k)

lemma D_zero (n : ℕ) (g : Fin 0 → Fin n → ℂ) : D n 0 g = 1 := by
  simp [D]

lemma sum_not_range {n m : ℕ} (f : Fin m ↪ Fin n) (h : Fin n → ℂ) :
    ∑ i : {i // i ∉ Set.range f}, h i = (∑ i, h i) - ∑ k, h (f k) := by
  rw [eq_sub_iff_add_eq]
  have h1 : ∑ i : {i // i ∉ Set.range f}, h i =
      ∑ i ∈ univ.filter (fun i => i ∉ Set.range f), h i :=
    (Finset.sum_subtype _ (fun i => by simp) h).symm
  have h2 : ∑ k, h (f k) = ∑ i ∈ univ.filter (fun i => i ∈ Set.range f), h i := by
    have : univ.filter (fun i => i ∈ Set.range f) = univ.map f := by
      ext i; simp
    rw [this, Finset.sum_map]
  rw [h1, h2, add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

lemma prod_update {m n : ℕ} (t : Fin m → Fin n → ℂ) (g0 : Fin n → ℂ) (f : Fin m → Fin n)
    (k0 : Fin m) :
    ∏ k, (Function.update t k0 (t k0 * g0)) k (f k) = (∏ k, t k (f k)) * g0 (f k0) := by
  have : ∀ k, (Function.update t k0 (t k0 * g0)) k (f k) =
      t k (f k) * (if k = k0 then g0 (f k0) else 1) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp
    · simp [hk]
  simp_rw [this, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

lemma D_succ (n m : ℕ) (g : Fin (m + 1) → Fin n → ℂ) :
    D n (m + 1) g = (∑ i, g 0 i) * D n m (Fin.tail g) -
      ∑ k : Fin m, D n m (Function.update (Fin.tail g) k (Fin.tail g k * g 0)) := by
  unfold D
  rw [← (Equiv.embeddingFinSucc m (Fin n)).symm.sum_comp, Fintype.sum_sigma]
  simp only [Equiv.coe_embeddingFinSucc_symm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp_rw [prod_update]
  have inner : ∀ f : Fin m ↪ Fin n, ∑ i : {i // i ∉ Set.range f}, g 0 i * ∏ k, g k.succ (f k)
      = (∏ k, Fin.tail g k (f k)) * ((∑ i, g 0 i) - ∑ k, g 0 (f k)) := by
    intro f
    rw [← Finset.sum_mul, sum_not_range, mul_comm]; rfl
  simp_rw [inner]
  rw [Finset.sum_comm (f := fun k (f : Fin m ↪ Fin n) => (∏ k, Fin.tail g k (f k)) * g 0 (f k))]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro f _; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

lemma D_one (n : ℕ) (g : Fin 1 → Fin n → ℂ) : D n 1 g = ∑ i, g 0 i := by
  rw [D_succ, D_zero]; simp

lemma D_two (n : ℕ) (g : Fin 2 → Fin n → ℂ) :
    D n 2 g = (∑ i, g 0 i) * (∑ i, g 1 i) - ∑ i, g 1 i * g 0 i := by
  rw [D_succ, D_one]; simp [D_one, Fin.tail]

lemma msum {n : ℕ} (x : Fin n → ℂ) (c0 c1 c2 c3 c4 : ℂ) :
    ∑ j, (c0 + c1 * x j + c2 * x j ^ 2 + c3 * x j ^ 3 + c4 * x j ^ 4) =
      c0 * n + c1 * (∑ j, x j) + c2 * (∑ j, x j ^ 2) + c3 * (∑ j, x j ^ 3) +
        c4 * (∑ j, x j ^ 4) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

lemma L1 {n : ℕ} (x : Fin n → ℂ) (u : ℂ) :
    ∑ j, (1 + u * x j) = n + u * (∑ j, x j) := by
  have := msum x 1 u 0 0 0
  simp only [zero_mul, add_zero, one_mul] at this
  rw [← this]

lemma L2 {n : ℕ} (x : Fin n → ℂ) (u v : ℂ) :
    ∑ j, (1 + u * x j) * (1 + v * x j) =
      n + (u + v) * (∑ j, x j) + u * v * (∑ j, x j ^ 2) := by
  rw [Finset.sum_congr rfl (fun j _ => show (1 + u * x j) * (1 + v * x j) =
    1 + (u + v) * x j + u * v * x j ^ 2 + 0 * x j ^ 3 + 0 * x j ^ 4 by ring), msum]
  ring

lemma L3 {n : ℕ} (x : Fin n → ℂ) (u v w : ℂ) :
    ∑ j, (1 + u * x j) * ((1 + v * x j) * (1 + w * x j)) =
      n + (u + v + w) * (∑ j, x j) + (u * v + u * w + v * w) * (∑ j, x j ^ 2) +
        u * v * w * (∑ j, x j ^ 3) := by
  rw [Finset.sum_congr rfl (fun j _ => show (1 + u * x j) * ((1 + v * x j) * (1 + w * x j)) =
    1 + (u + v + w) * x j + (u * v + u * w + v * w) * x j ^ 2 + u * v * w * x j ^ 3 +
      0 * x j ^ 4 by ring), msum]
  ring

lemma L4 {n : ℕ} (x : Fin n → ℂ) (u v w z : ℂ) :
    ∑ j, (1 + u * x j) * ((1 + v * x j) * ((1 + w * x j) * (1 + z * x j))) =
      n + (u + v + w + z) * (∑ j, x j) +
        (u * v + u * w + u * z + v * w + v * z + w * z) * (∑ j, x j ^ 2) +
        (u * v * w + u * v * z + u * w * z + v * w * z) * (∑ j, x j ^ 3) +
        u * v * w * z * (∑ j, x j ^ 4) := by
  rw [Finset.sum_congr rfl (fun j _ => show
    (1 + u * x j) * ((1 + v * x j) * ((1 + w * x j) * (1 + z * x j))) =
    1 + (u + v + w + z) * x j + (u * v + u * w + u * z + v * w + v * z + w * z) * x j ^ 2 +
      (u * v * w + u * v * z + u * w * z + v * w * z) * x j ^ 3 + u * v * w * z * x j ^ 4
      by ring), msum]
  ring

def E2 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 + a 0 * a 2 + a 0 * a 3 + a 1 * a 2 + a 1 * a 3 + a 2 * a 3
def E3 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 * a 2 + a 0 * a 1 * a 3 + a 0 * a 2 * a 3 + a 1 * a 2 * a 3
def E4 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 * a 2 * a 3

lemma F_closed (n : ℕ) (a : Fin 4 → ℂ) (x : Fin n → ℂ) (hx : ∑ j, x j = 0) :
    ∑ f : Fin 4 ↪ Fin n, ∏ i, (1 + a i * x (f i)) =
      (n : ℂ) * (n - 1) * (n - 2) * (n - 3) - E2 a * ((n - 2) * (n - 3)) * (∑ j, x j ^ 2) +
        2 * E3 a * (n - 3) * (∑ j, x j ^ 3) +
        E4 a * (3 * (∑ j, x j ^ 2) ^ 2 - 6 * (∑ j, x j ^ 4)) := by
  change D n 4 (fun k j => 1 + a k * x j) = _
  simp [D_succ, D_zero, Fin.sum_univ_succ, Fin.tail, Function.update_apply]
  simp only [mul_assoc, L1, L2, L3, L4, hx, E2, E3, E4]
  ring

lemma iso_core {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0) :
    Module.finrank ℂ K + Module.finrank ℂ K ≤ Module.finrank ℂ W +
      Module.finrank ℂ (LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K)) := by
  set T := W.subtype.dualMap ∘ₗ β.domRestrict K with hT
  set K' : Submodule ℂ W := K.comap W.subtype with hK'
  have hK'r : Module.finrank ℂ K' = Module.finrank ℂ K :=
    (Submodule.comapSubtypeEquivOfLe hKW).finrank_eq
  have hrange : LinearMap.range T ≤ K'.dualAnnihilator := by
    rintro φ ⟨y, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    simp only [hT, LinearMap.comp_apply, LinearMap.dualMap_apply, Submodule.subtype_apply,
      LinearMap.domRestrict_apply]
    exact hiso y y.2 w hw
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq K'
  have h2 := LinearMap.finrank_range_add_finrank_ker T
  have h3 := Submodule.finrank_mono hrange
  omega

lemma iso_bound0 {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0)
    (hrad : ∀ y ∈ K, (∀ z ∈ W, β y z = 0) → y = 0) :
    2 * Module.finrank ℂ K ≤ Module.finrank ℂ W := by
  have h := iso_core W K hKW β hiso
  have : LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have : (y : Fin n → ℂ) = 0 := by
      apply hrad y y.2
      intro z hz
      have := LinearMap.congr_fun hy ⟨z, hz⟩
      simpa using this
    exact Subtype.ext this
  rw [this, finrank_bot] at h
  omega

lemma iso_bound1 {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0) (ψ : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hrad : ∀ y ∈ K, (∀ z ∈ W, β y z = 0) → ψ y = 0 → y = 0) :
    2 * Module.finrank ℂ K ≤ Module.finrank ℂ W + 1 := by
  have h := iso_core W K hKW β hiso
  set R := LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K)
  set L : R →ₗ[ℂ] ℂ := ψ ∘ₗ K.subtype ∘ₗ R.subtype with hL
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have hy0 : ((y : K) : Fin n → ℂ) = 0 := by
      apply hrad _ (y : K).2
      · intro z hz
        have := LinearMap.congr_fun (LinearMap.mem_ker.mp y.2) ⟨z, hz⟩
        rw [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearMap.domRestrict_apply] at this
        simpa using this
      · simpa [hL] using hy
    exact Subtype.ext (Subtype.ext hy0)
  have h4 := LinearMap.finrank_range_add_finrank_ker (K := ℂ) (V := R) L
  rw [hker, finrank_bot] at h4
  have h5 := Submodule.finrank_le (LinearMap.range L)
  rw [Module.finrank_self] at h5
  omega

lemma generic {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) {ι : Type} (s : Finset ι)
    (g : ι → MvPolynomial (Fin n) ℂ)
    (h : ∀ m ∈ s, ∃ x ∈ K, MvPolynomial.eval x (g m) ≠ 0) :
    ∃ x ∈ K, ∀ m ∈ s, MvPolynomial.eval x (g m) ≠ 0 := by
  set b := Module.finBasis ℂ K
  set k := Module.finrank ℂ K
  let v : Fin n → MvPolynomial (Fin k) ℂ :=
    fun i => ∑ l, MvPolynomial.C ((b l : Fin n → ℂ) i) * MvPolynomial.X l
  let pt : (Fin k → ℂ) → (Fin n → ℂ) := fun c => ∑ l, c l • (b l : Fin n → ℂ)
  have hpt : ∀ c, pt c ∈ K := fun c =>
    Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (b l).2)
  have key : ∀ (c : Fin k → ℂ) (p : MvPolynomial (Fin n) ℂ),
      MvPolynomial.eval c (MvPolynomial.aeval v p) = MvPolynomial.eval (pt c) p := by
    intro c p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]
      congr 1
      simp [v, pt, Finset.sum_apply, mul_comm]
  have hne : ∀ m ∈ s, MvPolynomial.aeval v (g m) ≠ 0 := by
    intro m hm hz
    obtain ⟨x, hx, hxne⟩ := h m hm
    have hxe : pt (b.repr ⟨x, hx⟩) = x := by
      have h1 := b.sum_repr ⟨x, hx⟩
      calc pt (b.repr ⟨x, hx⟩) = ((∑ l, b.repr ⟨x, hx⟩ l • b l : K) : Fin n → ℂ) := by
            simp only [pt, Submodule.coe_sum, Submodule.coe_smul]
        _ = x := by rw [h1]
    apply hxne
    rw [← hxe, ← key, hz, map_zero]
  have hP : ∏ m ∈ s, MvPolynomial.aeval v (g m) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  obtain ⟨c, hc⟩ : ∃ c, MvPolynomial.eval c (∏ m ∈ s, MvPolynomial.aeval v (g m)) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hP (MvPolynomial.funext (fun c => by simpa using hall c))
  refine ⟨pt c, hpt c, fun m hm => ?_⟩
  rw [map_prod] at hc
  rw [← key]
  exact (Finset.prod_ne_zero_iff.mp hc) m hm

def pw {n : ℕ} (r : ℕ) (x : Fin n → ℂ) : ℂ := ∑ j, x j ^ r

lemma N_closed (n : ℕ) :
    ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ) = (n : ℂ) * (n - 1) * (n - 2) * (n - 3) := by
  have := F_closed n 0 0 (by simp)
  simpa [E2, E3, E4] using this

lemma pw_smul {n : ℕ} (r : ℕ) (t : ℂ) (x : Fin n → ℂ) : pw r (t • x) = t ^ r * pw r x := by
  simp [pw, Finset.mul_sum, mul_pow]

lemma coeffs {n : ℕ} (hn : 4 ≤ n) (a : Fin 4 → ℂ) (x : Fin n → ℂ)
    (hx : ∀ t : ℂ, ∑ j, (t • x) j = 0 ∧
      ∑ f : Fin 4 ↪ Fin n, ∏ i, (1 + a i * (t • x) (f i)) = ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ)) :
    E2 a * pw 2 x = 0 ∧ E3 a * pw 3 x = 0 ∧ E4 a * (3 * pw 2 x ^ 2 - 6 * pw 4 x) = 0 := by
  have key : ∀ t : ℂ, -(E2 a * (((n : ℂ) - 2) * ((n : ℂ) - 3)) * pw 2 x) * t ^ 2 +
      2 * E3 a * ((n : ℂ) - 3) * pw 3 x * t ^ 3 +
      E4 a * (3 * pw 2 x ^ 2 - 6 * pw 4 x) * t ^ 4 = 0 := by
    intro t
    obtain ⟨h1, h2⟩ := hx t
    rw [F_closed n a _ h1, N_closed] at h2
    have e2 := pw_smul 2 t x
    have e3 := pw_smul 3 t x
    have e4 := pw_smul 4 t x
    simp only [pw] at e2 e3 e4
    rw [e2, e3, e4] at h2
    simp only [pw]
    linear_combination h2
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key 2
  have hn2 : (n : ℂ) - 2 ≠ 0 := by
    intro h
    have : (n : ℂ) = 2 := by linear_combination h
    norm_cast at this; omega
  have hn3 : (n : ℂ) - 3 ≠ 0 := by
    intro h
    have : (n : ℂ) = 3 := by linear_combination h
    norm_cast at this; omega
  refine ⟨?_, ?_, ?_⟩
  · have hA : (E2 a * pw 2 x) * (((n : ℂ) - 2) * ((n : ℂ) - 3)) = 0 := by
      linear_combination -(k1 + k2 / 3 - k3 / 12)
    exact (mul_eq_zero.mp hA).resolve_right (mul_ne_zero hn2 hn3)
  · have hB : (E3 a * pw 3 x) * (2 * ((n : ℂ) - 3)) = 0 := by
      linear_combination (k1 - k2) / 2
    exact (mul_eq_zero.mp hB).resolve_right (mul_ne_zero two_ne_zero hn3)
  · linear_combination -k1 / 2 + k2 / 6 + k3 / 12

lemma some_E (a : Fin 4 → ℂ) (ha : a ≠ 0) (hs : ∑ i, a i = 0) :
    E2 a ≠ 0 ∨ E3 a ≠ 0 ∨ E4 a ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h2, h3, h4⟩ := h
  simp only [E2, E3, E4] at h2 h3 h4
  rw [Fin.sum_univ_four] at hs
  apply ha
  have z0 : a 0 ^ 4 = 0 := by
    linear_combination (a 0) ^ 3 * hs - (a 0) ^ 2 * h2 + (a 0) * h3 - h4
  have z1 : a 1 ^ 4 = 0 := by
    linear_combination (a 1) ^ 3 * hs - (a 1) ^ 2 * h2 + (a 1) * h3 - h4
  have z2 : a 2 ^ 4 = 0 := by
    linear_combination (a 2) ^ 3 * hs - (a 2) ^ 2 * h2 + (a 2) * h3 - h4
  have z3 : a 3 ^ 4 = 0 := by
    linear_combination (a 3) ^ 3 * hs - (a 3) ^ 2 * h2 + (a 3) * h3 - h4
  funext i
  fin_cases i
  · exact pow_eq_zero_iff (by norm_num) |>.mp z0
  · exact pow_eq_zero_iff (by norm_num) |>.mp z1
  · exact pow_eq_zero_iff (by norm_num) |>.mp z2
  · exact pow_eq_zero_iff (by norm_num) |>.mp z3

def Bf {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun y z => ∑ j, w j * y j * z j + κ * (∑ j, u j * y j) * (∑ j, u j * z j))
    (fun m₁ m₂ z => by
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]; ring)
    (fun c m z => by
      simp only [Pi.smul_apply, smul_eq_mul]
      have e1 : ∑ j, w j * (c * m j) * z j = c * ∑ j, w j * m j * z j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e2 : ∑ j, u j * (c * m j) = c * ∑ j, u j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1, e2]; ring)
    (fun y n₁ n₂ => by
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]; ring)
    (fun c y m => by
      simp only [Pi.smul_apply, smul_eq_mul]
      have e1 : ∑ j, w j * y j * (c * m j) = c * ∑ j, w j * y j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e2 : ∑ j, u j * (c * m j) = c * ∑ j, u j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1, e2]; ring)

lemma Bf_apply {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) (y z : Fin n → ℂ) :
    Bf w u κ y z = ∑ j, w j * y j * z j + κ * (∑ j, u j * y j) * (∑ j, u j * z j) := rfl

lemma Bf_single {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) (y : Fin n → ℂ) (i : Fin n) :
    Bf w u κ y (Pi.single i 1) = w i * y i + κ * (∑ j, u j * y j) * u i := by
  rw [Bf_apply]
  simp [Pi.single_apply]

lemma p2_add {n : ℕ} (x y : Fin n → ℂ) :
    pw 2 (x + y) = pw 2 x + 2 * (∑ j, x j * y j) + pw 2 y := by
  simp only [pw, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma p2_sub {n : ℕ} (x y : Fin n → ℂ) :
    pw 2 (x - y) = pw 2 x - 2 * (∑ j, x j * y j) + pw 2 y := by
  simp only [pw, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

def sumL (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ j, z j
  map_add' y z := by simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.mul_sum]

lemma finrank_sumL_ker {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank ℂ (LinearMap.ker (sumL n)) = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumL n)
  have hr : LinearMap.range (sumL n) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single ⟨0, by omega⟩ c, ?_⟩
    simp [sumL]
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

lemma case2 {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) (hq : ∀ x ∈ K, pw 2 x = 0) :
    2 * Module.finrank ℂ K ≤ n := by
  have h := iso_bound0 ⊤ K le_top (Bf (fun _ => 1) 0 0)
    (fun y hy z hz => by
      have e := p2_add y z
      rw [hq _ (K.add_mem hy hz), hq y hy, hq z hz] at e
      rw [Bf_apply]
      simp only [one_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      linear_combination -e / 2)
    (fun y _ hy => by
      funext i
      have := hy (Pi.single i 1) trivial
      rw [Bf_single] at this
      simpa using this)
  rwa [finrank_top, Module.finrank_fin_fun] at h

lemma case3 {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) (hq : ∀ x ∈ K, pw 3 x = 0) :
    2 * Module.finrank ℂ K ≤ n := by
  classical
  obtain ⟨x, hxK, hx⟩ := generic K (univ.filter (fun j => ∃ u ∈ K, u j ≠ 0))
    (fun j => MvPolynomial.X j) (fun j hj => by simpa using (Finset.mem_filter.mp hj).2)
  have hx' : ∀ j, (∃ u ∈ K, u j ≠ 0) → x j ≠ 0 := fun j hj => by
    simpa using hx j (Finset.mem_filter.mpr ⟨mem_univ _, hj⟩)
  have h := iso_bound0 ⊤ K le_top (Bf x 0 0)
    (fun y hy z hz => by
      have pol : 6 * ∑ j, x j * y j * z j = pw 3 (x + y + z) - pw 3 (x + y) - pw 3 (x + z)
          - pw 3 (y + z) + pw 3 x + pw 3 y + pw 3 z := by
        simp only [pw, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [hq _ (K.add_mem (K.add_mem hxK hy) hz), hq _ (K.add_mem hxK hy),
        hq _ (K.add_mem hxK hz), hq _ (K.add_mem hy hz), hq x hxK, hq y hy, hq z hz] at pol
      rw [Bf_apply]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      linear_combination pol / 6)
    (fun y hyK hy => by
      funext i
      have := hy (Pi.single i 1) trivial
      rw [Bf_single] at this
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at this
      by_contra hyi
      have h' : x i = 0 ∨ y i = 0 := by simpa using this
      exact hx' i ⟨y, hyK, hyi⟩ (h'.resolve_right hyi))
  rwa [finrank_top, Module.finrank_fin_fun] at h

lemma case4 {n : ℕ} (hn : 4 ≤ n) (K : Submodule ℂ (Fin n → ℂ))
    (hK0 : ∀ x ∈ K, ∑ j, x j = 0) (hq : ∀ x ∈ K, pw 2 x ^ 2 = 2 * pw 4 x) :
    2 * Module.finrank ℂ K ≤ n := by
  classical

  let g : Bool × Fin n → MvPolynomial (Fin n) ℂ := fun m =>
    cond m.1 ((∑ i, MvPolynomial.X i ^ 2) - MvPolynomial.C 6 * MvPolynomial.X m.2 ^ 2)
      (MvPolynomial.X m.2)
  obtain ⟨x, hxK, hx⟩ := generic K (univ.filter (fun m => ∃ u ∈ K, MvPolynomial.eval u (g m) ≠ 0))
    g (fun m hm => (Finset.mem_filter.mp hm).2)
  have G0 : ∀ j, (∃ u ∈ K, u j ≠ 0) → x j ≠ 0 := fun j ⟨u, hu, huj⟩ => by
    have := hx (false, j) (Finset.mem_filter.mpr ⟨mem_univ _, ⟨u, hu, by simpa [g] using huj⟩⟩)
    simpa [g] using this
  have G1 : ∀ j, (∃ u ∈ K, pw 2 u - 6 * u j ^ 2 ≠ 0) → pw 2 x - 6 * x j ^ 2 ≠ 0 :=
    fun j ⟨u, hu, huj⟩ => by
      have := hx (true, j) (Finset.mem_filter.mpr ⟨mem_univ _, ⟨u, hu, by simpa [g, pw] using huj⟩⟩)
      simpa [g, pw] using this
  set P := pw 2 x with hP
  set d : Fin n → ℂ := fun j => P - 6 * x j ^ 2 with hd

  have quad : ∀ w ∈ K, 4 * (∑ j, x j * w j) ^ 2 + 2 * P * pw 2 w
      - 12 * ∑ j, x j ^ 2 * w j ^ 2 = 0 := by
    intro w hw
    have h1 := hq _ (K.add_mem hxK hw)
    have h2 := hq _ (K.sub_mem hxK hw)
    have h3 := hq x hxK
    have h4 := hq w hw
    rw [p2_add] at h1
    rw [p2_sub] at h2
    have e4 : pw 4 (x + w) + pw 4 (x - w) = 2 * pw 4 x + 12 * (∑ j, x j ^ 2 * w j ^ 2)
        + 2 * pw 4 w := by
      simp only [pw, Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    linear_combination (h1 + h2) / 2 - h3 - h4 + e4

  have hiso : ∀ y ∈ K, ∀ z ∈ K, Bf d x 2 y z = 0 := by
    intro y hy z hz
    have q1 := quad _ (K.add_mem hy hz)
    have q2 := quad y hy
    have q3 := quad z hz
    rw [p2_add] at q1
    have ex : ∑ j, x j * (y + z) j = (∑ j, x j * y j) + ∑ j, x j * z j := by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have es : ∑ j, x j ^ 2 * (y + z) j ^ 2 = (∑ j, x j ^ 2 * y j ^ 2) +
        2 * (∑ j, x j ^ 2 * y j * z j) + ∑ j, x j ^ 2 * z j ^ 2 := by
      simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have ed : ∑ j, d j * y j * z j = P * (∑ j, y j * z j) - 6 * ∑ j, x j ^ 2 * y j * z j := by
      simp only [hd, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [ex, es] at q1
    rw [Bf_apply, ed]
    linear_combination (q1 - q2 - q3) / 4

  have L0 : ∀ y ∈ K, (∀ j, d j * y j = 0) → ∑ j, x j * y j = 0 → y = 0 := by
    intro y hy hdy hxy
    funext j
    by_cases hj : d j = 0
    · by_cases ha : ∃ u ∈ K, u j ≠ 0
      · have hx0 := G0 j ha
        have hz : ∀ u ∈ K, pw 2 u - 6 * u j ^ 2 = 0 := by
          intro u hu
          by_contra hne
          exact G1 j ⟨u, hu, hne⟩ hj
        have e1 := hz _ (K.add_mem hxK hy)
        have e2 := hz x hxK
        have e3 := hz y hy
        rw [p2_add] at e1
        simp only [Pi.add_apply] at e1
        have : x j * y j = 0 := by
          linear_combination (-(e1 - e2 - e3) + 2 * hxy) / 12
        simpa [hx0] using this
      · push Not at ha
        exact ha y hy
    · exact (mul_eq_zero.mp (hdy j)).resolve_left hj

  set W := LinearMap.ker (sumL n) with hW
  have hKW : K ≤ W := fun y hy => by simpa [hW, sumL] using hK0 y hy
  have hsingle : ∀ i j : Fin n, Pi.single i (1 : ℂ) - Pi.single j 1 ∈ W := by
    intro i j
    simp [hW, sumL, Finset.sum_sub_distrib]
  have hv : ∀ y : Fin n → ℂ, (∀ z ∈ W, Bf d x 2 y z = 0) → ∀ i j : Fin n,
      d i * y i + 2 * (∑ l, x l * y l) * x i = d j * y j + 2 * (∑ l, x l * y l) * x j := by
    intro y hy i j
    have := hy _ (hsingle i j)
    rw [map_sub, Bf_single, Bf_single] at this
    linear_combination this
  have hW1 : Module.finrank ℂ W = n - 1 := finrank_sumL_ker (by omega)

  suffices H : ∃ ψ : (Fin n → ℂ) →ₗ[ℂ] ℂ,
      ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) → ψ y = 0 → y = 0 by
    obtain ⟨ψ, hψ⟩ := H
    have := iso_bound1 W K hKW (Bf d x 2) hiso ψ hψ
    omega
  let cL : (Fin n → ℂ) →ₗ[ℂ] ℂ := (Bf x 0 0).flip (fun _ => 1)
  have hcL : ∀ y, cL y = ∑ l, x l * y l := by
    intro y
    simp [cL, Bf_apply]
  by_cases hA : ∃ i1, d i1 = 0
  · obtain ⟨i1, hi1⟩ := hA
    refine ⟨cL, fun y hyK hy hc => ?_⟩
    rw [hcL] at hc
    apply L0 y hyK _ hc
    intro j
    have := hv y hy j i1
    rw [hi1, hc] at this
    linear_combination this
  · push Not at hA
    set i0 : Fin n := ⟨0, by omega⟩
    set A := ∑ i, 1 / d i
    set Bc := ∑ i, x i / d i
    set C := ∑ i, x i ^ 2 / d i
    have hId : P * A - 6 * C = n := by
      have : ∑ i, d i / d i = n := by
        rw [Finset.sum_congr rfl (fun i _ => div_self (hA i))]
        simp
      rw [← this]
      simp only [A, C, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        have := hA i; field_simp; simp only [hd])

    have rel : ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) →
        (∀ i, y i = (Bf d x 2 y (Pi.single i0 1) - 2 * (∑ l, x l * y l) * x i) / d i) ∧
        (∑ l, x l * y l) * (1 + 2 * C) = Bf d x 2 y (Pi.single i0 1) * Bc ∧
        Bf d x 2 y (Pi.single i0 1) * A = 2 * (∑ l, x l * y l) * Bc := by
      intro y hyK hy
      set c := ∑ l, x l * y l with hc
      set μ := Bf d x 2 y (Pi.single i0 1) with hμ
      have hμ' : μ = d i0 * y i0 + 2 * c * x i0 := by rw [hμ, Bf_single]
      have yform : ∀ i, y i = (μ - 2 * c * x i) / d i := by
        intro i
        rw [eq_div_iff (hA i)]
        have := hv y hy i i0
        rw [hμ']
        linear_combination this
      refine ⟨yform, ?_, ?_⟩
      · have : (∑ l, x l * y l) = μ * Bc - 2 * c * C := by
          conv_lhs => rw [Finset.sum_congr rfl (fun i _ => by rw [yform i])]
          simp only [Bc, C, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by
            have := hA i; field_simp)
        linear_combination this
      · have hs := hK0 y hyK
        have : ∑ i, y i = μ * A - 2 * c * Bc := by
          conv_lhs => rw [Finset.sum_congr rfl (fun i _ => by rw [yform i])]
          simp only [A, Bc, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by
            have := hA i; field_simp)
        linear_combination hs - this
    have finish : ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) → ∑ l, x l * y l = 0 →
        Bf d x 2 y (Pi.single i0 1) = 0 → y = 0 := by
      intro y hyK hy hc hμ
      apply L0 y hyK _ hc
      intro j
      have := hv y hy j i0
      rw [Bf_single] at hμ
      rw [hc] at this hμ
      linear_combination this + hμ
    by_cases hBC : Bc ≠ 0 ∨ 1 + 2 * C ≠ 0
    · refine ⟨(Bf d x 2).flip (Pi.single i0 1), fun y hyK hy hμ => ?_⟩
      rw [LinearMap.flip_apply] at hμ
      obtain ⟨-, r1, r2⟩ := rel y hyK hy
      rw [hμ] at r1 r2
      apply finish y hyK hy _ hμ
      rcases hBC with hb | hb
      · have : 2 * (∑ l, x l * y l) * Bc = 0 := by linear_combination -r2
        have := (mul_eq_zero.mp this).resolve_right hb
        simpa using this
      · have : (∑ l, x l * y l) * (1 + 2 * C) = 0 := by linear_combination r1
        exact (mul_eq_zero.mp this).resolve_right hb
    · simp only [not_or, not_not] at hBC
      obtain ⟨hb, hcc⟩ := hBC
      refine ⟨cL, fun y hyK hy hc => ?_⟩
      rw [hcL] at hc
      obtain ⟨-, -, r2⟩ := rel y hyK hy
      rw [hc] at r2
      apply finish y hyK hy hc
      by_cases hA0 : A = 0
      · exfalso
        rw [hA0] at hId
        have h3 : (n : ℂ) = 3 := by linear_combination -hId - 3 * hcc
        norm_cast at h3
        omega
      · have : Bf d x 2 y (Pi.single i0 1) * A = 0 := by linear_combination r2
        exact (mul_eq_zero.mp this).resolve_right hA0

def pv (k : ℕ) (c : Fin k → ℂ) (m : ℕ) : ℂ :=
  if h : m < k then c ⟨m, h⟩ else if h2 : m < 2 * k then -c ⟨m - k, by omega⟩ else 0

lemma pv_sum (k n r : ℕ) (hkn : 2 * k ≤ n) (c : Fin k → ℂ) (hr : ∀ u : ℂ, u ^ r + (-u) ^ r = 0)
    (hr0 : (0 : ℂ) ^ r = 0) :
    ∑ m ∈ range n, pv k c m ^ r = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = k + (k + t) := ⟨n - 2 * k, by omega⟩
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∀ m ∈ range k, pv k c m ^ r = (if h : m < k then c ⟨m, h⟩ else 0) ^ r := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    simp [pv, hm']
  have e2 : ∀ m ∈ range k, pv k c (k + m) ^ r = (-(if h : m < k then c ⟨m, h⟩ else 0)) ^ r := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    have : ¬ (k + m < k) := by omega
    have h2 : k + m < 2 * k := by omega
    simp [pv, this, h2, hm']
  have e3 : ∀ m ∈ range t, pv k c (k + (k + m)) ^ r = 0 := by
    intro m _
    have : ¬ (k + (k + m) < k) := by omega
    have h2 : ¬ (k + (k + m) < 2 * k) := by omega
    simp [pv, this, h2, hr0]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3,
    Finset.sum_const_zero, add_zero, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun m _ => hr _)

def pvL (k n : ℕ) : (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun c := fun j => pv k c j.val
  map_add' c₁ c₂ := by
    funext j
    simp only [pv, Pi.add_apply]
    split_ifs <;> ring
  map_smul' t c := by
    funext j
    simp only [pv, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem main : (∀ (n k : ℕ), 4 ≤ n →
  ((∃ (a : Fin 4 → ℂ) (K : Submodule ℂ (Fin n → ℂ)),
      a ≠ 0 ∧ (∑ i, a i) = 0 ∧ Module.finrank ℂ K = k ∧
      ∀ x ∈ K, (∑ j, x j) = 0 ∧
        (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + a i * x (f i))) =
          (∑ _f : Fin 4 ↪ Fin n, (1 : ℂ))) ↔
    2 * k ≤ n)) := by
  intro n k hn
  constructor
  · rintro ⟨a, K, ha, hsa, hk, hK⟩
    subst hk
    have hK0 : ∀ x ∈ K, ∑ j, x j = 0 := fun x hx => (hK x hx).1
    have hco : ∀ x ∈ K, E2 a * pw 2 x = 0 ∧ E3 a * pw 3 x = 0 ∧
        E4 a * (3 * pw 2 x ^ 2 - 6 * pw 4 x) = 0 :=
      fun x hx => coeffs hn a x (fun t => hK _ (K.smul_mem t hx))
    rcases some_E a ha hsa with h2 | h3 | h4
    · exact case2 K (fun x hx => (mul_eq_zero.mp (hco x hx).1).resolve_left h2)
    · exact case3 K (fun x hx => (mul_eq_zero.mp (hco x hx).2.1).resolve_left h3)
    · refine case4 hn K hK0 (fun x hx => ?_)
      have := (mul_eq_zero.mp (hco x hx).2.2).resolve_left h4
      linear_combination this / 3
  · intro hkn
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-3 : ℂ) (n := 2) (by norm_num)
    set ω : ℂ := (-1 + s) / 2 with hωd
    have hω : ω ^ 2 + ω + 1 = 0 := by rw [hωd]; linear_combination hs / 4
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    have hinj : Function.Injective (pvL k n) := by
      intro c₁ c₂ h
      funext m
      have := congrFun h ⟨m, by omega⟩
      simpa [pvL, pv] using this
    refine ⟨![0, 1, ω, ω ^ 2], LinearMap.range (pvL k n), ?_, ?_, ?_, ?_⟩
    · intro h
      have := congrFun h 1
      simp at this
    · simp only [Fin.sum_univ_four]
      simp
      linear_combination hω
    · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
    · rintro x ⟨c, rfl⟩
      have hsum : ∑ j, pvL k n c j = 0 := by
        have := pv_sum k n 1 hkn c (fun u => by ring) (by ring)
        simp only [pow_one] at this
        rw [← this, ← Fin.sum_univ_eq_sum_range (fun m => pv k c m) n]
        rfl
      have hcube : ∑ j, pvL k n c j ^ 3 = 0 := by
        have := pv_sum k n 3 hkn c (fun u => by ring) (by ring)
        rw [← this, ← Fin.sum_univ_eq_sum_range (fun m => pv k c m ^ 3) n]
        rfl
      refine ⟨hsum, ?_⟩
      rw [F_closed n _ _ hsum, N_closed, hcube]
      have hE2 : E2 ![0, 1, ω, ω ^ 2] = 0 := by
        simp [E2]
        linear_combination hω + hω3
      have hE4 : E4 ![0, 1, ω, ω ^ 2] = 0 := by simp [E4]
      rw [hE2, hE4]
      ring

end RankOne

theorem RankOne : (∀ (n k : ℕ), 4 ≤ n →
  ((∃ (a : Fin 4 → ℂ) (K : Submodule ℂ (Fin n → ℂ)),
      a ≠ 0 ∧ (∑ i, a i) = 0 ∧ Module.finrank ℂ K = k ∧
      ∀ x ∈ K, (∑ j, x j) = 0 ∧
        (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + a i * x (f i))) =
          (∑ _f : Fin 4 ↪ Fin n, (1 : ℂ))) ↔
    2 * k ≤ n)) :=
  RankOne.main

end Reuse312

section Reuse306

namespace Quadratic_aux
open scoped BigOperators
variable {n : Nat}
abbrev Vec (n : Nat) := Fin n → ℂ
abbrev Mat (n : Nat) := Fin 4 → Fin n → ℂ
def dot (a b : Vec n) : ℂ := ∑ j, a j * b j
def mult3 (n : Nat) : ℂ := ((n-3 : Nat) : ℂ)
def mult2 (n : Nat) : ℂ := ((n-2 : Nat) : ℂ) * mult3 n
noncomputable def e0 (n : Nat) : ℂ := ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ)

noncomputable def e1 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n, (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3))

noncomputable def e2 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n,
    (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
     X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3))

noncomputable def e3 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n,
    (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
     X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3))

noncomputable def e4 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n, X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)

lemma poly_expand (X : Mat n) (t : ℂ) :
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + (t • X) i (f i))) =
      e0 n + t * e1 X + t ^ 2 * e2 X + t ^ 3 * e3 X + t ^ 4 * e4 X := by
  have hterm : ∀ f : Fin 4 ↪ Fin n,
      (∏ i : Fin 4, (1 + (t • X) i (f i))) =
        (1 : ℂ) +
        t * (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3)) +
        t ^ 2 * (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
          X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3)) +
        t ^ 3 * (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
          X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3)) +
        t ^ 4 * (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)) := by
    intro f
    rw [Fin.prod_univ_four]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

lemma coeffs_zero_of_const (X : Mat n)
    (h : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + (t • X) i (f i))) = e0 n) :
    e2 X = 0 ∧ e3 X = 0 ∧ e4 X = 0 := by
  have h0 := h 0; rw [poly_expand] at h0
  have h1 := h 1; rw [poly_expand] at h1
  have hm1 := h (-1); rw [poly_expand] at hm1
  have h2 := h 2; rw [poly_expand] at h2
  have hm2 := h (-2); rw [poly_expand] at hm2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (16 * h1 + 16 * hm1 - h2 - hm2 - 30 * h0) / 24
  · linear_combination (h2 - hm2 - 2 * h1 + 2 * hm1) / 12
  · linear_combination (h2 + hm2 - 4 * h1 - 4 * hm1 + 6 * h0) / 24

def validTuple (t : Fin n × Fin n × Fin n × Fin n) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧
  t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2

instance : DecidablePred (validTuple (n:=n)) := fun t => by
  unfold validTuple; infer_instance

lemma sum_emb_eq_nested (g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ f : Fin 4 ↪ Fin n, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 := by
  have h1 : (∑ f : Fin 4 ↪ Fin n, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ t ∈ Finset.univ.filter validTuple, g t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    refine Finset.sum_nbij (fun f => (f 0, f 1, f 2, f 3)) ?_ ?_ ?_ ?_
    · intro f _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, validTuple]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := f.injective h <;> omega
    · intro f1 _ f2 _ h
      have h0 : f1 0 = f2 0 := congrArg Prod.fst h
      have h1' : f1 1 = f2 1 := congrArg (fun p => p.2.1) h
      have h2' : f1 2 = f2 2 := congrArg (fun p => p.2.2.1) h
      have h3' : f1 3 = f2 3 := congrArg (fun p => p.2.2.2) h
      exact DFunLike.ext f1 f2 fun i => by fin_cases i <;> assumption
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, validTuple] at ht
      rcases t with ⟨j0, j1, j2, j3⟩
      rcases ht with ⟨h01, h02, h03, h12, h13, h23⟩
      refine ⟨⟨![j0, j1, j2, j3], ?_⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [Ne.symm]
    · intro f _
      rfl
  rw [h1]
  rw [Finset.sum_filter]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j0 _ => ?_
  have hf1 : ∀ x : Fin n, (∑ j2 : Fin n, ∑ j3 : Fin n,
      if validTuple (j0, x, j2, j3) then g j0 x j2 j3 else 0) =
      if x ∈ Finset.univ.erase j0 then
        ∑ j2 ∈ (Finset.univ.erase j0).erase x,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase x).erase j2, g j0 x j2 j3
      else 0 := by
    intro j1
    by_cases h01 : j0 = j1
    · subst h01
      simp [validTuple]
    · have hm1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨Ne.symm h01, Finset.mem_univ _⟩
      rw [if_pos hm1]
      trans ∑ j2 : Fin n, if j2 ∈ (Finset.univ.erase j0).erase j1 then
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 else 0
      · refine Finset.sum_congr rfl fun j2 _ => ?_
        by_cases h2 : j2 ∈ (Finset.univ.erase j0).erase j1
        · rw [if_pos h2]
          have h02 : j0 ≠ j2 := Ne.symm (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h2))
          have h12 : j1 ≠ j2 := Ne.symm (Finset.ne_of_mem_erase h2)
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext j3
          simp [validTuple, h01, h02, h12]; exact ⟨fun ⟨a, b, c⟩ => ⟨Ne.symm c, Ne.symm b, Ne.symm a⟩, fun ⟨c, b, a⟩ => ⟨Ne.symm a, Ne.symm b, Ne.symm c⟩⟩
        · rw [if_neg h2]
          have h2' : j0 = j2 ∨ j1 = j2 := by
            simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not] at h2
            by_cases h12 : j2 = j1
            · exact Or.inr h12.symm
            · exact Or.inl (h2 h12).symm
          apply Finset.sum_eq_zero
          intro j3 _
          rcases h2' with rfl | rfl <;> simp [validTuple]
      · rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j2; simp
  simp_rw [hf1]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j1; simp

lemma sum_emb_01 (a b : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1)) = -(mult2 n) * dot a b := by
  rw [sum_emb_eq_nested (fun j0 j1 _ _ => a j0 * b j1)]
  have hinner : ∀ (j0 : Fin n) (j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) = (mult2 n) * (a j0 * b j1) := by
    intro j0 j1 hj1
    have hcard1 : ((Finset.univ : Finset (Fin n)).erase j0).card = n-1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin n)).erase j0).erase j1).card = n-2 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
      omega
    have hstep : ∀ j2 ∈ ((Finset.univ : Finset (Fin n)).erase j0).erase j1,
        (∑ j3 ∈ (((Finset.univ : Finset (Fin n)).erase j0).erase j1).erase j2, a j0 * b j1) =
          (mult3 n) * (a j0 * b j1) := by
      intro j2 hj2
      rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
      simp [mult3, nsmul_eq_mul, Nat.sub_sub]
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, hcard2]
    simp [mult2,mult3,nsmul_eq_mul,mul_assoc]
  have h1 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0, (mult2 n) * (a j0 * b j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => hinner j0 j1 hj1
  rw [h1]
  have h2 : ∀ j0 : Fin n, (∑ j1 ∈ Finset.univ.erase j0, (mult2 n) * (a j0 * b j1)) = -(mult2 n) * (a j0 * b j0) := by
    intro j0
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h2, ← Finset.mul_sum]
  rfl

lemma sum_emb_pair_eq (i1 i2 : Fin 4) (hi : i1 ≠ i2) (a b : Vec n)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2)) = -(mult2 n) * dot a b := by
  have hswap : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 ∧ σ 1 = i2 := by
    have he : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 := ⟨Equiv.swap 0 i1, by simp⟩
    rcases he with ⟨σ1, hσ1⟩
    have hne : σ1.symm i2 ≠ 0 := by
      intro h
      have := congrArg σ1 h
      rw [Equiv.apply_symm_apply, hσ1] at this
      exact hi this.symm
    refine ⟨σ1 * Equiv.swap 1 (σ1.symm i2), ?_, ?_⟩
    · simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) hne.symm, hσ1]
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]
  rcases hswap with ⟨σ, hσ0, hσ1⟩
  have hbij : (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2)) =
      ∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) := by
    refine Finset.sum_nbij (fun f => σ.toEmbedding.trans f) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun x => by
        have := DFunLike.congr_fun h (σ.symm x)
        simpa using this
    · intro f _
      refine ⟨σ.symm.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact DFunLike.ext _ _ fun x => by simp
    · intro f _
      simp [hσ0, hσ1]
  rw [hbij]
  exact sum_emb_01 a b ha hb

lemma e2_eq (X : Mat n) (hr : ∀ i, ∑ j, X i j = 0) (hc : ∀ j, ∑ i, X i j = 0) :
    e2 X = (mult2 n / 2) * (dot (X 0) (X 0) + dot (X 1) (X 1) + dot (X 2) (X 2) + dot (X 3) (X 3)) := by
  unfold e2
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_pair_eq 0 1 (by decide) (X 0) (X 1) (hr 0) (hr 1),
      sum_emb_pair_eq 0 2 (by decide) (X 0) (X 2) (hr 0) (hr 2),
      sum_emb_pair_eq 0 3 (by decide) (X 0) (X 3) (hr 0) (hr 3),
      sum_emb_pair_eq 1 2 (by decide) (X 1) (X 2) (hr 1) (hr 2),
      sum_emb_pair_eq 1 3 (by decide) (X 1) (X 3) (hr 1) (hr 3),
      sum_emb_pair_eq 2 3 (by decide) (X 2) (X 3) (hr 2) (hr 3)]
  have hsq : ∑ j : Fin n, (X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := hc j
    rw [Fin.sum_univ_four] at hj
    rw [hj]; ring
  unfold dot
  have hcomb : ∑ j : Fin n,
      ((X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 -
       (X 0 j * X 0 j + X 1 j * X 1 j + X 2 j * X 2 j + X 3 j * X 3 j) -
       2 * (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j +
            X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j)) = 0 := by
    apply Finset.sum_eq_zero; intro j _; ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hcomb
  linear_combination (mult2 n / 2) * hcomb - (mult2 n / 2) * hsq

end Quadratic_aux

end Reuse306

section Reuse303

namespace Cubic
open Finset Module
noncomputable section
abbrev V := Fin 5 → ℂ
def HH (U : Submodule ℂ V) : Prop := ∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0
def Concl (U : Submodule ℂ V) : Prop :=
  ∃ π : Equiv.Perm (Fin 5),
      (∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
        u (π j) = (![s, -s, t, -t, 0] : Fin 5 → ℂ) j) ∨
      (∃ z : ℂ, IsPrimitiveRoot z 5 ∧
        ∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
          u (π j) = s * z^j.val + t * z^(4*j.val))
variable {U : Submodule ℂ V}
lemma fS (H : HH U) (π : Equiv.Perm (Fin 5)) {u : V} (hu : u ∈ U) :
    u (π 0) + u (π 1) + u (π 2) + u (π 3) + u (π 4) = 0 := by
  have h := (H u hu).1
  rw [← Equiv.sum_comp π u] at h
  simpa [Fin.sum_univ_five] using h
lemma fC (H : HH U) (π : Equiv.Perm (Fin 5)) {u : V} (hu : u ∈ U) :
    u (π 0)^3 + u (π 1)^3 + u (π 2)^3 + u (π 3)^3 + u (π 4)^3 = 0 := by
  have h := (H u hu).2
  rw [← Equiv.sum_comp π (fun j => u j ^ 3)] at h
  simpa [Fin.sum_univ_five] using h
lemma pol (H : HH U) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    (∑ j, x j ^ 2 * y j) = 0 := by
  have h1 := (H (x + y) (U.add_mem hx hy)).2
  have h2 := (H (x - y) (U.sub_mem hx hy)).2
  have h3 := (H y hy).2
  simp only [Pi.add_apply, Pi.sub_apply, Fin.sum_univ_five] at h1 h2 h3 ⊢
  linear_combination (h1 - h2 - 2 * h3) / 6
lemma fP (H : HH U) (π : Equiv.Perm (Fin 5)) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x (π 0)^2 * y (π 0) + x (π 1)^2 * y (π 1) + x (π 2)^2 * y (π 2) +
      x (π 3)^2 * y (π 3) + x (π 4)^2 * y (π 4) = 0 := by
  have h := pol H hx hy
  rw [← Equiv.sum_comp π (fun j => x j ^ 2 * y j)] at h
  simpa [Fin.sum_univ_five] using h
lemma GP (H : HH U) (π : Equiv.Perm (Fin 5)) {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (x0 : x (π 0) = 1) (x1 : x (π 1) = -1) (x2 : x (π 2) = 0) (x3 : x (π 3) = 0)
    (x4 : x (π 4) = 0) (y0 : y (π 0) = 0) (y1 : y (π 1) = 0) (y2 : y (π 2) = 1)
    (y3 : y (π 3) = -1) (y4 : y (π 4) = 0) : Concl U := by
  refine ⟨π, Or.inl fun u => ⟨fun hu => ?_, fun ⟨s, t, h⟩ => ?_⟩⟩
  · have p1 := fP H π hx hu
    have p2 := fP H π hy hu
    have p3 := fS H π hu
    rw [x0, x1, x2, x3, x4] at p1
    rw [y0, y1, y2, y3, y4] at p2
    refine ⟨u (π 0), u (π 2), fun j => ?_⟩
    fin_cases j <;> simp <;> first | linear_combination p1 | linear_combination p2 | linear_combination p3 - p1 - p2
  · have e : u = s • x + t • y := by
      funext k
      obtain ⟨j, rfl⟩ := π.surjective k
      rw [h j]
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4]
    rw [e]
    exact U.add_mem (U.smul_mem _ hx) (U.smul_mem _ hy)
lemma GF (H : HH U) (π : Equiv.Perm (Fin 5)) (z : ℂ) (hz : IsPrimitiveRoot z 5)
    (hd : finrank ℂ U ≤ 2) {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (x0 : x (π 0) = 2) (x1 : x (π 1) = z + z^4) (x2 : x (π 2) = z^2 + z^3)
    (x3 : x (π 3) = z^3 + z^2) (x4 : x (π 4) = z^4 + z)
    (y0 : y (π 0) = 0) (y1 : y (π 1) = z - z^4) (y2 : y (π 2) = z^2 - z^3)
    (y3 : y (π 3) = z^3 - z^2) (y4 : y (π 4) = z^4 - z) : Concl U := by
  have h5 : z ^ 5 = 1 := hz.pow_eq_one
  have e8 : z ^ 8 = z ^ 3 := by linear_combination z^3 * h5
  have e12 : z ^ 12 = z ^ 2 := by linear_combination (z^7 + z^2) * h5
  have e16 : z ^ 16 = z := by linear_combination (z^11 + z^6 + z) * h5
  refine ⟨π, Or.inr ⟨z, hz, fun u => ⟨fun hu => ?_, fun ⟨s, t, h⟩ => ?_⟩⟩⟩
  · have hne : z - z ^ 4 ≠ 0 := by
      intro e
      have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
      have e3 : z ^ 3 = 1 := by
        have : z * (z ^ 3 - 1) = 0 := by linear_combination -e
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hz0
        · linear_combination h
      exact hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) e3
    have hind : LinearIndependent ℂ ![x, y] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have a0 := congrFun hst (π 0)
      have a1 := congrFun hst (π 1)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, x0, y0, x1, y1] at a0 a1
      have hs : s = 0 := by linear_combination a0 / 2
      subst hs
      refine ⟨rfl, ?_⟩
      have : t * (z - z ^ 4) = 0 := by linear_combination a1
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hne
    have hsp : Submodule.span ℂ (Set.range ![x, y]) = U := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact hx
        · exact hy
      · rw [finrank_span_eq_card hind]; simpa using hd
    rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hu
    obtain ⟨c, hc⟩ := hu
    refine ⟨c 0 + c 1, c 0 - c 1, fun j => ?_⟩
    rw [← hc]
    fin_cases j <;> simp [Fin.sum_univ_two, x0, x1, x2, x3, x4, y0, y1, y2, y3, y4,
      e8, e12, e16] <;> ring
  · have e : u = ((s + t) / 2) • x + ((s - t) / 2) • y := by
      funext k
      obtain ⟨j, rfl⟩ := π.surjective k
      rw [h j]
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, e8, e12, e16] <;> ring
    rw [e]
    exact U.add_mem (U.smul_mem _ hx) (U.smul_mem _ hy)
lemma rev (U : Submodule ℂ V) (h : Concl U) : HH U := by
  obtain ⟨π, h⟩ := h
  intro u hu
  rw [← Equiv.sum_comp π u, ← Equiv.sum_comp π (fun j => u j ^ 3)]
  rcases h with h | ⟨z, hz, h⟩
  · obtain ⟨s, t, h⟩ := (h u).1 hu
    simp only [Fin.sum_univ_five, h]
    constructor <;> simp <;> ring
  · obtain ⟨s, t, h⟩ := (h u).1 hu
    have h5 : z ^ 5 = 1 := hz.pow_eq_one
    have e8 : z ^ 8 = z ^ 3 := by linear_combination z^3 * h5
    have e12 : z ^ 12 = z ^ 2 := by linear_combination (z^7 + z^2) * h5
    have e16 : z ^ 16 = z := by linear_combination (z^11 + z^6 + z) * h5
    have geo : 1 + z + z^2 + z^3 + z^4 = 0 := by
      have := hz.geom_sum_eq_zero (by norm_num : 1 < 5)
      simpa [Finset.sum_range_succ, add_assoc] using this
    simp only [Fin.sum_univ_five, h]
    simp [e8, e12, e16]
    constructor
    · linear_combination (s + t) * geo
    · linear_combination (s + t)^3 * geo + (3*z^1*s^2*t^1 + 3*z^4*s^1*t^2 + 1*z^7*s^0*t^3 +
        1*z^1*s^3*t^0 + 3*z^2*s^2*t^1 + 3*z^3*s^1*t^2 + 1*z^4*s^0*t^3 + 1*z^4*s^3*t^0 +
        3*z^3*s^2*t^1 + 3*z^2*s^1*t^2 + 1*z^1*s^0*t^3 + 1*z^7*s^3*t^0 + 3*z^4*s^2*t^1 +
        3*z^1*s^1*t^2 + 1*z^2*s^0*t^3 + 1*z^2*s^3*t^0) * h5
def mk5 (f g : Fin 5 → Fin 5) (h1 : ∀ i, g (f i) = i) (h2 : ∀ i, f (g i) = i) :
    Equiv.Perm (Fin 5) := ⟨f, g, h1, h2⟩
lemma mk5_apply (f g : Fin 5 → Fin 5) (h1 h2) (i : Fin 5) : mk5 f g h1 h2 i = f i := rfl
lemma tA0p (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (b : ℂ) (w0 : w (π 0) = 0) (w1 : w (π 1) = -0) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (r : ℂ)
    (v0 : v (π 0) = 0) (v1 : v (π 1) = -1) (v2 : v (π 2) = r) (v3 : v (π 3) = -r)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![4,1,2,3,0] ![4,1,2,3,0] (by decide) (by decide))
    (x := v - r • (b⁻¹ • w)) (y := b⁻¹ • w)
    (U.sub_mem hv (U.smul_mem _ (U.smul_mem _ hw))) (U.smul_mem _ hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, hb]
lemma tA0q (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (b : ℂ) (w0 : w (π 0) = 0) (w1 : w (π 1) = -0) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (r : ℂ)
    (v0 : v (π 0) = -1) (v1 : v (π 1) = 0) (v2 : v (π 2) = r) (v3 : v (π 3) = -r)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,4,2,3,1] ![0,4,2,3,1] (by decide) (by decide))
    (x := r • (b⁻¹ • w) - v) (y := b⁻¹ • w)
    (U.sub_mem (U.smul_mem _ (U.smul_mem _ hw)) hv) (U.smul_mem _ hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, hb]
lemma tB0r (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (a : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = 0) (w3 : w (π 3) = -0)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (v : V) (hv : v ∈ U) (p : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = -p) (v2 : v (π 2) = 0) (v3 : v (π 3) = -1)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,1,4,3,2] ![0,1,4,3,2] (by decide) (by decide))
    (x := a⁻¹ • w) (y := v - p • (a⁻¹ • w))
    (U.smul_mem _ hw) (U.sub_mem hv (U.smul_mem _ (U.smul_mem _ hw))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, ha]
lemma tB0s (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (a : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = 0) (w3 : w (π 3) = -0)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (v : V) (hv : v ∈ U) (p : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = -p) (v2 : v (π 2) = -1) (v3 : v (π 3) = 0)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,1,2,4,3] ![0,1,2,4,3] (by decide) (by decide))
    (x := a⁻¹ • w) (y := p • (a⁻¹ • w) - v)
    (U.smul_mem _ hw) (U.sub_mem (U.smul_mem _ (U.smul_mem _ hw)) hv) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, ha]
lemma alg1 (p q r s : ℂ) (hS : p + q + r + s + 1 = 0) (hT : r + s = 0)
    (hC : p^3 + q^3 + r^3 + s^3 + 1 = 0) : p = 0 ∨ q = 0 := by
  have hs : s = -r := by linear_combination hT
  subst hs
  have hq : q = -1 - p := by linear_combination hS
  subst hq
  have h : p * (-1 - p) = 0 := by linear_combination hC / 3
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  · exact Or.inr h
lemma alg2 (a b p r s : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (E1 : a^2*p + a^2*p + b^2*r + b^2*s = 0) (E2 : b*r^2 - b*s^2 = 0)
    (S : p + p + r + s + 1 = 0) (C : p^3 + p^3 + r^3 + s^3 + 1 = 0) :
    r = s ∧ s = -1/2 - p ∧ 4*p^2 + 2*p - 1 = 0 ∧ (b = 2*p*a ∨ b = -(2*p*a)) := by
  have h1 : (r - s) * (r + s) = 0 := by
    have : b * ((r - s) * (r + s)) = 0 := by linear_combination E2
    exact (mul_eq_zero.1 this).resolve_left hb
  rcases mul_eq_zero.1 h1 with h | h
  · have hrs : r = s := by linear_combination h
    subst hrs
    have hs : r = -1/2 - p := by linear_combination S / 2
    subst hs
    have hQ : 4*p^2 + 2*p - 1 = 0 := by linear_combination (-4/3) * C
    refine ⟨rfl, rfl, hQ, ?_⟩
    have e : (b - 2*p*a) * (b + 2*p*a) * (1/2 + p) = 0 := by
      linear_combination (-1/2) * E1 - a^2 * p * hQ
    have hp : (1/2 + p) ≠ 0 := by
      intro e2
      have : p = -1/2 := by linear_combination e2
      subst this; norm_num at hQ
    rcases mul_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hp) with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · exfalso
    have : a^2 = 0 := by linear_combination -E1 + a^2 * S + (b^2 - a^2) * h
    exact ha (pow_eq_zero_iff (by norm_num) |>.1 this)
lemma CaseBgen (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (p r s : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = p) (v2 : v (π 2) = r) (v3 : v (π 3) = s)
    (v4 : v (π 4) = 1) : Concl U := by
  have E1 := fP H π hw hv
  have E2 := fP H π hv hw
  have S := fS H π hv
  have C := fC H π hv
  rw [w0, w1, w2, w3, w4, v0, v1, v2, v3, v4] at E1 E2
  rw [v0, v1, v2, v3, v4] at S C
  obtain ⟨hrs, hs, hQ, hb'⟩ := alg2 a b p r s ha hb (by linear_combination E1)
    (by linear_combination E2) (by linear_combination S) (by linear_combination C)
  obtain ⟨d, hd2⟩ := IsAlgClosed.exists_pow_nat_eq (p^2 - 1) (by norm_num : 0 < 2)
  have hzq : (p + d)^2 - 2*p*(p + d) + 1 = 0 := by linear_combination hd2
  generalize p + d = z at hzq
  have geo : 1 + z + z^2 + z^3 + z^4 = 0 := by
    linear_combination (z^2 + (1 + 2*p)*z + 2*p*(1 + 2*p)) * hzq + (2*p*z - 1) * hQ
  have h5 : z ^ 5 = 1 := by linear_combination (z - 1) * geo
  have hz1 : z ≠ 1 := by
    intro e; subst e; norm_num at geo
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hz : IsPrimitiveRoot z 5 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime h5 hz1)
  have hm2 : 2*p = z + z^4 := by linear_combination (-z^4) * hzq + (z - 2*p) * h5
  have hca : ((z - z^4) * a⁻¹) * a = z - z^4 := by field_simp
  rcases hb' with hb' | hb'
  · refine GF H (π * mk5 ![4,0,2,3,1] ![1,4,2,3,0] (by decide) (by decide)) z hz hd
      (x := (2:ℂ) • v) (y := ((z - z^4) * a⁻¹) • w) (U.smul_mem _ hv) (U.smul_mem _ hw)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [mk5_apply, Equiv.Perm.mul_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4]
    · norm_num
    · linear_combination hm2
    · linear_combination 2 * hrs + 2 * hs - hm2 - geo
    · linear_combination 2 * hs - hm2 - geo
    · linear_combination hm2
    · ring
    · linear_combination hca
    · linear_combination ((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5
    · linear_combination -(((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5)
    · linear_combination -hca
  · refine GF H (π * mk5 ![4,0,3,2,1] ![1,4,3,2,0] (by decide) (by decide)) z hz hd
      (x := (2:ℂ) • v) (y := ((z - z^4) * a⁻¹) • w) (U.smul_mem _ hv) (U.smul_mem _ hw)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [mk5_apply, Equiv.Perm.mul_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4]
    · norm_num
    · linear_combination hm2
    · linear_combination 2 * hs - hm2 - geo
    · linear_combination 2 * hrs + 2 * hs - hm2 - geo
    · linear_combination hm2
    · ring
    · linear_combination hca
    · linear_combination -((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5
    · linear_combination ((z - z^4) * a⁻¹) * hb' - (2*p*hca + (z - z^4)*hm2 - z^3*h5)
    · linear_combination -hca
lemma CaseB1 (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hne : a ≠ 0 ∨ b ≠ 0) (v : V) (hv : v ∈ U) (p q r s : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = q) (v2 : v (π 2) = r) (v3 : v (π 3) = s)
    (v4 : v (π 4) = 1) : Concl U := by
  have E1 := fP H π hw hv
  have S := fS H π hv
  have C := fC H π hv
  rw [w0, w1, w2, w3, w4, v0, v1, v2, v3, v4] at E1
  rw [v0, v1, v2, v3, v4] at S C
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    have hb : b ≠ 0 := hne.resolve_left (by simp)
    have hrs : r + s = 0 := by
      have : b^2 * (r + s) = 0 := by linear_combination E1
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hb)
    rcases alg1 p q r s (by linear_combination S) hrs (by linear_combination C) with hp | hq
    · exact tA0p π H w hw b w0 w1 w2 w3 w4 hb v hv r (v0.trans hp)
        (by rw [v1]; linear_combination S - hp - hrs) v2 (by rw [v3]; linear_combination hrs) v4
    · exact tA0q π H w hw b w0 w1 w2 w3 w4 hb v hv r
        (by rw [v0]; linear_combination S - hq - hrs) (v1.trans hq) v2
        (by rw [v3]; linear_combination hrs) v4
  · by_cases hb : b = 0
    · subst hb
      have hpq : p + q = 0 := by
        have : a^2 * (p + q) = 0 := by linear_combination E1
        exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ ha)
      rcases alg1 r s p q (by linear_combination S) hpq (by linear_combination C) with hr | hs
      · exact tB0r π H w hw a w0 w1 w2 w3 w4 ha v hv p v0
          (by rw [v1]; linear_combination hpq) (v2.trans hr)
          (by rw [v3]; linear_combination S - hr - hpq) v4
      · exact tB0s π H w hw a w0 w1 w2 w3 w4 ha v hv p v0
          (by rw [v1]; linear_combination hpq)
          (by rw [v2]; linear_combination S - hs - hpq) (v3.trans hs) v4
    · have hvU : v + ((q - p) / (2 * a)) • w ∈ U := U.add_mem hv (U.smul_mem _ hw)
      refine CaseBgen π H hd w hw a b w0 w1 w2 w3 w4 ha hb _ hvU
        (p + (q - p) / (2 * a) * a) (r + (q - p) / (2 * a) * b) (s + (q - p) / (2 * a) * (-b))
        ?_ ?_ ?_ ?_ ?_
      all_goals simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w0, w1, w2, w3, w4,
        v0, v1, v2, v3, v4]
      · field_simp; ring
      · simp
lemma CaseB (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hne : a ≠ 0 ∨ b ≠ 0) (v : V) (hv : v ∈ U) (hv4 : v (π 4) ≠ 0) :
    Concl U := by
  have hvU : (v (π 4))⁻¹ • v ∈ U := U.smul_mem _ hv
  exact CaseB1 π H hd w hw a b w0 w1 w2 w3 w4 hne _ hvU _ _ _ _ rfl rfl rfl rfl
    (by simp [hv4])
lemma CaseA (π : Equiv.Perm (Fin 5)) (H : HH U) (x : V) (hx : x ∈ U)
    (a b : ℂ) (x0 : x (π 0) = a) (x1 : x (π 1) = -a) (x2 : x (π 2) = b) (x3 : x (π 3) = -b)
    (x4 : x (π 4) = 0) (y : V) (hy : y ∈ U)
    (a' b' : ℂ) (y0 : y (π 0) = a') (y1 : y (π 1) = -a') (y2 : y (π 2) = b') (y3 : y (π 3) = -b')
    (y4 : y (π 4) = 0) (hind : ∀ s t : ℂ, s • x + t • y = 0 → s = 0 ∧ t = 0) : Concl U := by
  have hdet : a * b' - a' * b ≠ 0 := by
    intro hd0
    have k1 := hind b' (-b) (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4] <;>
        first | linear_combination hd0 | linear_combination -hd0 | ring)
    have k2 := hind a' (-a) (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4] <;>
        first | linear_combination hd0 | linear_combination -hd0 | ring)
    have hb : b = 0 := by linear_combination -k1.2
    have ha : a = 0 := by linear_combination -k2.2
    have k3 := hind 1 0 (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, ha, hb])
    exact one_ne_zero k3.1
  refine GP H π (x := (a * b' - a' * b)⁻¹ • (b' • x - b • y))
    (y := (a * b' - a' * b)⁻¹ • (a • y - a' • x))
    (U.smul_mem _ (U.sub_mem (U.smul_mem _ hx) (U.smul_mem _ hy)))
    (U.smul_mem _ (U.sub_mem (U.smul_mem _ hy) (U.smul_mem _ hx))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, x0, x1, x2, x3, x4,
    y0, y1, y2, y3, y4]
  all_goals field_simp
  all_goals ring
lemma fac (H : HH U) {x : V} (hx : x ∈ U) (x4 : x 4 = 0) :
    (x 0 + x 1) * (x 0 + x 2) * (x 0 + x 3) = 0 := by
  have S := (H x hx).1
  have C := (H x hx).2
  simp only [Fin.sum_univ_five, x4] at S C
  have h3 : x 3 = -(x 0 + x 1 + x 2) := by linear_combination S
  rw [h3] at C ⊢
  linear_combination C / 3
lemma two {α β : ℂ} (l m : ℂ) (hlm : l ≠ m) (h1 : α + l * β = 0) (h2 : α + m * β = 0) :
    α = 0 ∧ β = 0 := by
  have hb : β = 0 := by
    have : (l - m) * β = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hlm)
  subst hb
  exact ⟨by linear_combination h1, rfl⟩
lemma pig (α1 β1 α2 β2 α3 β3 : ℂ)
    (F : ∀ l : ℂ, (α1 + l * β1) * (α2 + l * β2) * (α3 + l * β3) = 0) :
    (α1 = 0 ∧ β1 = 0) ∨ (α2 = 0 ∧ β2 = 0) ∨ (α3 = 0 ∧ β3 = 0) := by
  have e0 := F 0
  have e1 := F 1
  have e2 := F 2
  have e3 := F 3
  simp only [mul_eq_zero] at e0 e1 e2 e3
  rcases e0 with (a0 | b0) | c0 <;> rcases e1 with (a1 | b1) | c1 <;>
    rcases e2 with (a2 | b2) | c2 <;> rcases e3 with (a3 | b3) | c3 <;>
    first
    | exact Or.inl (two 0 1 (by norm_num) a0 a1)
    | exact Or.inl (two 0 2 (by norm_num) a0 a2)
    | exact Or.inl (two 0 3 (by norm_num) a0 a3)
    | exact Or.inl (two 1 2 (by norm_num) a1 a2)
    | exact Or.inl (two 1 3 (by norm_num) a1 a3)
    | exact Or.inl (two 2 3 (by norm_num) a2 a3)
    | exact Or.inr (Or.inl (two 0 1 (by norm_num) b0 b1))
    | exact Or.inr (Or.inl (two 0 2 (by norm_num) b0 b2))
    | exact Or.inr (Or.inl (two 0 3 (by norm_num) b0 b3))
    | exact Or.inr (Or.inl (two 1 2 (by norm_num) b1 b2))
    | exact Or.inr (Or.inl (two 1 3 (by norm_num) b1 b3))
    | exact Or.inr (Or.inl (two 2 3 (by norm_num) b2 b3))
    | exact Or.inr (Or.inr (two 0 1 (by norm_num) c0 c1))
    | exact Or.inr (Or.inr (two 0 2 (by norm_num) c0 c2))
    | exact Or.inr (Or.inr (two 0 3 (by norm_num) c0 c3))
    | exact Or.inr (Or.inr (two 1 2 (by norm_num) c1 c2))
    | exact Or.inr (Or.inr (two 1 3 (by norm_num) c1 c3))
    | exact Or.inr (Or.inr (two 2 3 (by norm_num) c2 c3))
lemma killG {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (X : Submodule ℂ M) {n : ℕ} (φ : M →ₗ[ℂ] (Fin n → ℂ)) (h : n < finrank ℂ X) :
    ∃ v ∈ X, v ≠ 0 ∧ φ v = 0 := by
  let ψ := φ.domRestrict X
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 : finrank ℂ (LinearMap.range ψ) ≤ n := by
    have := Submodule.finrank_le (LinearMap.range ψ); simpa using this
  have h3 : LinearMap.ker ψ ≠ ⊥ := by
    intro e; rw [e, finrank_bot] at h1; omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  refine ⟨w.1, w.2, fun e => hw0 (Subtype.ext e), ?_⟩
  have : ψ w = 0 := hw
  simpa [ψ] using this
def Q12 : Equiv.Perm (Fin 5) := mk5 ![0,2,1,3,4] ![0,2,1,3,4] (by decide) (by decide)
def Q13 : Equiv.Perm (Fin 5) := mk5 ![0,3,2,1,4] ![0,3,2,1,4] (by decide) (by decide)
lemma nzf (π : Equiv.Perm (Fin 5)) (w : V) (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a)
    (w2 : w (π 2) = b) (w3 : w (π 3) = -b) (w4 : w (π 4) = 0) (hw : w ≠ 0) :
    a ≠ 0 ∨ b ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  funext k
  obtain ⟨j, rfl⟩ := π.surjective k
  fin_cases j <;> simp [w0, w1, w2, w3, w4, h.1, h.2]
lemma topB (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U) (hw0 : w ≠ 0)
    (w4 : w 4 = 0) (v : V) (hv : v ∈ U) (hv4 : v 4 ≠ 0) : Concl U := by
  have S := (H w hw).1
  simp only [Fin.sum_univ_five, w4] at S
  rcases mul_eq_zero.1 (fac H hw w4) with h | h
  · rcases mul_eq_zero.1 h with h | h
    · have w0 : w ((1 : Equiv.Perm (Fin 5)) 0) = w 0 := rfl
      have w1 : w ((1 : Equiv.Perm (Fin 5)) 1) = -(w 0) := by
        show w 1 = _; linear_combination h
      have w2 : w ((1 : Equiv.Perm (Fin 5)) 2) = w 2 := rfl
      have w3 : w ((1 : Equiv.Perm (Fin 5)) 3) = -(w 2) := by
        show w 3 = _; linear_combination S - h
      have w4' : w ((1 : Equiv.Perm (Fin 5)) 4) = 0 := w4
      exact CaseB 1 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf 1 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
    · have w0 : w (Q12 0) = w 0 := rfl
      have w1 : w (Q12 1) = -(w 0) := by
        show w 2 = _; linear_combination h
      have w2 : w (Q12 2) = w 1 := rfl
      have w3 : w (Q12 3) = -(w 1) := by
        show w 3 = _; linear_combination S - h
      have w4' : w (Q12 4) = 0 := w4
      exact CaseB Q12 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf Q12 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
  · have w0 : w (Q13 0) = w 0 := rfl
    have w1 : w (Q13 1) = -(w 0) := by
      show w 3 = _; linear_combination h
    have w2 : w (Q13 2) = w 2 := rfl
    have w3 : w (Q13 3) = -(w 2) := by
      show w 1 = _; linear_combination S - h
    have w4' : w (Q13 4) = 0 := w4
    exact CaseB Q13 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf Q13 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
lemma topA (H : HH U) (x : V) (hx : x ∈ U) (x4 : x 4 = 0) (y : V) (hy : y ∈ U) (y4 : y 4 = 0)
    (hind : ∀ s t : ℂ, s • x + t • y = 0 → s = 0 ∧ t = 0) : Concl U := by
  have Sx := (H x hx).1
  have Sy := (H y hy).1
  simp only [Fin.sum_univ_five, x4, y4] at Sx Sy
  have F : ∀ l : ℂ, ((x 0 + x 1) + l * (y 0 + y 1)) * ((x 0 + x 2) + l * (y 0 + y 2)) *
      ((x 0 + x 3) + l * (y 0 + y 3)) = 0 := by
    intro l
    have := fac H (U.add_mem hx (U.smul_mem l hy)) (by simp [x4, y4])
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  rcases pig _ _ _ _ _ _ F with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact CaseA 1 H x hx (x 0) (x 2) rfl (by show x 1 = _; linear_combination h) rfl
      (by show x 3 = _; linear_combination Sx - h) x4 y hy (y 0) (y 2) rfl
      (by show y 1 = _; linear_combination h') rfl
      (by show y 3 = _; linear_combination Sy - h') y4 hind
  · exact CaseA Q12 H x hx (x 0) (x 1) rfl (by show x 2 = _; linear_combination h) rfl
      (by show x 3 = _; linear_combination Sx - h) x4 y hy (y 0) (y 1) rfl
      (by show y 2 = _; linear_combination h') rfl
      (by show y 3 = _; linear_combination Sy - h') y4 hind
  · exact CaseA Q13 H x hx (x 0) (x 2) rfl (by show x 3 = _; linear_combination h) rfl
      (by show x 1 = _; linear_combination Sx - h) x4 y hy (y 0) (y 2) rfl
      (by show y 3 = _; linear_combination h') rfl
      (by show y 1 = _; linear_combination Sy - h') y4 hind
lemma fwd (U : Submodule ℂ V) (hd : 2 ≤ finrank ℂ U) (H : HH U) : Concl U := by
  obtain ⟨b0, hb0, hb00, e0⟩ :=
    killG U (LinearMap.pi ![(LinearMap.proj 4 : V →ₗ[ℂ] ℂ)]) (by omega)
  have hb04 : b0 4 = 0 := by simpa using congrFun e0 0
  obtain ⟨k, hk⟩ : ∃ k, b0 k ≠ 0 := by
    by_contra h; push_neg at h; exact hb00 (funext h)
  by_cases hA : ∃ b1 ∈ U, b1 ≠ 0 ∧ b1 4 = 0 ∧ b1 k = 0
  · obtain ⟨b1, hb1, hb10, hb14, hb1k⟩ := hA
    refine topA H b0 hb0 hb04 b1 hb1 hb14 fun s t hst => ?_
    have e := congrFun hst k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb1k, mul_zero, add_zero,
      Pi.zero_apply] at e
    have hs : s = 0 := (mul_eq_zero.1 e).resolve_right hk
    subst hs
    refine ⟨rfl, ?_⟩
    simp only [zero_smul, zero_add, smul_eq_zero] at hst
    exact hst.resolve_right hb10
  · push_neg at hA
    have hd2 : finrank ℂ U ≤ 2 := by
      by_contra h3; push_neg at h3
      obtain ⟨b1, hb1, hb10, e⟩ := killG U (LinearMap.pi ![(LinearMap.proj 4 : V →ₗ[ℂ] ℂ),
        (LinearMap.proj k : V →ₗ[ℂ] ℂ)]) (by omega)
      exact hA b1 hb1 hb10 (by simpa using congrFun e 0) (by simpa using congrFun e 1)
    have hv : ∃ v ∈ U, v 4 ≠ 0 := by
      by_contra hv; push_neg at hv
      obtain ⟨b1, hb1, hb10, e⟩ :=
        killG U (LinearMap.pi ![(LinearMap.proj k : V →ₗ[ℂ] ℂ)]) (by omega)
      exact hA b1 hb1 hb10 (hv b1 hb1) (by simpa using congrFun e 0)
    obtain ⟨v, hv, hv4⟩ := hv
    exact topB H hd2 b0 hb0 hb00 hb04 v hv hv4
end
end Cubic
open Cubic in
theorem Cubic : ∀ U : Submodule ℂ (Fin 5 → ℂ), 2 ≤ Module.finrank ℂ U →
  ((∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0) ↔
    ∃ π : Equiv.Perm (Fin 5),
      (∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
        u (π j) = (![s, -s, t, -t, 0] : Fin 5 → ℂ) j) ∨
      (∃ z : ℂ, IsPrimitiveRoot z 5 ∧
        ∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
          u (π j) = s * z^j.val + t * z^(4*j.val))) := by
  intro U hd
  exact ⟨fwd U hd, rev U⟩

end Reuse303

section Reuse142

namespace Even_aux

open Finset

theorem key (n : ℕ) (w : Fin n → ℂ)
    (h : ∀ j : ℕ, 1 ≤ j →
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 * j), ∏ i ∈ S, w i = 0) :
    ∏ i, (1 + w i) + ∏ i, (1 - w i) = 2 := by
  have h1 : ∏ i, (1 - w i) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, (-1) ^ t.card * ∏ i ∈ t, w i := by
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_neg]
  have hk : ∀ k : ℕ,
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ((∏ i ∈ t, w i) + (-1) ^ t.card * ∏ i ∈ t, w i) =
      (1 + (-1) ^ k) * ∑ t ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ t, w i := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_powersetCard.mp ht).2]
    ring
  rw [Finset.prod_one_add, h1, ← Finset.sum_add_distrib,
    ← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
      (t := Finset.range ((Finset.univ : Finset (Fin n)).card + 1))
      (fun t _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ t)))]
  simp_rw [← Finset.powersetCard_eq_filter, hk]
  rw [Finset.sum_eq_single 0]
  · simp
    norm_num
  · intro k _ hk0
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show j + j = 2 * j by ring, h j (by omega), mul_zero]
    · rw [pow_succ, pow_mul]
      norm_num
  · intro h0
    simp at h0

theorem coord_zero (n : ℕ) (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ w ∈ W, ∏ i, (1 + w i) + ∏ i, (1 - w i) = 2)
    (u : Fin n → ℂ) (hu : u ∈ W) (k : Fin n) (huk : u k ≠ 0)
    (z : Fin n → ℂ) (hz : z ∈ W) (hzk : z k = 0) : z = 0 := by
  by_contra hne
  obtain ⟨i0, hi0⟩ : ∃ i0, z i0 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  set w0 : Fin n → ℂ := (-1 / u k) • u with hw0
  set s : ℂ := (1 - w0 i0) / z i0 with hs
  have hw : w0 + s • z ∈ W := W.add_mem (W.smul_mem _ hu) (W.smul_mem _ hz)
  have e := hW _ hw
  have hA : ∏ i, (1 + (w0 + s • z) i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [hw0, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzk, mul_zero, add_zero]
    field_simp
    ring
  have hB : ∏ i, (1 - (w0 + s • z) i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i0)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
    field_simp
    ring
  rw [hA, hB] at e
  norm_num at e

end Even_aux

open Even_aux in
theorem Even : ∀ (n : ℕ) (W : Submodule ℂ (Fin n → ℂ)), (∀ w ∈ W, ∀ j : ℕ, 1 ≤ j → ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 * j), ∏ i ∈ S, w i = 0) → Module.finrank ℂ W ≤ 1 := by
  intro n W hW
  have hW' : ∀ w ∈ W, ∏ i, (1 + w i) + ∏ i, (1 - w i) = 2 :=
    fun w hw => key n w (hW w hw)
  by_cases hex : ∃ u ∈ W, u ≠ 0
  · obtain ⟨u, hu, hu0⟩ := hex
    obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu0 (funext hall)
    refine finrank_le_one (⟨u, hu⟩ : W) fun w => ⟨w.1 k / u k, ?_⟩
    have hz := coord_zero n W hW' u hu k hk (u k • w.1 - w.1 k • u)
      (W.sub_mem (W.smul_mem _ w.2) (W.smul_mem _ hu)) (by simp; ring)
    apply Subtype.ext
    simp only [SetLike.val_smul]
    have hz' : u k • w.1 = w.1 k • u := sub_eq_zero.mp hz
    funext i
    have := congrFun hz' i
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp
    linear_combination this.symm
  · push Not at hex
    refine finrank_le_one (0 : W) fun w => ⟨0, ?_⟩
    apply Subtype.ext
    simp [hex w.1 w.2]

end Reuse142


open scoped BigOperators

abbrev Row := Fin 4 → ℂ
abbrev Col (n : ℕ) := Fin n → ℂ
abbrev Mat (n : ℕ) := Matrix (Fin 4) (Fin n) ℂ

def OnLevel {n : ℕ} (L : Submodule ℂ (Mat n)) : Prop :=
  ∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + X i (f i))) =
      (∑ _f : Fin 4 ↪ Fin n, (1 : ℂ))

lemma quadratic {n : ℕ} (hn : 4 ≤ n) {L : Submodule ℂ (Mat n)}
    (valid : OnLevel L) {X : Mat n} (hX : X ∈ L) :
    (∑ i, ∑ j, (X i j)^2) = 0 := by
  have q := (Quadratic_aux.coeffs_zero_of_const X
    (fun t => (valid _ (L.smul_mem t hX)).2.2)).1
  rw [Quadratic_aux.e2_eq X (valid _ hX).1 (valid _ hX).2.1] at q
  have nz : Quadratic_aux.mult2 n / 2 ≠ 0 := by
    unfold Quadratic_aux.mult2 Quadratic_aux.mult3
    exact div_ne_zero (mul_ne_zero (by exact_mod_cast (show n - 2 ≠ 0 by omega))
      (by exact_mod_cast (show n - 3 ≠ 0 by omega))) (by norm_num)
  simpa only [Fin.sum_univ_four, Quadratic_aux.dot, pow_two] using
    (mul_eq_zero.mp q).resolve_left nz

lemma rank_cap {n : ℕ} (X : Mat n) (h : ∀ j, ∑ i, X i j = 0) :
    X.rank ≤ 3 := by
  let A : Matrix (Fin 4) (Fin 3) ℂ :=
    !![1,0,0; 0,1,0; 0,0,1; -1,-1,-1]
  let B : Matrix (Fin 3) (Fin n) ℂ := fun i j => X i.castSucc j
  have fac : A * B = X := by
    apply Matrix.ext
    intro i j
    have hs := h j
    rw [Fin.sum_univ_four] at hs
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i
    · change (1 : ℂ) * X 0 j + 0 * X 1 j + 0 * X 2 j = X 0 j
      ring
    · change (0 : ℂ) * X 0 j + 1 * X 1 j + 0 * X 2 j = X 1 j
      ring
    · change (0 : ℂ) * X 0 j + 0 * X 1 j + 1 * X 2 j = X 2 j
      ring
    · change (-1 : ℂ) * X 0 j + (-1) * X 1 j + (-1) * X 2 j = X 3 j
      linear_combination -hs
  rw [← fac]
  exact (Matrix.rank_mul_le_left A B).trans (by simpa using Matrix.rank_le_card_width A)

lemma coord_nonzero {n : ℕ} {x : Col n} (h : x ≠ 0) :
    ∃ i, x i ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (funext hn)

lemma excluded_first {n : ℕ} (hn : 5 ≤ n) {L : Submodule ℂ (Mat n)}
    (valid : OnLevel L) (large : n ≤ Module.finrank ℂ L) :
    ¬ ∃ (a : Row) (K : Submodule ℂ (Col n)), a ≠ 0 ∧
      2 * Module.finrank ℂ L + 1 ≤ 2 * Module.finrank ℂ K + n ∧
      (∀ x ∈ K, (fun i j => a i * x j) ∈ L) := by
  rintro ⟨a, K, ha, hk, hK⟩
  obtain ⟨i, hi⟩ := coord_nonzero ha
  obtain ⟨x, hx, hxn⟩ : ∃ x ∈ K, x ≠ 0 := by
    by_contra h
    push Not at h
    have b : K = ⊥ := (Submodule.eq_bot_iff K).mpr h
    have zero : Module.finrank ℂ K = 0 := by simp [b]
    omega
  obtain ⟨j, hj⟩ := coord_nonzero hxn
  have ac : ∑ i, a i = 0 := by
    have h := (valid _ (hK x hx)).2.1 j
    change (∑ i, a i * x j) = 0 at h
    rw [← Finset.sum_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hj
  have xc (y : Col n) (hy : y ∈ K) : (∑ j, y j) = 0 := by
    have h := (valid _ (hK y hy)).1 i
    change (∑ j, a i * y j) = 0 at h
    rw [← Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left hi
  have bound : 2 * Module.finrank ℂ K ≤ n :=
    (RankOne n _ (by omega)).mp ⟨a, K, ha, ac, rfl,
      fun y hy => ⟨xc y hy, (valid _ (hK y hy)).2.2⟩⟩
  omega

lemma nonzero_cubic (U : Submodule ℂ (Col 5)) (hd : Module.finrank ℂ U = 2)
    (hi : ∀ u ∈ U, (∑ j, u j) = 0 ∧ RankOne.pw 2 u = 0) :
    ∃ u ∈ U, RankOne.pw 3 u ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have h' (u : Col 5) (hu : u ∈ U) :
      (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0 := ⟨(hi u hu).1, h u hu⟩
  obtain ⟨π, hp | ⟨z, hz, hp⟩⟩ := (Cubic U hd.ge).mp h'
  · let u : Col 5 := fun j => (![1,-1,0,0,0] : Col 5) (π.symm j)
    have hu : u ∈ U := (hp u).mpr ⟨1,0,by intro j; simp [u]⟩
    have q := (hi u hu).2
    unfold RankOne.pw at q
    rw [← Equiv.sum_comp π (fun j => u j ^ 2)] at q
    norm_num [u, Fin.sum_univ_five] at q
  · let u : Col 5 := fun j => z^(π.symm j).val
    let v : Col 5 := fun j => z^(4*(π.symm j).val)
    have hu : u ∈ U := (hp u).mpr ⟨1,0,by intro j; simp [u]⟩
    have hv : v ∈ U := (hp v).mpr ⟨0,1,by intro j; simp [v]⟩
    have q := RankOne.p2_add u v
    rw [(hi (u+v) (U.add_mem hu hv)).2, (hi u hu).2, (hi v hv).2] at q
    have cross : (∑ j, u j * v j) = (5 : ℂ) := by
      rw [← Equiv.sum_comp π (fun j => u j * v j)]
      have term (i : Fin 5) : u (π i) * v (π i) = 1 := by
        simp only [u, v, Equiv.symm_apply_apply, ← pow_add]
        rw [show i.val + 4 * i.val = 5 * i.val by omega, pow_mul, hz.pow_eq_one]
        simp
      simp [term]
    rw [cross] at q
    norm_num at q

lemma nonzero_quartic (U : Submodule ℂ (Col 5)) (hd : Module.finrank ℂ U = 2)
    (hi : ∀ u ∈ U, (∑ j, u j) = 0 ∧ RankOne.pw 2 u = 0) :
    ∃ u ∈ U, RankOne.pw 4 u ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have products (u : Col 5) (hu : u ∈ U) :
      (∏ j, (1 + u j)) + (∏ j, (1 - u j)) = 2 := by
    have h1 := (hi u hu).1
    have h2 := (hi u hu).2
    have h4 := h u hu
    simp only [RankOne.pw, Fin.sum_univ_five] at h1 h2 h4
    rw [Fin.prod_univ_five, Fin.prod_univ_five]
    let s := u 0 + u 1 + u 2 + u 3 + u 4
    let q := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + u 4 ^ 2
    let c := u 0 ^ 3 + u 1 ^ 3 + u 2 ^ 3 + u 3 ^ 3 + u 4 ^ 3
    linear_combination (s + s^3/12 - s*q/2 + 2*c/3)*h1 + (q/4-1)*h2 - h4/2
  obtain ⟨u, hu, hnu⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra h
    push Not at h
    have b : U = ⊥ := (Submodule.eq_bot_iff U).mpr h
    have zero : Module.finrank ℂ U = 0 := by simp [b]
    omega
  obtain ⟨j, hj⟩ := coord_nonzero hnu
  let f : U →ₗ[ℂ] ℂ := (LinearMap.proj j).comp U.subtype
  have inj : Function.Injective f := by
    intro a b hab
    have hz : (a.val - b.val) j = 0 := by
      change a.val j = b.val j at hab
      simp [hab]
    exact Subtype.ext (sub_eq_zero.mp
      (Even_aux.coord_zero 5 U products u hu j hj _ (U.sub_mem a.2 b.2) hz))
  have bound := LinearMap.finrank_le_finrank_of_injective inj
  simp [hd] at bound

noncomputable def moment (r : ℕ) : MvPolynomial (Fin 5) ℂ :=
  ∑ j, MvPolynomial.X j ^ r

lemma some_direction (U : Submodule ℂ (Col 5)) (hd : Module.finrank ℂ U = 2)
    (hi : ∀ u ∈ U, (∑ j, u j) = 0 ∧ RankOne.pw 2 u = 0) :
    ∃ u ∈ U, RankOne.pw 3 u ≠ 0 ∧ RankOne.pw 4 u ≠ 0 := by
  have ev (u : Col 5) (r : ℕ) :
      MvPolynomial.eval u (moment r) = RankOne.pw r u := by
    simp [moment, RankOne.pw]
  have h (i : ℕ) (hi' : i ∈ ({3,4} : Finset ℕ)) :
      ∃ u ∈ U, MvPolynomial.eval u (moment i) ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl
    · simpa only [ev] using nonzero_cubic U hd hi
    · simpa only [ev] using nonzero_quartic U hd hi
  obtain ⟨u, hu, h'⟩ := RankOne.generic U {3,4} moment h
  exact ⟨u,hu,by simpa only [ev] using h' 3 (by simp),
    by simpa only [ev] using h' 4 (by simp)⟩

def outer {n : ℕ} (u : Col n) : Row →ₗ[ℂ] Mat n where
  toFun a i j := a i * u j
  map_add' a b := by
    apply Matrix.ext
    intro i j
    exact add_mul (a i) (b i) (u j)
  map_smul' c a := by
    apply Matrix.ext
    intro i j
    exact mul_assoc c (a i) (u j)

lemma fibre_dimension {n : ℕ} {L : Submodule ℂ (Mat n)} (valid : OnLevel L)
    (U : Submodule ℂ (Col n)) (hd : Module.finrank ℂ U = 2)
    (hrows : ∀ X ∈ L, ∀ i, X i ∈ U) (u : Col n) (hu : u ∈ U) (hnu : u ≠ 0) :
    Module.finrank ℂ L ≤ Module.finrank ℂ (L.comap (outer u)) + 3 := by
  classical
  let u0 : U := ⟨u, hu⟩
  let K : Submodule ℂ U := ℂ ∙ u0
  let row (i : Fin 4) : L →ₗ[ℂ] U :=
    { toFun := fun X => ⟨X.val i, hrows X.val X.prop i⟩
      map_add' := fun X Y => Subtype.ext (by rfl)
      map_smul' := fun c X => Subtype.ext (by rfl) }
  let F : L →ₗ[ℂ] (Fin 3 → U ⧸ K) :=
    LinearMap.pi (fun i => K.mkQ.comp (row i.castSucc))
  let W := L.comap (outer u)
  obtain ⟨j0, hj0⟩ := coord_nonzero hnu
  have inLine (Y : LinearMap.ker F) (i : Fin 4) : row i Y.val ∈ K := by
    have first (k : Fin 3) : row k.castSucc Y.val ∈ K := by
      have z : F Y.val = 0 := Y.prop
      have hz := congrFun z k
      change K.mkQ (row k.castSucc Y.val) = 0 at hz
      have hh : row k.castSucc Y.val ∈ LinearMap.ker K.mkQ := hz
      rwa [Submodule.ker_mkQ] at hh
    have last : row 3 Y.val =
        -(row 0 Y.val + row 1 Y.val + row 2 Y.val) := by
      apply Subtype.ext
      funext j
      change Y.val.val 3 j = -(Y.val.val 0 j + Y.val.val 1 j + Y.val.val 2 j)
      have h := (valid Y.val.val Y.val.prop).2.1 j
      rw [Fin.sum_univ_four] at h
      linear_combination h
    fin_cases i
    · exact first 0
    · exact first 1
    · exact first 2
    · change row 3 Y.val ∈ K
      rw [last]
      exact K.neg_mem (K.add_mem (K.add_mem (first 0) (first 1)) (first 2))
  let project : Mat n →ₗ[ℂ] Row :=
    { toFun := fun X i => X i j0 / u j0
      map_add' := by intro X Y; funext i; simp [add_div]
      map_smul' := by intro a X; funext i; simp [mul_div_assoc] }
  let read : LinearMap.ker F →ₗ[ℂ] Row :=
    project.comp (L.subtype.comp (LinearMap.ker F).subtype)
  have reconstruct (Y : LinearMap.ker F) : outer u (read Y) = Y.val.val := by
    ext i j
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp (inLine Y i)
    have atCoord (k : Fin n) : b * u k = Y.val.val i k :=
      congrFun (congrArg Subtype.val hb) k
    change (Y.val.val i j0 / u j0) * u j = Y.val.val i j
    rw [← atCoord j0, mul_div_cancel_right₀ _ hj0, atCoord j]
  let readW := read.codRestrict W (fun Y => by
    change outer u (read Y) ∈ L
    rw [reconstruct Y]
    exact Y.val.prop)
  have injective : Function.Injective readW := by
    intro Y Z eq
    have h : read Y = read Z := congrArg Subtype.val eq
    exact Subtype.ext (Subtype.ext (by rw [← reconstruct Y, ← reconstruct Z, h]))
  have kerBound :
      Module.finrank ℂ (LinearMap.ker F) ≤ Module.finrank ℂ W :=
    LinearMap.finrank_le_finrank_of_injective injective
  have nu0 : u0 ≠ 0 := fun e => hnu (congrArg Subtype.val e)
  have dimK : Module.finrank ℂ K = 1 := finrank_span_singleton nu0
  have dimQ : Module.finrank ℂ (U ⧸ K) = 1 := by
    have q := K.finrank_quotient_add_finrank
    omega
  have dimCod : Module.finrank ℂ (Fin 3 → U ⧸ K) = 3 := by
    rw [Module.finrank, rank_fun_eq_lift_mul, Cardinal.toNat_mul, Cardinal.toNat_lift,
      Cardinal.toNat_natCast]
    change Fintype.card (Fin 3) * Module.finrank ℂ (U ⧸ K) = 3
    simp [dimQ]
  have rangeBound := LinearMap.finrank_le_finrank_of_injective
    (LinearMap.range F).subtype_injective
  rw [dimCod] at rangeBound
  have dims := F.finrank_range_add_finrank_ker
  change Module.finrank ℂ L ≤ Module.finrank ℂ W + 3
  omega

lemma small_row_space (W : Submodule ℂ Row)
    (centred : ∀ a ∈ W, ∑ i, a i = 0)
    (vanish3 : ∀ a ∈ W, RankOne.E3 a = 0)
    (vanish4 : ∀ a ∈ W, RankOne.E4 a = 0) :
    Module.finrank ℂ W ≤ 1 := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : Fin 4, ∀ a ∈ W, a z = 0 := by
    by_contra h
    push Not at h
    have good (i : Fin 4) (_ : i ∈ Finset.univ) :
        ∃ a ∈ W, MvPolynomial.eval a (MvPolynomial.X i) ≠ 0 := by
      simpa using h i
    obtain ⟨a,ha,hn⟩ := RankOne.generic W Finset.univ MvPolynomial.X good
    have hnz (i : Fin 4) : a i ≠ 0 := by simpa using hn i (Finset.mem_univ i)
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (hnz 0) (hnz 1)) (hnz 2)) (hnz 3))
      (vanish4 a ha)
  obtain ⟨w, hwz, hw⟩ : ∃ w : Fin 4, w ≠ z ∧ ∀ a ∈ W, a w = 0 := by
    by_contra h
    have good (i : Fin 4) (hi : i ∈ Finset.univ.erase z) :
        ∃ a ∈ W, MvPolynomial.eval a (MvPolynomial.X i) ≠ 0 := by
      have hn : ¬ ∀ a ∈ W, a i = 0 :=
        fun hg => h ⟨i, (Finset.mem_erase.mp hi).1, hg⟩
      push Not at hn
      simpa using hn
    obtain ⟨a,ha,hA⟩ := RankOne.generic W (Finset.univ.erase z) MvPolynomial.X good
    have nz (i : Fin 4) (hiz : i ≠ z) : a i ≠ 0 := by
      simpa using hA i (Finset.mem_erase.mpr ⟨hiz, Finset.mem_univ i⟩)
    have h3 := vanish3 a ha
    have zero := hz a ha
    fin_cases z
    · change a 0 = 0 at zero
      simp only [RankOne.E3, zero, zero_mul, mul_zero, add_zero, zero_add] at h3
      exact (mul_ne_zero (mul_ne_zero (nz 1 (by decide)) (nz 2 (by decide))) (nz 3 (by decide))) h3
    · change a 1 = 0 at zero
      simp only [RankOne.E3, zero, zero_mul, mul_zero, add_zero, zero_add] at h3
      exact (mul_ne_zero (mul_ne_zero (nz 0 (by decide)) (nz 2 (by decide))) (nz 3 (by decide))) h3
    · change a 2 = 0 at zero
      simp only [RankOne.E3, zero, zero_mul, mul_zero, add_zero, zero_add] at h3
      exact (mul_ne_zero (mul_ne_zero (nz 0 (by decide)) (nz 1 (by decide))) (nz 3 (by decide))) h3
    · change a 3 = 0 at zero
      simp only [RankOne.E3, zero, zero_mul, mul_zero, add_zero, zero_add] at h3
      exact (mul_ne_zero (mul_ne_zero (nz 0 (by decide)) (nz 1 (by decide))) (nz 2 (by decide))) h3
  obtain ⟨i, hiz, hiw⟩ : ∃ i : Fin 4, i ≠ z ∧ i ≠ w := by
    by_contra h
    push Not at h
    have hh : ({z, w} : Finset (Fin 4)) = Finset.univ := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
      exact (eq_or_ne j z).imp_right (h j)
    have sz := congrArg Finset.card hh
    simp [hwz.symm] at sz
  let f : W →ₗ[ℂ] ℂ := (LinearMap.proj i).comp W.subtype
  have injective : Function.Injective f := by
    intro a b eq
    let c := a.val - b.val
    have hc : c ∈ W := W.sub_mem a.prop b.prop
    have ez := hz c hc
    have ew := hw c hc
    have ei : c i = 0 := by
      change a.val i = b.val i at eq
      simp [c, eq]
    have hzero : c = 0 := by
      funext j
      change c j = 0
      by_cases hjz : j = z
      · simpa [hjz] using ez
      by_cases hjw : j = w
      · simpa [hjw] using ew
      by_cases hji : j = i
      · simpa [hji] using ei
      have all : ({j, i, z, w} : Finset (Fin 4)) = Finset.univ := by
        apply Finset.eq_univ_of_card
        simp [hji, hjz, hjw, hiz, hiw, hwz.symm]
      have hs := centred c hc
      rw [← all] at hs
      simpa [Finset.sum_insert, hji, hjz, hjw, hiz, hiw, hwz.symm, ez, ew, ei] using hs
    exact Subtype.ext (sub_eq_zero.mp hzero)
  simpa using LinearMap.finrank_le_finrank_of_injective injective

lemma excluded_second {L : Submodule ℂ (Mat 5)} (valid : OnLevel L)
    (large : 5 ≤ Module.finrank ℂ L)
    (U : Submodule ℂ (Col 5)) (hd : Module.finrank ℂ U = 2)
    (hi : ∀ u ∈ U, (∑ j, u j) = 0 ∧ RankOne.pw 2 u = 0)
    (hrows : ∀ X ∈ L, ∀ i, X i ∈ U) : False := by
  obtain ⟨u,hu,cub,quart⟩ := some_direction U hd hi
  have hnu : u ≠ 0 := by
    intro e
    apply cub
    simp [e, RankOne.pw]
  obtain ⟨j,hj⟩ := coord_nonzero hnu
  let W := L.comap (outer u)
  have dim : Module.finrank ℂ L ≤ Module.finrank ℂ W + 3 :=
    fibre_dimension valid U hd hrows u hu hnu
  have ac (a : Row) (ha : a ∈ W) : ∑ i, a i = 0 := by
    have h := (valid (outer u a) ha).2.1 j
    change (∑ i, a i * u j) = 0 at h
    rw [← Finset.sum_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hj
  have coeff (a : Row) (ha : a ∈ W) : RankOne.E3 a = 0 ∧ RankOne.E4 a = 0 := by
    have h (t : ℂ) : (∑ j, (t • u) j) = 0 ∧
        (∑ f : Fin 4 ↪ Fin 5, ∏ i, (1 + a i * (t • u) (f i))) =
        (∑ _f : Fin 4 ↪ Fin 5, (1 : ℂ)) := by
      have hz : outer (t • u) a = t • (outer u a) := by
        ext i j
        change a i * (t * u j) = t * (a i * u j)
        ring
      have hh := (valid _ (L.smul_mem t (show outer u a ∈ L from ha))).2.2
      rw [← hz] at hh
      refine ⟨?_, hh⟩
      simp [Pi.smul_apply, ← Finset.mul_sum, (hi u hu).1]
    have key := RankOne.coeffs (n:=5) (by decide) a u h
    refine ⟨(mul_eq_zero.mp key.2.1).resolve_right cub, ?_⟩
    have hz : 3 * RankOne.pw 2 u ^ 2 - 6 * RankOne.pw 4 u ≠ 0 := by
      rw [(hi u hu).2]
      simpa using mul_ne_zero (show (6 : ℂ) ≠ 0 by norm_num) quart
    exact (mul_eq_zero.mp key.2.2).resolve_right hz
  have small := small_row_space W ac (fun a h => (coeff a h).1) (fun a h => (coeff a h).2)
  omega

lemma finish (L : Submodule ℂ (Mat 5)) (valid : OnLevel L)
    (large : 5 ≤ Module.finrank ℂ L) : ∃ X ∈ L, X.rank = 3 := by
  by_contra h
  push Not at h
  have cap (X : Mat 5) (hx : X ∈ L) : X.rank ≤ 2 := by
    have hi := rank_cap X (valid X hx).2.1
    have hn := h X hx
    omega
  have cases := RankTwo 5 (by decide) L large (fun X hx =>
    ⟨(valid X hx).1, (valid X hx).2.1, quadratic (by decide) valid hx, cap X hx⟩)
  rcases cases with first | ⟨U, hd, hi, hu⟩
  · exact excluded_first (by decide) valid large first
  · exact excluded_second valid large U hd hi hu

end PEqualNP.Outside.L_gct_310

theorem PEqualNP.Outside.L_gct_310 : ∀ L : Submodule ℂ (Matrix (Fin 4) (Fin 5) ℂ),
    (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) →
    5 ≤ Module.finrank ℂ L →
    ∃ X ∈ L, X.rank = 3 := by
  intro L h large
  apply PEqualNP.Outside.L_gct_310.finish L _ large
  intro X hX
  obtain ⟨row,col,level⟩ := h X hX
  have base : (∑ _ : Fin 4 ↪ Fin 5, (1 : ℂ)) = 120 := by
    rw [PEqualNP.Outside.L_gct_310.RankOne.N_closed]
    norm_num
  exact ⟨row,col,level.trans base.symm⟩
