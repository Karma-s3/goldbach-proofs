import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace GoldbachPartial
open Finset
noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def paleyWeight (x : F) : ℤ := (1:MulChar F ℤ) x + quadraticChar F x
def paleyCorrelation (f : F→ℤ) (t : F) : ℤ := ∑x : F,f x*f (t-x)

omit [DecidableEq F] in
private theorem paley_character_conv (χ ψ : MulChar F ℤ) {t : F} (ht : t≠0) :
    (∑x : F,χ x*ψ (t-x))=χ t*ψ t*jacobiSum χ ψ := by
  rw [←Equiv.sum_comp (Equiv.mulLeft₀ t ht) (fun x : F=>χ x*ψ (t-x))]
  rw [jacobiSum,mul_sum]
  apply sum_congr rfl
  intro x _
  change χ (t*x)*ψ (t-t*x)=_
  rw [show t-t*x=t*(1-x) by ring,map_mul,map_mul]
  ring

theorem paleyWeight_values (x : F) : paleyWeight x=0 ∨ paleyWeight x=2 := by
  by_cases hx : x=0
  · subst x;left;simp [paleyWeight,(1:MulChar F ℤ).map_zero]
  · rw [paleyWeight,MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    rcases quadraticChar_dichotomy hx with h|h <;> rw [h] <;> norm_num

theorem paleyCorrelation_zero (hminus : quadraticChar F (-1) = -1) :
    paleyCorrelation (paleyWeight (F:=F)) 0=0 := by
  apply sum_eq_zero
  intro x _
  by_cases hx : x=0
  · subst x;simp [paleyWeight,(1:MulChar F ℤ).map_zero]
  have hn : -x≠0 := neg_ne_zero.mpr hx
  have hmap : quadraticChar F (-x)= -quadraticChar F x := by
    rw [←neg_one_mul x,map_mul,hminus,neg_one_mul]
  simp only [zero_sub,paleyWeight,MulChar.one_apply (isUnit_iff_ne_zero.mpr hx),
    MulChar.one_apply (isUnit_iff_ne_zero.mpr hn),hmap]
  nlinarith only [quadraticChar_sq_one hx]

theorem paleyCorrelation_eq_of_ne_zero (hminus : quadraticChar F (-1) = -1) {t : F} (ht : t≠0) :
    paleyCorrelation (paleyWeight (F:=F)) t = (Fintype.card F:ℤ)-1-2*quadraticChar F t := by
  let χ := quadraticChar F
  let u := (1:MulChar F ℤ)
  have hu : u t=1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)
  have hχ : χ≠1 := by
    intro he
    have hv := congrArg (fun v : MulChar F ℤ => v (-1)) he
    change quadraticChar F (-1)=_ at hv
    rw [hminus,MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))] at hv
    norm_num at hv
  have hInv : χ⁻¹=χ := by
    apply inv_eq_of_mul_eq_one_right
    exact (pow_two χ) ▸ (quadraticChar_isQuadratic F).sq_eq_one
  have hJJ : jacobiSum χ χ=1 := by
    have h:=jacobiSum_nontrivial_inv hχ
    rw [hInv,show χ (-1) = -1 from hminus] at h
    simpa using h
  have hUJ : jacobiSum u χ= -1 := jacobiSum_one_nontrivial hχ
  have hJU : jacobiSum χ u= -1 := (jacobiSum_comm ..).trans hUJ
  have hUU : jacobiSum u u=(Fintype.card F:ℤ)-2 := jacobiSum_one_one
  change (∑x:F,(u x+χ x)*(u (t-x)+χ (t-x)))=_
  simp only [add_mul,mul_add,sum_add_distrib,paley_character_conv _ _ ht,hJJ,hUJ,hJU,hUU,hu]
  change _=(Fintype.card F:ℤ)-1-2*χ t
  nlinarith only [show χ t^2=1 from quadraticChar_sq_one ht]


omit [DecidableEq F] in
private theorem paley_translated (f : F→ℤ) (s t : F) :
    paleyCorrelation (fun x=>f (x-s)) t=paleyCorrelation f (t-2*s) := by
  unfold paleyCorrelation
  rw [←Equiv.sum_comp (Equiv.addRight s) (fun x : F=>f (x-s)*f (t-x-s))]
  apply sum_congr rfl
  intro x _
  change f (x+s-s)*f (t-(x+s)-s)=f x*f (t-2*s-x)
  rw [add_sub_cancel_right]
  congr 2
  ring

theorem paley_predetermined_hole (p : ℕ) [Fact p.Prime] (hp : p%4=3) (v : ZMod p) :
    ∃ f : ZMod p→ℤ, (∀x,f x=0 ∨ f x=2) ∧ paleyCorrelation f v=0 ∧
      (∀ t≠v,paleyCorrelation f t=(p:ℤ)-3 ∨ paleyCorrelation f t=(p:ℤ)+1) ∧
      (∑t : ZMod p,(paleyCorrelation f t-(p:ℤ))^2)≤(p:ℤ)^2+9*p := by
  classical
  have hm : quadraticChar (ZMod p) (-1) = -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    intro h
    have hh := FiniteField.isSquare_neg_one_iff.mp h
    exact hh (by simpa only [ZMod.card] using hp)
  have h2 : (2:ZMod p)≠0 := by
    have hz : ¬p∣2 := by
      intro h
      have hh := Nat.le_of_dvd (by decide : 0<2) h
      omega
    simpa only [Nat.cast_ofNat] using mt (ZMod.natCast_eq_zero_iff 2 p).mp hz
  let s := v/2
  have hs : 2*s=v := by dsimp [s];field_simp
  let f := fun x : ZMod p => paleyWeight (x-s)
  have h0 : paleyCorrelation f v=0 := by
    rw [show paleyCorrelation f v=paleyCorrelation (paleyWeight (F:=ZMod p)) (v-2*s) from paley_translated _ s v,hs,sub_self]
    exact paleyCorrelation_zero hm
  have hhigh (t : ZMod p) (ht : t≠v) : paleyCorrelation f t=(p:ℤ)-3 ∨ paleyCorrelation f t=(p:ℤ)+1 := by
    rw [show paleyCorrelation f t=paleyCorrelation (paleyWeight (F:=ZMod p)) (t-2*s) from paley_translated _ s t,hs,
      paleyCorrelation_eq_of_ne_zero hm (sub_ne_zero.mpr ht),ZMod.card]
    rcases quadraticChar_dichotomy (sub_ne_zero.mpr ht) with h|h <;> rw [h] <;> omega
  refine ⟨f,fun x=>paleyWeight_values _,h0,hhigh,?_⟩
  rw [←sum_erase_add _ _ (mem_univ v),h0,zero_sub,neg_sq]
  have hsum : (∑ t ∈ univ.erase v, (paleyCorrelation f t-(p:ℤ))^2)≤∑_t : ZMod p,(9:ℤ) := by
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (erase_subset v univ) (fun _ _ _ => by decide : ∀a∈(univ:Finset (ZMod p)), a∉univ.erase v → (0:ℤ)≤9))
    apply sum_le_sum
    intro t ht
    rcases hhigh t (mem_erase.mp ht).1 with h|h <;> rw [h] <;> ring_nf <;> norm_num
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul] at hsum
  linarith only [hsum]


private theorem paley_prime_divisor (m : ℕ) (hm : m%4=3) :
    ∃p:ℕ,p.Prime ∧ p%4=3 ∧ p∣m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : m≠1)
    by_cases h3 : p%4=3
    · exact ⟨p,hp,h3,hd⟩
    let k := m/p
    have hpk : p*k=m := Nat.mul_div_cancel' hd
    have hk : k<m := Nat.div_lt_self (by omega) hp.one_lt
    have hmod : (p%4*(k%4))%4=3 := by rw [←Nat.mul_mod,hpk,hm]
    have hpL:=Nat.mod_lt p (by decide : 0<4)
    have hkL:=Nat.mod_lt k (by decide : 0<4)
    have hK3 : k%4=3 := by
      have hcase : p%4=0 ∨ p%4=1 ∨ p%4=2 := by omega
      rcases hcase with h|h|h <;> rw [h] at hmod <;> omega
    obtain ⟨q,hq,hq3,hqd⟩:=ih k hk hK3
    exact ⟨q,hq,hq3,hpk ▸ dvd_mul_of_dvd_right hqd p⟩

theorem paley_exists_large_prime (N : ℕ) : ∃p>N,p.Prime ∧ p%4=3 := by
  let A := (N+1).factorial
  have hA : 0<A := Nat.factorial_pos _
  let m := 4*A-1
  have hm : m%4=3 := by dsimp only [m];omega
  obtain ⟨p,hp,h3,hd⟩ := paley_prime_divisor m hm
  refine ⟨p,?_,hp,h3⟩
  by_contra! hsmall
  have hpa : p∣A := Nat.dvd_factorial hp.pos (by omega)
  have hv := Nat.dvd_sub (dvd_mul_of_dvd_right hpa 4) hd
  have h1 : 4*A-m=1 := by dsimp only [m];omega
  rw [h1] at hv
  exact hp.not_dvd_one hv


def paleyNaturalConvolution {p : ℕ} (f : ZMod p→ℤ) (m : ℕ) : ℤ :=
  ∑k∈range (m+1),f (k:ZMod p)*f ((m-k:ℕ):ZMod p)

private theorem paley_complete_block {p : ℕ} [NeZero p] (g : ZMod p→ℤ) (J : ℕ) :
    (∑k∈range (J*p),g (k:ZMod p))=(J:ℤ)*∑x:ZMod p,g x := by
  have hsum : (∑k∈range p,g (k:ZMod p))=∑x:ZMod p,g x := by
    apply sum_bij' (s:=range p) (t:=univ) (fun (k:ℕ) _=>(k:ZMod p)) (fun (x:ZMod p) _=>x.val)
    · simp
    · exact fun x _=>mem_range.mpr x.val_lt
    · exact fun k hk=>ZMod.val_natCast_of_lt (mem_range.mp hk)
    · exact fun x _=>ZMod.natCast_zmod_val x
    · exact fun _ _=>rfl
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Nat.succ_mul,sum_range_add,ih,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    congr 1
    simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add] using hsum

theorem paley_natural_predetermined_holes (p : ℕ) [Fact p.Prime] (hp : p%4=3) (v : ZMod p) :
    ∃f : ZMod p→ℤ, (∀x,f x=0 ∨ f x=2) ∧
      (∀m:ℕ,(m:ZMod p)=v → paleyNaturalConvolution f m=0) ∧
      (∀m:ℕ,(m:ZMod p)≠v → (((m+1)/p:ℕ):ℤ)*((p:ℤ)-3)≤paleyNaturalConvolution f m) := by
  obtain ⟨f,hf,hzero,hhigh,_⟩ := paley_predetermined_hole p hp v
  have hnon (x : ZMod p) : 0≤f x := by rcases hf x with h|h <;> simp [h]
  have hnat (m : ℕ) : paleyNaturalConvolution f m=∑k∈range (m+1),f (k:ZMod p)*f ((m:ZMod p)-k) := by
    apply sum_congr rfl
    intro k hk
    rw [Nat.cast_sub (mem_range_succ_iff.mp hk)]
  refine ⟨f,hf,?_,?_⟩
  · intro m hm
    rw [hnat,hm]
    apply sum_eq_zero
    intro k _
    have hh : f (k:ZMod p)*f (v-(k:ZMod p)) ≤ paleyCorrelation f v :=
      single_le_sum (fun x _=>mul_nonneg (hnon x) (hnon (v-x))) (mem_univ _)
    exact le_antisymm (hh.trans_eq hzero) (mul_nonneg (hnon _) (hnon _))
  · intro m hm
    let b := (m+1)/p
    have hh : (p:ℤ)-3≤paleyCorrelation f (m:ZMod p) := by
      rcases hhigh (m:ZMod p) hm with h|h <;> omega
    rw [hnat]
    calc
      _ ≤ (b:ℤ)*paleyCorrelation f (m:ZMod p) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = ∑k∈range (b*p),f (k:ZMod p)*f ((m:ZMod p)-k) :=
        (paley_complete_block (fun x=>f x*f ((m:ZMod p)-x)) b).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (Nat.div_mul_le_self (m+1) p))
        (fun k _ _=>mul_nonneg (hnon _) (hnon _))

end
end GoldbachPartial