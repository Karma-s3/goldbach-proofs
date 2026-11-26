import FixedTargetRoughPrimeMass
import Batteries.Tactic.OpenPrivate
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

theorem genuinePairBlock_sum_lower (X:ℕ)(P:Finset ℕ)(hp:∀p∈P,p.Prime)
    (hodd:∀p∈P,Odd p)(hpair:∀p∈P,∀q∈P,p+q∈Ico X (2*X)) :
    (∑p∈P,Real.log p)^2≤∑n∈(Ico X (2*X)).filter Even,corr n := by
  let S:=(Ico X (2*X)).filter Even
  let T (n:ℕ):=range (n+1)
  let e (v:ℕ×ℕ):Σ _:ℕ,ℕ:=⟨v.1+v.2,v.1⟩
  let f (v:ℕ×ℕ):ℝ:=Real.log v.1*Real.log v.2
  let g (v:Σ _:ℕ,ℕ):ℝ:=weight v.2*weight (v.1-v.2)
  have inj: (↑(P×ˢP):Set (ℕ×ℕ)).InjOn e := by
    rintro ⟨p,q⟩ _ ⟨p',q'⟩ _ h
    have hh:=congrArg Sigma.fst h
    have h₂:=congrArg (fun a:Σ _:ℕ,ℕ=>a.2) h
    change p+q=p'+q' at hh
    change p=p' at h₂
    obtain rfl:=h₂
    congr 1; omega
  have hg (n:ℕ):0≤weight n:=by unfold weight;split_ifs <;> positivity
  have hh:(∑v∈P×ˢP,f v)≤∑v∈S.sigma T,g v:=by
    apply sum_le_sum_of_injOn e inj
    · intro v hv;obtain ⟨⟨p,q⟩,h,rfl⟩:=mem_image.mp hv
      obtain ⟨hr,ht⟩:=mem_product.mp h
      exact mem_sigma.mpr ⟨mem_filter.mpr ⟨hpair p hr q ht,(hodd p hr).add_odd (hodd q ht)⟩,mem_range.mpr (by change p<p+q+1;omega)⟩
    · rintro ⟨p,q⟩ hv
      obtain ⟨hr,ht⟩:=mem_product.mp hv
      simp only [e,f,g,Nat.add_sub_cancel_left,weight,ite_eq_left (hp p hr),ite_eq_left (hp q ht),le_refl]
    · intro v _ _
      exact mul_nonneg (hg _) (hg _)
  rw [sum_product,sum_sigma] at hh
  simpa only [sq,sum_mul,mul_sum,f,g,S,T,corr] using (by simpa only [f,mul_comm] using hh : (∑x∈P,∑u∈P,Real.log u*Real.log x)≤∑a∈S,∑p∈T a,g ⟨a,p⟩)

open private fixedTarget_dyadic_mass from FixedTargetRoughPrimeMass

theorem genuine_dyadic_correlation_first_moment :
    ∀ᶠ X:ℕ in atTop,(X:ℝ)^2/9 ≤ ∑n∈(Ico X (2*X)).filter Even,corr n := by
  let y (X:ℕ):=(X-1)/2
  have ht:Tendsto y atTop atTop := by
    apply tendsto_atTop.mpr; intro b
    filter_upwards [eventually_ge_atTop (2*b+1)] with X hX
    dsimp [y];omega
  have hl:=Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually (fixedTarget_dyadic_mass 1 (by decide)),ht.eventually (hl.eventually_ge_atTop 1),
    eventually_ge_atTop (40:ℕ)] with X hm hL hX
  let Y:=y X
  let P:=(Ioc Y (2*Y)).filter Nat.Prime
  have hp (p:ℕ)(h:p∈P):p.Prime:=(mem_filter.mp h).2
  have hI {p:ℕ}(h:p∈P):Y<p ∧ p≤2*Y:=mem_Ioc.mp (mem_filter.mp h).1
  have hY:2≤Y:=by dsimp [Y,y];omega
  have ho (p:ℕ)(h:p∈P):Odd p := (hp p h).odd_of_ne_two (by have := (hI h).1;omega)
  have hpair (p:ℕ)(h:p∈P)(q:ℕ)(hq:q∈P):p+q∈Ico X (2*X) := by
    have hf:=hI h;have hs:=hI hq
    dsimp [Y,y] at hf hs;apply mem_Ico.mpr;omega
  change 1≤Real.log (y X:ℝ) at hL
  have hmass:=hm 1 0 (by decide) (by simpa only [pow_one,Nat.cast_one] using hL) (by decide) (by decide)
  have hmass':(3/4:ℝ)*Y≤∑p∈P,Real.log p := by
    dsimp only [P];rw [sum_filter]
    simpa only [Nat.mod_one,ite_true,Nat.totient_one,Nat.cast_one,div_one,weight] using hmass
  have h9:(4:ℝ)*X≤9*(Y:ℝ):=by exact_mod_cast (show 4*X≤9*Y by dsimp [Y,y];omega)
  have h3:(X:ℝ)/3 ≤∑p∈P,Real.log p:=by linarith only [h9,hmass']
  have hh:=pow_le_pow_left₀ (show 0≤(X:ℝ)/3 by positivity) h3 2
  exact (by convert hh using 1;ring : (X:ℝ)^2/9≤(∑p∈P,Real.log p)^2).trans (genuinePairBlock_sum_lower X P hp ho hpair)

end GoldbachPartial
