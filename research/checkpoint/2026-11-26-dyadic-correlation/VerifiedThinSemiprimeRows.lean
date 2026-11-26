import Mathlib.Data.Int.CardIntervalMod
import VerifiedBlockBonferroni
import Mathlib.Algebra.Field.ZMod

namespace GoldbachPartial
open Finset
noncomputable section

def thinPolyRoots (n L d : ℕ) : ℕ := Nat.card {x : ZMod d // x*((L:ZMod d)*x-(n:ZMod d))=0}

theorem thinPolyRoots_mul (n L a b : ℕ) (hc : a.Coprime b) :
    thinPolyRoots n L (a*b)=thinPolyRoots n L a * thinPolyRoots n L b := by
  let e := ZMod.chineseRemainder hc
  let P (d : ℕ) (x : ZMod d) := x*((L:ZMod d)*x-(n:ZMod d))=0
  have hmap (x : ZMod (a*b)) : P (a*b) x ↔ P a (e x).1 ∧ P b (e x).2 := by
    dsimp only [P]
    rw [← e.injective.eq_iff (a:=x*(_*x-_)) (b:=0)]
    simp only [map_mul,map_sub,map_natCast,map_zero,Prod.ext_iff]
    rfl
  let g := e.toEquiv.subtypeEquiv (p:=P (a*b)) (q:=fun z => P a z.1 ∧ P b z.2) hmap
  exact (Nat.card_congr (g.trans Equiv.subtypeProdEquivProd)).trans (Nat.card_prod ..)

theorem thinPolyRoots_prime (n L p : ℕ) (hp : p.Prime) (hn : ¬ p∣n) (hL : ¬p∣L) :
    thinPolyRoots n L p = 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hn' : (n:ZMod p)≠0 := mt (ZMod.natCast_eq_zero_iff ..).mp hn
  have hL' : (L:ZMod p)≠0 := mt (ZMod.natCast_eq_zero_iff ..).mp hL
  let s := (n:ZMod p)/(L:ZMod p)
  have hs : s≠0 := div_ne_zero hn' hL'
  have he : (univ.filter (fun x : ZMod p => x*((L:ZMod p)*x-(n:ZMod p))=0))={0,s} := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mul_eq_zero,sub_eq_zero,mem_insert,mem_singleton]
    dsimp [s]
    rw [eq_div_iff hL',mul_comm]
  rw [thinPolyRoots,Nat.card_eq_fintype_card,Fintype.card_subtype,he]
  simp [hs.symm]

theorem thinPolyRoots_prime_product (n L : ℕ) (T : Finset ℕ)
    (hT : ∀p∈T,p.Prime ∧ ¬p∣n ∧ ¬p∣L) :
    thinPolyRoots n L (∏p∈T,p) = 2^T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [prod_empty,card_empty,pow_zero]
    unfold thinPolyRoots
    exact @Nat.card_unique _ ⟨⟨0,by simp⟩⟩ inferInstance
  | @insert q T hq ih =>
    have hq' := hT q (mem_insert_self q T)
    have ht (p : ℕ) (hp : p∈T) := hT p (mem_insert_of_mem hp)
    have hc : q.Coprime (∏p∈T,p) := Nat.coprime_prod_right_iff.mpr (fun p hp =>
      (Nat.coprime_primes hq'.1 (ht p hp).1).mpr (by rintro rfl;exact hq hp))
    rw [prod_insert hq,card_insert_of_notMem hq,thinPolyRoots_mul _ _ _ _ hc,
      thinPolyRoots_prime _ _ _ hq'.1 hq'.2.1 hq'.2.2,ih ht,pow_succ,mul_comm]

private theorem thin_class_discrepancy (N r z:ℕ) (hr:0<r) :
    |(((Ioc 0 N).filter (fun x=>x ≡ z [MOD r])).card:ℝ)-(N:ℝ)/r|≤1 := by
  let b := ((N:ℚ)-z)/r
  let a := (-(z:ℚ))/r
  have hr' : (0:ℚ)<r := by exact_mod_cast hr
  have hab : a≤b := by dsimp [a,b];gcongr;linarith
  have hcard := Nat.Ioc_filter_modEq_card 0 N hr z
  change (((Ioc 0 N).filter (fun x=>x ≡ z [MOD r])).card:ℤ) = max (⌊b⌋-⌊((0:ℚ)-z)/r⌋) 0 at hcard
  rw [zero_sub,max_eq_left (sub_nonneg.mpr (Int.floor_mono hab))] at hcard
  have hcardQ := congrArg ((↑):ℤ→ℚ) hcard
  push_cast at hcardQ
  have hd : b-a=(N:ℚ)/r := by dsimp [a,b];ring
  have hrat : |(((Ioc 0 N).filter (fun x=>x ≡ z [MOD r])).card:ℚ)-(N:ℚ)/r|≤1 := by
    rw [←hd]
    apply abs_le.mpr
    constructor <;> linarith [Int.floor_le a,Int.lt_floor_add_one a,Int.floor_le b,Int.lt_floor_add_one b]
  have hc := (Rat.cast_le (K:=ℝ)).mpr hrat
  push_cast at hc
  exact hc



def thinPolyRow (n L d X : ℕ) : ℕ :=
  ((Ioc 0 X).filter fun b : ℕ => (b:ZMod d)*((L:ZMod d)*b-(n:ZMod d))=0).card

theorem thinPolyRow_abs (n L d X : ℕ) (hd : 0<d) :
    |(thinPolyRow n L d X:ℝ) - (thinPolyRoots n L d:ℝ) * ((X:ℝ)/d)| ≤ thinPolyRoots n L d := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  let B := Finset.univ.filter (fun x : ZMod d => x*((L:ZMod d)*x-(n:ZMod d))=0)
  have hB : thinPolyRoots n L d=B.card := by
    rw [thinPolyRoots,Nat.card_eq_fintype_card,Fintype.card_subtype]
  let C := fun a : ZMod d => ((Ioc 0 X).filter (fun b : ℕ => (b:ZMod d)=a)).card
  have he : (∑a∈B,C a)=thinPolyRow n L d X := by
    change (∑a∈B,((Ioc 0 X).filter (fun b : ℕ => (b:ZMod d)=a)).card)=_
    rw [sum_card_fiberwise_eq_card_filter]
    simp only [B,mem_filter,mem_univ,true_and,thinPolyRow]
  have hr (a : ZMod d) : |(C a:ℝ)-(X:ℝ)/d|≤1 := by
    have h (b : ℕ) : ((b:ZMod d)=a) ↔ b ≡ a.val [MOD d] := by
      rw [←ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    simpa only [C,h] using thin_class_discrepancy X d a.val hd
  rw [hB,←he,Nat.cast_sum,←nsmul_eq_mul,←sum_const,←sum_sub_distrib]
  exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun a _ => hr a)).trans_eq (by simp))

theorem thinPolyRow_prime_product (n L X : ℕ) (T : Finset ℕ)
    (hT : ∀p∈T,p.Prime ∧ ¬p∣n ∧ ¬p∣L) :
    |(thinPolyRow n L (∏p∈T,p) X:ℝ)-
      (2:ℝ)^T.card*((X:ℝ)/(∏p∈T,p:ℕ))|≤2^T.card := by
  have hd : 0<∏p∈T,p := prod_pos (fun p hp => (hT p hp).1.pos)
  simpa only [thinPolyRoots_prime_product n L T hT,Nat.cast_pow,Nat.cast_ofNat] using
    thinPolyRow_abs n L (∏p∈T,p) X hd

end
end GoldbachPartial