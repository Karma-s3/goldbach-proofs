import VerifiedThinSemiprimeRows

namespace GoldbachPartial
open Finset
open scoped Classical
noncomputable section

def thinBad (n L b p : ℕ) : Prop := b*(L*b) ≡ b*n [MOD p]

private theorem thinBad_prod_iff (n L b : ℕ) (T : Finset ℕ) (hT : ∀p∈T,p.Prime) :
    thinBad n L b (∏p∈T,p) ↔ ∀p∈T,thinBad n L b p := by
  induction T using Finset.induction_on with
  | empty => simp [thinBad,Nat.ModEq,Nat.mod_one]
  | @insert p T hp ih =>
    have hpr := hT p (mem_insert_self p T)
    have hq (q : ℕ) (hq : q∈T) := hT q (mem_insert_of_mem hq)
    have hc : p.Coprime (∏q∈T,q) := Nat.coprime_prod_right_iff.mpr (fun q h =>
      (Nat.coprime_primes hpr (hq q h)).mpr (by rintro rfl; exact hp h))
    rw [prod_insert hp,Finset.forall_mem_insert]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hc).symm.trans (and_congr_right fun _ => ih hq)

theorem thinPolyRow_eq_bad_intersection (n L X : ℕ) (T : Finset ℕ) (hT : ∀p∈T,p.Prime) :
    thinPolyRow n L (∏p∈T,p) X=((Ioc 0 X).filter (fun b => ∀p∈T,thinBad n L b p)).card := by
  unfold thinPolyRow
  congr 1
  ext b
  simp only [mem_filter,and_congr_right_iff]
  intro _
  rw [←thinBad_prod_iff n L b T hT,thinBad,←ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [mul_sub,sub_eq_zero]

def thinSurvivors (n L X : ℕ) (B : Finset ℕ) : ℕ :=
  ((Ioc 0 X).filter (fun b => ∀p∈B,¬thinBad n L b p)).card

theorem thinSurvivors_signed_upper (n L X z K : ℕ) (B : Finset ℕ)
    (hz : 1≤z) (hK : Even K) (hB : ∀p∈B,p.Prime ∧ ¬p∣n ∧ ¬p∣L) (hBz : ∀p∈B,p≤z) :
    (thinSurvivors n L X B:ℝ) ≤
      (X:ℝ)*(∑t∈B.powerset.filter (fun t=>t.card≤K), (-1:ℝ)^t.card*∏p∈t,((2:ℝ)/p)) +
        (z:ℝ)^K*(2:ℝ)^K := by
  let I := Ioc 0 X
  let A := B.powerset.filter (fun t => t.card≤K)
  let d (t : Finset ℕ) := ∏p∈t,p
  let M (t : Finset ℕ) := (X:ℝ)*(∏p∈t,((2:ℝ)/p))
  have H : (thinSurvivors n L X B:ℝ) ≤ ∑t∈A,(-1:ℝ)^t.card*thinPolyRow n L (d t) X := by
    calc
      _ = ∑b∈I,if ∀p∈B,¬thinBad n L b p then (1:ℝ) else 0 := by
        rw [←sum_filter]; simp [I,thinSurvivors]
      _ ≤ ∑b∈I,brunBlockUpper (B.filter (thinBad n L b)) K := by
        apply sum_le_sum
        intro b _
        have he : B.filter (thinBad n L b)=∅ ↔ ∀p∈B,¬thinBad n L b p := filter_eq_empty_iff
        simpa only [he] using (brunBlock_interval (B.filter (thinBad n L b)) hK).2
      _ = _ := by
        simp_rw [brunBlockUpper_at]
        rw [sum_comm]
        apply sum_congr rfl
        intro t ht
        have hs := mem_powerset.mp (mem_filter.mp ht).1
        rw [thinPolyRow_eq_bad_intersection n L X t (fun p hp => (hB p (hs hp)).1)]
        rw [←sum_filter,sum_const,nsmul_eq_mul,mul_comm]
  have hE (t : Finset ℕ) (ht : t∈A) :
      |(thinPolyRow n L (d t) X:ℝ)-M t|≤2^K := by
    have hs := mem_powerset.mp (mem_filter.mp ht).1
    have h := thinPolyRow_prime_product n L X t (fun p hp => hB p (hs hp))
    have he : M t=(2:ℝ)^t.card*((X:ℝ)/(∏p∈t,p:ℕ)) := by
      dsimp only [M]
      rw [prod_div_distrib,prod_const,Nat.cast_prod];ring
    rw [he]
    exact h.trans (pow_le_pow_right₀ (by norm_num) (mem_filter.mp ht).2)
  have hcard : (A.card:ℝ)≤(z:ℝ)^K := by
    exact_mod_cast truncatedPrimeSubsets_card B hz (fun p hp => (hB p hp).1) hBz
  calc
    _ ≤ _ := H
    _ ≤ ∑t∈A,((-1:ℝ)^t.card*M t+(2:ℝ)^K) := by
      apply sum_le_sum
      intro t ht
      have hh := hE t ht
      have hs : |(-1:ℝ)^t.card*((thinPolyRow n L (d t) X:ℝ)-M t)|≤2^K := by
        simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hh
      linarith only [le_abs_self (((-1:ℝ)^t.card)*((thinPolyRow n L (d t) X:ℝ)-M t)),hs]
    _ = (X:ℝ)*(∑t∈A,(-1:ℝ)^t.card*∏p∈t,((2:ℝ)/p))+(A.card:ℝ)*2^K := by
      rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_sum]
      congr 1
      exact sum_congr rfl fun t _ => by dsimp [M];ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right hcard (show (0:ℝ)≤2^K by positivity)) _

private theorem thinEulerTruncation (B : Finset ℕ) (K : ℕ) :
    (∑t∈B.powerset.filter (fun t=>t.card≤K),(-1:ℝ)^t.card*∏p∈t,((2:ℝ)/p)) ≤
      (∏p∈B,(1-(2:ℝ)/p)) + (∏p∈B,(1+(4:ℝ)/p))/(2:ℝ)^(K+1) := by
  let w (t : Finset ℕ) := ∏p∈t,((2:ℝ)/p)
  let f (t : Finset ℕ) := (-1:ℝ)^t.card*w t
  let T := B.powerset.filter (fun t=>K<t.card)
  have hw (t : Finset ℕ) : 0≤w t := prod_nonneg (fun _ _=>by positivity)
  have hsum : (∏p∈B,(1-(2:ℝ)/p))=∑t∈B.powerset,f t := by
    simp only [sub_eq_add_neg,prod_one_add,prod_neg,f,w]
  have hsplit := sum_filter_add_sum_filter_not B.powerset (fun t=>t.card≤K) f
  simp only [not_le] at hsplit
  have htail : (∑t∈T,w t)≤(∏p∈B,(1+(4:ℝ)/p))/(2:ℝ)^(K+1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [sum_mul]
    calc
      _ ≤ ∑t∈T,w t*(2:ℝ)^t.card := sum_le_sum (fun t ht =>
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (mem_filter.mp ht).2) (hw t))
      _ ≤ ∑t∈B.powerset,w t*(2:ℝ)^t.card := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun t _ _ => mul_nonneg (hw t) (by positivity))
      _ = _ := by
        rw [prod_one_add]
        apply sum_congr rfl
        intro t _
        change (∏p∈t,((2:ℝ)/p))*2^t.card=_
        rw [←prod_const (s:=t) (b:=(2:ℝ)),←prod_mul_distrib]
        exact prod_congr rfl (fun p _ => by ring)
  have hf : -(∑t∈T,f t)≤∑t∈T,w t := by
    rw [←sum_neg_distrib]
    apply sum_le_sum
    intro t _
    have he : |f t|=w t := by simp [f,abs_mul,abs_of_nonneg (hw t)]
    exact (neg_le_abs (f t)).trans_eq he
  change (∑t∈B.powerset.filter (fun t=>t.card≤K),f t)≤_
  rw [hsum,←hsplit]
  change _ ≤ (_+∑t∈T,f t)+_
  linarith only [hf,htail]

theorem thinSurvivors_euler_upper (n L X z K : ℕ) (B : Finset ℕ)
    (hz : 1≤z) (hK : Even K) (hB : ∀p∈B,p.Prime ∧ ¬p∣n ∧ ¬p∣L) (hBz : ∀p∈B,p≤z) :
    (thinSurvivors n L X B:ℝ) ≤
      (X:ℝ)*((∏p∈B,(1-(2:ℝ)/p)) + (∏p∈B,(1+(4:ℝ)/p))/(2:ℝ)^(K+1)) +
        (z:ℝ)^K*(2:ℝ)^K := by
  apply (thinSurvivors_signed_upper n L X z K B hz hK hB hBz).trans
  exact add_le_add_left (mul_le_mul_of_nonneg_left (thinEulerTruncation B K) (Nat.cast_nonneg _)) _

def thinPrimePairSet (n L X : ℕ) : Finset ℕ :=
  (Ioc 0 X).filter fun b => b.Prime ∧ (n-L*b).Prime

theorem thinPrimePairSet_upper (n L X z K : ℕ) (B : Finset ℕ) (hL : 0<L)
    (hz : 1≤z) (hK : Even K) (hB : ∀p∈B,p.Prime ∧ ¬p∣n ∧ ¬p∣L) (hBz : ∀p∈B,p≤z) :
    ((thinPrimePairSet n L X).card:ℝ)≤2*(z:ℝ) +
      (X:ℝ)*((∏p∈B,(1-(2:ℝ)/p)) + (∏p∈B,(1+(4:ℝ)/p))/(2:ℝ)^(K+1)) +
        (z:ℝ)^K*(2:ℝ)^K := by
  let A := thinPrimePairSet n L X
  let C := A.filter (fun b=>n-L*b≤z)
  let U := (Ioc 0 X).filter (fun b => ∀p∈B,¬thinBad n L b p)
  have hsmall : C.card≤z := by
    have hm : C.card≤(Ioc 0 z).card := by
      apply card_le_card_of_injOn (fun b=>n-L*b)
      · intro b hb
        obtain ⟨hbA,hbz⟩ := mem_filter.mp hb
        exact mem_Ioc.mpr ⟨(mem_filter.mp hbA).2.2.pos,hbz⟩
      · intro b hb c hc he
        have h1 := (mem_filter.mp (mem_filter.mp hb).1).2.2.pos
        have h2 := (mem_filter.mp (mem_filter.mp hc).1).2.2.pos
        change n-L*b=n-L*c at he
        exact Nat.eq_of_mul_eq_mul_left hL (by omega : L*b=L*c)
    simpa using hm
  have hsub : A⊆(Ioc 0 z)∪C∪U := by
    intro b hb
    obtain ⟨hbI,hbp,hpp⟩ := mem_filter.mp hb
    by_cases hbz : b≤z
    · exact mem_union_left _ (mem_union_left _ (mem_Ioc.mpr ⟨(mem_Ioc.mp hbI).1,hbz⟩))
    by_cases hpz : n-L*b≤z
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hb,hpz⟩))
    apply mem_union_right _ (mem_filter.mpr ⟨hbI,?_⟩)
    intro p hp hbad
    have hln : L*b≤n := by have hpos:=hpp.pos; omega
    have hv := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left b hln)).mp hbad
    rw [←Nat.mul_sub] at hv
    rcases (hB p hp).1.dvd_mul.mp hv with h|h
    · exact hbz ((Nat.prime_dvd_prime_iff_eq (hB p hp).1 hbp).mp h ▸ hBz p hp)
    · exact hpz ((Nat.prime_dvd_prime_iff_eq (hB p hp).1 hpp).mp h ▸ hBz p hp)
  have hcard := (card_le_card hsub).trans (card_union_le ..)
  have hcard' := card_union_le (Ioc 0 z) C
  have hc : A.card≤2*z+U.card := by simp only [Nat.card_Ioc,Nat.sub_zero] at hcard'; omega
  have hr : ((thinPrimePairSet n L X).card:ℝ)≤2*(z:ℝ)+thinSurvivors n L X B := by exact_mod_cast hc
  linarith only [hr,thinSurvivors_euler_upper n L X z K B hz hK hB hBz]

end
end GoldbachPartial