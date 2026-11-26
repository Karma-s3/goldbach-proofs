import TruncatedRamanujanSquare
import NaturalTubeSingleFrequency
namespace GoldbachPartial
open Finset
private abbrev mobR (k:ℕ) : ℝ := ArithmeticFunction.moebius k

private theorem sum_positive_multiples {A:Type*} [AddCommMonoid A] (f:ℕ→A) (X d:ℕ) (hd:0<d) :
    (∑j∈range X,if d∣j+1 then f ((j+1)/d) else 0)=∑k∈range (X/d),f (k+1) := by
  rw [←sum_filter]
  symm
  apply sum_bij (fun k _=>d*(k+1)-1)
  · intro k hk
    have h1 : k+1≤X/d := mem_range.mp hk
    have hx := (Nat.le_div_iff_mul_le hd).mp h1
    have ht : 0<d*(k+1) := Nat.mul_pos hd (Nat.succ_pos _)
    rw [Nat.mul_comm] at hx
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by rw [Nat.sub_add_cancel (by omega)];exact dvd_mul_right ..⟩
  · intro a _ b _ he
    have ha : 1≤d*(a+1) := Nat.mul_pos hd (Nat.succ_pos a)
    have hb : 1≤d*(b+1) := Nat.mul_pos hd (Nat.succ_pos b)
    change d*(a+1)-1=d*(b+1)-1 at he
    have heq := congrArg (fun z:ℕ=>z+1) he
    simp only [Nat.sub_add_cancel ha,Nat.sub_add_cancel hb] at heq
    exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left hd heq)
  · intro j hj
    obtain ⟨hj,hv⟩ := mem_filter.mp hj
    have hu : 0<(j+1)/d := Nat.div_pos (Nat.le_of_dvd (by omega) hv) hd
    have hx := Nat.mul_div_cancel' hv
    refine ⟨(j+1)/d-1,mem_range.mpr ?_,?_⟩
    · have hh := Nat.div_le_div_right (show j+1≤X from mem_range.mp hj) (c:=d)
      omega
    · rw [Nat.sub_add_cancel (by omega),hx];omega
  · intro k _
    have ht := Nat.mul_pos hd (Nat.succ_pos k)
    change f (k+1)=f (((d*(k+1)-1)+1)/d)
    rw [Nat.sub_add_cancel ht,Nat.mul_div_cancel_left _ hd]

private theorem moebius_floor_mass (N:ℕ) (hN:0<N) :
    (∑j∈range N,mobR (j+1)*((N/(j+1):ℕ):ℝ))=1 := by
  have hrow (j:ℕ) : mobR (j+1)*((N/(j+1):ℕ):ℝ) =
      ∑k∈range N,if j+1∣k+1 then mobR (j+1) else 0 := by
    rw [←sum_filter,sum_const,Nat.card_multiples,nsmul_eq_mul,mul_comm]
  have hcol (k:ℕ) (hk:k∈range N) :
      (∑j∈range N,if j+1∣k+1 then mobR (j+1) else 0)=if k=0 then 1 else 0 := by
    rw [←sum_filter]
    have he : (∑j∈(range N).filter (fun j=>j+1∣k+1),mobR (j+1))=∑d∈(k+1).divisors,mobR d := by
      apply sum_bij (fun j _=>j+1)
      · intro j hj;exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hj).2,by omega⟩
      · intro i _ j _ h;change i+1=j+1 at h;omega
      · intro d hd
        have hpos := Nat.pos_of_mem_divisors hd
        have hv := Nat.dvd_of_mem_divisors hd
        have hl := Nat.le_of_dvd (Nat.succ_pos k) hv
        have hkn := mem_range.mp hk
        exact ⟨d-1,mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa only [Nat.sub_add_cancel hpos] using hv⟩,
          Nat.sub_add_cancel hpos⟩
      · intro _ _;rfl
    rw [he]
    change ∑d∈(k+1).divisors,(ArithmeticFunction.moebius d:ℝ)=_
    have hf := sum_dyadicRamanujanDivisor_divisors 1 (Nat.succ_pos k)
    have heq (d:ℕ) : dyadicRamanujanDivisor 1 d=ArithmeticFunction.moebius d := by simp [dyadicRamanujanDivisor]
    simp_rw [heq] at hf
    by_cases hz : k=0
    · subst k;simp
    · have hh : ¬k+1∣1 := fun hh=>hz (by have := Nat.dvd_one.mp hh;omega)
      simp only [hh,ite_false] at hf
      rw [ite_eq_right hz];exact_mod_cast hf
  simp_rw [hrow]
  rw [sum_comm,sum_congr rfl hcol]
  simp [hN]

theorem moebius_reciprocal_prefix_bound (N:ℕ) :
    |∑j∈range N,mobR (j+1)/((j+1:ℕ):ℝ)|≤2 := by
  rcases Nat.eq_zero_or_pos N with rfl|hN
  · simp
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  let S := ∑j∈range N,mobR (j+1)/((j+1:ℕ):ℝ)
  have herr : |(N:ℝ)*S-1|≤N := by
    change |(N:ℝ)*(∑j∈range N,mobR (j+1)/((j+1:ℕ):ℝ))-1|≤_
    rw [←moebius_floor_mass N hN,mul_sum,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑_j∈range N,(1:ℝ) := by
           apply sum_le_sum
           intro j _
           let d := j+1
           have hd : 0<d := Nat.succ_pos j
           have hdr : (0:ℝ)<d := by exact_mod_cast hd
           have hmu : |mobR d|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
           have hhi : (N:ℝ)/(d:ℝ)<((N/d:ℕ):ℝ)+1 := by
             apply (div_lt_iff₀ hdr).mpr
             exact_mod_cast (Nat.lt_mul_div_succ N hd).trans_eq (Nat.mul_comm _ _)
           have hlo := Nat.cast_div_le (α:=ℝ) (m:=N) (n:=d)
           change |(N:ℝ)*(mobR d/d)-mobR d*((N/d:ℕ):ℝ)| ≤ 1
           rw [show (N:ℝ)*(mobR d/d)-mobR d*((N/d:ℕ):ℝ)=
                 mobR d*((N:ℝ)/d-((N/d:ℕ):ℝ)) by ring,abs_mul,abs_of_nonneg (sub_nonneg.mpr hlo)]
           exact (mul_le_of_le_one_left (sub_nonneg.mpr hlo) hmu).trans (by linarith)
         _ = _ := by simp
  have h := (abs_add_le ((N:ℝ)*S-1) 1).trans (add_le_add herr (le_refl _))
  rw [sub_add_cancel,abs_mul,abs_of_pos hn,abs_one] at h
  change |S|≤2
  apply le_of_mul_le_mul_left _ hn
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  linarith only [h,hn1]

private theorem ramanujan_divisors_right (h q:ℕ) (hh:0<h) (hq:0<q) :
    (dyadicRamanujanDivisor h q:ℝ) =
      ∑d∈h.divisors,if d∣q then mobR (q/d)*(d:ℝ) else 0 := by
  have hs : (q.gcd h).divisors=h.divisors.filter (fun d=>d∣q) := by
    ext d;simp [Nat.mem_divisors,Nat.dvd_gcd_iff,hh.ne',(Nat.gcd_pos_of_pos_left _ hq).ne',and_comm]
  unfold dyadicRamanujanDivisor
  push_cast
  rw [hs,sum_filter]

private theorem ramanujan_multiple_reciprocal (d X:ℕ) (hd:0<d) :
    (∑j∈range X,(if d∣j+1 then mobR ((j+1)/d)*(d:ℝ) else 0)/((j+1:ℕ):ℝ)) =
      ∑k∈range (X/d),mobR (k+1)/((k+1:ℕ):ℝ) := by
  rw [←sum_positive_multiples (fun t=>mobR t/(t:ℝ)) X d hd]
  apply sum_congr rfl
  intro j _
  by_cases hv : d∣j+1
  · simp only [ite_eq_left hv]
    have hpos := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos j) hv) hd
    have he : (d:ℝ)*(((j+1)/d:ℕ):ℝ)=((j+1:ℕ):ℝ) := by exact_mod_cast Nat.mul_div_cancel' hv
    rw [←he]
    field_simp
  · simp [hv]

theorem signedRamanujan_reciprocal_band (h R Q:ℕ) (hh:0<h) :
    |∑j∈Ico R Q,(dyadicRamanujanDivisor h (j+1):ℝ)/((j+1:ℕ):ℝ)|≤4*(h.divisors.card:ℝ) := by
  by_cases hRQ : R≤Q
  · simp_rw [ramanujan_divisors_right h _ hh (Nat.succ_pos _),sum_div,sum_comm (s:=Ico R Q)]
    apply (abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑ _d∈h.divisors,(4:ℝ) := by
           apply sum_le_sum
           intro d hd
           have hd0 := Nat.pos_of_mem_divisors hd
           rw [sum_Ico_eq_sub _ hRQ,ramanujan_multiple_reciprocal d Q hd0,ramanujan_multiple_reciprocal d R hd0]
           exact (abs_sub _ _).trans ((add_le_add (moebius_reciprocal_prefix_bound (Q/d))
             (moebius_reciprocal_prefix_bound (R/d))).trans_eq (by norm_num))
         _ = _ := by simp [nsmul_eq_mul,mul_comm]
  · simp [Ico_eq_empty_of_le (Nat.le_of_not_ge hRQ)]
end GoldbachPartial
