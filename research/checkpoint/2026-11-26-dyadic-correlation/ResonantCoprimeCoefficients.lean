import AllResonantMobiusReduction

namespace GoldbachPartial
open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta

def resonantCoprimePart (q j : ℕ) : ℕ :=
  j.gcd (∏ e∈j.divisors.filter (fun e => q.Coprime e),e)

theorem resonantCoprimePart_divisors {q j : ℕ} (hj : 0<j) :
    (resonantCoprimePart q j).divisors = j.divisors.filter (fun e => q.Coprime e) := by
  let S := j.divisors.filter (fun e => q.Coprime e)
  let P := ∏ e∈S,e
  have hcop : q.Coprime P := Nat.coprime_prod_right_iff.mpr (fun e he => (mem_filter.mp he).2)
  have hv : 0<j.gcd P := Nat.gcd_pos_of_pos_left _ hj
  change (j.gcd P).divisors = S
  ext e
  constructor
  · intro he
    have hd := Nat.dvd_of_mem_divisors he
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd.trans (Nat.gcd_dvd_left ..),hj.ne'⟩,
      hcop.coprime_dvd_right (hd.trans (Nat.gcd_dvd_right ..))⟩
  · intro he
    have hP : e∣P := dvd_prod_of_mem (fun x : ℕ => x) he
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (Nat.dvd_of_mem_divisors (mem_filter.mp he).1) hP,hv.ne'⟩

theorem resonantMobius_multiple_coefficient {n D q j : ℕ} (hD : D<q) (hj : 0<j) (hn : q*j≤n) :
    (∑ d ∈ ((Ioc D n).filter (fun d => q∣d)).filter (fun d => d∣q*j),crtLambdaCoefficient d) =
      (ArithmeticFunction.moebius q:ℝ)*
        (Λ (resonantCoprimePart q j) - (if resonantCoprimePart q j=1 then Real.log q else 0)) := by
  let v := resonantCoprimePart q j
  have hq : 0<q := by omega
  have hz : ∀ e∈j.divisors, ¬q.Coprime e → crtLambdaCoefficient (q*e)=0 := by
    intro e _ he
    have hsq : ¬Squarefree (q*e) := fun h => he (Nat.coprime_of_squarefree_mul h)
    simp [crtLambdaCoefficient,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  have hm (e : ℕ) (he : e∈v.divisors) :
      crtLambdaCoefficient (q*e) = (ArithmeticFunction.moebius q:ℝ)*
        (crtLambdaCoefficient e - (ArithmeticFunction.moebius e:ℝ)*Real.log q) := by
    have hd := (resonantCoprimePart_divisors (q:=q) hj) ▸ he
    have hc : q.Coprime e := (mem_filter.mp hd).2
    have he' : 0<e := Nat.pos_of_mem_divisors he
    rw [crtLambdaCoefficient,ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
      Nat.cast_mul,Real.log_mul (by exact_mod_cast hq.ne') (by exact_mod_cast he'.ne')]
    unfold crtLambdaCoefficient
    push_cast
    ring
  have hconv : (∑ e∈v.divisors,crtLambdaCoefficient e) = Λ v := by
    have h := ArithmeticFunction.sum_moebius_mul_log_eq (n:=v)
    simp only [ArithmeticFunction.log_apply] at h
    simp only [crtLambdaCoefficient,neg_mul,Finset.sum_neg_distrib,h,neg_neg]
  have hmu : (∑ e∈v.divisors,(ArithmeticFunction.moebius e:ℝ)) = if v=1 then 1 else 0 := by
    have hx := congrArg (fun f : ArithmeticFunction ℝ => f v)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R:=ℝ))
    change ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)*(ArithmeticFunction.zeta:ArithmeticFunction ℝ)) v =
      (1:ArithmeticFunction ℝ) v at hx
    rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at hx
    exact hx
  calc
    _ = ∑ e∈j.divisors,crtLambdaCoefficient (q*e) := by
      symm
      apply sum_bij (fun e _ => q*e)
      · intro e he
        have hd := Nat.dvd_of_mem_divisors he
        have hpos := Nat.pos_of_mem_divisors he
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hD.trans_le (Nat.le_mul_of_pos_right _ hpos),
          (Nat.mul_le_mul_left q (Nat.le_of_dvd hj hd)).trans hn⟩,dvd_mul_right _ _⟩,
          Nat.mul_dvd_mul_left q hd⟩
      · intro e he f hf hef
        exact Nat.eq_of_mul_eq_mul_left hq hef
      · intro d hd
        obtain ⟨hdi,hdiv⟩ := mem_filter.mp hd
        obtain ⟨e,rfl⟩ := (mem_filter.mp hdi).2
        exact ⟨e,Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left hq).mp hdiv,hj.ne'⟩,rfl⟩
      · intro _ _
        rfl
    _ = ∑ e∈v.divisors,crtLambdaCoefficient (q*e) := by
      rw [resonantCoprimePart_divisors hj]
      rw [sum_filter]
      apply sum_congr rfl
      intro e he
      by_cases hc : q.Coprime e <;> simp [hc,hz e he]
    _ = ∑ e∈v.divisors,(ArithmeticFunction.moebius q:ℝ)*(crtLambdaCoefficient e -
        (ArithmeticFunction.moebius e:ℝ)*Real.log q) := sum_congr rfl hm
    _ = _ := by
      rw [←mul_sum,sum_sub_distrib,hconv,←sum_mul,hmu]
      change _ = (ArithmeticFunction.moebius q:ℝ)*(ArithmeticFunction.vonMangoldt v - (if v=1 then Real.log q else 0))
      by_cases h : v=1 <;> simp [h]

theorem resonantCoprimePart_spec {q j : ℕ} (hj : 0<j) :
    let v := resonantCoprimePart q j
    0<v ∧ v∣j ∧ q.Coprime v ∧ ∀ e, e∣j → q.Coprime e → e∣v := by
  let v := resonantCoprimePart q j
  have hv : 0<v := Nat.gcd_pos_of_pos_left _ hj
  have he : v∈v.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _,hv.ne'⟩
  rw [show v.divisors=j.divisors.filter (fun d => q.Coprime d) from resonantCoprimePart_divisors hj] at he
  obtain ⟨hi,hc⟩ := mem_filter.mp he
  refine ⟨hv,Nat.dvd_of_mem_divisors hi,hc,?_⟩
  intro e hd hc
  have hk : e∈j.divisors.filter (fun d => q.Coprime d) := mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd,hj.ne'⟩,hc⟩
  rw [←resonantCoprimePart_divisors hj] at hk
  exact Nat.dvd_of_mem_divisors hk

theorem resonantCoprimePart_smooth_quotient {q j : ℕ} (hq : 0<q) (hj : 0<j) :
    (j/resonantCoprimePart q j).primeFactors ⊆ q.primeFactors := by
  let v := resonantCoprimePart q j
  obtain ⟨hv,hd,hcp,hmax⟩ := resonantCoprimePart_spec (q:=q) hj
  intro p hp
  obtain ⟨hprime,hdiv,_⟩ := Nat.mem_primeFactors.mp hp
  apply hprime.mem_primeFactors _ hq.ne'
  by_contra hn
  have hc : q.Coprime p := (hprime.coprime_iff_not_dvd.mpr hn).symm
  have hm : v*p ∣ j := by
    rw [←Nat.mul_div_cancel' hd]
    exact Nat.mul_dvd_mul_left _ hdiv
  have h := Nat.le_of_dvd hv (hmax (v*p) hm (hcp.mul_right hc))
  have hlt : v<v*p := by simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hprime.one_lt hv
  exact hlt.not_ge h

theorem resonantCoprimePart_smooth_mul {q u v : ℕ} (hu : 0<u) (hv : 0<v)
    (hs : u.primeFactors ⊆ q.primeFactors) (hc : q.Coprime v) :
    resonantCoprimePart q (u*v) = v := by
  let b := resonantCoprimePart q (u*v)
  obtain ⟨_,hbd,hcp,hmax⟩ := resonantCoprimePart_spec (q:=q) (Nat.mul_pos hu hv)
  have hbu : b.Coprime u := by
    by_contra h
    obtain ⟨p,hp,hpb,hpu⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hpq := Nat.dvd_of_mem_primeFactors (hs (hp.mem_primeFactors hpu hu.ne'))
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,hpq,hpb⟩) hcp
  exact Nat.dvd_antisymm (hbu.dvd_of_dvd_mul_left hbd) (hmax _ (dvd_mul_left ..) hc)

theorem resonant_smooth_coprime_sum {A : Type*} [AddCommMonoid A] {q : ℕ} (hq : 0<q)
    (X : ℕ) (f : ℕ→ℕ→A) :
    (∑ j∈Icc 1 X,f (j/resonantCoprimePart q j) (resonantCoprimePart q j)) =
      ∑ u ∈ (Icc 1 X).filter (fun u : ℕ => u.primeFactors ⊆ q.primeFactors),
        ∑ v ∈ (Icc 1 (X/u)).filter (fun v => q.Coprime v),f u v := by
  classical
  let uv (j : ℕ) : (Σ _ : ℕ, ℕ) := ⟨j/resonantCoprimePart q j,resonantCoprimePart q j⟩
  rw [sum_sigma']
  apply sum_bij (fun j _ => uv j)
  · intro j hj
    obtain ⟨hj0,hjX⟩ := mem_Icc.mp hj
    let v := resonantCoprimePart q j
    obtain ⟨hv,hd,hcop,_⟩ := resonantCoprimePart_spec (q:=q) hj0
    have hu : 0<j/v := Nat.div_pos (Nat.le_of_dvd hj0 hd) hv
    have hid : v*(j/v)=j := Nat.mul_div_cancel' hd
    apply mem_sigma.mpr
    exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hu,(Nat.div_le_self j v).trans hjX⟩,
      resonantCoprimePart_smooth_quotient hq hj0⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hv,(Nat.le_div_iff_mul_le hu).mpr (hid.le.trans hjX)⟩,hcop⟩⟩
  · intro i hi j hj he
    have hm := congrArg (fun z : (Σ _ : ℕ,ℕ) => z.2*z.1) he
    change resonantCoprimePart q i*(i/resonantCoprimePart q i) =
      resonantCoprimePart q j*(j/resonantCoprimePart q j) at hm
    rwa [Nat.mul_div_cancel' (resonantCoprimePart_spec (q:=q) (mem_Icc.mp hi).1).2.1,
      Nat.mul_div_cancel' (resonantCoprimePart_spec (q:=q) (mem_Icc.mp hj).1).2.1] at hm
  · rintro ⟨u,v⟩ h
    obtain ⟨hu,hv⟩ := mem_sigma.mp h
    obtain ⟨hu,hs⟩ := mem_filter.mp hu
    obtain ⟨hv,hc⟩ := mem_filter.mp hv
    obtain ⟨hu0,_⟩ := mem_Icc.mp hu
    obtain ⟨hv0,hvX⟩ := mem_Icc.mp hv
    have hid := resonantCoprimePart_smooth_mul (q:=q) (u:=u) (v:=v) hu0 hv0 hs hc
    have hx : u*v≤X := by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu0).mp hvX
    refine ⟨u*v,mem_Icc.mpr ⟨Nat.mul_pos hu0 hv0,hx⟩,?_⟩
    simp [uv,hid,Nat.mul_div_cancel _ hv0]
  · intro _ _
    rfl

noncomputable def resonantReducedCoefficient (q j : ℕ) : ℝ :=
  (ArithmeticFunction.moebius q:ℝ) * (Λ (resonantCoprimePart q j) -
    (if resonantCoprimePart q j=1 then Real.log q else 0))

theorem resonantMobiusWave_reduced {D q : ℕ} (hD : D<q) (n : ℕ) (β : ℝ) :
    resonantMobiusWave n D n q β =
    ∑ j∈Icc 1 (n/q),(resonantReducedCoefficient q j:ℂ)*ExtendedArcCoefficient.E (((q*j:ℕ):ℝ)*β) := by
  classical
  let I := ((Ioc D n).filter (fun d => q∣d))
  let a := fun d : ℕ => (crtLambdaCoefficient d:ℂ)
  let F := fun k : ℕ => (∑ d∈I.filter (fun d => d∣k),a d)*ExtendedArcCoefficient.E ((k:ℝ)*β)
  have hq : 0<q := by omega
  change smallDivisorWave n I a β=_
  rw [smallDivisorWave_coefficients]
  change (∑ k∈Icc 1 n,F k)=_
  have hs : (∑ k∈Icc 1 n,F k) = ∑ k∈(Icc 1 n).filter (fun k => q∣k),F k := by
    rw [sum_filter]
    apply sum_congr rfl
    intro k hk
    by_cases h : q∣k
    · simp [h]
    · rw [ite_eq_right h]
      have he : I.filter (fun d => d∣k) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro d hd hdk
        exact h ((mem_filter.mp hd).2.trans hdk)
      simp [F,he]
  rw [hs]
  symm
  apply sum_bij (fun j _ => q*j)
  · intro j hj
    obtain ⟨h0,hmax⟩ := mem_Icc.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hq h0,
      by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hmax⟩,dvd_mul_right ..⟩
  · intro i hi j hj h
    exact Nat.eq_of_mul_eq_mul_left hq h
  · intro k hk
    obtain ⟨hi,j,rfl⟩ := mem_filter.mp hk
    obtain ⟨hpos,hmax⟩ := mem_Icc.mp hi
    refine ⟨j,mem_Icc.mpr ⟨?_,(Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hmax)⟩,rfl⟩
    by_contra! h
    simp [show j=0 by omega] at hpos
  · intro j hj
    obtain ⟨hj0,hjX⟩ := mem_Icc.mp hj
    have hn : q*j≤n := by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hjX
    have hc := resonantMobius_multiple_coefficient hD hj0 hn
    dsimp only [F,a,I]
    rw [←Complex.ofReal_sum]
    exact congrArg (fun z : ℝ => (z:ℂ)*ExtendedArcCoefficient.E (((q*j:ℕ):ℝ)*β)) hc.symm

theorem resonantReducedCoefficient_sum {q : ℕ} (hq : 0<q) (X : ℕ) :
    (∑ j∈Icc 1 X,resonantReducedCoefficient q j) =
      (ArithmeticFunction.moebius q:ℝ) *
      ∑ u ∈ (Icc 1 X).filter (fun u : ℕ => u.primeFactors ⊆ q.primeFactors),
        ∑ v ∈ (Icc 1 (X/u)).filter (fun v => q.Coprime v),
        (Λ v - (if v=1 then Real.log q else 0)) := by
  unfold resonantReducedCoefficient
  rw [←mul_sum]
  congr 1
  exact resonant_smooth_coprime_sum hq X (fun _ v => Λ v - if v=1 then Real.log q else 0)

end GoldbachPartial