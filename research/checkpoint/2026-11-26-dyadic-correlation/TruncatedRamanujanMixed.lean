import TruncatedRamanujanSquare

namespace GoldbachPartial
open Finset

private theorem sum_totient_complement_multiples {d v : ℕ} (hd : 0<d) (hv : v∣d) :
    (∑ r∈d.divisors.filter (fun r => v∣r),(d/r).totient) = d/v := by
  let w := d/v
  have hv0 := Nat.pos_of_dvd_of_pos hv hd
  have hw0 : 0<w := Nat.div_pos (Nat.le_of_dvd hd hv) hv0
  have hprod : v*w=d := Nat.mul_div_cancel' hv
  calc
    _ = ∑ z∈w.divisors,(w/z).totient := by
      symm
      apply sum_bij (fun z _ => v*z)
      · intro z hz
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hprod ▸ Nat.mul_dvd_mul_left v (Nat.dvd_of_mem_divisors hz),hd.ne'⟩,
          dvd_mul_right v z⟩
      · intro x _ y _ he
        exact Nat.eq_of_mul_eq_mul_left hv0 he
      · intro r hr
        obtain ⟨hrd,⟨z,hz⟩⟩ := mem_filter.mp hr
        refine ⟨z,Nat.mem_divisors.mpr ⟨?_,hw0.ne'⟩,hz.symm⟩
        have h := Nat.dvd_of_mem_divisors hrd
        rw [hz,←hprod] at h
        exact Nat.dvd_of_mul_dvd_mul_left hv0 h
      · intro z _
        rw [←Nat.div_div_eq_div_mul]
    _ = _ := (Nat.sum_div_divisors w Nat.totient).trans (Nat.sum_totient w)

private theorem moebius_sum_gcd (n : ℕ) {d : ℕ} (hd : 0<d) :
    ∑ v∈(d.gcd n).divisors,(ArithmeticFunction.moebius v:ℝ)=if d.Coprime n then 1 else 0 := by
  let g := d.gcd n
  have hg : 0<g := Nat.gcd_pos_of_pos_left n hd
  have hs := sum_dyadicRamanujanDivisor_divisors 1 hg
  have hh (v : ℕ) : dyadicRamanujanDivisor 1 v = ArithmeticFunction.moebius v := by
    simp [dyadicRamanujanDivisor]
  simp_rw [hh] at hs
  change (∑ r∈g.divisors,ArithmeticFunction.moebius r)=if g∣1 then (g:ℤ) else 0 at hs
  by_cases h : g=1
  · change (∑ v∈g.divisors,(ArithmeticFunction.moebius v:ℝ))=if g=1 then 1 else 0
    simp [h]
  · have h' : ¬g∣1 := fun hh => h (Nat.dvd_one.mp hh)
    simp [h'] at hs
    change (∑ v∈g.divisors,(ArithmeticFunction.moebius v:ℝ))=if g=1 then 1 else 0
    rw [ite_eq_right h]
    exact_mod_cast hs

private theorem mu_row_step {d r v : ℕ} (hs : Squarefree d) (hr : r∣d) (hv : v∣r) :
    ((ArithmeticFunction.moebius (r/v):ℝ)*v) * ((ArithmeticFunction.moebius r:ℝ)/r.totient) =
      (ArithmeticFunction.moebius v:ℝ)*v*((d/r).totient:ℝ)/(d.totient:ℝ) := by
  have sr := hs.squarefree_of_dvd hr
  have hvr : v*(r/v)=r := Nat.mul_div_cancel' hv
  have hrd : r*(d/r)=d := Nat.mul_div_cancel' hr
  have cp := Nat.coprime_of_squarefree_mul (hvr.symm ▸ sr : Squarefree (v*(r/v)))
  have cp' := Nat.coprime_of_squarefree_mul (hrd.symm ▸ hs : Squarefree (r*(d/r)))
  have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime cp
  rw [hvr] at hm
  have ht := Nat.totient_mul cp'
  rw [hrd] at ht
  have hsq : (ArithmeticFunction.moebius (r/v):ℝ)^2=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (sr.squarefree_of_dvd (Nat.div_dvd_of_dvd hv))
  have htp : 0<(d/r).totient := Nat.totient_pos.mpr (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hr)
    (Nat.pos_of_ne_zero sr.ne_zero))
  have htp' : (0:ℝ)<(d/r).totient := by exact_mod_cast htp
  rw [hm,ht];push_cast
  field_simp
  linear_combination (v:ℝ)*(r.totient:ℝ)⁻¹*(ArithmeticFunction.moebius v:ℝ)*hsq

/-- The squarefree divisor identity underlying the prime-by-small-divisor main term. -/
theorem mixed_ramanujan_divisor_local (n : ℕ) {d : ℕ} (hs : Squarefree d) :
    (∑ r∈d.divisors,(dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/r.totient)) =
      if d.Coprime n then (d:ℝ)/d.totient else 0 := by
  let μ := fun z : ℕ => (ArithmeticFunction.moebius z:ℝ)
  let D := d.divisors
  let G := (d.gcd n).divisors
  let f := fun v r : ℕ => (μ v*(v:ℝ)/(d.totient:ℝ))*((d/r).totient:ℝ)
  have hd := Nat.pos_of_ne_zero hs.ne_zero
  have hg : 0<d.gcd n := Nat.gcd_pos_of_pos_left n hd
  have row (r : ℕ) (hr : r∈D) :
      (dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/r.totient) =
        ∑ v∈G, if v∣r then f v r else 0 := by
    have hrd := Nat.dvd_of_mem_divisors hr
    have hr0 := Nat.pos_of_dvd_of_pos hrd hd
    have hrg : 0<r.gcd n := Nat.gcd_pos_of_pos_left n hr0
    have hset : G.filter (fun v => v∣r)=(r.gcd n).divisors := by
      ext v
      constructor
      · intro h
        obtain ⟨hm,hvr⟩ := mem_filter.mp h
        exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hvr (Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hm)).2,hrg.ne'⟩
      · intro h
        obtain ⟨hvr,hvn⟩ := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors h)
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (hvr.trans hrd) hvn,hg.ne'⟩,hvr⟩
    rw [←sum_filter,hset,dyadicRamanujanDivisor];push_cast
    rw [sum_mul]
    apply sum_congr rfl;intro v hv
    have hvr := (Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hv)).1
    exact (mu_row_step hs hrd hvr).trans (by dsimp [f,μ];ring)
  have col (v : ℕ) (hv : v∈G) : (∑ r∈D,if v∣r then f v r else 0)=(d:ℝ)/d.totient*μ v := by
    have hvd := (Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hv)).1
    have ht : (∑ r∈D.filter (fun r => v∣r),((d/r).totient:ℝ))=((d/v:ℕ):ℝ) := by
      exact_mod_cast sum_totient_complement_multiples hd hvd
    rw [←sum_filter]
    dsimp only [f]
    rw [←mul_sum,ht]
    have hp : (v:ℝ)*((d/v:ℕ):ℝ)=(d:ℝ) := by exact_mod_cast Nat.mul_div_cancel' hvd
    linear_combination μ v/(d.totient:ℝ)*hp
  calc
    _ = ∑ r∈D,∑ v∈G,if v∣r then f v r else 0 := sum_congr rfl row
    _ = ∑ v∈G,(d:ℝ)/d.totient*μ v := by rw [sum_comm];exact sum_congr rfl col
    _ = _ := by
      rw [←mul_sum]
      change (d:ℝ)/d.totient*(∑ v∈(d.gcd n).divisors,(ArithmeticFunction.moebius v:ℝ))=_
      rw [moebius_sum_gcd n hd]
      split <;> simp

/-- Diagonal form of the prime progression main term, with the actual truncated divisor weights. -/
theorem crt_mixed_main_ramanujan (n R : ℕ) (X : ℝ) :
    (∑ d∈Icc 1 R,crtLambdaCoefficient d*(if d.Coprime n then X/(d.totient:ℝ) else 0)) =
    X*(∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/r.totient)*
      crtRamanujanTruncation R r) := by
  let I := Icc 1 R
  let C := fun r : ℕ => (dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/r.totient)
  let f := crtLambdaCoefficient
  let a := fun r d : ℕ => if r∣d then C r else 0
  have row (r : ℕ) :
      X*(C r*crtRamanujanTruncation R r)=∑ d∈I, X*(f d/(d:ℝ))*a r d := by
    unfold crtRamanujanTruncation
    rw [sum_filter,mul_sum,mul_sum]
    apply sum_congr rfl;intro d _
    by_cases h : r∣d <;> simp [a,f,h]
    ring
  have col (d : ℕ) (hd : d∈I) :
      (∑ r∈I,X*(f d/(d:ℝ))*a r d)= f d*(if d.Coprime n then X/(d.totient:ℝ) else 0) := by
    rw [←mul_sum]
    by_cases hs : Squarefree d
    · have hset : I.filter (fun r => r∣d)=d.divisors := by
        ext r
        constructor
        · intro h
          exact Nat.mem_divisors.mpr ⟨(mem_filter.mp h).2,hs.ne_zero⟩
        · intro h
          have hrd := Nat.dvd_of_mem_divisors h
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors h,
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hrd).trans (mem_Icc.mp hd).2⟩,hrd⟩
      dsimp only [a]
      rw [←sum_filter,hset]
      have hsum := mixed_ramanujan_divisor_local n hs
      change (∑ r∈d.divisors,C r)=_ at hsum
      rw [hsum]
      have hd' : (d:ℝ)≠0 := by exact_mod_cast hs.ne_zero
      split_ifs <;> field_simp
      ring
    · simp [f,crtLambdaCoefficient,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  symm
  change X*(∑ r∈I,C r*crtRamanujanTruncation R r)=_
  rw [mul_sum]
  calc
    _ = ∑ r∈I,∑ d∈I,X*(f d/(d:ℝ))*a r d := sum_congr rfl (fun r _ => row r)
    _ = _ := by rw [sum_comm];exact sum_congr rfl col

/-- The centered discrepancy for the exact progression with the endpoint k=n omitted. -/
noncomputable def primeSmallProgressionError (n d : ℕ) : ℝ :=
  (∑ k∈Ioo 0 n,if d∣n-k then ArithmeticFunction.vonMangoldt k else 0) -
    if d.Coprime n then ((n-1:ℕ):ℝ)/(d.totient:ℝ) else 0

/-- The mixed convolution in the true zero frequency, before taking any distributional estimates. -/
theorem truncatedLambda_mixed_ramanujan (n R : ℕ) :
    (∑ k∈Ioo 0 n,ArithmeticFunction.vonMangoldt k*truncatedLambdaDivisors R (n-k)) =
    ((n-1:ℕ):ℝ)*(∑ r∈Icc 1 R,(dyadicRamanujanDivisor n r:ℝ)*((ArithmeticFunction.moebius r:ℝ)/r.totient)*
      crtRamanujanTruncation R r) +
    ∑ d∈Icc 1 R,crtLambdaCoefficient d*primeSmallProgressionError n d := by
  let f := crtLambdaCoefficient
  let Λ' := ArithmeticFunction.vonMangoldt
  let S := Icc 1 R
  let K := Ioo 0 n
  rw [←crt_mixed_main_ramanujan,←sum_add_distrib]
  have hloc (k : ℕ) (hk : k∈K) : Λ' k*truncatedLambdaDivisors R (n-k)=
      ∑ d∈S,f d*(if d∣n-k then Λ' k else 0) := by
    have hnk : 0<n-k := by have h := mem_Ioo.mp hk;omega
    have hset : (n-k).divisors.filter (fun d => d≤R)=S.filter (fun d => d∣n-k) := by
      ext d
      dsimp only [S]
      simp only [mem_filter,mem_Icc,Nat.mem_divisors]
      constructor
      · rintro ⟨⟨h,_⟩,hr⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hnk,hr⟩,h⟩
      · rintro ⟨⟨_,hr⟩,h⟩
        exact ⟨⟨h,hnk.ne'⟩,hr⟩
    rw [truncatedLambdaDivisors,hset,sum_filter,mul_sum]
    apply sum_congr rfl;intro d _
    by_cases h : d∣n-k <;> simp [h,f,mul_comm]
  calc
    _ = ∑ k∈K,∑ d∈S,f d*(if d∣n-k then Λ' k else 0) := sum_congr rfl hloc
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl;intro d _
      rw [←mul_sum]
      dsimp only [primeSmallProgressionError,f,Λ',K]
      ring

end GoldbachPartial
