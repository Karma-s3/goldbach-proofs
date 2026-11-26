import TruncatedRamanujanSquare

namespace GoldbachPartial
open Finset

/-- Möbius inversion on the finite partially ordered set 1,...,R under divisibility. -/
noncomputable def finiteMultipleMobiusInverse (R : ℕ) (h : ℕ→ℝ) (d : ℕ) : ℝ :=
  ∑ m∈(Icc 1 R).filter (fun m => d∣m),(ArithmeticFunction.moebius (m/d):ℝ)*h m

/-- The transform of divisibility weights which occurs in the finite CRT expansion. -/
noncomputable def finiteRamanujanTransform (R : ℕ) (f : ℕ→ℝ) (r : ℕ) : ℝ :=
  ∑ d∈(Icc 1 R).filter (fun d => r∣d),f d/(d:ℝ)

noncomputable def exactRamanujanWeight (R d : ℕ) : ℝ :=
  (d:ℝ)*finiteMultipleMobiusInverse R (fun m : ℕ => (ArithmeticFunction.moebius m:ℝ)/(m.totient:ℝ)) d

private theorem finite_mu_divisors {w : ℕ} (hw : 0<w) :
    (∑ z∈w.divisors,(ArithmeticFunction.moebius z:ℝ))=if w=1 then 1 else 0 := by
  have hs := sum_dyadicRamanujanDivisor_divisors 1 hw
  have hh (v : ℕ) : dyadicRamanujanDivisor 1 v=ArithmeticFunction.moebius v := by simp [dyadicRamanujanDivisor]
  simp_rw [hh] at hs
  by_cases h : w=1
  · simp [h]
  · simp [h] at hs ⊢
    exact_mod_cast hs

private theorem multiple_mu_fiber {R r m : ℕ} (hr : 0<r) (hm : m∈Icc 1 R) :
    (∑ d∈(Icc 1 R).filter (fun d => r∣d ∧ d∣m),(ArithmeticFunction.moebius (m/d):ℝ)) =
      if m=r then 1 else 0 := by
  have hm0 : 0<m := (mem_Icc.mp hm).1
  by_cases h : r∣m
  · let w := m/r
    have hw : 0<w := Nat.div_pos (Nat.le_of_dvd hm0 h) hr
    have hprod : r*w=m := Nat.mul_div_cancel' h
    calc
      _ = ∑ z∈w.divisors,(ArithmeticFunction.moebius (w/z):ℝ) := by
        symm
        apply sum_bij (fun z _ => r*z)
        · intro z hz
          have hrd : r*z∣m := hprod ▸ Nat.mul_dvd_mul_left r (Nat.dvd_of_mem_divisors hz)
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hrd hm0,
            (Nat.le_of_dvd hm0 hrd).trans (mem_Icc.mp hm).2⟩,dvd_mul_right r z,hrd⟩
        · intro x _ y _ hx
          exact Nat.eq_of_mul_eq_mul_left hr hx
        · intro d hd
          obtain ⟨_,⟨z,hz⟩,hdm⟩ := mem_filter.mp hd
          refine ⟨z,Nat.mem_divisors.mpr ⟨?_,hw.ne'⟩,hz.symm⟩
          rw [hz,←hprod] at hdm
          exact Nat.dvd_of_mul_dvd_mul_left hr hdm
        · intro z _;rw [←Nat.div_div_eq_div_mul]
      _ = if w=1 then 1 else 0 := (Nat.sum_div_divisors w (fun z => (ArithmeticFunction.moebius z:ℝ))).trans (finite_mu_divisors hw)
      _ = _ := by
        have hiff : w=1 ↔ m=r := by
          constructor
          · intro hw;simpa [hw] using hprod.symm
          · rintro rfl;exact Nat.div_self hr
        simp only [hiff]
  · have hzero : (Icc 1 R).filter (fun d => r∣d ∧ d∣m)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro d hd;exact h ((mem_filter.mp hd).2.1.trans (mem_filter.mp hd).2.2)
    have hne : m≠r := fun hm => h (hm ▸ dvd_refl r)
    simp [hzero,hne]

/-- Summing the inverted weights over the multiples of r recovers h(r) for 1≤r≤R. -/
theorem sum_finiteMultipleMobiusInverse (R : ℕ) (h : ℕ→ℝ) {r : ℕ} (hr : r∈Icc 1 R) :
    (∑ d∈(Icc 1 R).filter (fun d => r∣d),finiteMultipleMobiusInverse R h d)=h r := by
  let I := Icc 1 R
  let f := fun d m : ℕ => (if r∣d ∧ d∣m then (ArithmeticFunction.moebius (m/d):ℝ) else 0)*h m
  have hex : (∑ d∈I.filter (fun d => r∣d),finiteMultipleMobiusInverse R h d) =
       ∑ d∈I,∑ m∈I,f d m := by
    rw [sum_filter]
    apply sum_congr rfl;intro d _
    unfold finiteMultipleMobiusInverse
    rw [sum_filter]
    by_cases hrd : r∣d <;> simp [hrd,f,I,ite_mul]
  rw [hex,sum_comm]
  calc
    _ = ∑ m∈I,(if m=r then (1:ℝ) else 0)*h m := by
      apply sum_congr rfl;intro m hm
      dsimp only [f]
      rw [←sum_mul,←sum_filter,multiple_mu_fiber (mem_Icc.mp hr).1 hm]
    _ = _ := by simp [ite_mul,show r∈I from hr]

theorem finiteRamanujanTransform_inversion (R : ℕ) (h : ℕ→ℝ) {r : ℕ} (hr : r∈Icc 1 R) :
    finiteRamanujanTransform R (fun d => (d:ℝ)*finiteMultipleMobiusInverse R h d) r=h r := by
  unfold finiteRamanujanTransform
  rw [←sum_finiteMultipleMobiusInverse R h hr]
  apply sum_congr rfl;intro d hd
  have hpos : (0:ℝ)<d := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hd).1).1
  field_simp

theorem exactRamanujanWeight_transform (R : ℕ) {r : ℕ} (hr : r∈Icc 1 R) :
    finiteRamanujanTransform R (exactRamanujanWeight R) r=(ArithmeticFunction.moebius r:ℝ)/(r.totient:ℝ) :=
  finiteRamanujanTransform_inversion R _ hr

/-- Direct quotient parametrization of the inverse weight. -/
theorem exactRamanujanWeight_eq_sum (R d : ℕ) (hd : 0<d) :
    exactRamanujanWeight R d=(d:ℝ)*∑ j∈Icc 1 (R/d),
      (ArithmeticFunction.moebius j:ℝ)*((ArithmeticFunction.moebius (j*d):ℝ)/((j*d).totient:ℝ)) := by
  unfold exactRamanujanWeight finiteMultipleMobiusInverse
  congr 1
  symm
  apply sum_bij (fun j _ => j*d)
  · intro j hj
    obtain ⟨hj0,hjR⟩ := mem_Icc.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hj0 hd,(Nat.le_div_iff_mul_le hd).mp hjR⟩,
      dvd_mul_left d j⟩
  · intro j _ k _ h
    exact Nat.eq_of_mul_eq_mul_right hd h
  · intro m hm
    obtain ⟨hi,hdm⟩ := mem_filter.mp hm
    have hm0 := (mem_Icc.mp hi).1
    have hmul := Nat.div_mul_cancel hdm
    refine ⟨m/d,mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hm0 hdm) hd,?_⟩,hmul⟩
    apply (Nat.le_div_iff_mul_le hd).mpr
    rw [hmul];exact (mem_Icc.mp hi).2
  · intro j _
    rw [Nat.mul_div_cancel _ hd]

/-- The divisor coefficients from finite inversion evaluate to the truncated Ramanujan series. -/
theorem finiteMultipleMobiusInverse_divisor_sum (R k : ℕ) (h : ℕ→ℝ) :
    (∑ d∈(Icc 1 R).filter (fun d => d∣k),(d:ℝ)*finiteMultipleMobiusInverse R h d) =
    ∑ m∈Icc 1 R,(dyadicRamanujanDivisor k m:ℝ)*h m := by
  let I := Icc 1 R
  let f := fun d m : ℕ => (if d∣k ∧ d∣m then (ArithmeticFunction.moebius (m/d):ℝ)*d else 0)*h m
  have hex (d : ℕ) : (if d∣k then (d:ℝ)*finiteMultipleMobiusInverse R h d else 0) = ∑ m∈I,f d m := by
    unfold finiteMultipleMobiusInverse
    rw [sum_filter,mul_sum]
    by_cases hdk : d∣k
    · simp only [hdk,ite_true]
      apply sum_congr rfl;intro m _
      by_cases hdm : d∣m <;> simp [f,hdk,hdm]
      ring
    · simp [hdk,f]
  rw [sum_filter]
  calc
    _ = ∑ d∈I,∑ m∈I,f d m := sum_congr rfl fun d _ => hex d
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl;intro m hm
      dsimp only [f];rw [←sum_mul,←sum_filter]
      have hm0 := (mem_Icc.mp hm).1
      have hset : I.filter (fun d => d∣k ∧ d∣m)=(m.gcd k).divisors := by
        ext d
        constructor
        · intro hd
          obtain ⟨_,hdk,hdm⟩ := mem_filter.mp hd
          exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdm hdk,(Nat.gcd_pos_of_pos_left k hm0).ne'⟩
        · intro hd
          obtain ⟨hdm,hdk⟩ := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hd)
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
            (Nat.le_of_dvd hm0 hdm).trans (mem_Icc.mp hm).2⟩,hdk,hdm⟩
      rw [hset,dyadicRamanujanDivisor];push_cast;rfl

theorem exactRamanujanWeight_divisor_sum (R k : ℕ) :
    (∑ d∈(Icc 1 R).filter (fun d => d∣k),exactRamanujanWeight R d) =
    ∑ m∈Icc 1 R,(dyadicRamanujanDivisor k m:ℝ)*((ArithmeticFunction.moebius m:ℝ)/(m.totient:ℝ)) :=
  finiteMultipleMobiusInverse_divisor_sum R k _

end GoldbachPartial
