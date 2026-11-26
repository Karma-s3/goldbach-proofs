import PrimeArcModelBounds

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

private theorem signedFiber_phase_conj (t:ℝ) : (starRingEnd ℂ) (E t)=E (-t) := by
  unfold E
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

theorem unit_exp_ramanujan_integer (m : ℤ) (q : ℕ) [NeZero q] :
    ∑ a : (ZMod q)ˣ, E ((m:ℝ)*((a:ZMod q).val:ℝ)/q) = (dyadicRamanujanDivisor m.natAbs q:ℂ) := by
  cases m with
  | ofNat k => exact unit_exp_ramanujan_eq_divisor k q
  | negSucc k =>
    have h := congrArg (starRingEnd ℂ) (unit_exp_ramanujan_eq_divisor (k+1) q)
    simp only [map_sum,map_intCast,signedFiber_phase_conj] at h
    refine (Finset.sum_congr rfl fun a _ => ?_).trans h
    congr 1
    push_cast
    ring

theorem signedModeRow_exact (q : ℕ) [NeZero q] (m : ℤ) (ρ : ℝ) :
    (∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, E ((m:ℝ)*(t+((a:ZMod q).val:ℝ)/q))) =
      (dyadicRamanujanDivisor m.natAbs q:ℂ)*(∫ t in -ρ..ρ, E ((m:ℝ)*t)) := by
  have h (a : (ZMod q)ˣ) (t:ℝ) :
      E ((m:ℝ)*(t+((a:ZMod q).val:ℝ)/q)) =
        E ((m:ℝ)*((a:ZMod q).val:ℝ)/q)*E ((m:ℝ)*t) := by
    rw [←phase_add]
    congr 1
    ring
  simp_rw [h,intervalIntegral.integral_const_mul]
  rw [←sum_mul,unit_exp_ramanujan_integer]

theorem ramanujan_frequency_mass (q N : ℕ) (hq : 0<q) :
    ∑ h ∈ range N, |(dyadicRamanujanDivisor (h+1) q:ℝ)| ≤ (N:ℝ)*q.divisors.card := by
  have hpoint (h:ℕ) :
      |(dyadicRamanujanDivisor (h+1) q:ℝ)| ≤ ∑ d ∈ q.divisors, if d ∣ h+1 then (d:ℝ) else 0 := by
    have he : (q.gcd (h+1)).divisors = q.divisors.filter (fun d => d∣h+1) := by
      ext d
      simp [Nat.mem_divisors,Nat.dvd_gcd_iff,hq.ne',(Nat.gcd_pos_of_pos_left _ hq).ne']
    unfold dyadicRamanujanDivisor
    push_cast
    rw [he,←sum_filter]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro d hd
    rw [abs_mul,show |(d:ℝ)|=(d:ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q/d)))
  calc
    _ ≤ ∑ h ∈ range N, ∑ d ∈ q.divisors, if d∣h+1 then (d:ℝ) else 0 := sum_le_sum fun h _ => hpoint h
    _ = ∑ d ∈ q.divisors, ∑ h ∈ range N, if d∣h+1 then (d:ℝ) else 0 := sum_comm
    _ ≤ ∑ _d ∈ q.divisors, (N:ℝ) := by
      apply sum_le_sum
      intro d _
      rw [←sum_filter,Finset.sum_const,Nat.card_multiples,nsmul_eq_mul]
      exact_mod_cast Nat.div_mul_le_self N d
    _ = _ := by simp [nsmul_eq_mul,mul_comm]


theorem ramanujan_frequency_mass_zero (q N : ℕ) (hq : 0<q) :
    ∑ h ∈ range (N+1), |(dyadicRamanujanDivisor h q:ℝ)| ≤ (N:ℝ)*q.divisors.card+q := by
  let _ : NeZero q := ⟨hq.ne'⟩
  have hz := unit_exp_ramanujan_eq_divisor 0 q
  simp [E,ZMod.card_units_eq_totient] at hz
  have h₀ : dyadicRamanujanDivisor 0 q = (q.totient:ℤ) := by exact_mod_cast hz.symm
  rw [sum_range_succ',h₀,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) q.totient)]
  exact add_le_add (ramanujan_frequency_mass q N hq) (by exact_mod_cast Nat.totient_le q)

private theorem signedFiber_harmonic (R : ℕ) :
    (∑ j ∈ range R, ((j+1:ℕ):ℝ)⁻¹) ≤ 1+Real.log R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    by_cases h : R=0
    · subst R; norm_num
    · have hR : (0:ℝ)<R := by exact_mod_cast Nat.pos_of_ne_zero h
      have hp : 0<(R:ℝ)+1 := by linarith
      have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hR)
      rw [Real.log_div hp.ne' hR.ne',inv_div] at hl
      have he : 1-(R:ℝ)/(R+1) = ((R:ℝ)+1)⁻¹ := by field_simp; ring
      rw [he] at hl
      push_cast at ih ⊢
      linarith only [ih,hl]

theorem signedFiber_divisor_harmonic (Q : ℕ) :
    (∑ j ∈ range Q, ((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ)) ≤ (1+Real.log Q)^2 := by
  let s := (range Q).sigma (fun j => (j+1).divisors)
  let g (p:ℕ×ℕ) := ((p.1+1:ℕ):ℝ)⁻¹*((p.2+1:ℕ):ℝ)⁻¹
  let F (x : Sigma (fun _ : ℕ => ℕ)) := (x.2-1,(x.1+1)/x.2-1)
  have hh (x : Sigma (fun _ : ℕ => ℕ)) (hx : x∈s) :
      0<x.2 ∧ 0<(x.1+1)/x.2 ∧ x.2*((x.1+1)/x.2)=x.1+1 ∧ x.1<Q := by
    obtain ⟨hj,hd⟩ := mem_sigma.mp hx
    have hdiv := Nat.dvd_of_mem_divisors hd
    exact ⟨Nat.pos_of_mem_divisors hd,Nat.div_pos (Nat.le_of_dvd (by omega) hdiv) (Nat.pos_of_mem_divisors hd),
      Nat.mul_div_cancel' hdiv,mem_range.mp hj⟩
  have hi : Set.InjOn F ↑s := by
    rintro ⟨i,d⟩ hx ⟨j,e⟩ hy he
    obtain ⟨hd,hdi,hm,_⟩ := hh _ hx
    obtain ⟨he',hje,hm',_⟩ := hh _ hy
    have hp := congrArg Prod.fst he
    have hq := congrArg Prod.snd he
    dsimp [F] at hp hq hd hdi hm he' hje hm'
    have hed : d=e := by omega
    have huv : (i+1)/d=(j+1)/e := by omega
    subst e
    rw [huv] at hm
    congr 1
    omega
  calc
    _ = ∑ x ∈ s, ((x.1+1:ℕ):ℝ)⁻¹ := by
      dsimp [s]
      rw [←sum_sigma' (range Q) (fun j => (j+1).divisors) (fun j _ => ((j+1:ℕ):ℝ)⁻¹)]
      simp [nsmul_eq_mul,div_eq_mul_inv]
    _ ≤ ∑ p ∈ (range Q) ×ˢ (range Q), g p := by
      apply sum_le_sum_of_injOn F hi
      · intro p hp
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
        obtain ⟨h1,h2,hm,hj⟩ := hh _ hx
        have hu : x.2 ≤ x.1+1 := (Nat.le_mul_of_pos_right _ h2).trans hm.le
        have hv : (x.1+1)/x.2 ≤ x.1+1 := Nat.div_le_self ..
        exact mem_product.mpr ⟨mem_range.mpr (by dsimp [F]; omega),mem_range.mpr (by dsimp [F]; omega)⟩
      · intro x hx
        obtain ⟨h1,h2,hm,hj⟩ := hh _ hx
        dsimp [g,F]
        rw [Nat.sub_add_cancel (by omega : 1≤x.2),Nat.sub_add_cancel (by omega : 1≤(x.1+1)/x.2),
          ←mul_inv,←Nat.cast_mul,hm]
      · intro p _ _
        dsimp [g]
        positivity
    _ = (∑ j ∈ range Q, ((j+1:ℕ):ℝ)⁻¹)^2 := by
      rw [sum_product,sq,Finset.sum_mul]
      exact sum_congr rfl fun j _ => by dsimp only [g]; rw [Finset.mul_sum]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) (signedFiber_harmonic Q) 2

private theorem signedFiber_abs_sum (s : Finset ℕ) (m : ℕ → ℤ) (N:ℕ) (f : ℕ → ℝ)
    (hm : Set.InjOn m ↑s) (hb : ∀ k∈s, (m k).natAbs ≤ N) (hf : ∀ h, 0≤f h) :
    ∑ k ∈ s, f (m k).natAbs ≤ 2*∑ h ∈ range (N+1), f h := by
  classical
  let P (k : ℕ) := 0 ≤ m k
  have hinj (a b:ℕ) (h : (m a).natAbs=(m b).natAbs) : m a=m b ∨ m a= -m b := Int.natAbs_eq_natAbs_iff.mp h
  have half (s' : Finset ℕ) (hs : s'⊆s)
      (hin : Set.InjOn (fun k => (m k).natAbs) ↑s') :
      ∑ k ∈ s', f (m k).natAbs ≤ ∑ h ∈ range (N+1), f h := by
    apply sum_le_sum_of_injOn (fun k => (m k).natAbs) hin
    · intro y hy
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hy
      exact mem_range.mpr (Nat.lt_succ_of_le (hb k (hs hk)))
    · exact fun _ _ => le_rfl
    · exact fun a _ _ => hf a
  have hp := half (s.filter P) (filter_subset ..) (by
    intro a ha b hb' he
    obtain ⟨has,hap⟩ := mem_filter.mp ha
    obtain ⟨hbs,hbp⟩ := mem_filter.mp hb'
    apply hm has hbs
    dsimp only [P] at hap hbp
    rcases hinj a b he with h|h <;> omega)
  have hn := half (s.filter fun k => ¬P k) (filter_subset ..) (by
    intro a ha b hb' he
    obtain ⟨has,hap⟩ := mem_filter.mp ha
    obtain ⟨hbs,hbp⟩ := mem_filter.mp hb'
    apply hm has hbs
    dsimp only [P] at hap hbp
    rcases hinj a b he with h|h <;> omega)
  rw [←sum_filter_add_sum_filter_not s P]
  linarith

private theorem signedModeRow_norm (q : ℕ) [NeZero q] (m:ℤ) {ρ:ℝ} (hρ : 0≤ρ) :
    ‖∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, E ((m:ℝ)*(t+((a:ZMod q).val:ℝ)/q))‖ ≤
      2*ρ*|(dyadicRamanujanDivisor m.natAbs q:ℝ)| := by
  rw [signedModeRow_exact,norm_mul,Complex.norm_intCast]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -ρ) (b := ρ) (f:=fun t:ℝ => E ((m:ℝ)*t)) (C:=1)
    (fun _ _ => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [abs_of_nonneg (by linarith : 0≤ρ- -ρ),one_mul] at hi
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [←Int.cast_abs]; ring

noncomputable def signedFiberRow (q : ℕ) [NeZero q] (s : Finset ℕ) (m : ℕ → ℤ) (w : ℕ → ℝ) (ρ:ℝ) : ℂ :=
  ∑ k ∈ s, (w k:ℂ)*∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, E (((m k):ℝ)*(t+((a:ZMod q).val:ℝ)/q))

theorem signedFiberRow_bound (q N : ℕ) [NeZero q] (s : Finset ℕ) (m : ℕ → ℤ) (w : ℕ → ℝ)
    {ρ A : ℝ} (hρ : 0≤ρ) (hA : 0≤A) (hm : Set.InjOn m ↑s) (hb : ∀ k∈s, (m k).natAbs ≤ N)
    (hw : ∀ k∈s, |w k|≤A) :
    ‖signedFiberRow q s m w ρ‖ ≤ 4*ρ*A*((N:ℝ)*q.divisors.card+q) := by
  let f (h : ℕ) := |(dyadicRamanujanDivisor h q:ℝ)|
  have hf := (signedFiber_abs_sum s m N f hm hb (fun _ => abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (ramanujan_frequency_mass_zero q N (NeZero.pos q)) (by norm_num))
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ k ∈ s, (2*ρ*A)*f (m k).natAbs := by
      apply sum_le_sum
      intro k hk
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul (hw k hk) (signedModeRow_norm q (m k) hρ) (norm_nonneg _) hA).trans_eq (by dsimp only [f]; ring)
    _ = (2*ρ*A)*(∑ k ∈ s, f (m k).natAbs) := (mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left hf (by positivity : 0≤2*ρ*A)).trans_eq (by ring)

/-- Every denominator in (R,Q] uses its full Dirichlet radius 1/(q Q). -/
theorem natural_signedFiber_bound (N R Q : ℕ) (hQ:0<Q) (s:Finset ℕ) (m:ℕ→ℤ) (w:ℕ→ℝ)
    {A:ℝ} (hA : 0≤A) (hm : Set.InjOn m ↑s) (hb : ∀ k∈s, (m k).natAbs≤N) (hw : ∀ k∈s, |w k|≤A) :
    ‖∑ j ∈ Ico R Q, signedFiberRow (j+1) s m w (1/(((j+1:ℕ):ℝ)*Q))‖ ≤
      4*A/(Q:ℝ)*((N:ℝ)*(1+Real.log Q)^2+Q) := by
  let J := Ico R Q
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hh : ∑ j ∈ J, ((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ) ≤ (1+Real.log Q)^2 :=
    (sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (mem_Ico.mp hj).2)
        (fun _ _ _ => by positivity)).trans (signedFiber_divisor_harmonic Q)
  calc
    _ ≤ ∑ j ∈ J, (4*A/(Q:ℝ))*((N:ℝ)*(((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ))+1) := by
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro j _
      exact (signedFiberRow_bound (j+1) N s m w (by positivity) hA hm hb hw).trans_eq (by
        have hq : (0:ℝ)<(j+1:ℕ) := by positivity
        field_simp)
    _ = (4*A/(Q:ℝ))*((N:ℝ)*(∑ j ∈ J, ((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ)) + (J.card:ℝ)) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum]
      simp
    _ ≤ _ := by
      have hcard : (J.card:ℝ)≤Q := by dsimp only [J]; rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le Q R
      gcongr

noncomputable def primeGapFrequencyIntegral (n d R Q : ℕ) : ℂ :=
  let s := (range (n+1)).filter (fun p => p+d≤n)
  ∑ j ∈ Ico R Q, signedFiberRow (j+1) s (fun p => 2*(p:ℤ)+d-n)
    (fun p => weight p*weight (p+d)) (1/(((j+1:ℕ):ℝ)*Q))

/-- The true logarithmic weight at a single prescribed gap, including the diagonal d=0. -/
theorem primeGapFrequencyIntegral_bound (n d R Q:ℕ) (hQ:0<Q) :
    ‖primeGapFrequencyIntegral n d R Q‖ ≤
      4*(Real.log (n:ℝ))^2/(Q:ℝ)*((n:ℝ)*(1+Real.log Q)^2+Q) := by
  let s := (range (n+1)).filter (fun p => p+d≤n)
  have weight_nonneg (p:ℕ) : 0≤weight p := by unfold weight; split_ifs <;> first | exact Real.log_natCast_nonneg p | exact le_rfl
  have hlog (p:ℕ) (hp:p≤n) : weight p≤Real.log (n:ℝ) := by
    unfold weight
    split_ifs with h
    · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hp)
    · exact Real.log_natCast_nonneg n
  apply natural_signedFiber_bound n R Q hQ s _ _ (sq_nonneg _)
  · intro p hp r hr he
    dsimp only at he
    omega
  · intro p hp
    obtain ⟨hpn,hpd⟩ := mem_filter.mp hp
    have hp' := mem_range.mp hpn
    omega
  · intro p hp
    obtain ⟨hpn,hpd⟩ := mem_filter.mp hp
    rw [abs_of_nonneg (mul_nonneg (weight_nonneg _) (weight_nonneg _)),sq]
    exact mul_le_mul (hlog _ (by have := mem_range.mp hpn; omega)) (hlog _ hpd) (weight_nonneg _) (Real.log_natCast_nonneg _)
/-- Expansion of the two prime waves with the original signed phase, on all reduced centers. -/
theorem primeGapFrequencyIntegral_eq_shifted (n d R Q:ℕ) :
    primeGapFrequencyIntegral n d R Q =
      ∑ j ∈ Ico R Q, ∑ a : (ZMod (j+1))ˣ,
        ∫ t in -(1/(((j+1:ℕ):ℝ)*Q))..(1/(((j+1:ℕ):ℝ)*Q)),
          let u := t+((a:ZMod (j+1)).val:ℝ)/(j+1:ℕ)
          ∑ p ∈ (range (n+1)).filter (fun p => p+d≤n),
            (((weight p:ℂ)*E ((p:ℝ)*u))*((weight (p+d):ℂ)*E (((p+d:ℕ):ℝ)*u)))*E (-(n:ℝ)*u) := by
  let s := (range (n+1)).filter (fun p => p+d≤n)
  let w (p:ℕ) := weight p*weight (p+d)
  let m (p:ℕ) := 2*(p:ℤ)+d-n
  have hp (p:ℕ) (u:ℝ) : (((weight p:ℂ)*E ((p:ℝ)*u))*((weight (p+d):ℂ)*E (((p+d:ℕ):ℝ)*u)))*E (-(n:ℝ)*u) =
      (w p:ℂ)*E (((m p):ℝ)*u) := by
    dsimp only [w,m]
    push_cast
    rw [show (2*(p:ℝ)+d-n)*u = ((p:ℝ)*u+(p+d)*u)+ -(n:ℝ)*u by ring,phase_add,phase_add]
    ring
  unfold primeGapFrequencyIntegral
  apply Finset.sum_congr rfl
  intro j _
  let r := 1/(((j+1:ℕ):ℝ)*Q)
  let u (a : (ZMod (j+1))ˣ) (t:ℝ) := t+((a:ZMod (j+1)).val:ℝ)/(j+1:ℕ)
  change signedFiberRow (j+1) s m w r = _
  simp_rw [hp]
  unfold signedFiberRow
  symm
  calc
    _ = ∑ a : (ZMod (j+1))ˣ, ∑ p ∈ s, ∫ t in -r..r, (w p:ℂ)*E (((m p):ℝ)*u a t) := by
      apply Finset.sum_congr rfl
      intro a _
      apply intervalIntegral.integral_finsetSum
      intro p _
      apply Continuous.intervalIntegrable
      dsimp only [u,E]
      fun_prop
    _ = _ := by rw [Finset.sum_comm]; simp_rw [intervalIntegral.integral_const_mul,Finset.mul_sum]; rfl


/-- Uniform in the selected lower denominator and in the set of gaps. -/
theorem primeGapFrequencyIntegral_band (n R Q : ℕ) (H : Finset ℕ) (hQ : 0<Q) :
    ‖∑ d ∈ H, primeGapFrequencyIntegral n d R Q‖ ≤
      (H.card:ℝ)*(4*(Real.log (n:ℝ))^2/(Q:ℝ)*((n:ℝ)*(1+Real.log Q)^2+Q)) := by
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _d ∈ H, (4*(Real.log (n:ℝ))^2/(Q:ℝ)*((n:ℝ)*(1+Real.log Q)^2+Q)) :=
      sum_le_sum fun d _ => primeGapFrequencyIntegral_bound n d R Q hQ
    _ = _ := by simp [nsmul_eq_mul]
end GoldbachPartial