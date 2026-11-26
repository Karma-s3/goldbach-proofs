import SignedPrimeArcBounds

/-! Ramanujan coefficients and explicit signed model bounds for prime arcs. -/

namespace GoldbachPartial

open scoped BigOperators
open Finset ExtendedArcCoefficient MeasureTheory

section RamanujanDyadicTail

theorem dyadic_divisor_fiber_bound {Y d : ℕ} (hY : 0<Y) (hd : 0<d) (s : Finset ℕ)
    (hs : ∀ q ∈ s, Y<q ∧ q≤2*Y ∧ d∣q) :
    ∑ q ∈ s, (d:ℝ)/(q:ℝ)^2 ≤ 1/(Y:ℝ) := by
  let M := Y/d
  have hy : Y < d*(M+1) := Nat.lt_mul_div_succ Y hd
  have hbase : M*d ≤ Y := Nat.div_mul_le_self Y d
  have hr {q : ℕ} (hq : q∈s) : M < q/d ∧ q/d ≤ 2*M+1 := by
    obtain ⟨h₁,h₂,h₃⟩ := hs q hq
    have hqd := Nat.div_mul_cancel h₃
    constructor
    · by_contra! h
      have hu := Nat.mul_le_mul_right d h
      omega
    · have hlt : q/d < 2*(M+1) := (Nat.div_lt_iff_lt_mul hd).mpr (by nlinarith only [h₂,hy])
      omega
  have hcard : s.card ≤ M+1 := by
    have hj : s.card ≤ (Finset.Ioc M (2*M+1)).card := by
      apply Finset.card_le_card_of_injOn (fun q => q/d)
      · intro q hq
        exact Finset.mem_Ioc.mpr (hr hq)
      · intro a ha b hb heq
        have he := congrArg (fun x => x*d) heq
        simpa only [Nat.div_mul_cancel (hs a ha).2.2, Nat.div_mul_cancel (hs b hb).2.2] using he
    rw [Nat.card_Ioc] at hj
    omega
  have hy' : 0 < (Y:ℝ) := by exact_mod_cast hY
  have hM : 0 < ((M:ℝ)+1) := by positivity
  calc
    _ ≤ ∑ _q ∈ s, 1 / ((Y:ℝ)*((M:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqY := (hs q hq).1.le
      have hqd : d*(M+1) ≤ q := by
        have h := Nat.mul_le_mul_left d (hr hq).1
        exact h.trans_eq (Nat.mul_div_cancel' (hs q hq).2.2)
      have hprod : Y*(d*(M+1)) ≤ q*q := Nat.mul_le_mul hqY hqd
      have hprod' : (Y:ℝ)*((d:ℝ)*((M:ℝ)+1)) ≤ (q:ℝ)*(q:ℝ) := by exact_mod_cast hprod
      have hqp : 0 < (q:ℝ) := by exact_mod_cast (hY.trans_le hqY)
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hprod']
    _ = (s.card:ℝ)*(1/((Y:ℝ)*((M:ℝ)+1))) := by simp
    _ ≤ ((M:ℝ)+1)*(1/((Y:ℝ)*((M:ℝ)+1))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = _ := by field_simp

theorem dyadic_gcd_over_sq (n Y : ℕ) (hn : 0<n) (hY : 0<Y) :
    ∑ q ∈ Finset.Ioc Y (2*Y), (q.gcd n:ℝ)/(q:ℝ)^2 ≤ (n.divisors.card:ℝ)/Y := by
  let s := Finset.Ioc Y (2*Y)
  have hmap (q : ℕ) (_h : q∈s) : q.gcd n ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q n,hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun q => (q.gcd n:ℝ)/(q:ℝ)^2)]
  calc
    _ ≤ ∑ _d ∈ n.divisors, 1/(Y:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      let t := s.filter (fun q => q.gcd n=d)
      have he (q : ℕ) (hq : q∈t) := (Finset.mem_filter.mp hq).2
      change ∑ q ∈ t, (q.gcd n:ℝ)/(q:ℝ)^2 ≤ _
      calc
        _ = ∑ q ∈ t, (d:ℝ)/(q:ℝ)^2 :=
          Finset.sum_congr rfl (fun q hq => by rw [he q hq])
        _ ≤ _ := dyadic_divisor_fiber_bound hY (Nat.pos_of_mem_divisors hd) t (by
          intro q hq
          obtain ⟨hu,hv⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
          exact ⟨hu,hv,he q hq ▸ Nat.gcd_dvd_left q n⟩)
    _ = _ := by simp [div_eq_mul_inv]

theorem squarefree_totient_gcd_factor {n q : ℕ} (hs : Squarefree q) :
    q.totient = (q.gcd n).totient * (q/(q.gcd n)).totient := by
  have hmul := Nat.mul_div_cancel' (Nat.gcd_dvd_left q n)
  have hc := Nat.coprime_of_squarefree_mul (hmul.symm ▸ hs : Squarefree (q.gcd n*(q/(q.gcd n))))
  exact (congrArg Nat.totient hmul).symm.trans (Nat.totient_mul hc)


open ArithmeticFunction
noncomputable def dyadicRamanujanDivisor (n q : ℕ) : ℤ :=
  ∑ d ∈ (q.gcd n).divisors, ArithmeticFunction.moebius (q/d) * (d:ℤ)

private lemma dyadic_totient_inversion {g : ℕ} (hg : 0<g) :
    ∑ d ∈ g.divisors, ArithmeticFunction.moebius (g/d) * (d:ℤ) = (g.totient:ℤ) := by
  have hs (k : ℕ) (_hk : 0<k) : ∑ d ∈ k.divisors, (d.totient:ℤ) = (k:ℤ) := by
    exact_mod_cast Nat.sum_totient k
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hs g hg
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal' (fun i j => ArithmeticFunction.moebius i*(j:ℤ))] at h
  exact h

theorem dyadicRamanujanDivisor_squarefree {n q : ℕ} (hs : Squarefree q) :
    dyadicRamanujanDivisor n q =
      ArithmeticFunction.moebius (q/(q.gcd n)) * ((q.gcd n).totient:ℤ) := by
  let g := q.gcd n
  have hdq : g∣q := Nat.gcd_dvd_left q n
  have hm : (q/g)*g = q := Nat.div_mul_cancel hdq
  have hcop := Nat.coprime_of_squarefree_mul (hm.symm ▸ hs : Squarefree ((q/g)*g))
  have hg : 0<g := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hs.ne_zero)
  unfold dyadicRamanujanDivisor
  change ∑ d ∈ g.divisors, _ = ArithmeticFunction.moebius (q/g) * (g.totient:ℤ)
  rw [← dyadic_totient_inversion hg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hgd := Nat.dvd_of_mem_divisors hd
  have hsplit : q/d = (q/g)*(g/d) := (congrArg (fun x => x/d) hm.symm).trans (Nat.mul_div_assoc _ hgd)
  rw [hsplit, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (hcop.coprime_dvd_right (Nat.div_dvd_of_dvd hgd)), mul_assoc]

theorem abs_dyadicRamanujanDivisor_squarefree {n q : ℕ} (hs : Squarefree q) :
    |dyadicRamanujanDivisor n q| = ((q.gcd n).totient:ℤ) := by
  rw [dyadicRamanujanDivisor_squarefree hs,abs_mul,
    ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (hs.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q n))),one_mul]
  exact abs_of_nonneg (Int.natCast_nonneg _)

theorem dyadic_ramanujan_tail_of_totient_ratio {n Y : ℕ} (hn : 0<n) (hY : 0<Y)
    {K : ℝ}
    (hratio : ∀ q ∈ Finset.Ioc Y (2*Y), Squarefree q → (q:ℝ) ≤ K*(q.totient:ℝ)) :
    ∑ q ∈ (Finset.Ioc Y (2*Y)).filter Squarefree,
        (|dyadicRamanujanDivisor n q|:ℝ)/(q.totient:ℝ)^2 ≤
      K^2*(n.divisors.card:ℝ)/Y := by
  classical
  let s := Finset.Ioc Y (2*Y)
  have hd := dyadic_gcd_over_sq n Y hn hY
  calc
    _ ≤ ∑ q ∈ s.filter Squarefree, K^2*((q.gcd n:ℝ)/(q:ℝ)^2) := by
      refine Finset.sum_le_sum (fun q hq => ?_)
      obtain ⟨hu,hf⟩ := Finset.mem_filter.mp hq
      have hc : |dyadicRamanujanDivisor n q| ≤ (q.gcd n:ℤ) := by
        rw [abs_dyadicRamanujanDivisor_squarefree hf]
        exact_mod_cast Nat.totient_le (q.gcd n)
      have hcr : |(dyadicRamanujanDivisor n q:ℝ)| ≤ (q.gcd n:ℝ) := by exact_mod_cast hc
      have hp : 0<(q.totient:ℝ) := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hf.ne_zero))
      have hqp : 0<(q:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hf.ne_zero)
      have hsq := pow_le_pow_left₀ hqp.le (hratio q hu hf) 2
      calc
        _ ≤ (q.gcd n:ℝ)/(q.totient:ℝ)^2 := by gcongr
        _ ≤ _ := by
          rw [← mul_div_assoc]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) (q.gcd n))]
    _ ≤ ∑ q ∈ s, K^2*((q.gcd n:ℝ)/(q:ℝ)^2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intros; positivity
    _ ≤ _ := by rw [← Finset.mul_sum,mul_div_assoc]; exact mul_le_mul_of_nonneg_left hd (sq_nonneg _)

private theorem dyadic_prime_product_ratio (s : Finset ℕ) (hs : ∀ p ∈ s, 2≤p) :
    (∏ p ∈ s, p) ≤ (s.card+1)*(∏ p ∈ s, (p-1)) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert p s hmax ih =>
    have hn : p∉s := fun h => (hmax p h).false
    have hp : 2≤p := hs p (Finset.mem_insert_self _ _)
    have h₁ : ∀ a ∈ s, 2≤a := fun a ha => hs a (Finset.mem_insert_of_mem ha)
    have hset : s ⊆ Finset.Ico 2 p := fun a ha => Finset.mem_Ico.mpr ⟨h₁ a ha,hmax a ha⟩
    have hcard := Finset.card_le_card hset
    rw [Nat.card_Ico] at hcard
    have hpred : p-1+1 = p := by omega
    have hx : p*(s.card+1) ≤ (s.card+1+1)*(p-1) := by
      have hh : s.card+2 ≤ p := by omega
      nlinarith only [hh,congrArg (fun x => (s.card+1)*x) hpred,hpred]
    rw [Finset.prod_insert hn,Finset.prod_insert hn,Finset.card_insert_of_notMem hn]
    calc
      _ ≤ p*((s.card+1)*∏ x ∈ s, (x-1)) := Nat.mul_le_mul_left _ (ih h₁)
      _ = (p*(s.card+1))*(∏ x ∈ s, (x-1)) := by ring
      _ ≤ ((s.card+1+1)*(p-1))*(∏ x ∈ s, (x-1)) := Nat.mul_le_mul_right _ hx
      _ = _ := by ring

theorem nat_le_totient_mul_log2_succ {q : ℕ} (hq : 0<q) :
    q ≤ (Nat.log 2 q + 1)*q.totient := by
  let s := q.primeFactors
  have hs (p : ℕ) (hp : p∈s) : 2≤p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hprod := dyadic_prime_product_ratio s hs
  have hz : 0 < ∏ p ∈ s, (p-1) := Finset.prod_pos (fun p hp => by have := hs p hp; omega)
  have hf : q*(∏ p ∈ s, (p-1)) = q.totient * ∏ p ∈ s, p := (Nat.totient_mul_prod_primeFactors q).symm
  have hq' : q ≤ (s.card+1)*q.totient := by
    apply Nat.le_of_mul_le_mul_right (c := ∏ p ∈ s, (p-1)) _ hz
    rw [hf]
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left q.totient hprod
  have hs₂ : 2^s.card ≤ ∏ p ∈ s, p := by
    calc
      _ = ∏ _p ∈ s, (2:ℕ) := by simp
      _ ≤ _ := Finset.prod_le_prod hs
  have hdiv := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hlog : s.card ≤ Nat.log 2 q := Nat.le_log_of_pow_le (by decide) (hs₂.trans hdiv)
  exact hq'.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hlog 1))

theorem dyadic_ramanujan_tail_explicit (n Y : ℕ) (hn : 0<n) (hY : 0<Y) :
    ∑ q ∈ (Finset.Ioc Y (2*Y)).filter Squarefree,
        (|dyadicRamanujanDivisor n q|:ℝ)/(q.totient:ℝ)^2 ≤
      (((Nat.log 2 (2*Y):ℕ):ℝ)+1)^2*(n.divisors.card:ℝ)/Y := by
  apply dyadic_ramanujan_tail_of_totient_ratio hn hY
  intro q hq hsf
  have hu := (Finset.mem_Ioc.mp hq).2
  have hlog := Nat.log_mono_right (b := 2) hu
  exact_mod_cast (nat_le_totient_mul_log2_succ (Nat.pos_of_ne_zero hsf.ne_zero)).trans
    (Nat.mul_le_mul_right q.totient (Nat.add_le_add_right hlog 1))

end RamanujanDyadicTail

section ActualRamanujan
open ExtendedArcCoefficient ArithmeticFunction
private noncomputable def ramPhase (n q a : ℕ) : ℂ := E ((n:ℝ)*(a:ℝ)/q)

private theorem actual_ram_geom (n q : ℕ) (hq : 0<q) :
    ∑ a ∈ Finset.range q, ramPhase n q a = if q∣n then (q:ℂ) else 0 := by
  let z := Complex.exp (2*Real.pi*Complex.I*(n:ℂ)/q)
  have he (a : ℕ) : ramPhase n q a = z^a := by
    unfold ramPhase E z
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [he]
  have hz : z=1 ↔ q∣n := Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne'
  by_cases hd : q∣n
  · simp [hz.mpr hd,hd]
  · simp only [hd,↓reduceIte]
    have hqn : (q:ℂ)≠0 := by exact_mod_cast hq.ne'
    have hpow : z^q = 1 := by
      unfold z
      rw [← Complex.exp_nat_mul]
      convert Complex.exp_nat_mul_two_pi_mul_I n using 2
      field_simp
    have hh := geom_sum_mul z q
    rw [hpow,sub_self] at hh
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr (fun h => hd (hz.mp h)))

private theorem actual_ram_geom_multiples {n q d : ℕ} (hq : 0<q) (hd : d∣q) :
    ∑ a ∈ (Finset.range q).filter (fun a => d∣a), ramPhase n q a =
      if q/d∣n then ((q/d:ℕ):ℂ) else 0 := by
  have hd0 := Nat.pos_of_dvd_of_pos hd hq
  have hm := Nat.mul_div_cancel' hd
  have hqp := Nat.div_pos (Nat.le_of_dvd hq hd) hd0
  rw [← actual_ram_geom n _ hqp]
  symm
  apply Finset.sum_nbij (fun k : ℕ => d*k)
  · intro k hk
    have hl := Finset.mem_range.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hm ▸ Nat.mul_lt_mul_of_pos_left hl hd0),dvd_mul_right ..⟩
  · intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_left hd0 he
  · intro a ha
    obtain ⟨ha,hda⟩ := Finset.mem_filter.mp ha
    obtain ⟨k,rfl⟩ := hda
    exact ⟨k,Finset.mem_range.mpr ((Nat.mul_lt_mul_left hd0).mp (hm.symm ▸ Finset.mem_range.mp ha)),rfl⟩
  · intro k _
    unfold ramPhase
    congr 1
    have hdc : (d:ℝ)≠0 := by exact_mod_cast hd0.ne'
    have hqc : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
    have hcc : ((q/d:ℕ):ℝ)≠0 := by exact_mod_cast hqp.ne'
    have hreal : (d:ℝ)*((q/d:ℕ):ℝ) = (q:ℝ) := by exact_mod_cast hm
    push_cast
    field_simp
    linear_combination -(n:ℝ)*(k:ℝ)*hreal

private lemma ram_coprime_indicator (q a : ℕ) (hq : 0<q) :
    (if a.Coprime q then (1:ℂ) else 0) =
      ∑ d ∈ q.divisors, if d∣a then (ArithmeticFunction.moebius d:ℂ) else 0 := by
  have hg : 0 < a.gcd q := Nat.gcd_pos_of_pos_right a hq
  have hset : q.divisors.filter (fun d => d∣a) = (a.gcd q).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors, Nat.dvd_gcd_iff, hq.ne',hg.ne',ne_eq,not_false_eq_true,and_true]
    tauto
  rw [← Finset.sum_filter,hset]
  have h := congrArg (fun f : ArithmeticFunction ℤ => f (a.gcd q)) ArithmeticFunction.moebius_mul_coe_zeta
  change ((ArithmeticFunction.moebius * _) : ArithmeticFunction ℤ) (a.gcd q) = _ at h
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at h
  change (if a.gcd q=1 then (1:ℂ) else 0) = _
  exact_mod_cast h.symm

theorem actualRamanujan_eq_divisor (n q : ℕ) (hq : 0<q) :
    ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), E ((n:ℝ)*(a:ℝ)/q) =
      (dyadicRamanujanDivisor n q:ℂ) := by
  classical
  let M := fun d : ℕ => (ArithmeticFunction.moebius d:ℂ)
  let P := ramPhase n q
  let F := fun d : ℕ => if d∣n then M (q/d)*(d:ℂ) else 0
  have hx (a : ℕ) : (if a.Coprime q then P a else 0) =
      ∑ d ∈ q.divisors, (if d∣a then M d else 0)*P a := by
    rw [← Finset.sum_mul]
    change _ = (∑ d ∈ q.divisors, if d∣a then (ArithmeticFunction.moebius d:ℂ) else 0)*P a
    rw [← ram_coprime_indicator q a hq]
    split_ifs <;> simp
  have hy (d : ℕ) (hd : d∈q.divisors) :
      ∑ a ∈ Finset.range q, (if d∣a then M d else 0)*P a = F (q/d) := by
    have hdd := Nat.dvd_of_mem_divisors hd
    have hcancel : q/(q/d)=d := by
      have hqp := Nat.div_pos (Nat.le_of_dvd hq hdd) (Nat.pos_of_mem_divisors hd)
      apply Nat.eq_of_mul_eq_mul_left hqp
      rw [Nat.mul_div_cancel' (Nat.div_dvd_of_dvd hdd), Nat.div_mul_cancel hdd]
    calc
      _ = M d * ∑ a ∈ (Finset.range q).filter (fun a => d∣a), P a := by
        rw [Finset.sum_filter,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp
      _ = F (q/d) := by
        unfold P F
        rw [actual_ram_geom_multiples hq hdd,hcancel]
        split_ifs <;> simp
  have hset : q.divisors.filter (fun d => d∣n) = (q.gcd n).divisors := by
    ext d
    have hg := Nat.gcd_pos_of_pos_left n hq
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hq.ne',hg.ne']
  change (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), P a) = _
  rw [Finset.sum_filter]
  simp_rw [hx]
  rw [Finset.sum_comm,Finset.sum_congr rfl hy,Nat.sum_div_divisors]
  unfold F
  rw [← Finset.sum_filter,hset]
  unfold dyadicRamanujanDivisor M
  push_cast
  rfl

theorem unit_exp_ramanujan_eq_divisor (n q : ℕ) [NeZero q] :
    ∑ u : (ZMod q)ˣ, E ((n:ℝ)*((u:ZMod q).val:ℝ)/q) = (dyadicRamanujanDivisor n q:ℂ) := by
  rw [← actualRamanujan_eq_divisor n q (Nat.pos_of_ne_zero (NeZero.ne q))]
  apply Finset.sum_nbij (fun u : (ZMod q)ˣ => (u:ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _),ZMod.val_coe_unit_coprime u⟩
  · intro a _ b _ hab
    exact Units.ext (ZMod.val_injective q hab)
  · intro t ht
    obtain ⟨hr,hc⟩ := Finset.mem_filter.mp ht
    refine ⟨ZMod.unitOfCoprime t hc,Finset.mem_univ _,?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)
  · intro _ _
    rfl

theorem principal_unitGauss_eq_moebius (q : ℕ) [NeZero q] :
    unitGaussCoefficient q 1 = (ArithmeticFunction.moebius q:ℂ) := by
  have h := unit_exp_ramanujan_eq_divisor 1 q
  simp only [Nat.cast_one,one_mul,dyadicRamanujanDivisor,Nat.gcd_one_right,
    Nat.divisors_one,Finset.sum_singleton,Nat.div_one,mul_one] at h
  unfold unitGaussCoefficient
  simp only [MulChar.one_apply_coe,mul_one]
  refine Eq.trans (Finset.sum_congr rfl (fun u _ => ?_)) h
  unfold E
  congr 2
  push_cast
  ring

theorem principal_unitGauss_norm_le_one (q : ℕ) [NeZero q] :
    ‖unitGaussCoefficient q 1‖ ≤ 1 := by
  rw [principal_unitGauss_eq_moebius,Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))

private lemma ram_conj_phase (x : ℝ) : E (-x) = starRingEnd ℂ (E x) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  norm_num
  left
  exact (map_ofNat (starRingEnd ℂ) 2).symm

theorem actualRamanujan_neg_eq_divisor (n q : ℕ) (hq : 0<q) :
    ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), E (-((n:ℝ)*(a:ℝ)/q)) =
      (dyadicRamanujanDivisor n q:ℂ) := by
  simp_rw [ram_conj_phase]
  rw [← map_sum, actualRamanujan_eq_divisor n q hq]
  simp

theorem actualRamanujan_of_coprime {n q : ℕ} (hq : 0<q) (hc : n.Coprime q) :
    ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), E ((a:ℝ)*(n:ℝ)/q) =
      (ArithmeticFunction.moebius q:ℂ) := by
  simp_rw [mul_comm (a := (_:ℝ)) (b := (n:ℝ))]
  rw [actualRamanujan_eq_divisor n q hq]
  simp [dyadicRamanujanDivisor,hc.symm.gcd_eq_one]

theorem actualRamanujan_signed_model_row (n q : ℕ) (hq : 1<q) :
    (∑ a ∈ (Finset.range (q+1)).filter (fun a => a.Coprime q),
      ((∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q), E ((r:ℝ)*(a:ℝ)/q)) /
        (q.totient:ℂ))^2 * E (-((n:ℝ)*(a:ℝ)/q))) =
      ((ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ))^2 * (dyadicRamanujanDivisor n q:ℂ) := by
  have hn : ¬q.Coprime q := by simpa [Nat.Coprime] using (show q≠1 by omega)
  have hr : (Finset.range (q+1)).filter (fun a => a.Coprime q) =
      (Finset.range q).filter (fun a => a.Coprime q) := by
    rw [Finset.range_add_one,Finset.filter_insert]
    simp [hn]
  have hp : 0<q := by omega
  rw [hr,← actualRamanujan_neg_eq_divisor n q hp,Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [actualRamanujan_of_coprime hp (Finset.mem_filter.mp ha).2]

noncomputable def actualRamanujanModel (n q : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range (q+1)).filter (fun a => a.Coprime q),
    ((∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q), E ((r:ℝ)*(a:ℝ)/q)) /
      (q.totient:ℂ))^2 * E (-((n:ℝ)*(a:ℝ)/q))

theorem norm_actualRamanujanModel (n q : ℕ) (hq : 1<q) :
    ‖actualRamanujanModel n q‖ =
      if Squarefree q then |(dyadicRamanujanDivisor n q:ℝ)|/(q.totient:ℝ)^2 else 0 := by
  unfold actualRamanujanModel
  rw [actualRamanujan_signed_model_row n q hq]
  by_cases hs : Squarefree q
  · simp only [hs,↓reduceIte,norm_mul,norm_pow,norm_div,Complex.norm_intCast,Complex.norm_natCast]
    rw [show (|(ArithmeticFunction.moebius q : ℤ)|:ℝ) = 1 by exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs]
    ring
  · simp [hs,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

theorem actualRamanujanModel_dyadic_norm_bound (n Y : ℕ) (hn : 0<n) (hY : 0<Y) :
    ∑ q ∈ Finset.Ioc Y (2*Y), ‖actualRamanujanModel n q‖ ≤
       (((Nat.log 2 (2*Y):ℕ):ℝ)+1)^2*(n.divisors.card:ℝ)/Y := by
  have he := dyadic_ramanujan_tail_explicit n Y hn hY
  rw [Finset.sum_filter] at he
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun q hq => ?_))) he
  exact norm_actualRamanujanModel n q (lt_of_le_of_lt hY (Finset.mem_Ioc.mp hq).1)

end ActualRamanujan

section PrimeDenominatorShell

/-- The whole prime-denominator shell has small reciprocal totient mass. -/
theorem prime_shell_reciprocal_totient {Y : ℕ} (hY : 2 ≤ Y) :
    (∑ q ∈ (Ioc Y (2*Y)).filter Nat.Prime, 1/(q.totient:ℝ)) ≤ 2*Real.log 4/Real.log Y := by
  let J := (Ioc Y (2*Y)).filter Nat.Prime
  have hr : 0 < (Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
  have hl : 0 < Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast hY)
  have hw (p : ℕ) : 0 ≤ weight p := by
    unfold weight
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · exact le_rfl
  have hweight (m : ℕ) : (∑ p ∈ range (m+1), weight p) ≤ (m:ℝ)*Real.log 4 := by
    have hlog : (∑ p ∈ range (m+1), weight p) = Real.log (primorial m:ℝ) := by
      rw [primorial,Nat.cast_prod,Real.log_prod]
      · simp [Finset.sum_filter,weight]
      · intro p hp
        exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    rw [hlog]
    have h := Real.log_le_log (show 0 < (primorial m:ℝ) by exact_mod_cast primorial_pos m)
      (show (primorial m:ℝ) ≤ (4:ℝ)^m by exact_mod_cast primorial_le_four_pow m)
    simpa using h
  have hprop {q : ℕ} (hq : q∈J) : (Y<q ∧ q≤2*Y) ∧ q.Prime := by
    simpa [J] using hq
  have hcnt : (J.card:ℝ)*Real.log Y ≤ (2*(Y:ℝ))*Real.log 4 := calc
    _ = ∑ _q ∈ J, Real.log Y := by simp
    _ ≤ ∑ q ∈ J, weight q := by
      refine Finset.sum_le_sum fun q hq => ?_
      have h := hprop hq
      rw [weight,ite_eq_left h.2]
      exact Real.log_le_log hr (by exact_mod_cast h.1.1.le)
    _ ≤ ∑ q ∈ range (2*Y+1), weight q := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => mem_range.mpr ?_) (fun q _ _ => hw q)
      exact Nat.lt_succ_of_le (hprop hq).1.2
    _ ≤ _ := by exact_mod_cast hweight (2*Y)
  calc
    _ ≤ ∑ _q ∈ J, 1/(Y:ℝ) := by
      refine Finset.sum_le_sum fun q hq => one_div_le_one_div_of_le hr ?_
      have h := hprop hq
      rw [Nat.totient_prime h.2]
      exact_mod_cast (show Y≤q-1 by omega)
    _ = (J.card:ℝ)/Y := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply (div_le_div_iff₀ hr hl).mpr
      linarith only [hcnt]

theorem actualRamanujan_weighted_dyadic_bound (n Y : ℕ) (hn : 0<n) (hY : 0<Y)
    (V : ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hV : ∀ q ∈ Ioc Y (2*Y), ‖V q‖ ≤ A) :
    ‖∑ q ∈ Ioc Y (2*Y), actualRamanujanModel n q * V q‖ ≤
       A*((((Nat.log 2 (2*Y):ℕ):ℝ)+1)^2*(n.divisors.card:ℝ)/Y) := by
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ q ∈ Ioc Y (2*Y), A*‖actualRamanujanModel n q‖ := by
      refine Finset.sum_le_sum fun q hq => ?_
      rw [norm_mul,mul_comm A]
      exact mul_le_mul_of_nonneg_left (hV q hq) (norm_nonneg _)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (actualRamanujanModel_dyadic_norm_bound n Y hn hY) hA

end PrimeDenominatorShell

noncomputable def dirichletGeometricKernel (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * t)

private theorem geometricPhase_conj (x : ℝ) :
    (starRingEnd ℂ) (E x) = E (-x) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem geometricPhase_nat (k : ℕ) : E k = 1 := by
  unfold E
  rw [show (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul_two_pi_mul_I k

private theorem geometricKernel_periodic (n : ℕ) :
    Function.Periodic (dirichletGeometricKernel n) 1 := by
  intro t
  unfold dirichletGeometricKernel
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_add, mul_one, phase_add, geometricPhase_nat, mul_one]

private theorem geometricKernel_reflect (n : ℕ) (t : ℝ) :
    dirichletGeometricKernel n t * E (-(n : ℝ) * t) =
      (starRingEnd ℂ) (dirichletGeometricKernel n t) := by
  unfold dirichletGeometricKernel
  rw [Finset.sum_mul, map_sum]
  have hf := Finset.sum_range_reflect
    (fun j : ℕ => (starRingEnd ℂ) (E ((j : ℝ) * t))) (n + 1)
  rw [← hf]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel, geometricPhase_conj, Nat.cast_sub hkn, ← phase_add]
  congr 1
  ring

theorem geometricKernel_unit_energy (n : ℕ) :
    (∫ t in (-(1 / 2) : ℝ)..(1 / 2), ‖dirichletGeometricKernel n t‖ ^ 2) = n + 1 := by
  have hper : Function.Periodic (fun t => ‖dirichletGeometricKernel n t‖ ^ 2) 1 :=
    fun t => congrArg (fun z : ℂ => ‖z‖ ^ 2) (geometricKernel_periodic n t)
  have hshift := hper.intervalIntegral_add_eq (-(1/2) : ℝ) 0
  norm_num at hshift
  rw [hshift]
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hp (t : ℝ) : ((‖dirichletGeometricKernel n t‖ ^ 2 : ℝ) : ℂ) =
      (dirichletGeometricKernel n t)^2 * E (-(n:ℝ)*t) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', sq, mul_assoc, geometricKernel_reflect]
  simp_rw [hp]
  simpa [dirichletGeometricKernel] using coefficient (fun _ => 1) n

theorem geometricKernel_window_energy (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1/2) :
    (∫ t in -ρ..ρ, ‖dirichletGeometricKernel n t‖ ^ 2) ≤ n + 1 := by
  rw [← geometricKernel_unit_energy n]
  apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hhalf
  · exact Filter.Eventually.of_forall fun t => sq_nonneg _
  · apply Continuous.intervalIntegrable
    unfold dirichletGeometricKernel E
    fun_prop

theorem normalized_geometric_window_energy (n q : ℕ) [NeZero q] (z : ℂ) (hz : ‖z‖ ≤ 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1/2) :
    (q.totient : ℝ) * (∫ t in -ρ..ρ, ‖z * dirichletGeometricKernel n t / (q.totient : ℂ)‖^2) ≤
      ((n : ℝ) + 1) / (q.totient : ℝ) := by
  have ht : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hscale (t : ℝ) : ‖z * dirichletGeometricKernel n t / (q.totient : ℂ)‖^2 =
      (‖z‖^2 / (q.totient : ℝ)^2) * ‖dirichletGeometricKernel n t‖^2 := by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    ring
  simp_rw [hscale]
  rw [intervalIntegral.integral_const_mul, le_div_iff₀ ht]
  have he := geometricKernel_window_energy n hρ hhalf
  have he0 : 0 ≤ ∫ t in -ρ..ρ, ‖dirichletGeometricKernel n t‖^2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)
  calc
    _ = ‖z‖^2 * (∫ t in -ρ..ρ, ‖dirichletGeometricKernel n t‖^2) := by field_simp
    _ ≤ 1 * (∫ t in -ρ..ρ, ‖dirichletGeometricKernel n t‖^2) :=
      mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg z, mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz)]) he0
    _ ≤ _ := by simpa using he

theorem geometricPrimeArcModel_window_energy (q : ℕ) [NeZero q] (n : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1/2) (hG : ‖unitGaussCoefficient q 1‖ ≤ 1) :
    (q.totient : ℝ) * (∫ t in -ρ..ρ, ‖geometricPrimeArcModel q n t‖^2) ≤
      ((n : ℝ) + 1) / (q.totient : ℝ) :=
  normalized_geometric_window_energy n q (unitGaussCoefficient q 1) hG hρ hhalf

theorem geometricKernel_sq_phase (n : ℕ) (t : ℝ) :
    (dirichletGeometricKernel n t)^2 * E (-(n:ℝ)*t) = ((‖dirichletGeometricKernel n t‖^2:ℝ):ℂ) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', sq, mul_assoc, geometricKernel_reflect]

theorem geometricPrimeArcModel_signed_row_integral (n q : ℕ) [NeZero q] (hq : 1<q) (ρ : ℝ) :
    (∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, (geometricPrimeArcModel q n t)^2 *
      E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q))) =
    actualRamanujanModel n q *
      ∫ t in -ρ..ρ, (dirichletGeometricKernel n t)^2 * E (-(n:ℝ)*t) := by
  let C := ((ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ))^2
  let U := fun t => (dirichletGeometricKernel n t)^2 * E (-(n:ℝ)*t)
  let h := fun a : (ZMod q)ˣ => E (-((n:ℝ)*((a:ZMod q).val:ℝ)/q))
  have hh : ∑ a : (ZMod q)ˣ, h a = (dyadicRamanujanDivisor n q:ℂ) := by
    unfold h
    simp_rw [← geometricPhase_conj]
    rw [← map_sum,unit_exp_ramanujan_eq_divisor]
    simp
  have hc : (∑ a : (ZMod q)ˣ, C*h a) = actualRamanujanModel n q := by
    rw [← Finset.mul_sum,hh]
    exact (actualRamanujan_signed_model_row n q hq).symm
  have hterm (a : (ZMod q)ˣ) (t : ℝ) :
      (geometricPrimeArcModel q n t)^2*E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q)) =
      (C*h a)*U t := by
    unfold geometricPrimeArcModel U dirichletGeometricKernel C h
    rw [principal_unitGauss_eq_moebius,mul_add,phase_add,
      show -(n:ℝ)*(((a:ZMod q).val:ℝ)/q) = -((n:ℝ)*((a:ZMod q).val:ℝ)/q) by ring]
    ring
  change _ = actualRamanujanModel n q * ∫ t in -ρ..ρ, U t
  simp_rw [hterm,intervalIntegral.integral_const_mul]
  rw [← Finset.sum_mul,hc]

theorem geometricPrimeArcModel_row_integral_norm_sq (n q : ℕ) [NeZero q] (hq : 1<q) (ρ : ℝ) :
    (∑ a : (ZMod q)ˣ, ∫ t in -ρ..ρ, (geometricPrimeArcModel q n t)^2 *
      E (-(n:ℝ)*(t+((a:ZMod q).val:ℝ)/q))) =
    actualRamanujanModel n q *
      ((∫ t in -ρ..ρ, ‖dirichletGeometricKernel n t‖^2 : ℝ):ℂ) := by
  rw [geometricPrimeArcModel_signed_row_integral n q hq]
  simp_rw [geometricKernel_sq_phase,intervalIntegral.integral_ofReal]

theorem geometricModel_dyadic_window_bound {n Y : ℕ} (hn : 0<n) (hY : 0<Y) (ρ : ℕ → ℝ)
    (hw : ∀ q ∈ Ioc Y (2*Y), 0 ≤ ρ q ∧ ρ q ≤ 1/2) :
    ‖∑ q ∈ Ioc Y (2*Y), actualRamanujanModel n q *
      ((∫ t in -(ρ q)..ρ q, ‖dirichletGeometricKernel n t‖^2:ℝ):ℂ)‖ ≤
      ((n:ℝ)+1)*((((Nat.log 2 (2*Y):ℕ):ℝ)+1)^2*(n.divisors.card:ℝ)/Y) := by
  apply actualRamanujan_weighted_dyadic_bound n Y hn hY _ (by positivity)
  intro q hq
  obtain ⟨hr,hh⟩ := hw q hq
  rw [Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg]
  · exact geometricKernel_window_energy n hr hh
  · exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)

end GoldbachPartial
