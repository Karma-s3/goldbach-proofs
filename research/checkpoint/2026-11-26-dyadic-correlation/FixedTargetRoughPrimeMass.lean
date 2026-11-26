import VerifiedUniformResidueCorrelation
import VerifiedPolylogPrimeClass
import Mathlib.NumberTheory.Primorial

namespace GoldbachPartial
open Finset Filter
open scoped Topology

def fixedTargetRoughPrimes (n q : ℕ) : Finset ℕ :=
  (Ioc (n/4) (n/2)).filter (fun p => Nat.Prime p ∧ (n-p).Coprime q)

private theorem fixedTarget_row_interval {u v : ℕ} (huv : u≤v) (q a : ℕ) :
    (∑ k ∈ Ioc u v, if k%q=a then weight k else 0) =
      GoldbachMajorArc.classMass (v+1) q a - GoldbachMajorArc.classMass (u+1) q a := by
  have hset : Ioc u v = Ico (u+1) (v+1) := by ext k; simp only [mem_Ioc,mem_Ico]; omega
  rw [hset,sum_Ico_eq_sub _ (by omega)]
  unfold GoldbachMajorArc.classMass
  simp only [sum_filter]
  rfl

private theorem fixedTarget_dyadic_mass (e : ℕ) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ q a : ℕ, 0<q → (q:ℝ)≤(Real.log X)^e → a<q → a.Coprime q →
      (3/4:ℝ)*X/q.totient ≤ ∑ k ∈ Ioc X (2*X), if k%q=a then weight k else 0 := by
  obtain ⟨C,hC,hp⟩ := polylog_window_uniform_prime_class e he
  obtain ⟨U,hU⟩ := eventually_atTop.mp hp
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop (max 1 (12*C)),eventually_ge_atTop (max 1 U)] with X hlog hX
  intro q a hq hqL ha hc
  let L := Real.log X
  have h1 : 1≤L := (le_max_left ..).trans hlog
  have hL := zero_lt_one.trans_le h1
  have hX' : (0:ℝ)<X := by exact_mod_cast (le_max_left _ _).trans hX
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hf : (q.totient:ℝ)≤L^e := (by exact_mod_cast Nat.totient_le q : (q.totient:ℝ)≤q).trans hqL
  have hLo := hU X ((le_max_right _ _).trans hX) q a hq hqL ha hc
  have hlim : L≤Real.log (2*X:ℕ) := Real.log_le_log hX' (by exact_mod_cast (show X≤2*X by omega))
  have hHi := hU (2*X) (by omega : U≤2*X) q a hq (hqL.trans (pow_le_pow_left₀ hL.le hlim _)) ha hc
  let D := C*X/L^(2*e+1)
  have hHi' : |GoldbachMajorArc.classMass (2*X+1) q a - ((2*X:ℕ):ℝ)/q.totient| ≤ 2*D := by
    apply hHi.trans
    calc
      _ ≤ C*((2*X:ℕ):ℝ)/L^(2*e+1) := div_le_div_of_nonneg_left (by positivity) (pow_pos hL _) (pow_le_pow_left₀ hL.le hlim _)
      _ = _ := by dsimp only [D]; push_cast; ring
  change |_ - (X:ℝ)/q.totient|≤D at hLo
  have hD : 12*D*q.totient ≤ (X:ℝ) := by
    calc
      _ ≤ 12*D*L^e := mul_le_mul_of_nonneg_left hf (by dsimp [D]; positivity)
      _ = (X:ℝ)*((12*C)/L^(e+1)) := by dsimp only [D]; rw [show 2*e+1=e+(e+1) by omega,pow_add]; field_simp
      _ ≤ _ := mul_le_of_le_one_right hX'.le ((div_le_one (pow_pos hL _)).mpr
        (((le_max_right 1 (12*C)).trans hlog).trans ((by simpa using (pow_le_pow_right₀ h1 (by omega : 1≤e+1))) : L≤L^(e+1))))
  rw [fixedTarget_row_interval (by omega)]
  have hD' := (le_div_iff₀ hφ).mpr hD
  have hlo := (abs_le.mp hLo).2
  have hhi := (abs_le.mp hHi').1
  push_cast at hhi
  linear_combination hhi+hlo+hD'/4

private theorem fixedTarget_partner {n q p a : ℕ} (hpn : p≤n) (ha : a<q) (hpa : p%q=a) :
    (n-p)%q=residueWindowPartner q n a := by
  have h : p≡a [MOD q] := Eq.trans hpa (Nat.mod_eq_of_lt ha).symm
  apply h.add_right_cancel
  change (n-p+p)%q=(n+q-a+a)%q
  rw [Nat.sub_add_cancel hpn,Nat.sub_add_cancel (by omega),Nat.add_mod_right]

theorem fixedTarget_roughPrimes_class_mass (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, 0<q → (q:ℝ)≤(Real.log n)^d →
      ((residueWindowAdmissible q n).card:ℝ)*(n:ℝ)/(8*q.totient) ≤
        ∑ p ∈ fixedTargetRoughPrimes n q, Real.log p := by
  let X := fun n : ℕ => n/4
  have hXtop : Tendsto X atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (4*b)] with n hn
    dsimp [X]
    omega
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hXtop.eventually (fixedTarget_dyadic_mass (d+1) (Nat.succ_pos d)),
    hXtop.eventually (ht.eventually_ge_atTop ((2:ℝ)^d)),eventually_ge_atTop (36:ℕ)] with n hclass hlog hn
  intro q hq hqL
  let x := X n
  let A := residueWindowAdmissible q n
  have hx : x=n/4 := rfl
  have hxpos : 0<(x:ℝ) := by exact_mod_cast (show 0<x by omega)
  have hnR : (n:ℝ) ≤ 5*x := by exact_mod_cast (show n≤5*x by omega)
  have hnX : n ≤ x^2 := by nlinarith only [show n≤5*x by omega, show 5≤x by omega]
  have hlogn : Real.log n ≤ 2*Real.log x := by
    have hcmp := Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hnX : (n:ℝ)≤(x:ℝ)^2)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hcmp
  have hq' : (q:ℝ)≤(Real.log x)^(d+1) := by
    calc
      _ ≤ (2*Real.log x)^d := hqL.trans (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hlogn d)
      _ = (2:ℝ)^d*(Real.log x)^d := mul_pow .. 
      _ ≤ _ := by rw [pow_succ,mul_comm ((Real.log x)^d)]; exact mul_le_mul_of_nonneg_right hlog (pow_nonneg (Real.log_natCast_nonneg _) _)
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hrow (a : ℕ) (ha : a∈A) :
      (n:ℝ)/(8*q.totient) ≤ ∑ p ∈ Ioc x (2*x), if p%q=a then weight p else 0 := by
    obtain ⟨har,hac,_⟩ := mem_filter.mp ha
    apply le_trans _ (hclass q a hq hq' (mem_range.mp har) hac)
    field_simp
    linarith
  have hsum := sum_le_sum hrow
  rw [sum_const,nsmul_eq_mul,sum_comm] at hsum
  change (A.card:ℝ)*(n:ℝ)/(8*q.totient) ≤ _
  rw [mul_div_assoc]
  apply hsum.trans
  calc
    _ ≤ ∑ p ∈ Ioc x (2*x), if p.Prime ∧ (n-p).Coprime q then Real.log p else 0 := by
      apply sum_le_sum
      intro p hp
      rw [sum_ite_eq]
      by_cases hm : p%q∈A
      · have hc := (mem_filter.mp hm).2.2
        have hpar := fixedTarget_partner (show p≤n by have := (mem_Ioc.mp hp).2;omega) (Nat.mod_lt p hq) rfl
        have he : (n-p).Coprime q := by
          have hh : residueWindowPartner q n (p%q) ≡ n-p [MOD q] := by
            change residueWindowPartner q n (p%q)%q=(n-p)%q
            rw [←hpar,Nat.mod_mod]
          exact hh.gcd_eq.symm.trans hc
        rw [ite_eq_left hm]
        by_cases hpp : p.Prime
        · rw [ite_eq_left ⟨hpp,he⟩,weight,ite_eq_left hpp]
        · rw [ite_eq_right (fun h => hpp h.1),weight,ite_eq_right hpp]
      · simp [hm]
        split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
    _ ≤ _ := by
      unfold fixedTargetRoughPrimes
      rw [sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hxp,hpx⟩ := mem_Ioc.mp hp
        exact mem_Ioc.mpr ⟨by omega,by omega⟩
      · intro p _ _
        split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl

/-- The exact number of admissible classes gives an absolute lower bound for every even target
and every even modulus in the fixed polylogarithmic range. -/
theorem fixedTarget_roughPrimes_even_mass (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, Even n → ∀ q : ℕ, 0<q → 2∣q → (q:ℝ)≤(Real.log n)^d →
      9*(n:ℝ)*q.totient/(64*q) ≤ ∑ p ∈ fixedTargetRoughPrimes n q, Real.log p := by
  filter_upwards [fixedTarget_roughPrimes_class_mass d] with n hn
  intro he q hq h2 hqL
  apply le_trans _ (hn q hq hqL)
  obtain ⟨t,ht⟩ := he
  have hcount := even_residue_count_floor q t hq h2
  rw [show 2*t=n by omega] at hcount
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hf : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hh := mul_le_mul_of_nonneg_right hcount (show 0≤(n:ℝ)*q.totient/(8*q) by positivity)
  convert hh using 1 <;> field_simp
  ring

/-- A concrete cutoff tending to infinity, whose primorial remains at most log n. -/
noncomputable def fixedTargetSieveLimit (n : ℕ) := Nat.log 4 ⌊Real.log n⌋₊

theorem fixedTargetSieveLimit_tendsto : Tendsto fixedTargetSieveLimit atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_ge_atTop ((4^k:ℕ):ℝ)] with n hn
  exact Nat.le_log_of_pow_le (by decide) (Nat.le_floor hn)

theorem fixedTargetSieveLimit_modulus :
    ∀ᶠ n : ℕ in atTop, 2∣primorial (fixedTargetSieveLimit n) ∧
      (primorial (fixedTargetSieveLimit n):ℝ)≤Real.log n := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [fixedTargetSieveLimit_tendsto.eventually_ge_atTop 2,ht.eventually_ge_atTop 1] with n hy hn
  refine ⟨Nat.prime_two.dvd_primorial_iff.mpr hy,?_⟩
  change (1:ℝ)≤Real.log n at hn
  have hfloor : 1≤⌊Real.log n⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hn)
  have hp := (primorial_le_four_pow (fixedTargetSieveLimit n)).trans (Nat.pow_log_le_self 4 (by omega : ⌊Real.log n⌋₊≠0))
  exact (by exact_mod_cast hp : (primorial (fixedTargetSieveLimit n):ℝ)≤(⌊Real.log n⌋₊:ℝ)).trans
    (Nat.floor_le (Real.log_natCast_nonneg _))

theorem fixedTarget_primorial_factor {n y p : ℕ} (hp : p∈fixedTargetRoughPrimes n (primorial y)) :
    p.Prime ∧ n/4<p ∧ p≤n/2 ∧ ∀ l : ℕ, l.Prime → l∣n-p → y<l := by
  obtain ⟨hi,hp',hc⟩ := mem_filter.mp hp
  refine ⟨hp',(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2,?_⟩
  intro l hl hd
  by_contra! hy
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨l,hl,hd,hl.dvd_primorial_iff.mpr hy⟩) hc

theorem fixedTarget_growing_sieve_mass :
    ∀ᶠ n : ℕ in atTop, Even n → let q := primorial (fixedTargetSieveLimit n)
      9*(n:ℝ)*q.totient/(64*q) ≤ ∑ p ∈ fixedTargetRoughPrimes n q, Real.log p := by
  filter_upwards [fixedTarget_roughPrimes_even_mass 1,fixedTargetSieveLimit_modulus] with n hmass hq
  intro hn
  exact hmass hn _ (primorial_pos _) hq.1 (by simpa only [pow_one] using hq.2)

theorem fixedTarget_growing_sieve_count :
    ∀ᶠ n : ℕ in atTop, Even n → let q := primorial (fixedTargetSieveLimit n)
      9*(n:ℝ)*q.totient/(64*q*Real.log n) ≤ (fixedTargetRoughPrimes n q).card := by
  filter_upwards [fixedTarget_growing_sieve_mass,eventually_ge_atTop (2:ℕ)] with n hmass hn
  intro he q
  have hL : 0<Real.log n := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hsum : (∑ p ∈ fixedTargetRoughPrimes n q, Real.log p) ≤ (fixedTargetRoughPrimes n q).card*Real.log n := by
    calc
      _ ≤ ∑ _p ∈ fixedTargetRoughPrimes n q, Real.log n := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hi,hp',_⟩ := mem_filter.mp hp
        exact Real.log_le_log (by exact_mod_cast hp'.pos) (by exact_mod_cast (show p≤n by have := (mem_Ioc.mp hi).2; omega))
      _ = _ := by simp
  rw [←div_div]
  exact (div_le_iff₀ hL).mpr ((hmass he).trans hsum)

end GoldbachPartial