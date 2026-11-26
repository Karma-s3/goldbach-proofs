import VerifiedPolylogPrimeClass
import LocalPrimeCorrelationWindows

namespace GoldbachPartial
open Finset Filter
open scoped Topology

/-- The divisibility row of the true first-prime weight. The upper endpoint is included. -/
noncomputable def fixedTargetDivisorRow (n d : ℕ) : ℝ :=
  ∑ k ∈ Ioc (n/4) (n/2), if d∣n-k then weight k else 0

theorem fixedTargetDivisorRow_prefix (n d : ℕ) :
    fixedTargetDivisorRow n d =
      GoldbachMajorArc.classMass (n/2+1) d (n%d) -
      GoldbachMajorArc.classMass (n/4+1) d (n%d) := by
  have hle : n/4 ≤ n/2 := by omega
  have hset : Ioc (n/4) (n/2) = Ico (n/4+1) (n/2+1) := by
    ext k; simp only [mem_Ioc,mem_Ico]; omega
  have he : fixedTargetDivisorRow n d =
      ∑ k ∈ Ioc (n/4) (n/2), if k%d=n%d then weight k else 0 := by
    unfold fixedTargetDivisorRow
    apply sum_congr rfl
    intro k hk
    have hkn : k≤n := by have := (mem_Ioc.mp hk).2; omega
    exact if_congr (Nat.modEq_iff_dvd' hkn).symm rfl rfl
  rw [he,hset,sum_Ico_eq_sub _ (by omega)]
  unfold GoldbachMajorArc.classMass
  simp only [sum_filter]
  rfl

/-- Arbitrary independent exponents for the polylogarithmic level and saving. -/
theorem fixedTarget_divisor_row_uniform (a b : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, 0<d →
      (d:ℝ)≤(Real.log n)^a → n.Coprime d →
      |fixedTargetDivisorRow n d - ((n/2-n/4:ℕ):ℝ)/d.totient| ≤ C*n/(Real.log n)^b := by
  let e := a+b+1
  obtain ⟨C,hC,hp⟩ := polylog_window_uniform_prime_class e (by dsimp [e];omega)
  obtain ⟨U,hU⟩ := eventually_atTop.mp hp
  refine ⟨2*C*(2:ℝ)^b,by positivity,?_⟩
  let X := fun n : ℕ => n/4
  have hXt : Tendsto X atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (4*j)] with n hn
    dsimp only [X]
    omega
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hXt.eventually (ht.eventually_ge_atTop ((2:ℝ)^a)),
    hXt.eventually_ge_atTop U,eventually_ge_atTop (36:ℕ)] with n hlog hth hn
  intro d hd hsize hc
  have hscale (u : ℕ) (hu : n/4≤u) (hu' : u≤n) :
      |GoldbachMajorArc.classMass (u+1) d (n%d) - (u:ℝ)/d.totient| ≤
        C*(2:ℝ)^b*n/(Real.log n)^b := by
    have hR : (2:ℝ)^a ≤ Real.log u :=
      (show (2:ℝ)^a≤Real.log (n/4:ℕ) from hlog).trans
        (Real.log_le_log (by exact_mod_cast (show 0<n/4 by omega)) (by exact_mod_cast hu))
    have h1 : 1≤Real.log u := (one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hR
    have hpos := zero_lt_one.trans_le h1
    have hlogn : Real.log n ≤ 2*Real.log u := by
      have hnu : n ≤ u^2 := by nlinarith only [show n≤5*u by omega,show 5≤u by omega]
      have hcmp := Real.log_le_log (show 0<(n:ℝ) by positivity) (by exact_mod_cast hnu : (n:ℝ)≤(u:ℝ)^2)
      simpa only [Real.log_pow,Nat.cast_ofNat] using hcmp
    have hM : (d:ℝ)≤(Real.log u)^e := calc
      _ ≤ (2*Real.log u)^a := hsize.trans (pow_le_pow_left₀ (Real.log_natCast_nonneg _) hlogn _)
      _ = (2:ℝ)^a*(Real.log u)^a := mul_pow ..
      _ ≤ (Real.log u)^(a+1) := by rw [pow_succ,mul_comm ((Real.log u)^a)];gcongr
      _ ≤ _ := pow_le_pow_right₀ h1 (by dsimp only [e];omega)
    have hmod : (n%d).Coprime d := by
      rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm]
      exact hc
    apply (hU u (hth.trans hu) d (n%d) hd hM (Nat.mod_lt _ hd) hmod).trans
    have hnlog : 0<Real.log n := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hden : (Real.log n)^b ≤ (2:ℝ)^b*(Real.log u)^(2*e+1) := calc
      _ ≤ (2*Real.log u)^b := pow_le_pow_left₀ hnlog.le hlogn b
      _ = _ := mul_pow ..
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by dsimp only [e];omega : b≤2*e+1)) (by positivity)
    apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hnlog _)).mpr
    calc
      _ ≤ (C*(u:ℝ))*((2:ℝ)^b*(Real.log u)^(2*e+1)) := mul_le_mul_of_nonneg_left hden (by positivity)
      _ ≤ (C*(n:ℝ))*((2:ℝ)^b*(Real.log u)^(2*e+1)) := by gcongr
      _ = _ := by ring
  rw [fixedTargetDivisorRow_prefix,Nat.cast_sub (by omega : n/4≤n/2)]
  have hhi := hscale (n/2) (by omega) (Nat.div_le_self ..)
  have hlo := hscale (n/4) le_rfl (Nat.div_le_self ..)
  set M := C*(2:ℝ)^b*n/(Real.log n)^b
  rw [show 2*C*(2:ℝ)^b*n/(Real.log n)^b=2*M by dsimp only [M];ring]
  apply abs_le.mpr
  constructor
  · linear_combination (abs_le.mp hhi).1 + (abs_le.mp hlo).2
  · linear_combination (abs_le.mp hhi).2 + (abs_le.mp hlo).1

/-- Active sieve primes for a fixed reflected prime argument. -/
def fixedTargetBrunPrimes (n z : ℕ) : Finset ℕ :=
  (range (z+1)).filter (fun p => p.Prime ∧ ¬p∣n)

private theorem brunProduct_totient (t : Finset ℕ) (hp : ∀ p∈t,p.Prime) :
    (∏ p∈t,p).totient = ∏ p∈t,(p-1) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert p t hpt ih =>
    have hprime := hp p (mem_insert_self ..)
    have ht (l : ℕ) (hl : l∈t) := hp l (mem_insert_of_mem hl)
    have hc : p.Coprime (∏ l∈t,l) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro l hl
      exact (Nat.coprime_primes hprime (ht l hl)).mpr (by rintro rfl; exact hpt hl)
    rw [prod_insert hpt,prod_insert hpt,Nat.totient_mul hc,Nat.totient_prime hprime,ih ht]

theorem fixedTarget_Brun_subset_row (a b : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ z : ℕ, ∀ t ⊆ fixedTargetBrunPrimes n z,
      ((∏ p∈t,p : ℕ):ℝ)≤(Real.log n)^a →
      |fixedTargetDivisorRow n (∏ p∈t,p) - ((n/2-n/4:ℕ):ℝ) *
        ∏ p∈t, (1/((p:ℝ)-1))| ≤ C*n/(Real.log n)^b := by
  obtain ⟨C,hC,he⟩ := fixedTarget_divisor_row_uniform a b
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with n hn
  intro z t ht hsize
  have hp (p : ℕ) (h : p∈t) := (mem_filter.mp (ht h)).2.1
  have hnc : n.Coprime (∏ p∈t,p) := Nat.coprime_prod_right_iff.mpr fun p h =>
    ((hp p h).coprime_iff_not_dvd.mpr (mem_filter.mp (ht h)).2.2).symm
  have H := hn (∏ p∈t,p) (prod_pos fun p h => (hp p h).pos) hsize hnc
  rw [brunProduct_totient t hp,Nat.cast_prod] at H
  simp only [←Finset.prod_inv_distrib,div_eq_mul_inv,one_mul] at H ⊢
  convert H using 1
  congr 3
  apply prod_congr rfl
  intro p h
  rw [Nat.cast_sub (hp p h).one_le,Nat.cast_one]

theorem fixedTarget_common_prime_excluded {n z p k : ℕ} (hz : z≤n/4)
    (hp : p.Prime) (hpz : p≤z) (hpn : p∣n) (hk : k.Prime)
    (hkI : k∈Ioc (n/4) (n/2)) : ¬p∣n-k := by
  intro hd
  have hkn : k≤n := by have := (mem_Ioc.mp hkI).2;omega
  have hpk : p∣k := Nat.sub_sub_self hkn ▸ Nat.dvd_sub hpn hd
  have he := ((Nat.dvd_prime hk).mp hpk).resolve_left hp.ne_one
  have := (mem_Ioc.mp hkI).1
  omega

end GoldbachPartial