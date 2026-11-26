import VerifiedMedDeskProgression
import LocalPrimeCorrelationWindows

namespace GoldbachPartial
open Finset Filter
open scoped Topology

private noncomputable def classPrime (q a k : ℕ) := if k%q=a then weight k else 0

private theorem classPrime_nonneg (q a k : ℕ) : 0≤classPrime q a k := by
  unfold classPrime weight
  split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl

private theorem classWindow_weight_nonneg (k : ℕ) : 0≤weight k := by
  unfold weight
  split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl

private theorem classPrime_le_weight (q a k : ℕ) : classPrime q a k≤weight k := by
  unfold classPrime
  split_ifs <;> first | exact le_rfl | exact classWindow_weight_nonneg _

private theorem residue_mass_interval (q a u v : ℕ) (h : u≤v) :
    ∑ k ∈ Ioc u v, classPrime q a k =
      GoldbachMajorArc.classMass (v+1) q a - GoldbachMajorArc.classMass (u+1) q a := by
  have hset : Ioc u v = Ico (u+1) (v+1) := by ext k; simp only [mem_Ioc,mem_Ico]; omega
  rw [hset, sum_Ico_eq_sub _ (by omega)]
  unfold GoldbachMajorArc.classMass
  simp only [sum_filter]
  rfl

private theorem classPrime_interval_shift (N H p q b : ℕ) (hp : p≤N) :
    (∑ m ∈ Ioc N (N+H), classPrime q b (m-p)) =
      ∑ r ∈ Ioc (N-p) (N+H-p), classPrime q b r := by
  apply sum_bij (fun m _ => m-p)
  · intro m hm
    have h := mem_Ioc.mp hm
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro m hm l hl h
    have h1 := mem_Ioc.mp hm
    have h2 := mem_Ioc.mp hl
    omega
  · intro r hr
    have h := mem_Ioc.mp hr
    exact ⟨r+p,mem_Ioc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro _ _; rfl

/-- The true ordered correlation with its first prime restricted to class a. -/
noncomputable def residueWindowCorrClass (q a m : ℕ) : ℝ :=
  ∑ p ∈ range (m+1), classPrime q a p * weight (m-p)

theorem residueWindowCorrClass_le (q a m : ℕ) : residueWindowCorrClass q a m ≤ corr m := by
  unfold residueWindowCorrClass corr
  exact sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (classPrime_le_weight ..) (classWindow_weight_nonneg _)

theorem sum_residueWindowCorrClass_le (q m : ℕ) (A : Finset ℕ) :
    ∑ a ∈ A, residueWindowCorrClass q a m ≤ corr m := by
  unfold residueWindowCorrClass corr
  rw [sum_comm]
  apply sum_le_sum
  intro p _
  rw [← sum_mul]
  apply mul_le_mul_of_nonneg_right _ (classWindow_weight_nonneg _)
  simp only [classPrime, sum_ite_eq]
  split_ifs <;> first | exact le_rfl | exact classWindow_weight_nonneg _

/-- First moment on a prescribed class from the true prime prefixes, sampled
only between X and 4X. -/
theorem residue_primeCorr_full_rectangle {X Y B N H q a b : ℕ} {D : ℝ}
    (hXY : X≤Y) (hYB : Y≤B) (hYN : Y+X≤N) (htop : N+H≤B+X)
    (hp : ∀ c ∈ ({a,b}:Finset ℕ), ∀ u ∈ Icc X B,
      |GoldbachMajorArc.classMass (u+1) q c - (u:ℝ)/q.totient| ≤ D)
    (hD : 2*D ≤ (H:ℝ)/q.totient) :
    (((Y:ℝ)-X)/q.totient-2*D)*((H:ℝ)/q.totient-2*D) ≤
      ∑ m ∈ (Ioc N (N+H)).filter (fun m => m%q=(a+b)%q), residueWindowCorrClass q a m := by

  have hseg (c : ℕ) (hc : c ∈ ({a,b}:Finset ℕ)) (u v : ℕ)
      (hu : X≤u) (hv : v≤B) (huv : u≤v) :
      ((v:ℝ)-u)/q.totient-2*D ≤ ∑ k ∈ Ioc u v, classPrime q c k := by
    rw [residue_mass_interval _ _ _ _ huv]
    have hhi := (abs_le.mp (hp _ hc _ (mem_Icc.mpr ⟨hu.trans huv,hv⟩))).1
    have hlo := (abs_le.mp (hp _ hc _ (mem_Icc.mpr ⟨hu,huv.trans hv⟩))).2
    rw [sub_div]
    linarith only [hhi,hlo]
  have hout := hseg a (by simp) X Y le_rfl hYB hXY
  have row (p : ℕ) (hp' : p ∈ Ioc X Y) :
      (H:ℝ)/q.totient-2*D ≤ ∑ m ∈ Ioc N (N+H), classPrime q b (m-p) := by
    have hpi := mem_Ioc.mp hp'
    have hpn : p≤N := by omega
    rw [classPrime_interval_shift _ _ _ _ _ hpn]
    have h := hseg b (by simp) (N-p) (N+H-p) (by omega) (by omega) (by omega)
    have heq : ((N+H-p:ℕ):ℝ)-((N-p:ℕ):ℝ)=H := by
      rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_sub hpn];ring
    rwa [heq] at h
  calc
    _ ≤ (∑ p ∈ Ioc X Y,classPrime q a p)*((H:ℝ)/q.totient-2*D) :=
      mul_le_mul_of_nonneg_right hout (sub_nonneg.mpr hD)
    _ ≤ ∑ p ∈ Ioc X Y, ∑ m ∈ Ioc N (N+H), classPrime q a p*classPrime q b (m-p) := by
      rw [sum_mul]
      refine sum_le_sum fun p hp' => ?_
      rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (row p hp') (classPrime_nonneg ..)
    _ = ∑ m ∈ Ioc N (N+H), ∑ p ∈ Ioc X Y, classPrime q a p*classPrime q b (m-p) := sum_comm
    _ ≤ _ := by
      rw [sum_filter]
      refine sum_le_sum fun m hm => ?_
      have hmi := mem_Ioc.mp hm
      by_cases hc : m%q=(a+b)%q
      · rw [ite_eq_left hc]
        unfold residueWindowCorrClass
        apply le_trans (sum_le_sum fun p _ => mul_le_mul (le_refl (classPrime q a p))
          (classPrime_le_weight q b (m-p)) (classPrime_nonneg ..) (classPrime_nonneg ..))
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp'
          exact mem_range.mpr (by have h := mem_Ioc.mp hp'; omega)
        · exact fun p _ _ => mul_nonneg (classPrime_nonneg ..) (classWindow_weight_nonneg _)
      · rw [ite_eq_right hc]
        apply le_of_eq (sum_eq_zero fun p hp' => ?_)
        have hpi := mem_Ioc.mp hp'
        by_cases ha' : p%q=a <;> by_cases hb' : (m-p)%q=b <;> simp [classPrime,ha',hb']
        exfalso
        apply hc
        calc
          _ = (p+(m-p))%q := by rw [Nat.add_sub_of_le (by omega : p≤m)]
          _ = _ := by rw [Nat.add_mod,ha',hb']

theorem residue_primeCorr_window_mass_restricted {X N H q a b : ℕ} {D : ℝ}
    (ht : 3*X≤N) (hTop : N+H≤5*X)
    (hp : ∀ c ∈ ({a,b}:Finset ℕ), ∀ u ∈ Icc X (4*X),
      |GoldbachMajorArc.classMass (u+1) q c - (u:ℝ)/q.totient| ≤ D)
    (hD : 2*D ≤ (H:ℝ)/q.totient) :
    ((X:ℝ)/q.totient-2*D)*((H:ℝ)/q.totient-2*D) ≤
      ∑ m ∈ (Ioc N (N+H)).filter (fun m => m%q=(a+b)%q), residueWindowCorrClass q a m := by
  have h := residue_primeCorr_full_rectangle (X:=X) (Y:=2*X) (B:=4*X) (N:=N) (H:=H)
    (by omega) (by omega) (by omega) (by omega) hp hD
  simpa only [Nat.cast_mul,Nat.cast_ofNat,show 2*(X:ℝ)-X=X by ring] using h

/-- First moment on a prescribed class from the true prime prefixes, sampled
only between X and 4X. -/
theorem residue_primeCorr_window_mass {X N H q a b : ℕ} {D : ℝ}
    (ht : 3*X≤N) (hTop : N+H≤5*X)
    (hp : ∀ c ∈ ({a,b}:Finset ℕ), ∀ u ∈ Icc X (4*X),
      |GoldbachMajorArc.classMass (u+1) q c - (u:ℝ)/q.totient| ≤ D)
    (hD : 2*D ≤ (H:ℝ)/q.totient) :
    ((X:ℝ)/q.totient-2*D)*((H:ℝ)/q.totient-2*D) ≤
      ∑ m ∈ (Ioc N (N+H)).filter (fun m => m%q=(a+b)%q), corr m
  := by
    apply (residue_primeCorr_window_mass_restricted ht hTop hp hD).trans
    exact sum_le_sum fun _ _ => residueWindowCorrClass_le ..

private theorem window_uniform_prime_class :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ u : ℕ in atTop,
      ∀ q a : ℕ, 0<q → (q:ℝ)≤Real.log u → a<q → a.Coprime q →
        |GoldbachMajorArc.classMass (u+1) q a - (u:ℝ)/q.totient| ≤ C*u/(Real.log u)^3 := by
  obtain ⟨M,hM,x₀,_,hap⟩ := GoldbachMajorArc.prime_progression_error 3 1 (by norm_num) (by norm_num)
  refine ⟨M+4,by positivity,?_⟩
  have htlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  have hpow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow 5 (by norm_num : (0:ℝ)<1/2))
  filter_upwards [htlog,hpow,eventually_ge_atTop (max 1 ⌈x₀⌉₊)] with u hlog hpow hu
  intro q a hq hqL ha hc
  let L := Real.log u
  have hx : x₀≤(u:ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right 1 ⌈x₀⌉₊).trans hu)
  have huR : (1:ℝ)≤u := by exact_mod_cast (le_max_left 1 ⌈x₀⌉₊).trans hu
  change 1≤L at hlog
  have hL : 0<L := by linarith
  have h5 : L^5 ≤ Real.sqrt u := by simpa only [L,Function.comp_def,Real.rpow_ofNat,Real.sqrt_eq_rpow] using hpow
  have hr := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) u)
  have h4 := (pow_le_pow_right₀ hlog (by decide : 4≤5)).trans h5
  have hroot : Real.sqrt u≤(u:ℝ) := by
    have h1 : 1≤Real.sqrt (u:ℝ) := by simpa using Real.sqrt_le_sqrt huR
    nlinarith only [hr,mul_nonneg (zero_le_one.trans h1) (sub_nonneg.mpr h1)]
  have hqlog : Real.log q≤L := by
    apply Real.log_le_log (by exact_mod_cast hq)
    exact hqL.trans (by have h := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le huR); linarith)
  have hnat : (Nat.log 2 u:ℝ)≤2*L := by
    have h := Real.natLog_le_logb u 2
    have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h₂
    simp only [Nat.cast_ofNat,Real.logb] at h
    apply h.trans ((div_le_iff₀ (by linarith : 0<Real.log 2)).mpr _)
    nlinarith only [mul_nonneg hL.le (show 0≤2*Real.log 2-1 by linarith)]
  have hAP := hap u q a hx hq (by simpa using hqL) ha hc
  change _ ≤ M*(u:ℝ)*L^(-(3:ℝ))+(Nat.log 2 u:ℝ)*Real.log q+2*Real.sqrt u*L at hAP
  rw [Real.rpow_neg hL.le,Real.rpow_ofNat,←div_eq_mul_inv] at hAP
  apply hAP.trans
  have hx1 : (Nat.log 2 u:ℝ)*Real.log q ≤ 2*(u:ℝ)/L^3 := by
    apply (mul_le_mul hnat hqlog (Real.log_natCast_nonneg _) (by positivity)).trans
    apply (le_div_iff₀ (pow_pos hL 3)).mpr
    linear_combination 2*(h5.trans hroot)
  have hx2 : 2*Real.sqrt u*L ≤ 2*(u:ℝ)/L^3 := by
    apply (le_div_iff₀ (pow_pos hL 3)).mpr
    have hh := mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg (u:ℝ))
    linear_combination 2*hh+2*hr
  change _≤(M+4)*(u:ℝ)/L^3
  linear_combination hx1+hx2

/-- Unconditional first moment in a prescribed sum of two reduced classes.
The threshold for X is independent of the modulus, classes, and window. -/
theorem prescribed_residue_primeCorr_mass_restricted :
    ∀ᶠ X : ℕ in atTop, ∀ N H q a b : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → a<q → a.Coprime q →
      b<q → b.Coprime q →
      (X:ℝ)*H / (4*(q.totient:ℝ)^2) ≤
        ∑ m ∈ (Ioc N (N+H)).filter (fun m => m%q=(a+b)%q), residueWindowCorrClass q a m := by
  obtain ⟨C,hC,hu⟩ := window_uniform_prime_class
  obtain ⟨u₀,hu₀⟩ := eventually_atTop.mp hu
  have ht := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (max 1 (16*C))
  filter_upwards [ht,eventually_ge_atTop (max u₀ 1)] with X hlog hX
  intro N H q a b ht htop hHX hH hq hqL ha hca hb hcb
  let L := Real.log X
  let φ := (q.totient:ℝ)
  let D := 4*C*X/L^3
  have hL : 0<L := lt_of_lt_of_le zero_lt_one ((le_max_left 1 (16*C)).trans hlog)
  have hC16 : 16*C≤L := (le_max_right 1 (16*C)).trans hlog
  have hX0 : (0:ℝ)<X := by exact_mod_cast (le_max_right u₀ 1).trans hX
  have hφ : 0<φ := by dsimp only [φ]; exact_mod_cast Nat.totient_pos.mpr hq
  have hφL : φ≤L := (by exact_mod_cast Nat.totient_le q : (q.totient:ℝ)≤q).trans hqL
  have hCX : 16*C*φ ≤ L^2 := by
    simpa only [sq] using mul_le_mul hC16 hφL hφ.le hL.le
  have hD : 4*D ≤ (H:ℝ)/φ := by
    apply (le_div_iff₀ hφ).mpr
    calc
      _ = (X:ℝ)/L * ((16*C*φ)/L^2) := by dsimp only [D]; ring
      _ ≤ (X:ℝ)/L := mul_le_of_le_one_right (by positivity) ((div_le_one (pow_pos hL 2)).mpr hCX)
      _ ≤ _ := hH
  have hpre (c : ℕ) (hc : c ∈ ({a,b}:Finset ℕ)) (u : ℕ) (huX : u ∈ Icc X (4*X)) :
      |GoldbachMajorArc.classMass (u+1) q c - (u:ℝ)/q.totient| ≤ D := by
    obtain ⟨hXu,hu4⟩ := mem_Icc.mp huX
    have hlu : L≤Real.log u := Real.log_le_log hX0 (by exact_mod_cast hXu)
    have hcla : c<q ∧ c.Coprime q := by
      simp only [mem_insert,mem_singleton] at hc
      rcases hc with rfl|rfl
      · exact ⟨ha,hca⟩
      · exact ⟨hb,hcb⟩
    have hpu := hu₀ u (((le_max_left u₀ 1).trans hX).trans hXu) q c hq
      (hqL.trans hlu) hcla.1 hcla.2
    apply hpu.trans
    have hu4r : (u:ℝ)≤4*X := by exact_mod_cast hu4
    calc
      _ ≤ C*(4*(X:ℝ))/L^3 := div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hu4r hC.le) (pow_pos hL 3) (pow_le_pow_left₀ hL.le hlu 3)
      _ = _ := by dsimp only [D]; ring
  have hD0 : 0≤D := by dsimp only [D]; positivity
  have hmass := residue_primeCorr_window_mass_restricted ht htop hpre (show 2*D≤(H:ℝ)/q.totient by linarith only [hD0,hD])
  have hh0 : 0≤(H:ℝ)/φ := by positivity
  have hXH : (H:ℝ)/φ≤(X:ℝ)/φ := div_le_div_of_nonneg_right (by exact_mod_cast hHX) hφ.le
  apply le_trans _ hmass
  calc
    _ = ((X:ℝ)/φ/2)*((H:ℝ)/φ/2) := by dsimp only [φ]; ring
    _ ≤ _ := mul_le_mul (by linarith only [hD,hXH]) (by linarith only [hD])
      (by positivity) (by linarith only [hD,hXH,hh0])
/-- Unconditional first moment in a prescribed sum of two reduced classes.
The threshold for X is independent of the modulus, classes, and window. -/
theorem prescribed_residue_primeCorr_mass :
    ∀ᶠ X : ℕ in atTop, ∀ N H q a b : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → a<q → a.Coprime q →
      b<q → b.Coprime q →
      (X:ℝ)*H / (4*(q.totient:ℝ)^2) ≤
        ∑ m ∈ (Ioc N (N+H)).filter (fun m => m%q=(a+b)%q), corr m
  := by
    filter_upwards [prescribed_residue_primeCorr_mass_restricted] with X h
    intro N H q a b hN hT hHX hH hq hqL ha hca hb hcb
    apply (h N H q a b hN hT hHX hH hq hqL ha hca hb hcb).trans
    exact sum_le_sum fun _ _ => residueWindowCorrClass_le ..

/-- Every even residue is a sum of two reduced residues, for every
positive modulus, including non-squarefree moduli. -/
theorem even_residue_reduced_pair (q t : ℕ) (hq : 0<q) :
    ∃ a<q, ∃ b<q, a.Coprime q ∧ b.Coprime q ∧ (a+b)%q=(2*t)%q := by
  let P := q.primeFactors.filter (fun p => ¬p∣t)
  let s := ∏ p ∈ P, p
  have hsd : s∣q :=
    (prod_dvd_prod_of_subset _ _ id (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd q)
  have hsle := Nat.le_of_dvd hq hsd
  have hts : t.Coprime s := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    exact (hprime.coprime_iff_not_dvd.mpr (mem_filter.mp hp).2).symm
  have hlocal {p : ℕ} (hpr : p.Prime) (hpq : p∣q) :
      (p∣t ∧ ¬p∣s) ∨ (¬p∣t ∧ p∣s) := by
    by_cases hpt : p∣t
    · exact Or.inl ⟨hpt,fun hps => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hpr,hpt,hps⟩) hts⟩
    · have hmem : p ∈ P := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpr,hpq,hq.ne'⟩, hpt⟩
      exact Or.inr ⟨hpt,Finset.dvd_prod_of_mem id hmem⟩
  have hy : t+q-s+s=t+q := by omega
  have hA : (t+s).Coprime q := by
    by_contra hh
    obtain ⟨p,hp,hpd,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    rcases hlocal hp hpq with ⟨ht,hs⟩|⟨ht,hs⟩
    · exact hs ((Nat.dvd_add_right ht).mp hpd)
    · exact ht ((Nat.dvd_add_left hs).mp hpd)
  have hB : (t+q-s).Coprime q := by
    by_contra hh
    obtain ⟨p,hp,hpd,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    rcases hlocal hp hpq with ⟨ht,hs⟩|⟨ht,hs⟩
    · apply hs
      exact (Nat.dvd_add_right hpd).mp (hy.symm ▸ Nat.dvd_add ht hpq)
    · apply ht
      exact (Nat.dvd_add_left hpq).mp (hy ▸ Nat.dvd_add hpd hs)
  have hmod (j : ℕ) (hj : j.Coprime q) : (j%q).Coprime q := by
    rw [Nat.coprime_iff_gcd_eq_one, ← Nat.gcd_rec, Nat.gcd_comm]
    exact hj.gcd_eq_one
  refine ⟨(t+s)%q,Nat.mod_lt _ hq,(t+q-s)%q,Nat.mod_lt _ hq,hmod _ hA,hmod _ hB,?_⟩
  rw [← Nat.add_mod,show t+s+(t+q-s)=2*t+q by omega,Nat.add_mod_right]

theorem all_even_residue_primeCorr_mass :
    ∀ᶠ X : ℕ in atTop, ∀ N H q t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X →
      (X:ℝ)*H / (4*(q.totient:ℝ)^2) ≤
        ∑ m ∈ (Ioc N (N+H)).filter (fun m => m%q=(2*t)%q), corr m := by
  filter_upwards [prescribed_residue_primeCorr_mass] with X h
  intro N H q t h1 h2 h3 h4 hq hqL
  obtain ⟨a,ha,b,hb,hca,hcb,he⟩ := even_residue_reduced_pair q t hq
  simpa only [he] using h N H q a b h1 h2 h3 h4 hq hqL ha hca hb hcb
private theorem class_window_card {N H q r : ℕ} (hq : 0<q) :
    q * ((Ioc N (N+H)).filter (fun m => m%q=r)).card ≤ H+2*q := by
  let S := (Ioc N (N+H)).filter (fun m => m%q=r)
  let T := Icc (N/q) ((N+H)/q)
  have hm : S.card ≤ T.card := by
    apply card_le_card_of_injOn (fun m => m/q)
    · intro m hm
      have h := mem_Ioc.mp (mem_filter.mp hm).1
      exact mem_Icc.mpr ⟨Nat.div_le_div_right h.1.le,Nat.div_le_div_right h.2⟩
    · intro m hm l hl he
      have wr := (mem_filter.mp hm).2.trans (mem_filter.mp hl).2.symm
      have h₁ := Nat.mod_add_div m q
      have h₂ := Nat.mod_add_div l q
      change m/q=l/q at he
      rw [wr,he] at h₁
      omega
  have hr : N/q ≤ (N+H)/q := Nat.div_le_div_right (Nat.le_add_right ..)
  have hsum : S.card+N/q ≤ (N+H)/q+1 := by
    simp only [T,Nat.card_Icc] at hm
    omega
  have hs := Nat.mul_le_mul_left q hsum
  rw [Nat.mul_add,Nat.mul_add,Nat.mul_one] at hs
  have h₁ := Nat.mod_add_div N q
  have h₂ := Nat.mod_add_div (N+H) q
  have h₃ := Nat.mod_lt N hq
  change q*S.card ≤ _
  omega

/-- A nearby linear witness in the designated even class. The estimate holds
simultaneously for every even q in the indicated growing range. -/
theorem all_even_residue_primeCorr_witness :
    ∀ᶠ X : ℕ in atTop, ∀ N H q t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → q≤H → 2∣q →
      ∃ m ∈ Ioc N (N+H), m%q=(2*t)%q ∧ Even m ∧
        (m:ℝ)*q / (60*(q.totient:ℝ)^2) ≤ corr m := by
  filter_upwards [all_even_residue_primeCorr_mass,eventually_ge_atTop (1:ℕ)] with X hf hX
  intro N H q t h1 h2 h3 h4 hq hqL hqh hqeven
  let S := (Ioc N (N+H)).filter (fun m => m%q=(2*t)%q)
  let φ := (q.totient:ℝ)
  have hφ : 0<φ := by dsimp only [φ]; exact_mod_cast Nat.totient_pos.mpr hq
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hx : (0:ℝ)<X := by exact_mod_cast hX
  have hr : (0:ℝ)<H := by exact_mod_cast hq.trans_le hqh
  have hm := hf N H q t h1 h2 h3 h4 hq hqL
  change (X:ℝ)*H / (4*φ^2) ≤ ∑ m ∈ S,corr m at hm
  have hpos : 0<(X:ℝ)*H/(4*φ^2) := by positivity
  have hnonempty : S.Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh, sum_empty] at hm
    linarith
  have hcard : (q:ℝ)*S.card≤3*H := by
    exact_mod_cast (class_window_card (r:=(2*t)%q) (N:=N) (H:=H) hq).trans (by omega : H+2*q≤3*H)
  have hw : ∃ m ∈ S, (X:ℝ)*q/(12*φ^2) ≤ corr m := by
    by_contra! hbad
    have hh := sum_lt_sum_of_nonempty hnonempty hbad
    rw [sum_const,nsmul_eq_mul] at hh
    have hb : (S.card:ℝ)*((X:ℝ)*q/(12*φ^2)) ≤ (X:ℝ)*H/(4*φ^2) := by
      calc
        _ = ((q:ℝ)*S.card)*((X:ℝ)/(12*φ^2)) := by ring
        _ ≤ (3*(H:ℝ))*((X:ℝ)/(12*φ^2)) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring
    linarith only [hh,hb,hm]
  obtain ⟨m,hm,hmass⟩ := hw
  obtain ⟨hmi,hmod⟩ := mem_filter.mp hm
  have he : Even m := by
    apply Nat.even_iff.mpr
    have ht := congrArg (fun k : ℕ => k%2) hmod
    change (m%q)%2=((2*t)%q)%2 at ht
    rw [Nat.mod_mod_of_dvd _ hqeven,Nat.mod_mod_of_dvd _ hqeven] at ht
    simpa using ht
  refine ⟨m,hmi,hmod,he,le_trans ?_ hmass⟩
  have hmR : (m:ℝ)≤5*X := by exact_mod_cast (mem_Ioc.mp hmi).2.trans h2
  calc
    _ ≤ (5*(X:ℝ))*q/(60*φ^2) := by dsimp only [φ]; gcongr
    _ = _ := by ring
/-- All admissible first-prime classes may be counted simultaneously: their
ordered prime pairs are disjoint. -/
theorem all_reduced_pairs_primeCorr_mass :
    ∀ᶠ X : ℕ in atTop, ∀ N H q c : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X →
      ∀ (A : Finset ℕ) (b : ℕ → ℕ),
        (∀ a ∈ A, a<q ∧ a.Coprime q ∧ b a<q ∧ (b a).Coprime q ∧ (a+b a)%q=c%q) →
        (A.card:ℝ) * ((X:ℝ)*H / (4*(q.totient:ℝ)^2)) ≤
          ∑ m ∈ (Ioc N (N+H)).filter (fun m => m%q=c%q), corr m := by
  filter_upwards [prescribed_residue_primeCorr_mass_restricted] with X h
  intro N H q c hN hT hHX hH hq hqL A b hA
  let S := (Ioc N (N+H)).filter (fun m => m%q=c%q)
  calc
    _ = ∑ _a ∈ A, ((X:ℝ)*H / (4*(q.totient:ℝ)^2)) := by simp
    _ ≤ ∑ a ∈ A, ∑ m ∈ S, residueWindowCorrClass q a m := by
      refine sum_le_sum fun a ha => ?_
      obtain ⟨har,hac,hbr,hbc,he⟩ := hA a ha
      simpa only [he,S] using h N H q a (b a) hN hT hHX hH hq hqL har hac hbr hbc
    _ = ∑ m ∈ S, ∑ a ∈ A, residueWindowCorrClass q a m := sum_comm
    _ ≤ _ := sum_le_sum fun _ _ => sum_residueWindowCorrClass_le ..
noncomputable def residueWindowPartner (q c a : ℕ) := (c+q-a)%q
noncomputable def residueWindowAdmissible (q c : ℕ) :=
  (range q).filter (fun a => a.Coprime q ∧ (residueWindowPartner q c a).Coprime q)

private theorem partner_sum (q c a : ℕ) (ha : a<q) :
    (a+residueWindowPartner q c a)%q = c%q := by
  unfold residueWindowPartner
  rw [Nat.add_mod_mod,show a+(c+q-a)=c+q by omega,Nat.add_mod_right]

theorem admissible_residue_primeCorr_mass :
    ∀ᶠ X : ℕ in atTop, ∀ N H q c : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X →
      ((residueWindowAdmissible q c).card:ℝ) * ((X:ℝ)*H / (4*(q.totient:ℝ)^2)) ≤
        ∑ m ∈ (Ioc N (N+H)).filter (fun m => m%q=c%q), corr m := by
  filter_upwards [all_reduced_pairs_primeCorr_mass] with X h
  intro N H q c hN hT hHX hH hq hqL
  apply h N H q c hN hT hHX hH hq hqL _ (residueWindowPartner q c)
  intro a ha
  have hb := mem_filter.mp ha
  have har := mem_range.mp hb.1
  exact ⟨har,hb.2.1,Nat.mod_lt _ hq,hb.2.2,partner_sum _ _ _ har⟩

theorem residueWindowAdmissible_two_pow (j t : ℕ) :
    (residueWindowAdmissible (2^(j+1)) (2*t)).card = (2^(j+1)).totient := by
  let q := 2^(j+1)
  change (residueWindowAdmissible q (2*t)).card = q.totient
  unfold residueWindowAdmissible Nat.totient
  congr 1
  ext a
  simp only [mem_filter,mem_range]
  constructor
  · exact fun h => ⟨h.1,h.2.1.symm⟩
  · rintro ⟨har,hac⟩
    refine ⟨har,hac.symm,?_⟩
    have haodd : Odd a := Nat.coprime_two_right.mp
      ((Nat.coprime_pow_right_iff (Nat.succ_pos j) a 2).mp hac.symm)
    have he : ∃ k, q=2*k := ⟨2^j,by dsimp only [q];rw [pow_succ,mul_comm]⟩
    have hodd : Odd (2*t+q-a) := by
      rcases haodd with ⟨u,hu⟩
      rcases he with ⟨v,hv⟩
      exact ⟨t+v-(u+1),by omega⟩
    have hbc : (2*t+q-a).Coprime q :=
      (Nat.coprime_pow_right_iff (Nat.succ_pos j) _ 2).mpr (Nat.coprime_two_right.mpr hodd)
    unfold residueWindowPartner
    rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec,Nat.gcd_comm]
    exact hbc.gcd_eq_one

theorem admissible_even_residue_primeCorr_witness :
    ∀ᶠ X : ℕ in atTop, ∀ N H q t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → q≤H → 2∣q →
      ∃ m ∈ Ioc N (N+H), m%q=(2*t)%q ∧ Even m ∧
        ((residueWindowAdmissible q (2*t)).card:ℝ) * (m:ℝ)*q / (60*(q.totient:ℝ)^2) ≤ corr m := by
  filter_upwards [admissible_residue_primeCorr_mass,all_even_residue_primeCorr_witness] with X hf hex
  intro N H q t h1 h2 h3 h4 hq hqL hqh hqeven
  let S := (Ioc N (N+H)).filter (fun m => m%q=(2*t)%q)
  let φ := (q.totient:ℝ)
  let K : ℝ := (residueWindowAdmissible q (2*t)).card
  have hφ : 0<φ := by dsimp only [φ]; exact_mod_cast Nat.totient_pos.mpr hq
  have hK : 0≤K := Nat.cast_nonneg _
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hm := hf N H q (2*t) h1 h2 h3 h4 hq hqL
  change K*((X:ℝ)*H / (4*φ^2)) ≤ ∑ m ∈ S,corr m at hm
  obtain ⟨w,hw,hmod,_,_⟩ := hex N H q t h1 h2 h3 h4 hq hqL hqh hqeven
  have hne : S.Nonempty := ⟨w,mem_filter.mpr ⟨hw,hmod⟩⟩
  have hcard : (q:ℝ)*S.card≤3*H := by
    exact_mod_cast (class_window_card (r:=(2*t)%q) (N:=N) (H:=H) hq).trans (by omega : H+2*q≤3*H)
  have hw' : ∃ m ∈ S, K*(X:ℝ)*q/(12*φ^2) ≤ corr m := by
    by_contra! hbad
    have hh := sum_lt_sum_of_nonempty hne hbad
    rw [sum_const,nsmul_eq_mul] at hh
    have hb : (S.card:ℝ)*(K*(X:ℝ)*q/(12*φ^2)) ≤ K*((X:ℝ)*H/(4*φ^2)) := by
      calc
        _ = ((q:ℝ)*S.card)*(K*(X:ℝ)/(12*φ^2)) := by ring
        _ ≤ (3*(H:ℝ))*(K*(X:ℝ)/(12*φ^2)) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring
    linarith only [hh,hb,hm]
  obtain ⟨m,hm,hmass⟩ := hw'
  obtain ⟨hmi,hmod⟩ := mem_filter.mp hm
  have he : Even m := by
    apply Nat.even_iff.mpr
    have ht := congrArg (fun k : ℕ => k%2) hmod
    change (m%q)%2=((2*t)%q)%2 at ht
    rw [Nat.mod_mod_of_dvd _ hqeven,Nat.mod_mod_of_dvd _ hqeven] at ht
    simpa using ht
  refine ⟨m,hmi,hmod,he,le_trans ?_ hmass⟩
  have hmR : (m:ℝ)≤5*X := by exact_mod_cast (mem_Ioc.mp hmi).2.trans h2
  calc
    _ ≤ K*(5*(X:ℝ))*q/(60*φ^2) := by dsimp only [φ,K]; gcongr
    _ = _ := by ring

/-- An absolute witness constant in every even class to a growing power
of two. The witness may vary across classes. -/
theorem power_two_residue_primeCorr_witness :
    ∀ᶠ X : ℕ in atTop, ∀ N H j t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → ((2^(j+1) : ℕ):ℝ)≤Real.log X → 2^(j+1)≤H →
      ∃ m ∈ Ioc N (N+H), m%(2^(j+1))=(2*t)%(2^(j+1)) ∧ Even m ∧ (m:ℝ)/30 ≤ corr m := by
  filter_upwards [admissible_even_residue_primeCorr_witness] with X h
  intro N H j t h1 h2 h3 h4 hqL hqh
  let q := 2^(j+1)
  have hqp : 0<q := pow_pos (by decide) _
  have hqe : 2∣q := ⟨2^j, by dsimp only [q];rw [pow_succ,mul_comm]⟩
  obtain ⟨m,hm,hr,he,hcorr⟩ := h N H q t h1 h2 h3 h4 hqp hqL hqh hqe
  refine ⟨m,hm,hr,he,le_trans ?_ hcorr⟩
  dsimp only [q]
  rw [residueWindowAdmissible_two_pow,Nat.totient_prime_pow_succ Nat.prime_two j]
  simp only [Nat.reduceSub,mul_one,Nat.cast_pow,Nat.cast_ofNat,pow_succ]
  push_cast
  exact le_of_eq (by field_simp;ring)

end GoldbachPartial
