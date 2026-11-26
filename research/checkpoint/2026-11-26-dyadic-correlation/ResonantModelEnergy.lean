import MixedMobiusPrincipalModel

namespace GoldbachPartial
open Finset MeasureTheory

private theorem model_integer_euler_product (N:ℕ) :
    (∏k∈Icc 2 (N+1), (k:ℝ)^2/((k:ℝ)^2-1))=2*((N:ℝ)+1)/((N:ℝ)+2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [prod_Icc_succ_top (by omega:2≤N+1+1),ih]
    push_cast
    have hN : 0≤(N:ℝ) := Nat.cast_nonneg _
    have ha : (N:ℝ)+2≠0 := by linarith
    have hb : (N:ℝ)+1+2≠0 := by linarith
    have hc : ((N:ℝ)+1+1)^2-1≠0 := by nlinarith [sq_nonneg (N:ℝ)]
    field_simp
    ring

theorem model_totient_ratio_le_divisor_reciprocals (q:ℕ) (hq:0<q) :
    (q:ℝ)/q.totient ≤ 2*∑d∈q.divisors,(d:ℝ)⁻¹ := by
  classical
  let F (k:ℕ) := (k:ℝ)^2/((k:ℝ)^2-1)
  have hp2 {p:ℕ} (hp:p∈q.primeFactors) : 2≤p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hF {p:ℕ} (hp:2≤p) : 1≤F p := by
    have hr : (2:ℝ)≤p := by exact_mod_cast hp
    have hd : 0<(p:ℝ)^2-1 := by nlinarith [sq_nonneg ((p:ℝ)-2)]
    dsimp only [F]
    exact (le_div_iff₀ hd).mpr (by linarith)
  have hfac : ∏ p∈q.primeFactors,F p ≤ 2 := by
    have hsub : q.primeFactors ⊆ Icc 2 (q+1) := fun p hp => mem_Icc.mpr ⟨hp2 hp,(Nat.le_of_dvd hq (Nat.dvd_of_mem_primeFactors hp)).trans (Nat.le_succ _)⟩
    apply (prod_le_prod_of_subset_of_one_le₀ hsub (fun p hp => zero_le_one.trans (hF (hp2 hp))) (fun p hp _ => hF (mem_Icc.mp hp).1)).trans
    change (∏k∈Icc 2 (q+1),(k:ℝ)^2/((k:ℝ)^2-1))≤2
    rw [model_integer_euler_product,div_le_iff₀ (by positivity)]
    linarith
  have hsum : ∏ p∈q.primeFactors,(1+(p:ℝ)⁻¹) ≤ ∑d∈q.divisors,(d:ℝ)⁻¹ := by
    rw [prod_one_add]
    let f (s:Finset ℕ) := ∏p∈s,p
    have hprime {s:Finset ℕ} (hs:s∈q.primeFactors.powerset) : (f s).primeFactors=s :=
      Nat.primeFactors_prod fun _ hp => Nat.prime_of_mem_primeFactors ((mem_powerset.mp hs) hp)
    apply sum_le_sum_of_injOn f
    · intro s hs t ht he
      rw [←hprime hs,←hprime ht,he]
    · intro k hk
      obtain ⟨s,hs,rfl⟩ := mem_image.mp hk
      exact Nat.mem_divisors.mpr ⟨(prod_dvd_prod_of_subset _ _ id (mem_powerset.mp hs)).trans (Nat.prod_primeFactors_dvd q),hq.ne'⟩
    · intro s _
      dsimp only [f]
      rw [prod_inv_distrib,Nat.cast_prod]
    · intro k _ _
      positivity
  have hφ : (q.totient:ℝ)=q*∏ p∈q.primeFactors,(1-(p:ℝ)⁻¹) := by
    have hv := congrArg (fun v:ℚ=>(v:ℝ)) (Nat.totient_eq_mul_prod_factors q)
    push_cast at hv
    exact hv
  have hre : (q:ℝ)/q.totient = ∏p∈q.primeFactors,(1-(p:ℝ)⁻¹)⁻¹ := by
    rw [prod_inv_distrib,hφ]
    field_simp [show (q:ℝ)≠0 by exact_mod_cast hq.ne']
  rw [hre]
  calc _ = ∏p∈q.primeFactors,(F p*(1+(p:ℝ)⁻¹)) := by
         apply prod_congr rfl
         intro p hp
         have hr : (2:ℝ)≤p := by exact_mod_cast hp2 hp
         have h0 : (p:ℝ)≠0 := by linarith
         have h1 : (p:ℝ)^2-1≠0 := by nlinarith [sq_nonneg ((p:ℝ)-2)]
         have h2 : (p:ℝ)-1≠0 := by linarith
         dsimp only [F]
         field_simp
         ring
       _ = (∏p∈q.primeFactors,F p)*(∏p∈q.primeFactors,(1+(p:ℝ)⁻¹)) := prod_mul_distrib
       _ ≤ _ := mul_le_mul hfac hsum (prod_nonneg fun p _ => by positivity) (by norm_num)

private theorem modelHarmonic_bound (Q:ℕ) :
    (∑j∈Icc 1 Q,(j:ℝ)⁻¹)≤1+Real.log Q := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [sum_Icc_succ_top (by omega:1≤Q+1)]
    by_cases h:Q=0
    · subst Q; norm_num
    have hQ : (0:ℝ)<Q := by exact_mod_cast Nat.pos_of_ne_zero h
    have hp : (0:ℝ)<Q+1 := by positivity
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hQ)
    rw [Real.log_div hp.ne' hQ.ne',inv_div] at hl
    have he : 1-(Q:ℝ)/(Q+1)=((Q:ℝ)+1)⁻¹ := by field_simp; ring
    rw [he] at hl
    push_cast
    linarith

private theorem modelInverseSquares_bound (Q:ℕ) : (∑d∈Icc 1 Q,1/(d:ℝ)^2) ≤ 2 := by
  let f (j:ℕ):ℝ := -(2/(j:ℝ))
  change (∑d∈Ico 1 (Q+1),1/(d:ℝ)^2) ≤ 2
  calc
    _ ≤ ∑d∈Ico 1 (Q+1),(f (d+1)-f d) := by
      apply sum_le_sum
      intro d hd
      have hr : (1:ℝ)≤d := by exact_mod_cast (mem_Ico.mp hd).1
      dsimp only [f]
      push_cast
      field_simp
      nlinarith only [hr,mul_nonneg (sub_nonneg.mpr hr) (show (0:ℝ)≤d by linarith)]
    _ = f (Q+1)-f 1 := sum_Ico_sub _ (by omega)
    _ ≤ _ := by simp only [f,Nat.cast_one,div_one]; linarith [show 0≤2/((Q+1:ℕ):ℝ) by positivity]

private theorem modelMultiples_harmonic (R Q d:ℕ) (hd:0<d) :
    (∑j∈Ico R Q,if d∣j+1 then (d:ℝ)/((j+1:ℕ):ℝ) else 0) ≤1+Real.log Q := by
  rw [←sum_filter]
  apply le_trans _ (modelHarmonic_bound Q)
  let f (j:ℕ):ℕ := (j+1)/d
  have hh (j:ℕ) (hj:j∈(Ico R Q).filter (fun k=>d∣k+1)) :
      0<f j ∧ d*f j=j+1 ∧ f j≤Q := by
    obtain ⟨hm,hdiv⟩ := mem_filter.mp hj
    exact ⟨Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) hdiv) hd,Nat.mul_div_cancel' hdiv,
      (Nat.div_le_self _ _).trans (mem_Ico.mp hm).2⟩
  apply sum_le_sum_of_injOn f
  · intro i hi j hj he
    have hv := congrArg (d*·) he
    rw [(hh _ hi).2.1,(hh _ hj).2.1] at hv
    omega
  · intro k hk
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    exact mem_Icc.mpr ⟨(hh _ hj).1,(hh _ hj).2.2⟩
  · intro j hj
    have hv : (d:ℝ)*((f j:ℕ):ℝ)=((j+1:ℕ):ℝ) := by exact_mod_cast (hh j hj).2.1
    have hd' : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
    rw [←hv]
    field_simp
    exact le_rfl
  · intro j _ _
    positivity

theorem modelTotientReciprocal_sum (R Q:ℕ) :
    (∑j∈Ico R Q,1/((j+1).totient:ℝ))≤4*(1+Real.log Q) := by
  let W (d j:ℕ):ℝ := if d∣j+1 then (d:ℝ) / ((j+1:ℕ):ℝ) else 0
  have hrow (j:ℕ) (hj:j∈Ico R Q) : 1/((j+1).totient:ℝ) ≤
      2*∑d∈Icc 1 Q,(1/(d:ℝ)^2)*W d j := by
    have he : (j+1).divisors=(Icc 1 Q).filter (fun d=>d∣j+1) := by
      ext d
      rw [mem_filter,mem_Icc,Nat.mem_divisors]
      constructor
      · rintro ⟨h,_⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h (Nat.succ_pos j),(Nat.le_of_dvd (Nat.succ_pos j) h).trans (mem_Ico.mp hj).2⟩,h⟩
      · exact fun h => ⟨h.2,(Nat.succ_ne_zero _)⟩
    have h := model_totient_ratio_le_divisor_reciprocals (j+1) (Nat.succ_pos _)
    have hR : (0:ℝ)<((j+1:ℕ):ℝ) := by positivity
    apply (mul_le_mul_iff_right₀ hR).mp
    calc
      _ = ((j+1:ℕ):ℝ)/((j+1).totient:ℝ) := by ring
      _ ≤ _ := h
      _ = 2*(((j+1:ℕ):ℝ)*∑d∈Icc 1 Q,(1/(d:ℝ)^2)*W d j) := by
        rw [he,sum_filter]
        apply congrArg (fun z:ℝ => 2*z)
        rw [mul_sum]
        apply sum_congr rfl
        intro d hd
        have hd' : (d:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hd).1)
        by_cases hdiv:d∣j+1
        · simp only [W,ite_eq_left hdiv]
          field_simp
        · simp [W,hdiv]
      _ = _ := by ring
  have hs : ∑j∈Ico R Q,1/((j+1).totient:ℝ) ≤
      2*∑d∈Icc 1 Q,(1/(d:ℝ)^2)*(∑j∈Ico R Q,W d j) := by
    calc _ ≤ ∑j∈Ico R Q,2*∑d∈Icc 1 Q,(1/(d:ℝ)^2)*W d j := sum_le_sum hrow
         _ = _ := by rw [←mul_sum,sum_comm]; simp_rw [mul_sum]
  apply hs.trans
  calc
    _ ≤ 2*∑d∈Icc 1 Q,(1/(d:ℝ)^2)*(1+Real.log Q) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum fun d hd => mul_le_mul_of_nonneg_left (modelMultiples_harmonic R Q d (mem_Icc.mp hd).1) (by positivity)
    _ ≤ _ := by
      rw [←sum_mul]
      have hlog : 0≤1+Real.log Q := by linarith [Real.log_natCast_nonneg Q]
      nlinarith only [mul_le_mul_of_nonneg_right (modelInverseSquares_bound Q) hlog]

theorem resonantArcModel_family_energy (n R Q:ℕ) (ρ:ℕ→ℝ)
    (h:∀j∈Ico R Q,0≤ρ (j+1) ∧ ρ (j+1)≤1/2) :
    (∑j∈Ico R Q, ∑ _a∈(range (j+1)).filter (fun a=>a.Coprime (j+1)),
      ∫β in -(ρ (j+1))..ρ (j+1),‖resonantPrincipalModel n (j+1) β‖^2) ≤
      4*((n:ℝ)+1)*(1+Real.log Q) := by
  have hrow (j:ℕ) (hj:j∈Ico R Q) :
      (∑ _a∈(range (j+1)).filter (fun a=>a.Coprime (j+1)),∫β in -(ρ (j+1))..ρ (j+1),‖resonantPrincipalModel n (j+1) β‖^2) ≤
        ((n:ℝ)+1)*(1/((j+1).totient:ℝ)) := by
    let q := j+1
    let _ : NeZero q := ⟨Nat.succ_ne_zero j⟩
    have hm : ‖(ArithmeticFunction.moebius q:ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=q)
    have hcard : ((range q).filter (fun a=>a.Coprime q)).card=q.totient := by
      rw [Nat.totient_eq_card_coprime]
      congr 1
      ext a
      simp only [mem_filter,mem_range]
      exact and_congr_right (fun _ => Nat.coprime_comm)
    have heq (β:ℝ) : resonantPrincipalModel n q β=(ArithmeticFunction.moebius q:ℂ)*dirichletGeometricKernel n β/(q.totient:ℂ) := by
      unfold resonantPrincipalModel
      push_cast
      ring
    change (∑_a∈(range q).filter (fun a=>a.Coprime q),∫β in -(ρ q)..ρ q,‖resonantPrincipalModel n q β‖^2) ≤ _
    simp only [sum_const,hcard,nsmul_eq_mul,heq]
    exact (normalized_geometric_window_energy n q _ hm (h j hj).1 (h j hj).2).trans_eq (by ring)
  calc
    _ ≤ ∑j∈Ico R Q,((n:ℝ)+1)*(1/((j+1).totient:ℝ)) := sum_le_sum hrow
    _ ≤ _ := by
      rw [←mul_sum]
      exact (mul_le_mul_of_nonneg_left (modelTotientReciprocal_sum R Q) (by positivity : 0≤(n:ℝ)+1)).trans_eq (by ring)

theorem resonantArcModel_terminal_energy :
    ∀ᶠ n:ℕ in Filter.atTop,let R:=terminalPrimeArcCutoff n;let Q:=naturalTubeScale n
      (∑j∈Ico R Q, ∑_a∈(range (j+1)).filter (fun a=>a.Coprime (j+1)),
        ∫β in -(naturalTubeRadius (3*Q) (j+1))..naturalTubeRadius (3*Q) (j+1),
          ‖resonantPrincipalModel n (j+1) β‖^2) ≤ 8*(n:ℝ)*(1+Real.log n) := by
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ)] with n hn
  dsimp only
  let Q := naturalTubeScale n
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hr : 1≤Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr hn'
  have hQ : 1≤Q := Nat.le_floor (by exact_mod_cast hr)
  have hQ' : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hQN : (Q:ℝ)≤n := (Nat.floor_le (Real.sqrt_nonneg _)).trans (by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),Real.sqrt_nonneg (n:ℝ),mul_nonneg (sub_nonneg.mpr hn') (Nat.cast_nonneg (α:=ℝ) n)])
  have hradius (j:ℕ) : 0≤naturalTubeRadius (3*Q) (j+1) ∧ naturalTubeRadius (3*Q) (j+1)≤1/2 := by
    dsimp only [naturalTubeRadius]
    push_cast
    have hj : (1:ℝ)≤(j:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) j]
    have hb := mul_le_mul_of_nonneg_right hQ' (show 0≤(j:ℝ)+1 by linarith)
    constructor
    · positivity
    · apply one_div_le_one_div_of_le (by norm_num)
      nlinarith only [hb,hj]
  apply (resonantArcModel_family_energy n (terminalPrimeArcCutoff n) Q (naturalTubeRadius (3*Q)) (fun j _ => hradius j)).trans
  have hlog := Real.log_le_log (by linarith:0<(Q:ℝ)) hQN
  have hL : 0≤1+Real.log Q := by linarith [Real.log_natCast_nonneg Q]
  calc _ ≤ 4*(2*(n:ℝ))*(1+Real.log n) := by
         apply mul_le_mul _ (by linarith only [hlog]) hL (by positivity)
         linarith
       _ = _ := by ring

end GoldbachPartial