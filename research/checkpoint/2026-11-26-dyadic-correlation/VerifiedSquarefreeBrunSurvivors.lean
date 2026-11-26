import VerifiedTrueBrunMass
import VerifiedBrunNearPowerScale
namespace GoldbachPartial
open Finset Filter
open scoped Topology Classical

noncomputable def fixedTargetNonsquarefreeMass (n z:ℕ) : ℝ :=
  ∑k∈(fixedTargetBrunPrimeSurvivors n z).filter (fun k=>¬Squarefree (n-k)),Real.log k

private theorem sf_weight_nonneg (k:ℕ) : 0≤weight k := by unfold weight;split_ifs <;> positivity

private theorem sf_inverse_tail (z R:ℕ) :
    (∑p∈Ioc z R,1/(p:ℝ)^2)≤2/((z:ℝ)+1) := by
  by_cases hz:z≤R
  · let f:=fun p:ℕ=>-(2/(p:ℝ))
    have he : Ioc z R=Ico (z+1) (R+1) := by ext p;simp only [mem_Ioc,mem_Ico];omega
    rw [he]
    calc _ ≤ ∑p∈Ico (z+1) (R+1),(f (p+1)-f p) := by
           apply sum_le_sum;intro p hp
           have hp1:(1:ℝ)≤p := by exact_mod_cast (show 1≤p by have := (mem_Ico.mp hp).1;omega)
           dsimp only [f];push_cast;field_simp;nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (by linarith : (0:ℝ)≤p)]
         _ = f (R+1)-f (z+1) := sum_Ico_sub _ (by omega)
         _ ≤ _ := by dsimp [f];push_cast;linarith [show 0≤2/((R:ℝ)+1) by positivity]
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty];positivity

theorem fixedTargetDivisorRow_trivial (n d:ℕ) :
    fixedTargetDivisorRow n d ≤ (n:ℝ)/(d:ℝ)*Real.log n := by
  let S := (Ioc (n/4) (n/2)).filter (fun k=>d∣n-k)
  have hcard : S.card≤n/d := by
    rw [←Nat.card_multiples' n d]
    apply card_le_card_of_injOn (fun k:ℕ=>n-k)
    · intro k hk
      obtain ⟨hk,hd⟩:=mem_filter.mp hk
      obtain ⟨hl,hu⟩:=mem_Ioc.mp hk
      change n-k∈(range n.succ).filter _
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,hd⟩
    · intro k hk l hl he
      have hk':= (mem_Ioc.mp (mem_filter.mp hk).1).2
      have hl':= (mem_Ioc.mp (mem_filter.mp hl).1).2
      dsimp at he;omega
  unfold fixedTargetDivisorRow
  rw [←sum_filter]
  calc _ ≤ ∑_k∈S,Real.log n := by
         apply sum_le_sum;intro k hk
         have hh := (mem_Ioc.mp (mem_filter.mp hk).1).2
         unfold weight;split_ifs with h
         · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast (show k≤n by omega))
         · exact Real.log_natCast_nonneg n
       _ ≤ _ := by
         simp only [sum_const,nsmul_eq_mul]
         apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
         exact (by exact_mod_cast hcard : (S.card:ℝ)≤(n/d:ℕ)).trans Nat.cast_div_le

private theorem sf_row_nonneg (n d:ℕ) : 0≤fixedTargetDivisorRow n d :=
  sum_nonneg fun k _=>by split_ifs <;> first | exact sf_weight_nonneg k | rfl

theorem fixedTargetNonsquarefree_split (n z Y:ℕ) (hY:Y≤n/4) :
    fixedTargetNonsquarefreeMass n z ≤
      (∑p∈(Ioc z Y).filter (fun p=>p.Prime ∧ ¬p∣n),fixedTargetDivisorRow n (p^2))+
      (∑p∈Ioc Y n,fixedTargetDivisorRow n (p^2)) := by
  let I:=Ioc (n/4) (n/2)
  let S:=(fixedTargetBrunPrimeSurvivors n z).filter fun k=>¬Squarefree (n-k)
  let B:=(Ioc z Y).filter fun p=>p.Prime ∧ ¬p∣n
  let C:=Ioc Y n
  let f (k p:ℕ):ℝ:=if p^2∣n-k then weight k else 0
  have hf (k p:ℕ):0≤f k p := by dsimp only [f];split_ifs <;> first | exact sf_weight_nonneg _ | rfl
  have hSI : S⊆I := fun k hk=>(mem_filter.mp (mem_filter.mp hk).1).1
  have hsingle (k:ℕ)(hk:k∈S) : Real.log k≤(∑p∈B,f k p)+(∑p∈C,f k p) := by
    obtain ⟨hk0,hbad⟩:=mem_filter.mp hk
    obtain ⟨hI,hprime,hrough⟩:=mem_filter.mp hk0
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push Not at hbad
    obtain ⟨p,hp,hd⟩:=hbad
    have hd' : p^2∣n-k := by simpa only [sq] using hd
    have hdiv : p∣n-k := (dvd_mul_right p p).trans hd
    have hkn := (mem_Ioc.mp hI).2
    have hkl := (mem_Ioc.mp hI).1
    have hpos : 0<n-k := by omega
    have hsz : p≤n := (Nat.le_of_dvd hpos hdiv).trans (Nat.sub_le ..)
    have hw : f k p=Real.log k := by simp only [f,ite_eq_left hd',weight,ite_eq_left hprime]
    by_cases hpy:p≤Y
    · have hpn : ¬p∣n := by
        intro hh
        have hpk : p∣k := by simpa only [Nat.sub_sub_self (by omega : k≤n)] using Nat.dvd_sub hh hdiv
        have he:= (Nat.prime_dvd_prime_iff_eq hp hprime).mp hpk
        omega
      have hb:p∈B := mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_not_ge (fun hz=>hrough p hp hz hdiv),hpy⟩,hp,hpn⟩
      exact (hw.ge.trans (single_le_sum (fun p _=>hf k p) hb)).trans
        (le_add_of_nonneg_right (sum_nonneg fun p _=>hf k p))
    · have hc:p∈C := mem_Ioc.mpr ⟨by omega,hsz⟩
      exact (hw.ge.trans (single_le_sum (fun p _=>hf k p) hc)).trans
        (le_add_of_nonneg_left (sum_nonneg fun p _=>hf k p))
  unfold fixedTargetNonsquarefreeMass
  apply (sum_le_sum hsingle).trans
  calc _ ≤ ∑k∈I,((∑p∈B,f k p)+(∑p∈C,f k p)) := sum_le_sum_of_subset_of_nonneg hSI
         (fun k _ _=>add_nonneg (sum_nonneg fun p _=>hf k p) (sum_nonneg fun p _=>hf k p))
       _ = _ := by rw [sum_add_distrib,sum_comm (s:=I) (t:=B),sum_comm (s:=I) (t:=C)];rfl

/-- Uniform over every roughness cutoff; the two error terms beyond 4n/(z+1)
come from Siegel--Walfisz on squares and a direct count of large-square multiples. -/
theorem fixedTargetNonsquarefree_budget :
    ∃C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,∀z:ℕ,
      fixedTargetNonsquarefreeMass n z ≤ 4*(n:ℝ)/((z:ℝ)+1)+C*n/(Real.log n)^6+2*n/Real.log n := by
  obtain ⟨C,hC,hAP⟩:=fixedTarget_divisor_row_uniform 4 8
  refine ⟨C,hC,?_⟩
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hnlog : Tendsto (fun n:ℕ=>(Real.log n)^2/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_ofNat,Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [hAP,hl.eventually_ge_atTop 1,eventually_ge_atTop (2:ℕ),
    hnlog.eventually_lt_const (show 0<(1:ℝ)/4 by norm_num)] with n hp hL hn hsmall
  intro z
  let L:=Real.log (n:ℝ)
  let Y:=⌊L^2⌋₊
  let B:=(Ioc z Y).filter fun p=>p.Prime ∧ ¬p∣n
  let E:=C*(n:ℝ)/L^8
  have hnR:(0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hY: (Y:ℝ)≤L^2 := Nat.floor_le (sq_nonneg _)
  have hY': L^2 < (Y:ℝ)+1 := Nat.lt_floor_add_one _
  have hYN : Y≤n/4 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    have hh := (div_lt_iff₀ hnR).mp hsmall
    exact_mod_cast (show (Y:ℝ)*4≤n by change L^2<1/4*(n:ℝ) at hh; linarith only [hh,hY])
  have hrow {p:ℕ} (hb:p∈B) : fixedTargetDivisorRow n (p^2) ≤ 2*(n:ℝ)*(1/(p:ℝ)^2)+E := by
    have ⟨hm,hpp,hpn⟩:=mem_filter.mp hb
    have hpy := (mem_Ioc.mp hm).2
    have hpr : (p:ℝ)≤L^2 := (by exact_mod_cast hpy : (p:ℝ)≤Y).trans hY
    have h4 : ((p^2:ℕ):ℝ)≤L^4 := by
      push_cast
      calc _ ≤ (L^2)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hpr _
           _ = _ := by ring
    have hcp : n.Coprime (p^2) := (hpp.coprime_iff_not_dvd.mpr hpn).symm.pow_right _
    have hh := (abs_le.mp (hp (p^2) (pow_pos hpp.pos 2) h4 hcp)).2
    have h2 : (2:ℝ)≤p := by exact_mod_cast hpp.two_le
    have hφ : ((p^2).totient:ℝ)= (p:ℝ)*((p:ℝ)-1) := by
      rw [Nat.totient_prime_pow_succ hpp 1,pow_one,Nat.cast_mul,Nat.cast_sub hpp.one_le,Nat.cast_one]
    rw [hφ] at hh
    have hlength : ((n/2-n/4:ℕ):ℝ)≤n := by exact_mod_cast (show n/2-n/4≤n by omega)
    have hdp : 0<(p:ℝ)*((p:ℝ)-1) := by nlinarith only [h2,mul_nonneg (sub_nonneg.mpr h2) (Nat.cast_nonneg (α:=ℝ) p)]
    have hpos : (0:ℝ)<p := by linarith only [h2]
    have hden : (n:ℝ)/((p:ℝ)*((p:ℝ)-1)) ≤ 2*n*(1/(p:ℝ)^2) := by
      rw [←div_eq_mul_one_div,div_le_div_iff₀ hdp (sq_pos_of_pos hpos)]
      nlinarith only [mul_nonneg hnR.le (mul_nonneg (Nat.cast_nonneg (α:=ℝ) p) (sub_nonneg.mpr h2))]
    have hmain := (div_le_div_of_nonneg_right hlength hdp.le).trans hden
    change _ - _ ≤E at hh
    linarith only [hh,hmain]
  have hB : B.card≤Y := (card_filter_le ..).trans (by simp)
  have hBin : (∑p∈B,1/(p:ℝ)^2)≤2/((z:ℝ)+1) := (sum_le_sum_of_subset_of_nonneg (filter_subset ..)
    (fun p _ _=>by positivity)).trans (sf_inverse_tail z Y)
  have h1 : (∑p∈B,fixedTargetDivisorRow n (p^2)) ≤ 4*(n:ℝ)/((z:ℝ)+1)+C*n/L^6 := by
    apply (sum_le_sum (fun p h=>hrow h)).trans
    rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left hBin (by positivity : (0:ℝ)≤2*n)).trans_eq (by ring)
    · have hh : (B.card:ℝ)≤L^2 := (by exact_mod_cast hB : (B.card:ℝ)≤Y).trans hY
      apply (mul_le_mul_of_nonneg_right hh (by dsimp [E];positivity)).trans_eq
      dsimp [E];field_simp
  have h2 : (∑p∈Ioc Y n,fixedTargetDivisorRow n (p^2)) ≤ 2*n/L := by
    calc _ ≤ ∑p∈Ioc Y n,((n:ℝ)*L)*(1/(p:ℝ)^2) := by
           apply sum_le_sum;intro p _
           apply (fixedTargetDivisorRow_trivial n (p^2)).trans_eq
           push_cast;dsimp [L];ring
         _ = _ := by rw [←mul_sum]
         _ ≤ (n*L)*(2/((Y:ℝ)+1)) := mul_le_mul_of_nonneg_left (sf_inverse_tail _ _) (by positivity)
         _ ≤ _ := by
           calc _ ≤ (n*L)*(2/L^2) := by gcongr
                _ = _ := by field_simp
  exact (fixedTargetNonsquarefree_split n z Y hYN).trans (add_le_add h1 h2)

noncomputable def fixedTargetSquarefreeMass (n z:ℕ) : ℝ :=
  ∑k∈(fixedTargetBrunPrimeSurvivors n z).filter (fun k=>Squarefree (n-k)),Real.log k

theorem fixedTarget_squarefree_partition (n z:ℕ) :
    fixedTargetSquarefreeMass n z+fixedTargetNonsquarefreeMass n z=fixedTargetBrunSurvivorMass n z := by
  rw [fixedTarget_Brun_mass_eq_prime_sum]
  exact sum_filter_add_sum_filter_not _ _ _

private theorem sf_log_div_limit {w:ℕ→ℝ} (hw:Tendsto w atTop atTop) :
    Tendsto (fun n=>Real.log (w n)/w n) atTop (𝓝 0) := by
  simpa only [Function.comp_def,Real.rpow_one] using
    ((isLittleO_log_rpow_rpow_atTop (1:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp hw)

theorem fixedTargetNonsquarefree_polylog_small (z:ℕ→ℕ) (A:ℕ)
    (hz:Tendsto z atTop atTop) (hsize:∀ᶠ n:ℕ in atTop,(z n:ℝ)≤(Real.log n)^A)
    {ε:ℝ} (hε:0<ε) : ∀ᶠ n:ℕ in atTop,
      fixedTargetNonsquarefreeMass n (z n) ≤ ε*(n:ℝ)/(1+Real.log (z n)) := by
  obtain ⟨C,hC,hbud⟩:=fixedTargetNonsquarefree_budget
  let L:=fun n:ℕ=>Real.log (n:ℝ)
  let Z:=fun n:ℕ=>(z n:ℝ)
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hZ : Tendsto Z atTop atTop := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hz
  have lim (w:ℕ→ℝ) (hw:Tendsto w atTop atTop) (M:ℝ) :
      Tendsto (fun n=>(1+M*Real.log (w n))/w n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n=>1/w n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hw
    simpa only [add_div,mul_div_assoc,mul_zero,add_zero] using h1.add ((sf_log_div_limit hw).const_mul M)
  have hsmall := ((lim Z hZ 1).const_mul 4).add ((lim L hL (A:ℝ)).const_mul (C+2))
  simp only [one_mul,mul_zero,add_zero] at hsmall
  filter_upwards [hbud,hsize,hL.eventually_ge_atTop 1,hZ.eventually_ge_atTop 1,
    hsmall.eventually_lt_const hε] with n hb hsz hl hz' hh
  let D:=1+Real.log (Z n)
  have hD : 0<D := by dsimp only [D];linarith only [Real.log_nonneg hz']
  have hL' : 0<L n := lt_of_lt_of_le zero_lt_one hl
  have hZ' : 0<Z n := lt_of_lt_of_le zero_lt_one hz'
  have hlz:=Real.log_le_log hZ' hsz
  change Real.log (Z n)≤Real.log ((L n)^A) at hlz
  rw [Real.log_pow] at hlz
  have hD' : D≤1+(A:ℝ)*Real.log (L n) := add_le_add_right hlz _
  have hs6 : L n≤(L n)^6 := le_self_pow₀ hl (by decide)
  have hb' := hb (z n)
  change fixedTargetNonsquarefreeMass n (z n) ≤ 4*(n:ℝ)/(Z n+1)+C*n/(L n)^6+2*n/L n at hb'
  apply hb'.trans
  apply (le_div_iff₀ hD).mpr
  have hfst : (4*(n:ℝ)/(Z n+1))*D ≤ (4*(D/Z n))*(n:ℝ) := by
    calc _ ≤ (4*(n:ℝ)/(Z n))*D := by gcongr;linarith
         _ = _ := by ring
  have hsec : ((C*(n:ℝ)/(L n)^6)+2*n/L n)*D ≤ ((C+2)*((1+(A:ℝ)*Real.log (L n))/L n))*(n:ℝ) := by
    calc _ ≤ ((C*(n:ℝ)/(L n))+2*n/L n)*(1+(A:ℝ)*Real.log (L n)) := by
           apply mul_le_mul _ hD' hD.le (by positivity)
           exact add_le_add (div_le_div_of_nonneg_left (by positivity) hL' hs6) le_rfl
         _ = _ := by ring
  change 4*(D/Z n)+(C+2)*((1+(A:ℝ)*Real.log (L n))/L n)<ε at hh
  nlinarith only [hfst,hsec,mul_le_mul_of_nonneg_right hh.le (Nat.cast_nonneg (α:=ℝ) n)]

theorem fixedTargetNonsquarefree_nearPower_small {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop, fixedTargetNonsquarefreeMass n (brunNearPowerCutoff n) ≤
      ε*(n:ℝ)/(1+Real.log (brunNearPowerCutoff n)) := by
  apply fixedTargetNonsquarefree_polylog_small _ 1 brunNearPowerCutoff_tendsto _ hε
  filter_upwards [brunNearPower_parameters] with n hn
  have hne : brunNearPowerRank n≠0 := by obtain ⟨m,hm⟩:=hn.1;omega
  have hz : brunNearPowerCutoff n≤⌊Real.log n⌋₊ := (Nat.le_self_pow hne _).trans hn.2.2.1
  simpa only [pow_one] using (show (brunNearPowerCutoff n:ℝ)≤Real.log n from
    (by exact_mod_cast hz : (brunNearPowerCutoff n:ℝ)≤(⌊Real.log n⌋₊:ℕ)).trans (Nat.floor_le (Real.log_natCast_nonneg n)))


theorem fixedTargetSquarefree_nearPower_mass :
    ∀ᶠ n:ℕ in atTop, Even n →
      (n:ℝ)/(4096*(1+Real.log (brunNearPowerCutoff n))) ≤
        fixedTargetSquarefreeMass n (brunNearPowerCutoff n) := by
  filter_upwards [fixedTargetNonsquarefree_nearPower_small (ε:=1/4096) (by norm_num),
    brunNearPower_parameters,fixedTarget_Brun_power_rank_mass] with n he hp hm
  intro hn
  let z:=brunNearPowerCutoff n
  let k:=brunNearPowerRank n
  let D:=1+Real.log (z:ℝ)
  have hD : 0<D := by dsimp only [D];positivity
  have hlevel : ((z^k:ℕ):ℝ)≤Real.log n := (by exact_mod_cast hp.2.2.1 : ((z^k:ℕ):ℝ)≤(⌊Real.log n⌋₊:ℕ)).trans
    (Nat.floor_le (Real.log_natCast_nonneg n))
  have h := hm hn z k hp.2.1 hp.1 hlevel hp.2.2.2
  have hh:=fixedTarget_squarefree_partition n z
  change (n:ℝ)/(2048*D) ≤ _ at h
  change _≤(1/4096:ℝ)*n/D at he
  change (n:ℝ)/(4096*D)≤_
  have hid : (n:ℝ)/(2048*D)= (n:ℝ)/(4096*D)+(1/4096:ℝ)*n/D := by field_simp;ring
  rw [hid] at h
  change fixedTargetNonsquarefreeMass n z ≤ _ at he
  linarith only [h,he,hh]

end GoldbachPartial
