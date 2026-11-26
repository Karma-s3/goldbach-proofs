import NaturalPrimeGapArcs
import NaturalDirichletTubeGeometry
import VariableDenominatorTubes

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient
open GoldbachDeepFourth (deepTube)

theorem naturalTubeUnion_integral_rows (R Q M:ℕ) (h : 2*Q<M) (F:ℝ→ℂ) (hF : Continuous F) :
    (∫ t in naturalTubeUnion R Q M, F t) =
      ∑ j ∈ Ico R Q, ∑ a : (ZMod (j+1))ˣ,
        ∫ t in -(naturalTubeRadius M (j+1))..(naturalTubeRadius M (j+1)),
          F (t+((a:ZMod (j+1)).val:ℝ)/(j+1:ℕ)) := by
  classical
  have hd : variableTubesDisjoint R Q (naturalTubeRadius M) := naturalTube_pairwise h
  have hu := integral_biUnion_finset (f:=F) («μ»:=volume) (naturalTubeIndices R Q)
    (s:=fun i => deepTube (naturalTubeRadius M (i.1+1)) (i.1+1) i.2)
    (fun _ _ => measurableSet_Icc) hd (fun _ _ => hF.continuousOn.integrableOn_Icc)
  refine hu.trans ?_
  rw [Finset.sum_sigma]
  apply sum_congr rfl
  intro j hj
  symm
  apply sum_bij (fun (a : (ZMod (j+1))ˣ) _ => (a : ZMod (j+1)).val)
  · intro a _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ he
    exact Units.ext (ZMod.val_injective (j+1) he)
  · intro a ha
    obtain ⟨har,hac⟩ := mem_filter.mp ha
    exact ⟨ZMod.unitOfCoprime a hac,mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp har)⟩
  · intro a _
    let r := naturalTubeRadius M (j+1)
    let c := ((a:ZMod (j+1)).val:ℝ)/(j+1:ℕ)
    have hr : 0≤r := by dsimp [r,naturalTubeRadius]; positivity
    change (∫ t in -r..r, F (t+c)) = ∫ t in Set.Icc (c-r) (c+r), F t
    rw [intervalIntegral.integral_comp_add_right,show -r+c=c-r by ring,add_comm r c,
      intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]

noncomputable def signedFiberKernel (s : Finset ℕ) (m : ℕ→ℤ) (w : ℕ→ℝ) (t:ℝ) : ℂ :=
  ∑ k ∈ s, (w k:ℂ)*E (((m k):ℝ)*t)

theorem signedFiberKernel_continuous (s : Finset ℕ) (m : ℕ→ℤ) (w : ℕ→ℝ) :
    Continuous (signedFiberKernel s m w) := by unfold signedFiberKernel E; fun_prop

theorem signedFiberKernel_integral_rows (R Q M:ℕ) (h : 2*Q<M)
    (s : Finset ℕ) (m : ℕ→ℤ) (w : ℕ→ℝ) :
    (∫ t in naturalTubeUnion R Q M, signedFiberKernel s m w t) =
      ∑ j ∈ Ico R Q, signedFiberRow (j+1) s m w (naturalTubeRadius M (j+1)) := by
  rw [naturalTubeUnion_integral_rows R Q M h _ (signedFiberKernel_continuous s m w)]
  apply sum_congr rfl
  intro j _
  let r := naturalTubeRadius M (j+1)
  let c (a : (ZMod (j+1))ˣ) := ((a:ZMod (j+1)).val:ℝ)/(j+1:ℕ)
  unfold signedFiberKernel signedFiberRow
  calc
    _ = ∑ a : (ZMod (j+1))ˣ, ∑ k ∈ s,
        ∫ t in -r..r, (w k:ℂ)*E (((m k):ℝ)*(t+c a)) := by
      apply sum_congr rfl
      intro a _
      apply intervalIntegral.integral_finsetSum
      intro k _
      apply Continuous.intervalIntegrable
      unfold E
      fun_prop
    _ = _ := by rw [sum_comm]; simp_rw [intervalIntegral.integral_const_mul,Finset.mul_sum]; rfl

theorem signedFiberKernel_naturalTube_bound (N R Q M : ℕ) (hsep : 2*Q<M)
    (s : Finset ℕ) (m : ℕ→ℤ) (w : ℕ→ℝ) {A:ℝ} (hA : 0≤A) (hm : Set.InjOn m ↑s)
    (hb : ∀ k∈s, (m k).natAbs≤N) (hw : ∀ k∈s, |w k|≤A) :
    ‖∫ t in naturalTubeUnion R Q M, signedFiberKernel s m w t‖ ≤
      4*A/(M:ℝ)*((N:ℝ)*(1+Real.log Q)^2+Q) := by
  rw [signedFiberKernel_integral_rows R Q M hsep]
  let J := Ico R Q
  have hM' : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hh : ∑ j ∈ J, ((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ) ≤ (1+Real.log Q)^2 :=
    (sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (mem_Ico.mp hj).2)
        (fun _ _ _ => by positivity)).trans (signedFiber_divisor_harmonic Q)
  calc
    _ ≤ ∑ j ∈ J, (4*A/(M:ℝ))*((N:ℝ)*(((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ))+1) := by
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro j _
      exact (signedFiberRow_bound (j+1) N s m w (ρ:=naturalTubeRadius M (j+1))
        (by unfold naturalTubeRadius; positivity) hA hm hb hw).trans_eq (by
        have hq : (0:ℝ)<(j+1:ℕ) := by positivity
        unfold naturalTubeRadius
        field_simp)
    _ = (4*A/(M:ℝ))*((N:ℝ)*(∑ j ∈ J, ((j+1).divisors.card:ℝ)/((j+1:ℕ):ℝ)) + (J.card:ℝ)) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum]
      simp
    _ ≤ _ := by
      have hcard : (J.card:ℝ)≤Q := by dsimp only [J]; rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le Q R
      gcongr

noncomputable def primeGapKernel (n d : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ (range (n+1)).filter (fun p => p+d≤n),
    (((weight p:ℂ)*E ((p:ℝ)*t))*((weight (p+d):ℂ)*E (((p+d:ℕ):ℝ)*t)))*E (-(n:ℝ)*t)

theorem primeGapKernel_naturalTube_bound (n d R Q M : ℕ) (hsep : 2*Q<M) :
    ‖∫ t in naturalTubeUnion R Q M, primeGapKernel n d t‖ ≤
      4*(Real.log (n:ℝ))^2/(M:ℝ)*((n:ℝ)*(1+Real.log Q)^2+Q) := by
  let s := (range (n+1)).filter (fun p => p+d≤n)
  let m (p:ℕ) := 2*(p:ℤ)+d-n
  let w (p:ℕ) := weight p*weight (p+d)
  have he : primeGapKernel n d = signedFiberKernel s m w := by
    funext t
    apply sum_congr rfl
    intro p _
    dsimp only [w,m]
    push_cast
    rw [show (2*(p:ℝ)+d-n)*t = ((p:ℝ)*t+(p+d)*t)+ -(n:ℝ)*t by ring,phase_add,phase_add]
    ring
  rw [he]
  have weight_nonneg (p:ℕ) : 0≤weight p := by unfold weight; split_ifs <;> first | exact Real.log_natCast_nonneg p | exact le_rfl
  have hlog (p:ℕ) (hp:p≤n) : weight p≤Real.log (n:ℝ) := by
    unfold weight
    split_ifs with h
    · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hp)
    · exact Real.log_natCast_nonneg n
  apply signedFiberKernel_naturalTube_bound n R Q M hsep s m w (sq_nonneg _)
  · intro p hp r hr he
    dsimp only [m] at he
    omega
  · intro p hp
    obtain ⟨hpn,hpd⟩ := mem_filter.mp hp
    have hp' := mem_range.mp hpn
    dsimp only [m]; omega
  · intro p hp
    obtain ⟨hpn,hpd⟩ := mem_filter.mp hp
    dsimp only [w]
    rw [abs_of_nonneg (mul_nonneg (weight_nonneg _) (weight_nonneg _)),sq]
    exact mul_le_mul (hlog _ (by have := mem_range.mp hpn; omega)) (hlog _ hpd) (weight_nonneg _) (Real.log_natCast_nonneg _)

theorem primeGapKernel_band_naturalTube_bound (n R Q M : ℕ) (H:Finset ℕ) (hR : 0<R)
    (hsep : 2*Q<M) :
    ‖∫ t in naturalTubeUnion R Q M, ∑ d ∈ H, primeGapKernel n d t‖ ≤
      (H.card:ℝ)*(4*(Real.log (n:ℝ))^2/(M:ℝ)*((n:ℝ)*(1+Real.log Q)^2+Q)) := by
  have hsub := naturalTubeUnion_inside_unit (B:=R) (R:=Q) hR (by omega : 0<M)
  have hi (d:ℕ) : IntegrableOn (primeGapKernel n d) (naturalTubeUnion R Q M) := by
    have hc : Continuous (primeGapKernel n d) := by unfold primeGapKernel E; fun_prop
    exact hc.integrableOn_Icc.mono_set hsub
  rw [integral_finsetSum H (fun d _ => hi d)]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _d ∈ H, (4*(Real.log (n:ℝ))^2/(M:ℝ)*((n:ℝ)*(1+Real.log Q)^2+Q)) :=
      sum_le_sum fun d _ => primeGapKernel_naturalTube_bound n d R Q M hsep
    _ = _ := by simp [nsmul_eq_mul]

theorem primeGapKernel_disjoint_natural_band (n R Q : ℕ) (H : Finset ℕ) (hR:0<R) (hQ:0<Q) :
    ‖∫ t in naturalTubeUnion R Q (3*Q), ∑ d ∈ H, primeGapKernel n d t‖ ≤
      (H.card:ℝ)*(4*(Real.log (n:ℝ))^2/(3*(Q:ℝ))*((n:ℝ)*(1+Real.log Q)^2+Q)) := by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    primeGapKernel_band_naturalTube_bound n R Q (3*Q) H hR (by omega)

end GoldbachPartial