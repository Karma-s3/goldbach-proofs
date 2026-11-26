import Mathlib.NumberTheory.EulerProduct.Basic
import DyadicCorrelationReduction

namespace GoldbachPartial
open Finset Filter
open scoped Topology

noncomputable def smoothRootEuler (q:ℕ) : ℝ :=
  ∏p∈q.primeFactors,(1-(Real.sqrt p)⁻¹)⁻¹

private noncomputable def smoothRootHom : ℕ →* ℝ where
  toFun n := (Real.sqrt n)⁻¹
  map_one' := by simp
  map_mul' a b := by simp [Real.sqrt_mul (Nat.cast_nonneg (α:=ℝ) a),mul_comm]

private noncomputable def smoothInvHom : ℕ →* ℝ where
  toFun n := (n:ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by simp [mul_comm]

theorem smoothRoot_hasSum (q:ℕ) :
    HasSum (fun m : Nat.factoredNumbers q.primeFactors => (Real.sqrt (m:ℕ))⁻¹) (smoothRootEuler q) := by
  have h (p:ℕ) (hp:p.Prime) : ‖smoothRootHom p‖<1 := by
    change ‖(Real.sqrt (p:ℝ))⁻¹‖<1
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),inv_lt_one_iff₀]
    apply Or.inr
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p),Real.sqrt_nonneg (p:ℝ),show (1:ℝ)<p by exact_mod_cast hp.one_lt]
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric (f:=smoothRootHom) (fun {p} => h p) q.primeFactors).2
  have he : q.primeFactors.filter Nat.Prime = q.primeFactors := filter_eq_self.mpr fun _ hp => Nat.prime_of_mem_primeFactors hp
  simpa only [he,smoothRootEuler,smoothRootHom,MonoidHom.coe_mk,OneHom.coe_mk] using hh

theorem smoothReciprocal_hasSum (q:ℕ) (hq:0<q) :
    HasSum (fun m : Nat.factoredNumbers q.primeFactors => ((m:ℕ):ℝ)⁻¹) ((q:ℝ)/q.totient) := by
  have h (p:ℕ) (hp:p.Prime) : ‖smoothInvHom p‖<1 := by
    change ‖(p:ℝ)⁻¹‖<1
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),inv_lt_one_iff₀]
    exact Or.inr (by exact_mod_cast hp.one_lt)
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric (f:=smoothInvHom) (fun {p} => h p) q.primeFactors).2
  have he : q.primeFactors.filter Nat.Prime = q.primeFactors := filter_eq_self.mpr fun _ hp => Nat.prime_of_mem_primeFactors hp
  rw [he] at hh
  change HasSum _ (∏p∈q.primeFactors,(1-(p:ℝ)⁻¹)⁻¹) at hh
  rw [prod_inv_distrib] at hh
  have hphi : (q.totient:ℝ) = q*(∏p∈q.primeFactors,(1-(p:ℝ)⁻¹)) := by
    have hv := congrArg (fun v:ℚ => (v:ℝ)) (Nat.totient_eq_mul_prod_factors q)
    push_cast at hv
    exact hv
  have hn : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  have hφ : (q.totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hfac : ∏p∈q.primeFactors,(1-(p:ℝ)⁻¹)=(q.totient:ℝ)/q := by
    apply (eq_div_iff hn).mpr
    rw [mul_comm,hphi]
  rw [hfac,inv_div] at hh
  exact hh

theorem smoothRootEuler_le_smallPower {ε:ℝ} (hε:0<ε) :
    ∃C:ℝ, 0<C ∧ ∀q:ℕ,0<q → smoothRootEuler q≤C*(q:ℝ)^ε := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp (((tendsto_rpow_atTop hε).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 4)
  refine ⟨4^B,by positivity,?_⟩
  intro q hq
  let L (p:ℕ) := (1-(Real.sqrt p)⁻¹)⁻¹
  have hl (p:ℕ) (hp:p∈q.primeFactors) : 0≤L p ∧ L p≤4 := by
    have hpr : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hs : 4/3≤Real.sqrt p := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p),Real.sqrt_nonneg (p:ℝ)]
    have hspos : 0<Real.sqrt p := by linarith
    have hi : (Real.sqrt p)⁻¹≤3/4 := (inv_le_iff_one_le_mul₀ hspos).mpr (by linarith)
    have hd : 0<1-(Real.sqrt p)⁻¹ := by linarith
    exact ⟨(inv_pos.mpr hd).le,(inv_le_iff_one_le_mul₀ hd).mpr (by linarith)⟩
  let S := q.primeFactors.filter (fun p=>p<B)
  have hsub : S ⊆ range B := fun p hp => mem_range.mpr (mem_filter.mp hp).2
  have hcard : S.card≤B := (card_le_card hsub).trans (card_range B).le
  have hprod : (∏p∈q.primeFactors,(p:ℝ)) ≤ q := by
    rw [←Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  calc
    _ ≤ ∏ p∈q.primeFactors, ((if p<B then (4:ℝ) else 1)*(p:ℝ)^ε) := by
      apply Finset.prod_le_prod₀ (fun p hp => (hl p hp).1)
      intro p hp
      by_cases hc:p<B
      · rw [ite_eq_left hc]
        have h1 : (1:ℝ)≤(p:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le) hε.le
        exact (hl p hp).2.trans (le_mul_of_one_le_right (by norm_num) h1)
      · rw [ite_eq_right hc,one_mul]
        exact (hl p hp).2.trans (hB p (by omega))
    _ = 4^S.card*(∏p∈q.primeFactors,(p:ℝ))^ε := by
      rw [prod_mul_distrib,Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p),←prod_filter]
      simp [S]
    _ ≤ _ := mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard)
      (Real.rpow_le_rpow (prod_nonneg fun p _ => Nat.cast_nonneg p) hprod hε.le)
      (by positivity) (by positivity)

theorem smoothRoot_finite_sum_le (q:ℕ) (I:Finset ℕ) (hI:∀m∈I,m∈Nat.factoredNumbers q.primeFactors) :
    (∑m∈I,(Real.sqrt m)⁻¹) ≤ smoothRootEuler q := by
  classical
  rw [←sum_subtype_of_mem (fun m:ℕ=>(Real.sqrt m)⁻¹) hI]
  let h := smoothRoot_hasSum q
  rw [←h.tsum_eq]
  exact h.summable.sum_le_tsum _ (fun m _ => by positivity)

def resonantSmoothUpTo (q X:ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun u:ℕ => u.primeFactors ⊆ q.primeFactors)

private theorem smooth_mem {q X u:ℕ} (h:u∈resonantSmoothUpTo q X) :
    u∈Nat.factoredNumbers q.primeFactors :=
  Nat.mem_factoredNumbers_of_primeFactors_subset (Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp h).1).1) (mem_filter.mp h).2

theorem resonantSmooth_root_sum (q X:ℕ) :
    (∑u∈resonantSmoothUpTo q X,(Real.sqrt u)⁻¹) ≤ smoothRootEuler q :=
  smoothRoot_finite_sum_le _ _ fun _ hu => smooth_mem hu

theorem resonantSmooth_card (q X:ℕ) :
    ((resonantSmoothUpTo q X).card:ℝ) ≤ Real.sqrt X*smoothRootEuler q := by
  let I := resonantSmoothUpTo q X
  calc
    _ = ∑_u∈I,(1:ℝ) := by simp [I]
    _ ≤ ∑u∈I,Real.sqrt X*(Real.sqrt u)⁻¹ := by
      apply sum_le_sum
      intro u hu
      have hx := mem_Icc.mp (mem_filter.mp hu).1
      have hr : 0<Real.sqrt (u:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hx.1)
      rw [←div_eq_mul_inv,le_div_iff₀ hr,one_mul]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hx.2)
    _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (resonantSmooth_root_sum q X) (Real.sqrt_nonneg _)

theorem resonantSmooth_reciprocal_tail (q X:ℕ) (hq:0<q) :
    0 ≤ (X:ℝ)*((q:ℝ)/q.totient)-(∑u∈resonantSmoothUpTo q X,(X:ℝ)/u) ∧
    (X:ℝ)*((q:ℝ)/q.totient)-(∑u∈resonantSmoothUpTo q X,(X:ℝ)/u) ≤ Real.sqrt X*smoothRootEuler q := by
  classical
  let I := resonantSmoothUpTo q X
  let J := I.subtype (fun m => m∈Nat.factoredNumbers q.primeFactors)
  let f (m:Nat.factoredNumbers q.primeFactors) := (X:ℝ)*(m.val:ℝ)⁻¹
  let g (m:Nat.factoredNumbers q.primeFactors) := Real.sqrt X*(Real.sqrt m.val)⁻¹
  let h (m:Nat.factoredNumbers q.primeFactors) := if m∈J then f m else 0
  have hf : HasSum f ((X:ℝ)*((q:ℝ)/q.totient)) := (smoothReciprocal_hasSum q hq).mul_left _
  have hg : HasSum g (Real.sqrt X*smoothRootEuler q) := (smoothRoot_hasSum q).mul_left _
  have hh : HasSum h (∑u∈I,(X:ℝ)/u) := by
    have hsum : HasSum h (∑m∈J,h m) := hasSum_sum_of_ne_finset_zero (f:=h) (s:=J) (fun m hm => by simp [h,hm])
    have he : (∑m∈J,h m)=(∑m∈J,f m) := sum_congr rfl fun m hm => by simp [h,hm]
    rw [he] at hsum
    change HasSum h (∑m∈I,_) 
    rw [←sum_subtype_of_mem (fun m:ℕ => (X:ℝ)/m) (fun m (hm:m∈I) => smooth_mem hm)]
    simpa only [div_eq_mul_inv,J,f] using hsum
  have hhf (m) : h m≤f m := by
    by_cases hm:m∈J
    · simp [h,hm]
    · simp [h,hm,f]; positivity
  have hfg (m) : f m≤h m+g m := by
    by_cases hm:m∈J
    · simpa only [h,ite_eq_left hm,le_add_iff_nonneg_right] using (show 0≤g m by dsimp only [g]; positivity)
    · have hx : X<m.val := by
        by_contra! hle
        apply hm
        apply mem_subtype.mpr
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero m.property.1,hle⟩,Nat.primeFactors_subset_of_mem_factoredNumbers m.property⟩
      have hv : 0<(m.val:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero m.property.1
      have hrv : 0<Real.sqrt (m.val:ℝ) := Real.sqrt_pos.mpr hv
      have hs := Real.sqrt_le_sqrt (show (X:ℝ)≤m.val by exact_mod_cast hx.le)
      simp only [h,ite_eq_right hm,zero_add,f,g,←div_eq_mul_inv]
      apply (div_le_div_iff₀ hv hrv).mpr
      have hblock := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (X:ℝ))
      have hsize := mul_le_mul_of_nonneg_right hblock hrv.le
      rw [Real.mul_self_sqrt (Nat.cast_nonneg X),mul_assoc,Real.mul_self_sqrt hv.le] at hsize
      exact hsize
  have hle := hh.summable.tsum_le_tsum hhf hf.summable
  have hup := hf.summable.tsum_le_tsum hfg (hh.add hg).summable
  rw [hh.tsum_eq,hf.tsum_eq] at hle
  rw [hf.tsum_eq,(hh.add hg).tsum_eq] at hup
  constructor <;> linarith

end GoldbachPartial