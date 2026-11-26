import VerifiedNativeCharacterConductor
namespace GoldbachPartial
open Finset Filter
open scoped Classical Topology
theorem native_twice_prime_conductor {p:ℕ} (hp:p.Prime)
    (χ:DirichletCharacter ℂ (2*p)) (hχ:χ≠1) : p≤χ.conductor := by
  classical
  let _ : NeZero (2*p) := ⟨Nat.mul_ne_zero (by decide) hp.ne_zero⟩
  by_contra! hf
  have hcop:= (hp.coprime_iff_not_dvd.mpr (fun hd=>hf.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero χ.conductor_ne_zero) hd))).symm
  have hdiv:χ.conductor∣2:=hcop.dvd_of_dvd_mul_right χ.conductor_dvd_level
  have hthrough:χ.FactorsThrough 2 :=
    (χ.mem_conductorSet_iff_conductor_dvd (dvd_mul_right 2 p)).mpr hdiv
  have hcard:Fintype.card (DirichletCharacter ℂ 2)≤1:=by
    rw [←Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    decide
  let _:Subsingleton (DirichletCharacter ℂ 2):=Fintype.card_le_one_iff_subsingleton.mp hcard
  apply hχ
  rw [hthrough.eq_changeLevel,Subsingleton.elim hthrough.χ₀ 1,DirichletCharacter.changeLevel_one]

theorem native_twice_prime_cyclic {p:ℕ} (hp:p.Prime)(hodd:Odd p) :
    IsCyclic (DirichletCharacter ℂ (2*p)) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero p:=⟨hp.ne_zero⟩
  let _ : NeZero (2*p):=⟨Nat.mul_ne_zero (by decide) hp.ne_zero⟩
  let hpφ:=Nat.totient_mul (Nat.coprime_two_left.mpr hodd)
  have hcard (q:ℕ)[NeZero q]: Fintype.card (DirichletCharacter ℂ q)=q.totient:=by
    rw [←Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  let f:=DirichletCharacter.changeLevel (R:=ℂ) (show p∣2*p by exact dvd_mul_left p 2)
  have hf:Function.Bijective f:= (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨DirichletCharacter.changeLevel_injective _,by rw [hcard,hcard,hpφ,Nat.totient_two,one_mul]⟩
  apply (MulEquiv.ofBijective f hf).isCyclic.mp
  exact (DirichletCharacter.mulEquiv_units ℂ p).some.isCyclic.mpr inferInstance

theorem native_cyclic_low_order_card {n:ℕ} [NeZero n] [IsCyclic (DirichletCharacter ℂ n)]
    (K:ℕ) (S:Finset (DirichletCharacter ℂ n)) (hs:∀χ∈S,orderOf χ≤K) : S.card≤K^2:=by
  classical
  have hsub:S⊆ Finset.univ.filter (fun χ:DirichletCharacter ℂ n => orderOf χ∈Icc 1 K):=fun χ hχ=>
    mem_filter.mpr ⟨mem_univ _,mem_Icc.mpr ⟨orderOf_pos χ,hs χ hχ⟩⟩
  apply (Finset.card_le_card hsub).trans
  rw [←Finset.sum_card_fiberwise_eq_card_filter]
  calc _ ≤ ∑ _k∈Finset.Icc 1 K,K := by
         apply Finset.sum_le_sum;intro k hk
         have hsub':Finset.univ.filter (fun χ:DirichletCharacter ℂ n => orderOf χ=k) ⊆ Finset.univ.filter (fun χ:DirichletCharacter ℂ n=> χ^k=1):=by
           intro χ hχ
           exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [←(Finset.mem_filter.mp hχ).2,pow_orderOf_eq_one]⟩
         exact (Finset.card_le_card hsub').trans ((IsCyclic.card_pow_eq_one_le (Finset.mem_Icc.mp hk).1).trans (Finset.mem_Icc.mp hk).2)
       _ = _ := by simp [sq]

open private native_character_log_pay from VerifiedNativeCharacterConductor

theorem native_sparse_nonprincipal_saving (hψ:grhAllUniform) {δ:ℝ} (hδ:0<δ) :
    ∀ᶠ n:ℕ in atTop,∀ (_:NeZero n) (S:Finset (DirichletCharacter ℂ n)), 1∉S →
      (S.card:ℝ)≤(n:ℝ)^(1-δ) →
      ‖∑χ∈S,χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)‖/(n.totient:ℝ) ≤ (n:ℝ)^(1-δ/2) := by
  obtain ⟨C,hC,hE⟩:=native_nonprincipal_energy_of_uniform_psi hψ
  let a:=δ/4
  have ha:0<a:=by dsimp [a];linarith
  filter_upwards [native_divisor_eventually_rpow ha,native_character_log_pay C hC ha,eventually_ge_atTop (2:ℕ)] with n hτ hlog hn
  intro _ S hs hS
  have hn':0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hφ:0<(n.totient:ℝ):=by exact_mod_cast Nat.totient_pos.mpr (show 0<n by omega)
  let τ:ℝ:=n.divisors.card
  have hratio:(n:ℝ)/n.totient ≤ 2*τ:=by
    apply (model_totient_ratio_le_divisor_reciprocals n (by omega)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc _ ≤ ∑_d∈n.divisors,(1:ℝ) := sum_le_sum (fun d hd=>inv_le_one_of_one_le₀ (by exact_mod_cast Nat.pos_of_mem_divisors hd))
         _ = τ := by simp [τ]
  calc _ ≤ ((S.card:ℝ)*(C*n*Real.log (2*(n:ℝ)^2)^4))/(n.totient:ℝ) :=
          div_le_div_of_nonneg_right (hE n hn S hs) hφ.le
       _ = (S.card:ℝ)*(C*Real.log (2*(n:ℝ)^2)^4)*((n:ℝ)/n.totient) := by ring
       _ ≤ (S.card:ℝ)*(C*Real.log (2*(n:ℝ)^2)^4)*(2*τ) := mul_le_mul_of_nonneg_left hratio (by positivity)
       _ = (S.card:ℝ)*τ*(2*C*Real.log (2*(n:ℝ)^2)^4) := by ring
       _ ≤ (n:ℝ)^(1-δ)*(n:ℝ)^a*(n:ℝ)^a := by
         apply mul_le_mul _ hlog (by positivity) (by positivity)
         exact mul_le_mul hS hτ (by positivity) (by positivity)
       _ = _ := by
         simp only [←Real.rpow_add hn']
         congr 1
         dsimp [a];ring

theorem native_cyclic_low_order_saving (hψ:grhAllUniform) {δ:ℝ} (hδ:0<δ) :
    ∀ᶠ n:ℕ in atTop,∀ (_:NeZero n) (_:IsCyclic (DirichletCharacter ℂ n)) (S:Finset (DirichletCharacter ℂ n)),
      1∉S → (∀χ∈S,(orderOf χ:ℝ)≤(n:ℝ)^(1/2-δ)) →
      ‖∑χ∈S,χ (-1)*(Complex.normSq (primeUnitTransform n χ):ℂ)‖/(n.totient:ℝ) ≤ (n:ℝ)^(1-δ) := by
  filter_upwards [native_sparse_nonprincipal_saving hψ (show 0<2*δ by linarith)] with n hh
  intro _ _ S hs hS
  let K:=⌊(n:ℝ)^(1/2-δ)⌋₊
  have hK:(K:ℝ)≤(n:ℝ)^(1/2-δ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hc:S.card≤K^2:=native_cyclic_low_order_card K S (fun χ hχ=>Nat.le_floor (hS χ hχ))
  have hb:(S.card:ℝ)≤(n:ℝ)^(1-2*δ):=calc
    _ ≤ (K:ℝ)^2 :=by exact_mod_cast hc
    _ ≤ ((n:ℝ)^(1/2-δ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hK _
    _ = _ :=by rw [←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
               congr 1
               push_cast;ring
  simpa only [show 2*δ/2=δ by ring] using hh _ S hs hb

end GoldbachPartial

