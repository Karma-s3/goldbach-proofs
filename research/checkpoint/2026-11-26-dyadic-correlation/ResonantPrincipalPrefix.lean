import ResonantCoprimeCoefficients
import ResonantSmoothRankin

namespace GoldbachPartial
open Finset
open scoped ArithmeticFunction.vonMangoldt

theorem resonant_principal_character_mass (q Y : ℕ) :
    grhPsi0 (1 : DirichletCharacter ℂ q) (Y:ℝ) =
      ((∑ v∈(Icc 1 Y).filter (fun v => q.Coprime v), Λ v) - (Y:ℝ):ℝ) := by
  classical
  unfold grhPsi0
  rw [Nat.floor_natCast,ite_eq_left rfl,Complex.ofReal_sub,Complex.ofReal_natCast,Complex.ofReal_sum,sum_filter]
  congr 1
  apply sum_congr rfl
  intro k _
  by_cases hc : q.Coprime k
  · rw [ite_eq_left hc,MulChar.one_apply ((ZMod.isUnit_iff_coprime k q).mpr hc.symm),mul_one]
  · rw [ite_eq_right hc,MulChar.map_nonunit _ (by rw [ZMod.isUnit_iff_coprime]; exact fun h => hc h.symm),mul_zero]

theorem resonant_principal_error (hψ : grhAllUniform) :
    ∃ K : ℝ, 0<K ∧ ∀ (q Y : ℕ), 0<q → 1≤Y →
      |(∑ v∈(Icc 1 Y).filter (fun v => q.Coprime v),Λ v)-(Y:ℝ)| ≤
        K*Real.sqrt Y*(Real.log (2*(q:ℝ)*Y))^2 + 1 := by
  obtain ⟨K,hK,h⟩ := hψ
  refine ⟨K,hK,?_⟩
  intro q Y hq hY
  by_cases hy : Y=1
  · subst Y
    have hone : ((Icc 1 (1:ℕ)).filter (fun v => q.Coprime v))={1} := by
      rw [Icc_self,filter_singleton,ite_eq_left (Nat.coprime_one_right _)]
    rw [hone,sum_singleton]
    simp only [Nat.cast_one,Real.sqrt_one,mul_one]
    have hv : Λ 1=0 := ArithmeticFunction.vonMangoldt_apply_one
    rw [hv,zero_sub,abs_neg,abs_one]
    linarith only [mul_nonneg hK.le (sq_nonneg (Real.log (2*(q:ℝ))))]
  · have : NeZero q := ⟨hq.ne'⟩
    have h2 : (2:ℝ)≤Y := by exact_mod_cast (show 2≤Y by omega)
    have h' := h q 1 Y h2
    rw [resonant_principal_character_mass,Complex.norm_real,Real.norm_eq_abs] at h'
    linarith only [h']

theorem resonant_inner_eq {q Y : ℕ} (hY : 1≤Y) :
    (∑ v∈(Icc 1 Y).filter (fun v => q.Coprime v),
        (Λ v - (if v=1 then Real.log q else 0))) =
      (∑ v∈(Icc 1 Y).filter (fun v => q.Coprime v),Λ v)-Real.log q := by
  rw [sum_sub_distrib]
  have hmem : 1∈(Icc 1 Y).filter (fun v => q.Coprime v) :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,hY⟩,Nat.coprime_one_right q⟩
  rw [sum_ite_eq' _ _ _,ite_eq_left hmem]

theorem resonantReducedCoefficient_finite_approx (hψ : grhAllUniform) :
    ∃ K : ℝ, 0<K ∧ ∀ (q X : ℕ), 0<q → 0<X →
      let S := (Icc 1 X).filter (fun u : ℕ => u.primeFactors ⊆ q.primeFactors)
      |(∑ j∈Icc 1 X,resonantReducedCoefficient q j) -
       (ArithmeticFunction.moebius q:ℝ)*(∑ u∈S,(X:ℝ)/u)| ≤
        (K*(Real.log (2*(q:ℝ)*X))^2+2+Real.log q)*Real.sqrt X*
          ∑ u∈S,1/Real.sqrt u := by
  obtain ⟨K,hK,h⟩ := resonant_principal_error hψ
  refine ⟨K,hK,?_⟩
  intro q X hq hX S
  let e := fun u : ℕ => ∑ v∈(Icc 1 (X/u)).filter (fun v => q.Coprime v),
    (Λ v - (if v=1 then Real.log q else 0))
  let L := Real.log (2*(q:ℝ)*X)
  let C := K*L^2+2+Real.log q
  have hmu : |(ArithmeticFunction.moebius q:ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q))
  have hu (u : ℕ) (hu : u∈S) : |e u - (X:ℝ)/u| ≤ C*Real.sqrt X*(1/Real.sqrt u) := by
    obtain ⟨hu1,huX⟩ := mem_Icc.mp (mem_filter.mp hu).1
    let Y := X/u
    let F := Real.sqrt X/Real.sqrt u
    have hY : 1≤Y := Nat.div_pos huX hu1
    have hu' : (0:ℝ)<u := by exact_mod_cast hu1
    have hq' : (1:ℝ)≤q := by exact_mod_cast hq
    have hY' : (1:ℝ)≤Y := by exact_mod_cast hY
    have hyX : (Y:ℝ)≤X := by exact_mod_cast (Nat.div_le_self X u)
    have hy : (Y:ℝ)≤(X:ℝ)/u := (le_div_iff₀ hu').mpr (by exact_mod_cast Nat.div_mul_le_self X u)
    have hyu : (X:ℝ)/u < (Y:ℝ)+1 := by
      apply (div_lt_iff₀ hu').mpr
      exact_mod_cast (show X<(Y+1)*u by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ X hu1)
    have hF : 1≤F := by
      rw [show F=Real.sqrt ((X:ℝ)/u) from (Real.sqrt_div (Nat.cast_nonneg _) _).symm]
      exact Real.one_le_sqrt.mpr (hY'.trans hy)
    have hS : Real.sqrt Y ≤ F := by
      rw [show F=Real.sqrt ((X:ℝ)/u) from (Real.sqrt_div (Nat.cast_nonneg _) _).symm]
      exact Real.sqrt_le_sqrt hy
    have hbase : 1≤2*(q:ℝ)*Y := by nlinarith only [one_le_mul_of_one_le_of_one_le hq' hY']
    have hlog : Real.log (2*(q:ℝ)*Y) ≤ L :=
      Real.log_le_log (zero_lt_one.trans_le hbase) (mul_le_mul_of_nonneg_left hyX (by positivity))
    have hscale := mul_le_mul (mul_le_mul_of_nonneg_left hS hK.le)
      (pow_le_pow_left₀ (Real.log_nonneg hbase) hlog 2) (sq_nonneg _) (by positivity : 0≤K*F)
    have hp := h q Y hq hY
    have hrest : |e u - (X:ℝ)/u| ≤ K*F*L^2+2+Real.log q := by
      rw [abs_le] at hp ⊢
      dsimp only [e]
      rw [resonant_inner_eq hY]
      constructor <;> linarith only [hp.1,hp.2,hscale,hy,hyu,Real.log_natCast_nonneg q]
    have hbig := mul_le_mul_of_nonneg_left hF (show 0≤2+Real.log q by linarith [Real.log_natCast_nonneg q])
    apply hrest.trans
    change _ ≤ C*(Real.sqrt X)*(1/Real.sqrt u)
    rw [show C*Real.sqrt X*(1/Real.sqrt u)=C*F by dsimp only [F]; ring]
    dsimp only [C]
    linarith only [hbig]
  rw [resonantReducedCoefficient_sum hq X,←mul_sub,abs_mul]
  change |(ArithmeticFunction.moebius q:ℝ)| * |(∑ u∈S,e u)-(∑ u∈S,(X:ℝ)/u)| ≤ _
  rw [←sum_sub_distrib]
  apply (mul_le_of_le_one_left (abs_nonneg _) hmu).trans
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact (sum_le_sum hu).trans_eq (mul_sum ..).symm

theorem resonantReducedCoefficient_prefix_bound (hψ : grhAllUniform) :
    ∃ K : ℝ, 0<K ∧ ∀ (q X : ℕ), 0<q → 0<X → ∀ j≤X,
      |(∑ v∈Icc 1 j,resonantReducedCoefficient q v) -
        ((ArithmeticFunction.moebius q:ℝ)*((q:ℝ)/q.totient))*(j:ℝ)| ≤
        (K*(Real.log (2*(q:ℝ)*X))^2 + 3 + Real.log q)*Real.sqrt X*smoothRootEuler q := by
  obtain ⟨K,hK,h⟩ := resonantReducedCoefficient_finite_approx hψ
  refine ⟨K,hK,?_⟩
  intro q X hq hX j hj
  let L := Real.log (2*(q:ℝ)*X)
  let C := K*L^2+2+Real.log q
  have hC : 0≤C := by dsimp [C]; linarith [mul_nonneg hK.le (sq_nonneg L),Real.log_natCast_nonneg q]
  have hZ : 0≤smoothRootEuler q := (sum_nonneg (fun _ _ => by positivity)).trans (resonantSmooth_root_sum q j)
  rcases Nat.eq_zero_or_pos j with rfl|hj0
  · simp only [Icc_eq_empty_of_lt (by decide : 0<1),sum_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero]
    apply mul_nonneg _ hZ
    apply mul_nonneg _ (Real.sqrt_nonneg _)
    change 0≤K*L^2+3+Real.log q
    dsimp only [C] at hC; linarith
  let s := ∑ u∈resonantSmoothUpTo q j,(j:ℝ)/u
  let m := (j:ℝ)*((q:ℝ)/q.totient)
  let μq := (ArithmeticFunction.moebius q:ℝ)
  have hsj := resonantSmooth_reciprocal_tail q j hq
  change 0≤m-s ∧ m-s≤Real.sqrt j*smoothRootEuler q at hsj
  have hh := h q j hq hj0
  have hr := resonantSmooth_root_sum q j
  simp only [←one_div] at hr
  change |(∑v∈Icc 1 j,resonantReducedCoefficient q v)-μq*s|≤
    (K*(Real.log (2*(q:ℝ)*j))^2+2+Real.log q)*Real.sqrt j*(∑ u∈resonantSmoothUpTo q j,1/Real.sqrt u) at hh
  have hjr : (1:ℝ)≤j := by exact_mod_cast hj0
  have hqr : (1:ℝ)≤q := by exact_mod_cast hq
  have hbase : 1≤2*(q:ℝ)*j := by nlinarith only [one_le_mul_of_one_le_of_one_le hqr hjr]
  have hlog : Real.log (2*(q:ℝ)*j)≤L :=
    Real.log_le_log (zero_lt_one.trans_le hbase) (mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (by positivity))
  have hlogpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg hbase) hlog 2) hK.le
  have hcoeff : K*(Real.log (2*(q:ℝ)*j))^2+2+Real.log q ≤ C := by dsimp only [C]; linarith only [hlogpow]
  have hs := Real.sqrt_le_sqrt (show (j:ℝ)≤X by exact_mod_cast hj)
  have hl : |(∑v∈Icc 1 j,resonantReducedCoefficient q v)-μq*s|≤C*Real.sqrt X*smoothRootEuler q := by
    apply hh.trans
    exact mul_le_mul (mul_le_mul hcoeff hs (Real.sqrt_nonneg _) hC) hr (sum_nonneg fun _ _ => by positivity) (by positivity)
  have hμ : |μq|≤1 := by dsimp [μq]; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=q))
  have herr : |μq*s-μq*m|≤Real.sqrt X*smoothRootEuler q := by
    rw [←mul_sub,abs_mul,abs_sub_comm,abs_of_nonneg hsj.1]
    exact (mul_le_of_le_one_left hsj.1 hμ).trans (hsj.2.trans (mul_le_mul_of_nonneg_right hs hZ))
  rw [show ((ArithmeticFunction.moebius q:ℝ)*((q:ℝ)/q.totient))*(j:ℝ)=μq*m by dsimp [μq,m];ring]
  apply (abs_sub_le _ (μq*s) _).trans
  change _ ≤ (K*L^2+3+Real.log q)*Real.sqrt X*smoothRootEuler q
  dsimp only [C] at hl
  linarith only [hl,herr]

end GoldbachPartial