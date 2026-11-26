import TruncatedRamanujanMixed
import GRHWindowCertificate
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace GoldbachPartial
open Finset Filter
open scoped Topology ArithmeticFunction.vonMangoldt

noncomputable def grhUnitResidueError (X d a:ℕ) : ℝ :=
  (∑k∈(Icc 1 X).filter (fun k=>k ≡ a [MOD d]),Λ k) - (X:ℝ)/d.totient

theorem grhUnitResidueError_identity (X d a:ℕ) [NeZero d] (ha:a.Coprime d) :
    (d.totient:ℂ)*(grhUnitResidueError X d a:ℂ)=
      ∑χ:DirichletCharacter ℂ d,χ ((a:ZMod d)⁻¹)*grhPsi0 χ (X:ℝ) := by
  classical
  let _ : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod d)ˣ) :=
    ⟨⟨_,Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩,rootsOfUnity.isCyclic ..⟩
  have hu := (ZMod.isUnit_iff_coprime a d).mpr ha
  have hp : (d.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos d)).ne'
  have hui : IsUnit ((a:ZMod d)⁻¹) := by
    rw [←hu.unit_spec,ZMod.inv_coe_unit];exact Units.isUnit _
  have hc : (∑χ:DirichletCharacter ℂ d,χ ((a:ZMod d)⁻¹)*(if χ=1 then (X:ℂ) else 0))=(X:ℂ) := by
    simp [mul_ite,MulChar.one_apply hui]
  unfold grhPsi0
  simp only [Nat.floor_natCast,Complex.ofReal_natCast,mul_sub,sum_sub_distrib,hc]
  unfold grhUnitResidueError
  rw [Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_natCast,mul_sub,
    mul_div_cancel₀ _ hp,Complex.ofReal_sum,Finset.sum_filter]
  congr 1
  simp only [mul_sum]
  rw [sum_comm (s:=univ)]
  apply sum_congr rfl
  intro k _
  have hz : ((a:ZMod d)=(k:ZMod d)) ↔ k ≡ a [MOD d] := by
    rw [eq_comm,ZMod.natCast_eq_natCast_iff]
  rw [show (∑χ:DirichletCharacter ℂ d,χ ((a:ZMod d)⁻¹)*((Λ k:ℂ)*χ (k:ZMod d)))=
      (Λ k:ℂ)*(∑χ:DirichletCharacter ℂ d,χ ((a:ZMod d)⁻¹)*χ (k:ZMod d)) by
        rw [mul_sum];apply sum_congr rfl;intro χ _;ring]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu]
  simp only [hz];split <;> simp [mul_comm]

theorem grhUnitResidueError_bound_of_uniform (hψ:grhAllUniform) :
    ∃K:ℝ,0<K ∧ ∀X d a:ℕ, 2≤X → 0<d → a.Coprime d →
      |grhUnitResidueError X d a|≤K*Real.sqrt X*(Real.log (2*(d:ℝ)*X))^2 := by
  obtain ⟨K,hK,hu⟩ := hψ
  refine ⟨K,hK,?_⟩
  intro X d a hX hd ha
  let _ : NeZero d := ⟨hd.ne'⟩
  let _ : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod d)ˣ) :=
    ⟨⟨_,Complex.isPrimitiveRoot_exp _ (NeZero.ne _)⟩,rootsOfUnity.isCyclic ..⟩
  let B := K*Real.sqrt X*(Real.log (2*(d:ℝ)*X))^2
  have hchar (χ:DirichletCharacter ℂ d) : ‖χ ((a:ZMod d)⁻¹)*grhPsi0 χ (X:ℝ)‖≤B := by
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans
    exact hu d χ X (by exact_mod_cast hX)
  have hc : Fintype.card (DirichletCharacter ℂ d)=d.totient := by
    simpa only [Nat.card_eq_fintype_card] using DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  have hbound := (norm_sum_le ..).trans (sum_le_sum (fun χ (_:χ∈univ)=>hchar χ))
  rw [←grhUnitResidueError_identity X d a ha,norm_mul,Complex.norm_natCast,Complex.norm_real,
    Real.norm_eq_abs,sum_const,card_univ,nsmul_eq_mul,hc] at hbound
  exact (le_of_mul_le_mul_left hbound (by exact_mod_cast Nat.totient_pos.mpr hd))

theorem primeSmallProgressionError_unit {n d:ℕ} (hc:d.Coprime n) :
    primeSmallProgressionError n d=grhUnitResidueError (n-1) d n := by
  unfold primeSmallProgressionError grhUnitResidueError
  rw [ite_eq_left hc,Finset.sum_filter]
  have hset : Ioo 0 n=Icc 1 (n-1) := by ext k;simp only [mem_Ioo,mem_Icc];omega
  congr 1
  rw [←hset]
  apply sum_congr rfl
  intro k hk
  have ht := Nat.modEq_iff_dvd' (n:=d) ((mem_Ioo.mp hk).2.le)
  simp only [ht]

theorem primeSmallProgressionError_unit_terminal (hψ:grhAllUniform) :
    ∃K:ℝ,0<K ∧ ∀n:ℕ,3≤n →
      let R := terminalPrimeArcCutoff n
      |∑d∈(Icc 1 R).filter (fun d=>d.Coprime n),
        crtLambdaCoefficient d * primeSmallProgressionError n d| ≤
          K*(n:ℝ)/(terminalPrimeArcLog n)^2 := by
  obtain ⟨K,hK,hrow⟩ := grhUnitResidueError_bound_of_uniform hψ
  refine ⟨9*K,by positivity,?_⟩
  intro n hn
  let L := terminalPrimeArcLog n
  let R := terminalPrimeArcCutoff n
  let X := n-1
  let I := (Icc 1 R).filter (fun d=>d.Coprime n)
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg n)
  have hL : 0<L := by linarith
  have hR : (R:ℝ)≤Real.sqrt n/L^5 := Nat.floor_le (by positivity)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  have hrootn : Real.sqrt n≤(n:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),sq_nonneg (Real.sqrt n-1)]
  have hrn : (R:ℝ)≤n := hR.trans ((div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hL1)).trans hrootn)
  have hX : 2≤X := by dsimp [X];omega
  have hXn : (X:ℝ)≤n := by exact_mod_cast Nat.sub_le n 1
  have hX1 : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
  have hrX := Real.sqrt_le_sqrt hXn
  have hln : Real.log n≤L := by dsimp [L,terminalPrimeArcLog];linarith
  let B := K*Real.sqrt n*(3*L)^2*L
  have hB : 0≤B := by dsimp [B];positivity
  have hpoint (d:ℕ) (hd:d∈I) : |crtLambdaCoefficient d*primeSmallProgressionError n d|≤B := by
    obtain ⟨hdI,hc⟩ := mem_filter.mp hd
    obtain ⟨hd0,hDR⟩ := mem_Icc.mp hdI
    have hd1 : (1:ℝ)≤d := by exact_mod_cast hd0
    have hd' : (0:ℝ)<d := by linarith
    have hdn : (d:ℝ)≤n := (by exact_mod_cast hDR : (d:ℝ)≤R).trans hrn
    have hld := (Real.log_le_log hd' hdn).trans hln
    have harg : 1≤2*(d:ℝ)*X := by nlinarith [mul_le_mul hd1 hX1 (by norm_num) (Nat.cast_nonneg (α:=ℝ) d)]
    have hlg0 := Real.log_nonneg harg
    have hlog : Real.log (2*(d:ℝ)*X)≤3*L := by
      rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) hd'.ne']
      have hf := Real.log_le_log (by linarith : (0:ℝ)<X) hXn
      have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      dsimp only [L,terminalPrimeArcLog] at hld hL1 ⊢
      linarith
    have hmu : |(ArithmeticFunction.moebius d:ℝ)|≤1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
    have hcoef : |crtLambdaCoefficient d|≤L := by
      rw [crtLambdaCoefficient,abs_mul,abs_neg,abs_of_nonneg (Real.log_natCast_nonneg _)]
      exact (mul_le_of_le_one_left (Real.log_natCast_nonneg _) hmu).trans hld
    have hrow' := hrow X d n hX hd0 hc.symm
    rw [abs_mul,primeSmallProgressionError_unit hc,mul_comm]
    apply (mul_le_mul hrow' hcoef (abs_nonneg _) (by positivity)).trans
    dsimp [B];gcongr
  change |∑d∈I,crtLambdaCoefficient d*primeSmallProgressionError n d|≤_
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum hpoint).trans
  rw [sum_const,nsmul_eq_mul]
  have hcard : (I.card:ℝ)≤(R:ℝ) := by
    exact_mod_cast (card_filter_le _ _).trans_eq (by simp : (Icc 1 R).card=R)
  calc _ ≤ (Real.sqrt n/L^5)*B := mul_le_mul_of_nonneg_right (hcard.trans hR) hB
       _ = _ := by
         change _=(9*K)*(n:ℝ)/L^2
         dsimp only [B]
         calc _ = (9*K)*(Real.sqrt n)^2/L^2 := by field_simp;ring
              _ = _ := by rw [Real.sq_sqrt hn0.le]

theorem primeSmallProgressionError_unit_terminal_small (hψ:grhAllUniform) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ n:ℕ in atTop,
      |∑d∈(Icc 1 (terminalPrimeArcCutoff n)).filter (fun d=>d.Coprime n),
        crtLambdaCoefficient d*primeSmallProgressionError n d|≤ε*(n:ℝ) := by
  obtain ⟨K,hK,h⟩ := primeSmallProgressionError_unit_terminal hψ
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (3:ℕ),hlog.eventually_ge_atTop (K/ε)] with n hn hh
  apply (h n hn).trans
  let L := terminalPrimeArcLog n
  have hL1 : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg _)
  have hL : 0<L := by linarith
  have hk : K/ε≤L := hh.trans (by change Real.log n≤1+Real.log n;linarith)
  have he : K≤ε*L^2 := ((div_le_iff₀ hε).mp hk).trans ((mul_comm L ε).le.trans
    (mul_le_mul_of_nonneg_left (le_self_pow₀ hL1 (by decide:2≠0)) hε.le))
  change K*(n:ℝ)/L^2≤ε*n
  apply (div_le_iff₀ (pow_pos hL 2)).mpr
  simpa only [mul_comm,mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) n)
end GoldbachPartial
