import VerifiedCommonWidthKernel
import VerifiedFixedUniformMajorArcs

namespace GoldbachPartial
open Finset Filter MeasureTheory ExtendedArcCoefficient
open scoped Classical Topology

noncomputable def uniformPrimeDenominator (b N : ℕ) : ℕ := ⌊(Real.log N)^b⌋₊
noncomputable def uniformPrimeWidth (b N : ℕ) : ℝ := 2*(uniformPrimeDenominator b N:ℝ)/N
noncomputable def uniformPrimeMinor (b N : ℕ) : Set ℝ :=
  Set.Icc 0 1 \ fixedUniformMajorArcs (uniformPrimeDenominator b N) (uniformPrimeWidth b N)

def UniformPrimeApproximation : Prop :=
  ∀ A b : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ q a : ℕ, 0<q → (q:ℝ)≤(Real.log N)^b →
    ∀ β : ℝ, (N:ℝ)*|β|≤(Real.log N)^b →
      ‖centralPrimeWave N ((a:ℝ)/q+β)-GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N β‖
        ≤ C*N/(Real.log N)^A

theorem uniformPrime_geometry (b : ℕ) (hb : 0<b) :
    ∀ᶠ N : ℕ in atTop, let Q := uniformPrimeDenominator b N
      let ρ := uniformPrimeWidth b N
      16≤Q ∧ 0<ρ ∧ ρ≤1/(4*(Q:ℝ)^2) ∧ ρ≤1/2 ∧
      (∀ m : ℕ, N≤2*m → 16/ρ≤(m:ℝ)) := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hq := tendsto_nat_floor_atTop.comp ((tendsto_pow_atTop hb.ne').comp ht)
  have hp := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (OAI.LargePrimeGaps.eventually_log_rpow_le_rpow ((3*b+1:ℕ):ℝ) (by norm_num : (0:ℝ)<1))
  filter_upwards [hq.eventually_ge_atTop 16,ht.eventually_ge_atTop 8,hp,eventually_ge_atTop (1:ℕ)] with N h16 hl hx hN
  let Q := uniformPrimeDenominator b N
  let L := Real.log N
  let ρ := uniformPrimeWidth b N
  change 16≤Q at h16
  change 8≤L at hl
  have hQ : (Q:ℝ)≤L^b := Nat.floor_le (pow_nonneg (Real.log_natCast_nonneg _) _)
  have hQr : (16:ℝ)≤Q := by exact_mod_cast h16
  have hQp : (0:ℝ)<Q := by linarith
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hL : 0≤L := Real.log_natCast_nonneg N
  have hpow : L^(3*b+1)≤(N:ℝ) := by
    simpa only [L,Function.comp_def,Real.rpow_natCast,Real.rpow_one] using hx
  have h8 : 8*(Q:ℝ)^3 ≤ (N:ℝ) := by
    apply le_trans _ hpow
    rw [pow_succ L (3*b), mul_comm 3 b,pow_mul]
    have hh := mul_le_mul (pow_le_pow_left₀ hQp.le hQ 3) hl (by norm_num : (0:ℝ)≤8) (pow_nonneg (pow_nonneg hL _) _)
    linarith only [hh]
  have hρ : 0<ρ := by dsimp only [ρ,uniformPrimeWidth];change 0<2*(Q:ℝ)/N;positivity
  have hh : ρ≤1/(4*(Q:ℝ)^2) := by
    change 2*(Q:ℝ)/N ≤ 1/(4*(Q:ℝ)^2)
    rw [div_le_div_iff₀ hNp (by positivity)]
    linarith only [h8]
  refine ⟨h16,hρ,hh,hh.trans (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (by nlinarith)),?_⟩
  intro m hm
  have hi : (N:ℝ)≤2*(m:ℝ) := by exact_mod_cast hm
  change 16/(2*(Q:ℝ)/N) ≤ (m:ℝ)
  field_simp
  nlinarith only [hi,mul_le_mul_of_nonneg_right hQr (Nat.cast_nonneg (α:=ℝ) m)]

theorem uniformPrime_major_floor_of_approximation (hlocal : UniformPrimeApproximation)
    (b : ℕ) (hb : 0<b) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m≤N → N≤2*m → Even m →
      (m:ℝ)/12 ≤ (fixedPrimeArcMode (fixedUniformMajorArcs (uniformPrimeDenominator b N)
        (uniformPrimeWidth b N)) N (m:ℤ)).re := by
  let k := 3*b+1
  obtain ⟨C,hC,hSW⟩ := hlocal k (b+1)
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [uniformPrime_geometry b hb,hSW,ht.eventually_ge_atTop (max 2 (768*C)),
    eventually_ge_atTop (2:ℕ)] with N hg hs hL' hn
  let L := Real.log N
  let Q := uniformPrimeDenominator b N
  let ρ := uniformPrimeWidth b N
  let D := C*N/L^k
  change max 2 (768*C) ≤ L at hL'
  have hL2 := (le_max_left ..).trans hL'
  have hL : 0<L := by linarith
  have hN : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hNp : (0:ℝ)<N := zero_lt_one.trans_le hN
  have hQ : (Q:ℝ)≤L^b := Nat.floor_le (pow_nonneg hL.le _)
  obtain ⟨h16,hρ,hgap,hhalf,hsize⟩ := hg
  change 16≤Q at h16
  have hQpos : 0<Q := by omega
  have h2Q : 2*(Q:ℝ)≤L^(b+1) := by
    rw [pow_succ, mul_comm (L^b)]
    exact mul_le_mul hL2 hQ (Nat.cast_nonneg _) hL.le
  have hclose (q : ℕ) (hq : q∈Icc 1 Q) (a : ℕ) (_ha : a∈fixedUniformNumerators q)
      (β : ℝ) (hβ : β∈Set.Icc (-ρ) ρ) : ‖centralPrimeWave N ((a:ℝ)/q+β) -
        GoldbachMajorArc.unitMean q a*dirichletGeometricKernel N β‖ ≤ D := by
    apply hs q a (mem_Icc.mp hq).1 ((by exact_mod_cast (mem_Icc.mp hq).2 : (q:ℝ)≤Q).trans
      ((by linarith [Nat.cast_nonneg (α:=ℝ) Q] : (Q:ℝ)≤2*Q).trans h2Q))
    apply (mul_le_mul_of_nonneg_left (abs_le.mpr hβ) hNp.le).trans
    change (N:ℝ)*(2*Q/N) ≤ _
    calc _ = 2*(Q:ℝ) := by field_simp
         _ ≤ _ := h2Q
  have hcost : 8*(Q:ℝ)^2*ρ*D*((N:ℝ)+1) ≤ (N:ℝ)/24 := by
    have h' := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) Q) hQ 3
    have hc := (le_max_right 2 (768*C)).trans hL'
    have hstep : 8*(Q:ℝ)^2*ρ*D*((N:ℝ)+1) = (16*C/L^k)*((Q:ℝ)^3*((N:ℝ)+1)) := by
      dsimp only [ρ,D,uniformPrimeWidth]
      change 8*(Q:ℝ)^2*(2*Q/N)*(C*N/L^k)*((N:ℝ)+1) = _
      field_simp
      ring
    rw [hstep]
    calc _ ≤ (16*C/L^k)*((L^b)^3*(2*N)) := by gcongr; linarith
         _ = (32*C/L)*N := by dsimp only [k];rw [pow_succ,mul_comm 3 b,pow_mul];field_simp;ring
         _ ≤ _ := by
            have h32 : 32*C/L ≤ 1/24 := (div_le_iff₀ hL).mpr (by linarith only [hc])
            linarith only [mul_le_mul_of_nonneg_right h32 (Nat.cast_nonneg (α:=ℝ) N)]
  intro m hm hNm he
  have hbound := fixedUniformMajorArcs_error hQpos hρ.le hgap (show 0≤D by dsimp [D];positivity) N m hclose
  have hfloor := common_width_model_floor N m Q hm he hQpos hρ hhalf (hsize m hNm)
  change (m:ℝ)/6 ≤ ((∑q∈Icc 1 Q,GoldbachMajorArc.coefficient q m)*fixedUniformModelKernel N (m:ℤ) ρ).re at hfloor
  have hdist := (Complex.re_le_norm _).trans ((norm_sub_rev _ _).le.trans (hbound.trans hcost))
  simp only [Complex.sub_re] at hdist
  have hcmp : (N:ℝ)≤2*(m:ℝ) := by exact_mod_cast hNm
  linarith only [hdist,hfloor,hcmp]

end GoldbachPartial