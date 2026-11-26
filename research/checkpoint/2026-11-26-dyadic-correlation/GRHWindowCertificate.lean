import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace GoldbachPartial
noncomputable section
open Finset
/-- GRH specializes a truncated, multiplicity-weighted explicit formula at T = x. -/
theorem psi_uniform_of_window_data {A C q x : ℝ} (hA : 0≤A) (hC : 0≤C)
    (hq : 1≤q) (hx : 2≤x) (P : ℂ) (S : Finset ℂ) (m : ℂ → ℕ)
    (hline : ∀ z ∈ S, z.re=1/2)
    (hcount : ∑ z ∈ S.filter (fun z => |z.im|≤1), (m z:ℝ)*1 ≤ C*Real.log (3*q))
    (hhi : ∑ z ∈ S, (m z:ℝ)*(if 1 < |z.im| then 1/‖z‖ else 0) ≤ C*Real.log (q*x)^2)
    (hformula : ‖P + ∑ z ∈ S, (m z:ℂ)*((x:ℂ)^z/z)‖ ≤
      A*(x*Real.log (q*x*x)^2/x + Real.log (q*x) +
        ∑ z ∈ S.filter (fun z => |z.im|≤1), (m z:ℝ)*(1/‖z‖))) :
    ‖P‖ ≤ (A*(5+2*C)+3*C+1)*Real.sqrt x*Real.log (2*q*x)^2 := by
  let L := Real.log (2*q*x)
  have hx0 : 0<x := by linarith
  have hq0 : 0<q := by linarith
  have hs := Real.one_le_sqrt.mpr (show 1≤x by linarith)
  have hL : 1≤L := by
    have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h₂
    have hnum : (2:ℝ)^2 ≤ 2*q*x := by nlinarith [mul_le_mul_of_nonneg_right hq hx0.le]
    have hp := Real.log_le_log (by norm_num : (0:ℝ)<2^2) hnum
    rw [Real.log_pow] at hp
    dsimp [L]
    norm_num at hp
    linarith
  have hL2 : L ≤ L^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (show 0≤L by linarith)]
  have hqx : 0 ≤ Real.log (q*x) := Real.log_nonneg (by nlinarith [mul_le_mul_of_nonneg_right hq hx0.le])
  have hxx : 0 ≤ Real.log (q*x*x) := Real.log_nonneg (by
    have h₁ := mul_le_mul_of_nonneg_right hq hx0.le
    nlinarith [mul_le_mul_of_nonneg_right h₁ hx0.le, sq_nonneg (x-1)])
  have hl₁ : Real.log (q*x) ≤ L := Real.log_le_log (by positivity) (by nlinarith [mul_pos hq0 hx0])
  have hl₂ : Real.log (3*q) ≤ L := Real.log_le_log (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hx hq0.le])
  have hl₃ : Real.log (q*x*x) ≤ 2*L := by
    have ha : q*x*x ≤ (2*q*x)^2 := by
      have h := mul_le_mul_of_nonneg_right hq (by positivity : 0≤q*x*x)
      nlinarith [sq_nonneg (q*x)]
    have hb := Real.log_le_log (by positivity) ha
    rw [Real.log_pow] at hb
    simpa [L] using hb
  let low := S.filter (fun z => |z.im|≤1)
  let f := fun z : ℂ => (m z:ℝ)*(1/‖z‖)
  have hc₁ : (∑ z ∈ low, f z) ≤ 2*C*L := by
    calc
      _ ≤ 2*(∑ z ∈ low, (m z:ℝ)*1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun z hz => ?_)
        have hz' := hline z (Finset.mem_filter.mp hz).1
        have hRe := Complex.re_le_norm z
        rw [hz'] at hRe
        have hv : 1/‖z‖ ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
        simpa only [f,mul_one,mul_comm (2:ℝ)] using mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α := ℝ) (m z))
      _ ≤ _ := by
        have hl := mul_le_mul_of_nonneg_left hl₂ hC
        dsimp [low]
        linarith only [hcount,hl]
  have hcT : (∑ z ∈ S, f z) ≤ 3*C*L^2 := by
    have hsplit : (∑ z ∈ S, f z) =
        (∑ z ∈ low, f z)+(∑ z ∈ S, (m z:ℝ)*(if 1 < |z.im| then 1/‖z‖ else 0)) := by
      rw [show (∑ z ∈ low, f z) = ∑ z ∈ S, if |z.im|≤1 then f z else 0 from Finset.sum_filter ..,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : |z.im|≤1 <;> simp [f,h,not_lt_of_ge,lt_of_not_ge]
    rw [hsplit]
    have hsq := pow_le_pow_left₀ hqx hl₁ 2
    nlinarith only [hc₁,hhi,mul_le_mul_of_nonneg_left hsq hC,mul_le_mul_of_nonneg_left hL2 hC]
  have hzsum : ‖∑ z ∈ S, (m z:ℂ)*((x:ℂ)^z/z)‖ ≤ Real.sqrt x*(3*C*L^2) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ = Real.sqrt x*(∑ z ∈ S, f z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [norm_mul,norm_div,Complex.norm_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hx0,hline z hz,
          Real.sqrt_eq_rpow]
        unfold f
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcT (Real.sqrt_nonneg _)
  have hsqr := pow_le_pow_left₀ hxx hl₃ 2
  have hform : ‖P + ∑ z ∈ S, (m z:ℂ)*((x:ℂ)^z/z)‖ ≤ A*((5+2*C)*L^2) := by
    refine hformula.trans (mul_le_mul_of_nonneg_left ?_ hA)
    rw [show x*Real.log (q*x*x)^2/x = Real.log (q*x*x)^2 by field_simp]
    change _ + _ + (∑ z ∈ low, f z) ≤ _
    nlinarith only [hsqr,hl₁,hL2,hc₁,mul_le_mul_of_nonneg_left hL2 hC]
  let Z := ∑ z ∈ S, (m z:ℂ)*((x:ℂ)^z/z)
  have hp := norm_sub_le (P+Z) Z
  rw [add_sub_cancel_right] at hp
  have hbase : 0≤A*((5+2*C)*L^2) := by positivity
  have hscale := mul_le_mul_of_nonneg_right hs hbase
  change ‖P‖ ≤ (A*(5+2*C)+3*C+1)*Real.sqrt x*L^2
  change ‖Z‖ ≤ _ at hzsum
  change ‖P+Z‖ ≤ _ at hform
  nlinarith only [hp,hform,hzsum,hscale,mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg L)]

open scoped ArithmeticFunction
open Classical in
noncomputable def grhPsi0 {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt k:ℝ):ℂ)*χ (k:ZMod q)) -
    (if χ=1 then (x:ℂ) else 0)

variable (Lfun : {q : ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℂ)

def grhZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) : Set ℂ :=
  {z | 0<z.re ∧ z.re<1 ∧ |z.im-t|≤T ∧ Lfun χ z=0}

variable (mult : {q : ℕ} → [NeZero q] → DirichletCharacter ℂ q → ℂ → ℕ)

noncomputable def grhComplexSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ z ∈ grhZeros Lfun χ t T, (mult χ z:ℂ)*f z

noncomputable def grhRealSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t T : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ᶠ z ∈ grhZeros Lfun χ t T, (mult χ z:ℝ)*f z

abbrev grhStripInput : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ),
    0<z.re → z.re<1 → Lfun χ z=0 → z.re=1/2

abbrev grhFiniteInput : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ), (grhZeros Lfun χ t T).Finite

abbrev grhZeroCountInput : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ T : ℝ, 2≤T →
    grhRealSum Lfun mult χ 0 T (fun z => if 1 < |z.im| then 1/‖z‖ else 0) ≤ C*Real.log (q*T)^2 ∧
    grhRealSum Lfun mult χ 0 1 (fun _ => 1) ≤ C*Real.log (3*q)

abbrev grhExplicitInput : Prop :=
  ∃ A : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ x T : ℝ, 2≤T → T≤x →
    ‖grhPsi0 χ x + grhComplexSum Lfun mult χ 0 T (fun z => (x:ℂ)^z/z)‖ ≤
      A*(x*Real.log (q*x*T)^2/T + Real.log (q*x) + grhRealSum Lfun mult χ 0 1 (fun z => 1/‖z‖))

/-- The four inputs are direct instances of the audited upstream declarations. -/
theorem uniform_primitive_psi_of_GRH_inputs (hgrh : grhStripInput Lfun) (hfin : grhFiniteInput Lfun)
    (hZ : grhZeroCountInput Lfun mult) (hE : grhExplicitInput Lfun mult) :
    ∃ K : ℝ, 0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
        ∀ x : ℝ, 2≤x → ‖grhPsi0 χ x‖ ≤ K*Real.sqrt x*Real.log (2*q*x)^2 := by
  classical
  obtain ⟨A,hA⟩ := hE
  obtain ⟨C,hC⟩ := hZ
  refine ⟨|A| * (5+2 * |C|)+3 * |C| + 1,by positivity,?_⟩
  intro q _ χ hp x hx
  let S := (hfin q χ 0 x).toFinset
  let S₁ := (hfin q χ 0 1).toFinset
  have hsub : S.filter (fun z => |z.im|≤1) = S₁ := by
    ext z
    simp only [S,S₁,Finset.mem_filter,Set.Finite.mem_toFinset]
    change ((0<z.re ∧ z.re<1 ∧ |z.im-0|≤x ∧ Lfun χ z=0) ∧ |z.im|≤1) ↔
      (0<z.re ∧ z.re<1 ∧ |z.im-0|≤1 ∧ Lfun χ z=0)
    simp only [sub_zero]
    constructor
    · rintro ⟨⟨a,b,_,c⟩,d⟩
      exact ⟨a,b,d,c⟩
    · rintro ⟨a,b,c,d⟩
      exact ⟨⟨a,b,(c.trans (by linarith)),d⟩,c⟩
  have hLow (f : ℂ → ℝ) : grhRealSum Lfun mult χ 0 1 f =
      ∑ z ∈ S.filter (fun z => |z.im|≤1), (mult χ z:ℝ)*f z := by
    rw [hsub]
    exact finsum_mem_eq_finite_toFinset_sum _ _
  have hLarge (f : ℂ→ℝ) : grhRealSum Lfun mult χ 0 x f = ∑ z ∈ S, (mult χ z:ℝ)*f z :=
    finsum_mem_eq_finite_toFinset_sum _ _
  have hComplex (f : ℂ→ℂ) : grhComplexSum Lfun mult χ 0 x f = ∑ z ∈ S, (mult χ z:ℂ)*f z :=
    finsum_mem_eq_finite_toFinset_sum _ _
  have hq : (1:ℝ)≤q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hx0 : 0<x := by linarith
  have hlog : 0≤Real.log (q*x) := Real.log_nonneg (by nlinarith [mul_le_mul_of_nonneg_right hq hx0.le])
  obtain ⟨hhi,hlo⟩ := hC q χ hp x hx
  have hf := hA q χ hp x x hx le_rfl
  rw [hLarge] at hhi
  rw [hLow] at hlo
  rw [hComplex,hLow] at hf
  apply psi_uniform_of_window_data (abs_nonneg A) (abs_nonneg C) hq hx (grhPsi0 χ x) S (mult χ)
  · intro z hz
    have hm := (Set.Finite.mem_toFinset (hfin q χ 0 x)).mp hz
    exact hgrh q χ z hm.1 hm.2.1 hm.2.2.2
  · exact hlo.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith)))
  · exact hhi.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  · exact hf.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))

abbrev grhPrimitiveUniform : Prop :=
  ∃ K : ℝ, 0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ x : ℝ, 2≤x → ‖grhPsi0 χ x‖ ≤ K*Real.sqrt x*Real.log (2*q*x)^2

abbrev grhAllUniform : Prop :=
  ∃ K : ℝ, 0<K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    ∀ x : ℝ, 2≤x → ‖grhPsi0 χ x‖ ≤ K*Real.sqrt x*Real.log (2*q*x)^2

abbrev grhInductionInput : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ),
  ‖(∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt k:ℝ):ℂ)*χ (k:ZMod q)) -
    ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt k:ℝ):ℂ)*χ.primitiveCharacter (k:ZMod χ.conductor)‖ ≤
      Nat.log 2 N*Real.log q

theorem uniform_all_psi_of_primitive (hprimitive : grhPrimitiveUniform)
    (hind : grhInductionInput) : grhAllUniform := by
  classical
  obtain ⟨K,hK,hprim⟩ := hprimitive
  refine ⟨K+2,by linarith,?_⟩
  intro q _ χ x hx
  have hx0 : 0<x := by linarith
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hq : (1:ℝ)≤q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hc1 : (1:ℝ)≤χ.conductor := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero)
  have hcq : (χ.conductor:ℝ)≤q := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hone : χ.primitiveCharacter = 1 ↔ χ = 1 := by
    constructor
    · intro h
      rw [← χ.changeLevel_primitiveCharacter,h,map_one]
    · rintro rfl
      exact DirichletCharacter.primitiveCharacter_one
  let L := Real.log (2*q*x)
  have hlq : Real.log q ≤ L := Real.log_le_log (by linarith) (by nlinarith [mul_le_mul_of_nonneg_left hx (show 0≤(q:ℝ) by positivity)])
  have hL : 0≤L := (Real.log_nonneg hq).trans hlq
  have hlx : Real.log x ≤ L := Real.log_le_log hx0 (by nlinarith [mul_le_mul_of_nonneg_right hq hx0.le])
  have hlogN : (Nat.log 2 ⌊x⌋₊:ℝ) ≤ 2*L := by
    have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have he : (2:ℝ)^(Nat.log 2 ⌊x⌋₊) ≤ (⌊x⌋₊:ℕ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : ⌊x⌋₊≠0)
    have hlog := Real.log_le_log (by positivity) (he.trans (Nat.floor_le hx0.le))
    rw [Real.log_pow] at hlog
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hl
    have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) (Nat.log 2 ⌊x⌋₊))
    linarith
  have herr : ‖grhPsi0 χ x - grhPsi0 χ.primitiveCharacter x‖ ≤ (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q := by
    unfold grhPsi0
    rw [propext hone]
    simpa only [sub_sub_sub_cancel_right] using hind q χ ⌊x⌋₊
  have hp := hprim χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive x hx
  have hcm : 1 ≤ 2*(χ.conductor:ℝ)*x := by nlinarith [mul_le_mul_of_nonneg_right hc1 hx0.le]
  have hcl : Real.log (2*(χ.conductor:ℝ)*x) ≤ L :=
    Real.log_le_log (by linarith) (by nlinarith [mul_le_mul_of_nonneg_right hcq hx0.le])
  have hp' : ‖grhPsi0 χ.primitiveCharacter x‖ ≤ K*Real.sqrt x*L^2 :=
    hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg hcm) hcl 2) (by positivity))
  have hd' : (Nat.log 2 ⌊x⌋₊:ℝ)*Real.log q ≤ (2*L)*L :=
    mul_le_mul hlogN hlq (Real.log_nonneg hq) (by positivity)
  have htri := norm_add_le (grhPsi0 χ x - grhPsi0 χ.primitiveCharacter x) (grhPsi0 χ.primitiveCharacter x)
  rw [sub_add_cancel] at htri
  have hr := mul_le_mul_of_nonneg_right (Real.one_le_sqrt.mpr (show 1≤x by linarith)) (sq_nonneg L)
  change _ ≤ (K+2)*Real.sqrt x*L^2
  nlinarith only [htri,herr,hd',hp',hr]

end
end GoldbachPartial
