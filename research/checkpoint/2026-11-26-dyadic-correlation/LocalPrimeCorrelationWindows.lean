import GRHTruePrimePrefix
import OddPrimeHalfPeriod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace GoldbachPartial
open Finset Filter ExtendedArcCoefficient
open scoped Topology

noncomputable def oddPrimeMassBefore (u : ℕ) : ℝ := ∑ k ∈ range u, oddPrimeWeight k

private theorem oddWnonneg (k : ℕ) : 0 ≤ oddPrimeWeight k := by
  by_cases hp : k.Prime
  · simp only [oddPrimeWeight,weight,ite_eq_left hp]
    split_ifs <;> first | exact le_rfl | exact Real.log_natCast_nonneg _
  · simp [oddPrimeWeight,weight,hp]

private theorem oddWvanishes {k : ℕ} (hk : ¬Odd k) : oddPrimeWeight k = 0 := by
  by_cases hp : k.Prime
  · have h2 := hp.eq_two_or_odd'.resolve_right hk
    simp [oddPrimeWeight,h2]
  · simp [oddPrimeWeight,weight,hp]

private theorem oddPrime_interval_lower {T : ℕ} {D : ℝ}
    (h : ∀ u≤T, |oddPrimeMassBefore u-(u:ℝ)| ≤ D)
    {a b : ℕ} (hab : a≤b) (hb : b≤T) :
    (b:ℝ)-a-2*D ≤ ∑ k ∈ Ico a b, oddPrimeWeight k := by
  rw [sum_Ico_eq_sub _ hab]
  change _ ≤ oddPrimeMassBefore b - oddPrimeMassBefore a
  linarith only [(abs_le.mp (h b hb)).1,(abs_le.mp (h a (hab.trans hb))).2]

private theorem oddPrime_interval_shift {p X H : ℕ} (hp : p≤X) :
    (∑ m ∈ Ico X (X+H), oddPrimeWeight (m-p)) =
      ∑ k ∈ Ico (X-p) (X+H-p), oddPrimeWeight k := by
  apply sum_bij (fun m _ => m-p)
  · intro m hm
    have h := mem_Ico.mp hm
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  · intro m hm m' hm' he
    have h := mem_Ico.mp hm
    have h' := mem_Ico.mp hm'
    omega
  · intro k hk
    have h := mem_Ico.mp hk
    exact ⟨k+p,mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · simp

noncomputable def oddPrimeCorr (m : ℕ) : ℝ :=
  ∑ k ∈ range (m+1), oddPrimeWeight k*oddPrimeWeight (m-k)

private theorem oddPrimeCorr_zero_of_not_even {m : ℕ} (hm : ¬Even m) : oddPrimeCorr m = 0 := by
  unfold oddPrimeCorr
  apply sum_eq_zero
  intro p hp
  have h := mem_range.mp hp
  by_cases ho : Odd p
  · have hq : ¬Odd (m-p) := by
      intro hq
      have he := ho.add_odd hq
      have eq : p+(m-p) = m := by omega
      exact hm (eq ▸ he)
    rw [oddWvanishes hq,mul_zero]
  · rw [oddWvanishes ho,zero_mul]

/-- A maximum error D for the odd-prime counting weight up to X+H controls
the sum of the individual binary coefficients on every such interval. -/
theorem localPrimeCorr_mass {X H : ℕ} {D : ℝ}
    (hp : ∀ u≤X+H, |oddPrimeMassBefore u-(u:ℝ)| ≤ D) (hd : 2*D ≤ H) :
    ((X:ℝ)-D)*((H:ℝ)-2*D) ≤ ∑ m ∈ Ico X (X+H), oddPrimeCorr m := by
  have hX := (abs_le.mp (hp X (by omega))).1
  have hW : (X:ℝ)-D ≤ oddPrimeMassBefore X := by linarith
  have hrow (p : ℕ) (hp' : p∈range X) :
      (H:ℝ)-2*D ≤ ∑ m ∈ Ico X (X+H), oddPrimeWeight (m-p) := by
    have h := mem_range.mp hp'
    rw [oddPrime_interval_shift (by omega : p≤X)]
    have ht := oddPrime_interval_lower hp (show X-p ≤ X+H-p by omega) (show X+H-p ≤ X+H by omega)
    have he : X+H-p = X-p+H := by omega
    rw [he,Nat.cast_add] at ht
    rw [he]
    linarith
  calc
    _ ≤ oddPrimeMassBefore X*((H:ℝ)-2*D) := mul_le_mul_of_nonneg_right hW (sub_nonneg.mpr hd)
    _ = ∑ p ∈ range X, oddPrimeWeight p*((H:ℝ)-2*D) := Finset.sum_mul .. 
    _ ≤ ∑ p ∈ range X, ∑ m ∈ Ico X (X+H), oddPrimeWeight p*oddPrimeWeight (m-p) := by
      apply sum_le_sum
      intro p h
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hrow p h) (oddWnonneg p)
    _ = ∑ m ∈ Ico X (X+H), ∑ p ∈ range X, oddPrimeWeight p*oddPrimeWeight (m-p) := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro m hm
      have h := mem_Ico.mp hm
      exact sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : X≤m+1))
        (fun p _ _ => mul_nonneg (oddWnonneg p) (oddWnonneg (m-p)))

theorem localPrimeCorr_witness {X H : ℕ} (hX : 4<X) (hH : 0<H) (hHX : H≤X) {D : ℝ}
    (hp : ∀ u≤X+H, |oddPrimeMassBefore u-(u:ℝ)| ≤ D) (hD : 4*D≤H) :
    ∃ m ∈ Ico X (X+H), Even m ∧ (m:ℝ)/8 ≤ corr m := by
  have h0 : 0≤D := (abs_nonneg _).trans (hp X (by omega))
  have hXR : (H:ℝ)≤X := by exact_mod_cast hHX
  have hlow := localPrimeCorr_mass hp (by linarith)
  have hx : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hh : (0:ℝ)<H := by exact_mod_cast hH
  have hprod : ((X:ℝ)/2)*((H:ℝ)/2) ≤ ((X:ℝ)-D)*((H:ℝ)-2*D) := by
    apply mul_le_mul <;> linarith
  have hgood : ∃ m ∈ Ico X (X+H), (X:ℝ)/4 ≤ oddPrimeCorr m := by
    by_contra! hf
    have hne : (Ico X (X+H)).Nonempty := ⟨X,mem_Ico.mpr ⟨le_rfl,by omega⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne hf
    rw [sum_const,Nat.card_Ico,show X+H-X=H by omega,nsmul_eq_mul] at hlt
    linarith only [hlt,hlow,hprod]
  obtain ⟨m,hm,hc⟩ := hgood
  have he : Even m := by
    by_contra h
    rw [oddPrimeCorr_zero_of_not_even h] at hc
    linarith
  refine ⟨m,hm,he,?_⟩
  have hw := mem_Ico.mp hm
  rw [corr_eq_oddPrime_convolution (by omega) he]
  change _ ≤ oddPrimeCorr m
  have hu : (m:ℝ) ≤ 2*X := by exact_mod_cast (show m≤2*X by omega)
  linarith


private theorem oddPrime_mass_error {N : ℕ} {D : ℝ} (hD : 0≤D)
    (h : ∀ j≤N, ‖centeredPrimeArcTransform 1 j 0 ((j:ℂ)+1) 1‖ ≤ D) :
    ∀ u≤N, |oddPrimeMassBefore u-(u:ℝ)| ≤ D+Real.log 2 := by
  have h2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hφ (k : ℕ) : (1 : DirichletCharacter ℂ 1) (k : ZMod 1) = 1 :=
    MulChar.one_apply (by rw [Subsingleton.elim (k : ZMod 1) 1]; exact isUnit_one)
  intro u hu
  cases u with
  | zero => simpa [oddPrimeMassBefore] using add_nonneg hD h2
  | succ j =>
    have hz := h j (by omega)
    simp only [centeredPrimeArcTransform,weightedArcCharacterSum,ite_true,hφ,star_one,mul_one,
      mul_zero,E,Complex.ofReal_zero,zero_mul,Complex.exp_zero] at hz
    have heq : (∑ k ∈ range (j+1), (weight k:ℂ))-((j:ℂ)+1) =
        ((∑ k ∈ range (j+1), weight k)-((j:ℝ)+1) : ℝ) := by push_cast; rfl
    rw [heq,Complex.norm_real,Real.norm_eq_abs] at hz
    have hsplit (k : ℕ) : oddPrimeWeight k = weight k - (if k=2 then Real.log 2 else 0) := by
      by_cases hk : k=2
      · subst k; simp [oddPrimeWeight,weight,Nat.prime_two]
      · simp [oddPrimeWeight,hk]
    unfold oddPrimeMassBefore
    simp_rw [hsplit]
    rw [sum_sub_distrib]
    simp only [Finset.sum_ite_eq',Nat.cast_succ]
    split_ifs
    · rw [abs_le] at hz ⊢
      constructor <;> linarith only [hz.1,hz.2,h2]
    · rw [sub_zero]
      exact hz.trans (by linarith)

/-- Uniform local scale supplied by the modulus-one prime prefix bound. -/
noncomputable def localPrimeScale (X : ℕ) : ℝ := Real.sqrt X*(1+Real.log X)^2

theorem oddPrimeMass_local_prefix (hψ : grhAllUniform) :
    ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 1≤X → ∀ u≤2*X,
      |oddPrimeMassBefore u-(u:ℝ)| ≤ C*localPrimeScale X := by
  obtain ⟨K,hK,h⟩ := true_prime_prefix_uniform_of_grhAllUniform hψ
  refine ⟨18*K+1,by linarith,?_⟩
  intro X hX
  have hx : (1:ℝ)≤X := by exact_mod_cast hX
  have hx0 : 0<(X:ℝ) := zero_lt_one.trans_le hx
  let L := 1+Real.log (X:ℝ)
  have hL : 1≤L := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
  have hs : 1 ≤ Real.sqrt X := by simpa using Real.sqrt_le_sqrt hx
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog : Real.log (2*(2*(X:ℝ))^2) ≤ 3*L := by
    rw [show 2*(2*(X:ℝ))^2 = 2^3*(X:ℝ)^2 by ring,Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,Real.log_pow]
    dsimp [L]
    linarith [Real.log_natCast_nonneg X]
  have hS : Real.sqrt (2*(X:ℝ)) ≤ 2*Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num)]
    gcongr
    rw [Real.sqrt_le_iff]
    norm_num
  have hpos : 0≤Real.log (2*(2*(X:ℝ))^2) := Real.log_nonneg (by nlinarith [sq_nonneg ((X:ℝ)-1)])
  have hbase : 1≤localPrimeScale X :=
    (one_le_mul_of_one_le_of_one_le hs (one_le_pow₀ (n:=2) hL))
  have hraw := oddPrime_mass_error (N:=2*X) (D:=K*Real.sqrt (2*(X:ℝ))*Real.log (2*(2*(X:ℝ))^2)^2)
    (by positivity) (fun j hj => by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using h (2*X) (by omega) 1 (by omega) 1 j hj)
  intro u hu
  refine (hraw u hu).trans ?_
  calc
    _ ≤ K*(2*Real.sqrt X)*(3*L)^2 + localPrimeScale X := by
      exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hS hK)
        (pow_le_pow_left₀ hpos hlog 2) (sq_nonneg _) (by positivity)) (hlog2.trans hbase)
    _ = _ := by dsimp [localPrimeScale,L]; ring

theorem localPrimeCorr_window_of_uniform_psi (hψ : grhAllUniform) :
    ∃ K : ℝ, 0<K ∧ ∀ X H : ℕ, 4<X → 0<H → H≤X → K*localPrimeScale X≤H →
      ∃ m ∈ Ico X (X+H), Even m ∧ (m:ℝ)/8≤corr m := by
  obtain ⟨C,hC,h⟩ := oddPrimeMass_local_prefix hψ
  refine ⟨4*C,by positivity,?_⟩
  intro X H hX hH hHX hwidth
  apply localPrimeCorr_witness hX hH hHX (D:=C*localPrimeScale X)
  · exact fun u hu => h X (by omega) u (by omega)
  · linarith only [hwidth]


theorem eventual_localPrimeScale_ceil_le (K : ℝ) (hK : 0<K) :
    ∀ᶠ X : ℕ in atTop, ⌈K*localPrimeScale X⌉₊ ≤ X := by
  have hb := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/2)).bound
    (show 0<(1:ℝ)/(4*K) by positivity)
  have hb' := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hb
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  filter_upwards [hb',hl,eventually_ge_atTop (1:ℕ)] with X h hlog hX
  change 1≤Real.log (X:ℝ) at hlog
  have hx : (0:ℝ)<X := by exact_mod_cast hX
  have hlog0 : 0≤Real.log (X:ℝ) := Real.log_natCast_nonneg X
  have hsmall : (Real.log X)^2 ≤ (1/(4*K))*Real.sqrt X := by
    change ‖(Real.log (X:ℝ))^(2:ℝ)‖ ≤ 1/(4*K)*‖(X:ℝ)^(1/2:ℝ)‖ at h
    rw [← Real.sqrt_eq_rpow,Real.norm_of_nonneg (Real.sqrt_nonneg _),
      show (Real.log (X:ℝ))^(2:ℝ) = (Real.log X)^2 from Real.rpow_natCast ..,
      Real.norm_of_nonneg (sq_nonneg _)] at h
    exact h
  apply Nat.ceil_le.mpr
  have hsq : (1+Real.log X)^2 ≤ (2*Real.log X)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc
    K*localPrimeScale X ≤ K*Real.sqrt X*(2*Real.log X)^2 := by
      dsimp [localPrimeScale]; rw [← mul_assoc]; gcongr
    _ = (4*K*Real.sqrt X)*(Real.log X)^2 := by ring
    _ ≤ (4*K*Real.sqrt X)*((1/(4*K))*Real.sqrt X) := by gcongr
    _ = (Real.sqrt X)^2 := by field_simp
    _ = X := Real.sq_sqrt hx.le

/-- Every sufficiently late window of square-root times log-squared length
contains an even integer satisfying the linear Goldbach correlation bound. -/
theorem localPrimeCorr_near_every_point (hψ : grhAllUniform) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ X : ℕ in atTop,
      ∃ m : ℕ, X≤m ∧ m<X+⌈K*localPrimeScale X⌉₊ ∧ Even m ∧ (m:ℝ)/8≤corr m := by
  obtain ⟨K,hK,h⟩ := localPrimeCorr_window_of_uniform_psi hψ
  refine ⟨K,hK,?_⟩
  filter_upwards [eventual_localPrimeScale_ceil_le K hK,eventually_ge_atTop (5:ℕ)] with X hcut hX
  have hs : 0<localPrimeScale X := by
    have : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
    have hL : 0<1+Real.log (X:ℝ) := by linarith [Real.log_natCast_nonneg X]
    dsimp [localPrimeScale]; positivity
  obtain ⟨m,hm,he,hc⟩ := h X _ (by omega) (Nat.ceil_pos.mpr (mul_pos hK hs)) hcut (Nat.le_ceil _)
  exact ⟨m,(mem_Ico.mp hm).1,(mem_Ico.mp hm).2,he,hc⟩

end GoldbachPartial
