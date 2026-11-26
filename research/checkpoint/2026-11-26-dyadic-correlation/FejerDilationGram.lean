import NaturalPrimeGapArcs

namespace GoldbachPartial
open Finset MeasureTheory ExtendedArcCoefficient

abbrev fejerGramModes (K:ℕ) : Finset ℤ := Icc (-(K:ℤ)) K
def fejerGramPairs (K d e:ℕ) : Finset (ℤ×ℤ) :=
  ((fejerGramModes K) ×ˢ (fejerGramModes K)).filter (fun p => p.1*d+p.2*e=0)

private theorem gram_fst_divisible {d e:ℕ} (hd:0<d) (_he:0<e) {h k:ℤ}
    (hx:h*(d:ℤ)+k*e=0) : (↑(e/(d.gcd e)):ℤ) ∣ h := by
  let g := d.gcd e
  have hg : 0<g := Nat.gcd_pos_of_pos_left e hd
  have hg' : (g:ℤ)≠0 := by exact_mod_cast hg.ne'
  have hdg : ((d/g:ℕ):ℤ)*g=d := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left d e)
  have heg : ((e/g:ℕ):ℤ)*g=e := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right d e)
  have hred : h*((d/g:ℕ):ℤ) = (-k)*((e/g:ℕ):ℤ) := by
    apply mul_right_cancel₀ hg'
    rw [mul_assoc,mul_assoc,hdg,heg]
    linarith
  have hc := (Nat.coprime_div_gcd_div_gcd (m:=d) (n:=e) hg).symm.isCoprime
  exact hc.dvd_of_dvd_mul_right ⟨-k,hred.trans (mul_comm ..)⟩

theorem fejerGramPairs_card (K d e :ℕ) (hd:0<d) (he:0<e) :
    (fejerGramPairs K d e).card ≤ 2*(K/(e/(d.gcd e)))+1 := by
  let u := e/(d.gcd e)
  let S := fejerGramPairs K d e
  let f (p:ℤ×ℤ) := p.1/(u:ℤ)
  have hu : 0<u := Nat.div_pos (Nat.le_of_dvd he (Nat.gcd_dvd_right d e)) (Nat.gcd_pos_of_pos_left e hd)
  have he' : (e:ℤ)≠0 := by exact_mod_cast he.ne'
  have props {p:ℤ×ℤ} (hp:p∈S) :
      f p*(u:ℤ)=p.1 ∧ p.1*(d:ℤ)+p.2*e=0 ∧ p.1.natAbs≤K := by
    obtain ⟨hab,hrow⟩ := Finset.mem_filter.mp hp
    have hmem := Finset.mem_Icc.mp (Finset.mem_product.mp hab).1
    exact ⟨Int.ediv_mul_cancel (gram_fst_divisible hd he hrow),hrow,by omega⟩
  have hcard : S.card ≤ (fejerGramModes (K/u)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      obtain ⟨hm,_,hb⟩ := props hp
      have hh := congrArg Int.natAbs hm
      simp only [Int.natAbs_mul,Int.natAbs_natCast] at hh
      have hh' : (f p).natAbs ≤ K/u := (Nat.le_div_iff_mul_le hu).mpr (hh.le.trans hb)
      apply mem_Icc.mpr
      omega
    · intro p hp r hr heq
      obtain ⟨h₁,h₂,_⟩ := props hp
      obtain ⟨h₃,h₄,_⟩ := props hr
      rw [heq] at h₁
      have hf : p.1=r.1 := h₁.symm.trans h₃
      have hs : p.2*(e:ℤ)=r.2*e := by rw [hf] at h₂; linarith
      exact Prod.ext hf (mul_right_cancel₀ he' hs)
  apply hcard.trans_eq
  change (Icc (-(↑(K/u):ℤ)) (↑(K/u):ℤ)).card = 2*(K/u)+1
  rw [Int.card_Icc]
  omega

theorem fejerGramPairs_real_bound (K d e : ℕ) (hd:0<d) (he:0<e) :
    ((fejerGramPairs K d e).card:ℝ) ≤ 1+2*(K:ℝ)*(d.gcd e:ℝ)/e := by
  let u := e/(d.gcd e)
  have hg := Nat.gcd_pos_of_pos_left e hd
  have hu : 0<u := Nat.div_pos (Nat.le_of_dvd he (Nat.gcd_dvd_right d e)) hg
  have hue : (u:ℝ)*(d.gcd e:ℝ)=e := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right d e)
  have hu' : (0:ℝ)<u := by exact_mod_cast hu
  have hg' : (0:ℝ)<d.gcd e := by exact_mod_cast hg
  calc
    _ ≤ 2*((K/u:ℕ):ℝ)+1 := by exact_mod_cast fejerGramPairs_card K d e hd he
    _ ≤ 2*((K:ℝ)/u)+1 := by gcongr; exact Nat.cast_div_le
    _ = _ := by rw [←hue]; field_simp; ring

noncomputable def fejerGramPolynomial (K : ℕ) (c:ℤ→ℂ) (x:ℝ) : ℂ :=
  ∑ h ∈ fejerGramModes K, c h * E ((h:ℝ)*x)

theorem fejerGramPolynomial_integral (K d e:ℕ) (a b:ℤ→ℂ) :
    (∫ t in (0:ℝ)..1, fejerGramPolynomial K a ((d:ℝ)*t)*fejerGramPolynomial K b ((e:ℝ)*t)) =
      ∑ p ∈ fejerGramPairs K d e, a p.1*b p.2 := by
  let S := fejerGramModes K
  let term (p:ℤ×ℤ) (t:ℝ) := (a p.1*b p.2)*E (((p.1*(d:ℤ)+p.2*e:ℤ):ℝ)*t)
  have hpt (t:ℝ) : fejerGramPolynomial K a ((d:ℝ)*t)*fejerGramPolynomial K b ((e:ℝ)*t) =
      ∑ p ∈ S ×ˢ S, term p t := by
    rw [Finset.sum_product]
    unfold fejerGramPolynomial
    rw [sum_mul]
    apply sum_congr rfl
    intro h _
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    dsimp only [term]
    push_cast
    rw [show ((h:ℝ)*d+(k:ℝ)*e)*t=(h:ℝ)*(d*t)+(k:ℝ)*(e*t) by ring,phase_add]
    ring
  simp_rw [hpt]
  have hhi (p:ℤ×ℤ):Continuous (term p) := by dsimp [term,E];fun_prop
  rw [intervalIntegral.integral_finsetSum (fun p _ => (hhi p).intervalIntegrable _ _)]
  simp only [term,intervalIntegral.integral_const_mul,fourier_mode]
  unfold fejerGramPairs
  rw [sum_filter]
  exact sum_congr rfl fun p _ => by split_ifs <;> simp

theorem fejerGramPolynomial_pair_bound (K d e:ℕ) (hd:0<d) (he:0<e) (a b:ℤ→ℂ) {A B:ℝ}
    (ha:∀h∈fejerGramModes K,‖a h‖≤A) (hb:∀h∈fejerGramModes K,‖b h‖≤B) :
    ‖∫ t in (0:ℝ)..1, fejerGramPolynomial K a ((d:ℝ)*t)*fejerGramPolynomial K b ((e:ℝ)*t)‖ ≤
       A*B*(1+2*(K:ℝ)*(d.gcd e:ℝ)/e) := by
  rw [fejerGramPolynomial_integral]
  have hzero : (0:ℤ)∈fejerGramModes K := mem_Icc.mpr ⟨by omega,by omega⟩
  have hA : 0≤A := (norm_nonneg _).trans (ha 0 hzero)
  have hB : 0≤B := (norm_nonneg _).trans (hb 0 hzero)
  calc
    _ ≤ ∑ _p ∈ fejerGramPairs K d e, A*B := by
      apply (norm_sum_le ..).trans
      apply sum_le_sum
      intro p hp
      have hm := mem_product.mp (mem_filter.mp hp).1
      rw [norm_mul]
      exact mul_le_mul (ha _ hm.1) (hb _ hm.2) (norm_nonneg _) hA
    _ = A*B*((fejerGramPairs K d e).card:ℝ) := by simp [nsmul_eq_mul,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (fejerGramPairs_real_bound K d e hd he) (mul_nonneg hA hB)

end GoldbachPartial