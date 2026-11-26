import VerifiedFixedUniformMajorArcs
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace GoldbachPartial
open Finset

theorem fixedUniformMajorArcs_mem_of_approx {Q q a : ℕ} {ρ t : ℝ}
    (hq : 0<q) (hqQ : q≤Q) (haq : a≤q) (hc : a.Coprime q)
    (ht : t∈Set.Icc (0:ℝ) 1) (h : |t-(a:ℝ)/q|≤ρ) :
    t∈fixedUniformMajorArcs Q ρ := by
  have hset (k : ℕ) (hk : k<q) (hcp : k.Coprime q) (htk : t∈fixedUniformMajorPiece ρ q k) :
      t∈fixedUniformMajorArcs Q ρ := by
    unfold fixedUniformMajorArcs
    exact Set.mem_iUnion.mpr ⟨⟨q,k⟩,Set.mem_iUnion.mpr ⟨mem_sigma.mpr
      ⟨mem_Icc.mpr ⟨hq,hqQ⟩,mem_filter.mpr ⟨mem_range.mpr hk,hcp⟩⟩,htk⟩⟩
  rcases haq.eq_or_lt with heq|hlt
  · subst a
    have hq1 := (Nat.coprime_self q).mp hc
    subst q
    apply hset 0 (by decide) (by decide)
    simp only [fixedUniformMajorPiece,ite_true,Set.mem_union,Set.mem_Icc]
    right
    norm_num at h
    exact ⟨by linarith only [(abs_le.mp h).1],ht.2⟩
  · apply hset a hlt hc
    by_cases ha : a=0
    · subst a
      simp only [fixedUniformMajorPiece,ite_true,Set.mem_union,Set.mem_Icc]
      left
      rw [Nat.cast_zero,zero_div,sub_zero,abs_of_nonneg ht.1] at h
      exact ⟨ht.1,h⟩
    · rw [fixedUniformMajorPiece,ite_eq_right ha]
      exact ⟨by linarith only [(abs_le.mp h).1],by linarith only [(abs_le.mp h).2]⟩

/-- The rational approximation supplied by Dirichlet is already reduced.
Its numerator lies strictly between 0 and q on the complement of the arcs. -/
theorem fixedUniform_dirichlet_cover {Q R : ℕ} {ρ t : ℝ} (hQ : 0<Q) (hR : 0<R)
    (hρ : 1/((R:ℝ)+1)≤ρ) (ht : t∈Set.Icc (0:ℝ) 1) (hout : t∉fixedUniformMajorArcs Q ρ) :
    ∃ a q : ℕ, Q<q ∧ q≤R ∧ 0<a ∧ a<q ∧ a.Coprime q ∧
      |t-(a:ℝ)/q|≤1/(((R:ℝ)+1)*q) ∧ |t-(a:ℝ)/q|≤1/(q:ℝ)^2 := by
  obtain ⟨r,hd,hden⟩ := Real.exists_rat_abs_sub_le_and_den_le t hR
  let q := r.den
  have hq : 0<q := r.pos
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  have hq0 : (0:ℝ)<q := by positivity
  have hR0 : (0:ℝ)<R := by exact_mod_cast hR
  have hRo : (0:ℝ)<(R:ℝ)+1 := by positivity
  rw [Rat.cast_def] at hd
  change |t-(r.num:ℝ)/q|≤1/(((R:ℝ)+1)*q) at hd
  have hscaled : |(q:ℝ)*t-r.num|≤1/((R:ℝ)+1) := by
    calc _ = |(t-(r.num:ℝ)/q)*(q:ℝ)| := by
           apply congrArg abs
           field_simp
         _ = |t-(r.num:ℝ)/q| * (q:ℝ) := by rw [abs_mul,abs_of_pos hq0]
         _ ≤ (1/(((R:ℝ)+1)*q))*(q:ℝ) := mul_le_mul_of_nonneg_right hd hq0.le
         _ = _ := by field_simp
  have hon : 1/((R:ℝ)+1)<1 := (div_lt_one hRo).mpr (by linarith)
  have hn0 : 0≤r.num := by
    have hr : (-1:ℝ)<r.num := by
      linarith only [(abs_le.mp hscaled).2,hon,mul_nonneg hq0.le ht.1]
    have hh : (-1:ℤ)<r.num := by exact_mod_cast hr
    omega
  have hnq : r.num≤(q:ℤ) := by
    have hhR : (r.num:ℝ)<(q:ℝ)+1 := by
      have hh := mul_le_mul_of_nonneg_left ht.2 hq0.le
      linarith only [hh,(abs_le.mp hscaled).1,hon]
    have hhZ : r.num<(q:ℤ)+1 := by exact_mod_cast hhR
    omega
  let a := r.num.natAbs
  have ha : (a:ℤ)=r.num := Int.natAbs_of_nonneg hn0
  have hac : (a:ℝ)=(r.num:ℝ) := by exact_mod_cast ha
  have haq : a≤q := by exact_mod_cast ha.trans_le hnq
  have hcp : a.Coprime q := r.reduced
  rw [←hac] at hd
  have hg : 1/(((R:ℝ)+1)*q)≤1/((R:ℝ)+1) := by
    apply one_div_le_one_div_of_le hRo
    exact le_mul_of_one_le_right hRo.le hqR
  have hqbig : Q<q := by
    by_contra! h
    exact hout (fixedUniformMajorArcs_mem_of_approx hq h haq hcp ht (hd.trans (hg.trans hρ)))
  have hapos : 0<a := by
    by_contra! h
    have hz : a=0 := by omega
    simp [hz] at hcp
    omega
  have haq' : a<q := by
    apply lt_of_le_of_ne haq
    intro heq
    have hh := (Nat.coprime_self q).mp (heq ▸ hcp)
    omega
  refine ⟨a,q,hqbig,hden,hapos,haq',hcp,hd,hd.trans ?_⟩
  apply one_div_le_one_div_of_le (sq_pos_of_pos hq0)
  rw [pow_two]
  apply mul_le_mul_of_nonneg_right _ hq0.le
  exact (show (q:ℝ)≤R by exact_mod_cast hden).trans (by linarith)

theorem fixedUniform_dirichlet_cover_div {N Q : ℕ} {ρ t : ℝ}
    (hQ : 0<Q) (hQN : Q≤N) (hρ : (Q:ℝ)/N≤ρ)
    (ht : t∈Set.Icc (0:ℝ) 1) (hout : t∉fixedUniformMajorArcs Q ρ) :
    ∃ a q : ℕ, Q<q ∧ q≤N/Q ∧ 0<a ∧ a<q ∧ a.Coprime q ∧
      |t-(a:ℝ)/q|≤1/((((N/Q:ℕ):ℝ)+1)*q) ∧ |t-(a:ℝ)/q|≤1/(q:ℝ)^2 := by
  have hR : 0<N/Q := Nat.div_pos hQN hQ
  have hN : (0:ℝ)<N := by exact_mod_cast hQ.trans_le hQN
  have hR' : (0:ℝ)<((N/Q:ℕ):ℝ)+1 := by positivity
  have hb : 1/(((N/Q:ℕ):ℝ)+1)≤(Q:ℝ)/N := by
    apply (div_le_div_iff₀ hR' hN).mpr
    rw [one_mul]
    exact_mod_cast (Nat.lt_mul_div_succ N hQ).le
  exact fixedUniform_dirichlet_cover hQ hR (hb.trans hρ) ht hout

end GoldbachPartial