import VerifiedThinSemiprimeLogUpper

namespace GoldbachPartial
open Finset
noncomputable section

def thinRootPrimeShell (u : ℕ) : Finset ℕ :=
  (Ioc 0 u).filter (fun L=>L.Prime ∧ u≤2*L)

def thinRootPrimeMass (n u : ℕ) : ℝ := ∑L∈thinRootPrimeShell u,
  ∑b∈thinPrimePairSet n L (2*u),weight (n-L*b)

theorem thinRootPrimeMass_log_upper (n u z K : ℕ) (hn : n≤u^2) (hlog : 1≤Real.log n)
    (hne : Even n) (hz : 1≤z) (hK : Even K) :
    thinRootPrimeMass n u ≤ (4*Real.log 4)*(u:ℝ)*
      (2*(z:ℝ)+(2*(u:ℝ))*((128*(1+Real.log (3*Real.log u))/Real.log ((z:ℝ)+1))^2+
        (64*(1+Real.log z))^4/(2:ℝ)^(K+1))+(z:ℝ)^K*(2:ℝ)^K) := by
  have hn0 : 0<n := by
    by_contra! h
    have hh : n=0 := by omega
    norm_num [hh] at hlog
  have hlz : 0<Real.log ((z:ℝ)+1) := by
    apply Real.log_pos
    have : (1:ℝ)≤z := by exact_mod_cast hz
    linarith
  let A := 2*(z:ℝ)+(2*(u:ℝ))*((128*(1+Real.log (3*Real.log u))/Real.log ((z:ℝ)+1))^2+
        (64*(1+Real.log z))^4/(2:ℝ)^(K+1))+(z:ℝ)^K*(2:ℝ)^K
  have hA : 0≤A := by dsimp [A]; positivity
  let S := thinRootPrimeShell u
  have hp (L : ℕ) (h : L∈S) := (mem_filter.mp h).2
  have hu (L : ℕ) (h : L∈S) : L≤u := (mem_Ioc.mp (mem_filter.mp h).1).2
  have hpt (L : ℕ) (h : L∈S) : ((thinPrimePairSet n L (2*u)).card:ℝ)≤A := by
    obtain ⟨hprime,_⟩ := hp L h
    have hnL : n≤n*L := Nat.le_mul_of_pos_right _ hprime.pos
    have hm : 1≤Real.log (n*L:ℕ) := hlog.trans (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnL))
    have he : 2∣n*L := dvd_mul_of_dvd_left (even_iff_two_dvd.mp hne) L
    have hcard := thinPrimePairSet_log_upper n L (2*u) z K hprime.pos hz hK he hm
    have hnu : n*L≤u^3 := by
      calc _ ≤ u^2*u := Nat.mul_le_mul hn (hu L h)
           _ = _ := by ring
    have h3 := Real.log_le_log (show (0:ℝ)<(n*L:ℕ) by exact_mod_cast Nat.mul_pos hn0 hprime.pos)
      (show ((n*L:ℕ):ℝ)≤((u^3:ℕ):ℝ) by exact_mod_cast hnu)
    rw [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at h3
    have hLL := Real.log_le_log (zero_lt_one.trans_le hm) h3
    push_cast only [Nat.cast_mul,Nat.cast_ofNat] at hcard
    apply hcard.trans
    dsimp only [A]
    have hpos : 0≤Real.log (Real.log (n*L:ℕ)) := Real.log_nonneg hm
    push_cast only [Nat.cast_mul] at hpos hLL
    gcongr
  have hweight (L b : ℕ) (hL : L∈S) (hb : b∈thinPrimePairSet n L (2*u)) :
      weight (n-L*b)≤4*Real.log L := by
    obtain ⟨hpr,hhalf⟩ := hp L hL
    have hpb := (mem_filter.mp hb).2.2
    rw [weight,ite_eq_left hpb]
    have hQ : u≤L^2 := hhalf.trans (by simpa only [pow_two] using Nat.mul_le_mul_right L hpr.two_le)
    have hnL : n≤L^4 := by
      calc _ ≤ u^2 := hn
           _ ≤ (L^2)^2 := Nat.pow_le_pow_left hQ _
           _ = _ := by ring
    have hR := Real.log_le_log (show (0:ℝ)<(n-L*b:ℕ) by exact_mod_cast hpb.pos)
      (show ((n-L*b:ℕ):ℝ)≤((L^4:ℕ):ℝ) by exact_mod_cast (Nat.sub_le n (L*b)).trans hnL)
    simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] using hR
  have hP : S⊆(Ioc 0 u).filter Nat.Prime := fun L h => mem_filter.mpr ⟨(mem_filter.mp h).1,(hp L h).1⟩
  have hsum : (∑L∈S,Real.log L)≤Real.log 4*u := by
    apply (sum_le_sum_of_subset_of_nonneg hP (fun L _ _=>Real.log_natCast_nonneg _)).trans
    simpa only [Chebyshev.theta,Nat.floor_natCast] using Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α:=ℝ) u)
  calc
    _ ≤ ∑L∈S,A*(4*Real.log L) := by
      apply sum_le_sum
      intro L hL
      have h := sum_le_sum (fun b hb=>hweight L b hL hb)
      simpa only [sum_const,nsmul_eq_mul] using h.trans ((sum_const _).trans_le (by
        rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (hpt L hL) (by positivity)))
    _ = (A*4)*(∑L∈S,Real.log L) := by simp only [mul_sum,mul_assoc]
    _ ≤ _ := by
      change (A*4)*(∑L∈S,Real.log L)≤(4*Real.log 4)*(u:ℝ)*A
      simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left hsum (mul_nonneg hA (by norm_num : (0:ℝ)≤4))
open scoped Classical

/-- Distinct initial primes in representations n=p+L*b, where L is in the
near-square-root shell. The sum counts each initial prime once. -/
def thinSemiprimePrimes (n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun p=>p.Prime ∧ ∃L b : ℕ, L.Prime ∧ b.Prime ∧
    L≤b ∧ L^2≤n ∧ n<4*L^2 ∧ n=p+L*b)

theorem thinSemiprimePrimes_mass_le (n : ℕ) :
    (∑p∈thinSemiprimePrimes n,weight p)≤thinRootPrimeMass n (n.sqrt+1) := by
  classical
  let u := n.sqrt+1
  let T := (thinRootPrimeShell u).sigma (fun L=>thinPrimePairSet n L (2*u))
  let f := fun v : Sigma (fun _ : ℕ => ℕ) => n-v.1*v.2
  have hsub : thinSemiprimePrimes n⊆T.image f := by
    intro p hp
    obtain ⟨_,hp',L,b,hL,hb,_hLb,hLn,hL4,he⟩ := mem_filter.mp hp
    have hU : n<u*u := Nat.lt_succ_sqrt n
    have h2 : u≤2*L := Nat.sqrt_lt.mpr (by nlinarith only [hL4])
    have hLu : L≤u := by
      by_contra! h
      have hh : u*u≤L*L := Nat.mul_le_mul h.le h.le
      nlinarith only [hU,hLn,hh]
    have hbu : b≤2*u := Nat.le_of_mul_le_mul_left (by
      have h : u*u ≤ (2*L)*u := Nat.mul_le_mul_right u h2
      nlinarith only [h,he,hU,Nat.zero_le p]) hL.pos
    have hf : n-L*b=p := by omega
    refine mem_image.mpr ⟨⟨L,b⟩,mem_sigma.mpr ⟨?_,?_⟩,hf⟩
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hL.pos,hLu⟩,hL,h2⟩
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hb.pos,hbu⟩,hb,hf ▸ hp'⟩
  have hnon (p : ℕ) : 0≤weight p := by unfold weight;split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _=>hnon p)).trans
  have hImage := sum_image_le_of_nonneg (s:=T) (g:=f) (fun p _=>hnon p)
  exact hImage.trans_eq (sum_sigma ..)

end
end GoldbachPartial