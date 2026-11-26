import VerifiedPaleyPropagationObstruction

namespace GoldbachPartial
open Finset

def thueSign : ℕ → ℤ
  | 0 => 1
  | n+1 => if (n+1)%2=0 then thueSign ((n+1)/2) else -thueSign ((n+1)/2)
termination_by n => n
decreasing_by all_goals omega

private theorem sign_zero : thueSign 0 = 1 := by rw [thueSign]
private theorem sign_even (n : ℕ) : thueSign (2*n)=thueSign n := by
  cases n with
  | zero => rfl
  | succ n =>
    conv_lhs => rw [show 2*(n+1)=(2*n+1)+1 by omega,thueSign]
    have hdiv : (2*n+1+1)/2=n+1 := by omega
    have hmod : (2*n+1+1)%2=0 := by omega
    simp only [hmod,ite_true,hdiv]

private theorem sign_odd (n : ℕ) : thueSign (2*n+1) = -thueSign n := by
  conv_lhs => rw [thueSign]
  simp only [show (2*n+1)%2≠0 by omega,ite_false, show (2*n+1)/2=n by omega]

theorem thueSign_values (n : ℕ) : thueSign n=1 ∨ thueSign n= -1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => exact Or.inl sign_zero
    | succ n =>
      have hv := ih ((n+1)/2) (by omega)
      rw [thueSign]
      rcases hv with h | h <;> simp [h] <;> omega

private theorem int_pair_sum (f:ℕ→ℤ) (m:ℕ) :
    (∑k∈range (2*m),f k)=∑k∈range m,(f (2*k)+f (2*k+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega,sum_range_succ,sum_range_succ,ih,sum_range_succ]
    ring

def thueSignConvolution (m : ℕ) : ℤ := ∑k∈range m,thueSign k*thueSign (m-1-k)

theorem thueSignConvolution_even (m : ℕ) : thueSignConvolution (2*m)= -2*thueSignConvolution m := by
  unfold thueSignConvolution
  rw [int_pair_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkm := mem_range.mp hk
  rw [show 2*m-1-2*k=2*(m-1-k)+1 by omega,show 2*m-1-(2*k+1)=2*(m-1-k) by omega,
    sign_odd,sign_even,sign_even,sign_odd]
  ring

theorem thueSignConvolution_odd (m : ℕ) :
    thueSignConvolution (2*m+1)=thueSignConvolution (m+1)+thueSignConvolution m := by
  unfold thueSignConvolution
  simp only [Nat.add_sub_cancel]
  rw [sum_range_succ,int_pair_sum,sum_range_succ]
  simp only [Nat.sub_self,sign_zero,sign_even,mul_one]
  rw [add_right_comm,←sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkm := mem_range.mp hk
  rw [show 2*m-2*k=2*(m-k) by omega,show 2*m-(2*k+1)=2*(m-1-k)+1 by omega,
    sign_even,sign_odd,sign_odd]
  ring

def thueEnergy (m : ℕ) : ℤ :=
  2*(thueSignConvolution (m+1))^2+thueSignConvolution (m+1)*thueSignConvolution m+
    2*(thueSignConvolution m)^2

private theorem energy_below (m : ℕ) : (thueSignConvolution m)^2 ≤ thueEnergy m := by
  unfold thueEnergy
  nlinarith only [sq_nonneg (thueSignConvolution (m+1)+thueSignConvolution m),
    sq_nonneg (thueSignConvolution (m+1)),sq_nonneg (thueSignConvolution m)]

private theorem energy_children (m : ℕ) : thueEnergy (2*m)+thueEnergy (2*m+1)≤6*thueEnergy m := by
  unfold thueEnergy
  rw [show 2*m+1+1=2*(m+1) by omega]
  simp only [thueSignConvolution_even,thueSignConvolution_odd]
  nlinarith only [sq_nonneg (thueSignConvolution (m+1)+thueSignConvolution m),
    sq_nonneg (thueSignConvolution (m+1)),sq_nonneg (thueSignConvolution m)]

theorem thueSignConvolution_dyadic_energy (j : ℕ) :
    (∑m∈range (2^j),(thueSignConvolution m)^2) ≤ 2*6^j := by
  calc
    _ ≤ ∑m∈range (2^j), thueEnergy m := sum_le_sum (fun m _ => energy_below m)
    _ ≤ _ := by
      induction j with
      | zero => simp [thueEnergy,thueSignConvolution,sign_zero]
      | succ j ih =>
        rw [pow_succ, Nat.mul_comm (2^j) 2,int_pair_sum]
        calc
          _ ≤ ∑m∈range (2^j),6*thueEnergy m := sum_le_sum (fun m _ => energy_children m)
          _ = 6*∑m∈range (2^j),thueEnergy m := (mul_sum ..).symm
          _ ≤ _ := by rw [pow_succ]; linarith

def thuePrefix (m : ℕ) : ℤ := ∑k∈range m,thueSign k

private theorem prefix_even (m : ℕ) : thuePrefix (2*m)=0 := by
  unfold thuePrefix
  rw [int_pair_sum]
  simp [sign_even,sign_odd]

private theorem prefix_odd (m : ℕ) : thuePrefix (2*m+1)=thueSign m := by
  unfold thuePrefix
  rw [sum_range_succ,←thuePrefix,prefix_even,sign_even,zero_add]

private theorem prefix_lo (m : ℕ) : -1 ≤ thuePrefix m := by
  have hv := thueSign_values (m/2)
  by_cases h : m%2=0
  · rw [show m=2*(m/2) by omega,prefix_even]
    decide
  · rw [show m=2*(m/2)+1 by omega,prefix_odd]
    omega

def thueWeight (k : ℕ) : ℤ := 1+thueSign k

def thueConvolution (m : ℕ) : ℤ := ∑k∈range m,thueWeight k * thueWeight (m-1-k)

theorem thueConvolution_formula (m : ℕ) :
    thueConvolution m=m+2*thuePrefix m+thueSignConvolution m := by
  unfold thueConvolution thueWeight thuePrefix thueSignConvolution
  simp_rw [add_mul,mul_add,one_mul,mul_one]
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,sum_range_reflect]
  ring

private theorem tm_dyad (d : ℕ) : thueSignConvolution (2^d)=(-2)^d := by
  induction d with
  | zero => simp [thueSignConvolution,sign_zero]
  | succ d ih =>
    rw [pow_succ, Nat.mul_comm (2^d) 2,thueSignConvolution_even,ih,pow_succ,mul_comm]

theorem thueConvolution_dyadic_hole (j : ℕ) : thueConvolution (2^(2*j+1))=0 := by
  rw [thueConvolution_formula,tm_dyad]
  have hp : thuePrefix (2^(2*j+1))=0 := by rw [pow_succ,Nat.mul_comm,prefix_even]
  rw [hp]
  push_cast
  rw [(show Odd (2*j+1) from ⟨j,rfl⟩).neg_pow (2:ℤ)]
  ring

/-- The exceptional count in [2^j,2^(j+1)) has proportion at most 192 (3/4)^j. -/
theorem thueConvolution_exception_count (j : ℕ) (hj : 3 ≤ j) :
    (((Ico (2^j) (2^(j+1))).filter (fun m : ℕ => 2*thueConvolution m<(m:ℤ))).card:ℤ) *
      4^j ≤ 192*6^j := by
  let B := (Ico (2^j) (2^(j+1))).filter (fun m : ℕ => 2*thueConvolution m<(m:ℤ))
  have hj8 : 8≤2^j := by
    calc
      8 = 2^3 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hj
  have hsmall (m : ℕ) (hm : m∈B) : (4:ℤ)^j ≤ 16*(thueSignConvolution m)^2 := by
    obtain ⟨hint, hval⟩ := mem_filter.mp hm
    have hlow := (mem_Ico.mp hint).1
    rw [thueConvolution_formula] at hval
    have hp := prefix_lo m
    have he : (8:ℤ)≤m := by exact_mod_cast hj8.trans hlow
    have hm2 : (2:ℤ)^j≤m := by exact_mod_cast hlow
    have hneg : (2:ℤ)^j≤ -(4*thueSignConvolution m) := by omega
    have hh := mul_self_le_mul_self (show (0:ℤ)≤2^j by positivity) hneg
    rw [show (4:ℤ)^j=(2^j)*(2^j) by rw [←mul_pow]; norm_num]
    nlinarith only [hh]
  have hsub : B⊆range (2^(j+1)) := by
    intro m hm
    exact mem_range.mpr (mem_Ico.mp (mem_filter.mp hm).1).2
  calc
    (B.card:ℤ)*4^j = ∑m∈B,(4:ℤ)^j := by simp
    _ ≤ ∑m∈B,16*(thueSignConvolution m)^2 := sum_le_sum hsmall
    _ = 16*∑m∈B,(thueSignConvolution m)^2 := (mul_sum ..).symm
    _ ≤ 16*∑m∈range (2^(j+1)),(thueSignConvolution m)^2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => sq_nonneg _)) (by decide)
    _ ≤ 16*(2*6^(j+1)) := mul_le_mul_of_nonneg_left (thueSignConvolution_dyadic_energy (j+1)) (by decide)
    _ = _ := by rw [pow_succ]; ring

/-- A single nonnegative sequence on the odd natural numbers. -/
def thueOddWeight (k : ℕ) : ℤ := if k%2=1 then thueWeight (k/2) else 0

theorem thueOddWeight_values (k : ℕ) : thueOddWeight k=0 ∨ thueOddWeight k=2 := by
  unfold thueOddWeight thueWeight
  rcases thueSign_values (k/2) with h|h <;> by_cases hk : k%2=1 <;> simp [h,hk]

theorem thueOddWeight_convolution (m : ℕ) :
    (∑k∈range (2*m+1),thueOddWeight k*thueOddWeight (2*m-k)) = thueConvolution m := by
  rw [sum_range_succ,int_pair_sum]
  have hEven (k : ℕ) : thueOddWeight (2*k) = 0 := by
    simp [thueOddWeight]
  have hOdd (k : ℕ) : thueOddWeight (2*k+1)=thueWeight k := by
    simp [thueOddWeight,show (2*k+1)%2=1 by omega,show (2*k+1)/2=k by omega]
  simp only [hEven,zero_mul,zero_add,add_zero]
  apply sum_congr rfl
  intro k hk
  have h := mem_range.mp hk
  rw [show 2*m-(2*k+1)=2*(m-1-k)+1 by omega,hOdd,hOdd]

theorem thueOddWeight_infinite_even_holes (j : ℕ) :
    let n := 2 * 2^(2*j+1)
    (∑ k∈range (n+1), thueOddWeight k*thueOddWeight (n-k))=0 :=
  (thueOddWeight_convolution _).trans (thueConvolution_dyadic_hole j)

private theorem prefix_square_le_one (m : ℕ) : (thuePrefix m)^2≤1 := by
  by_cases h : m%2=0
  · rw [show m=2*(m/2) by omega,prefix_even]
    decide
  · rw [show m=2*(m/2)+1 by omega,prefix_odd]
    rcases thueSign_values (m/2) with hh|hh <;> rw [hh] <;> decide

theorem thueConvolution_dyadic_square_error (j : ℕ) :
    (∑m∈range (2^j),(thueConvolution m-(m:ℤ))^2) ≤ 4*6^j+8*2^j := by
  calc
    _ ≤ ∑ m∈range (2^j), (2*(thueSignConvolution m)^2+8) := by
      apply sum_le_sum
      intro m _
      rw [thueConvolution_formula]
      nlinarith only [sq_nonneg (2*thuePrefix m-thueSignConvolution m),prefix_square_le_one m]
    _ = 2*(∑m∈range (2^j),(thueSignConvolution m)^2)+8*2^j := by
      rw [sum_add_distrib,←mul_sum]
      simp [mul_comm]
    _ ≤ _ := by linarith [thueSignConvolution_dyadic_energy j]

private theorem tm_dyad_prev (d : ℕ) : 3*thueSignConvolution (2^d-1) = 1-(-2)^d := by
  induction d with
  | zero => simp [thueSignConvolution]
  | succ d ih =>
    have hpos : 0<(2:ℕ)^d := by positivity
    rw [pow_succ,show 2^d*2-1=2*(2^d-1)+1 by omega,thueSignConvolution_odd,
      show 2^d-1+1=2^d by omega,tm_dyad,pow_succ]
    linarith

private theorem tm_dyad_next (d : ℕ) : 3*thueSignConvolution (2^d+1) = -5-(-2)^d := by
  induction d with
  | zero => change 3*thueSignConvolution (2*1)= -5-1
            rw [thueSignConvolution_even]; norm_num [thueSignConvolution,sign_zero]
  | succ d ih =>
    rw [pow_succ,Nat.mul_comm (2^d) 2,thueSignConvolution_odd,tm_dyad,pow_succ]
    linarith

private theorem sign_last (d : ℕ) : thueSign (2^d-1) = (-1)^d := by
  induction d with
  | zero => simp [sign_zero]
  | succ d ih =>
    have hpos : 0<(2:ℕ)^d := by positivity
    rw [pow_succ,show 2^d*2-1=2*(2^d-1)+1 by omega,sign_odd,ih,pow_succ]
    ring

/-- Both adjacent even targets have large convolution next to every prescribed hole. -/
theorem thueConvolution_neighbours (j : ℕ) :
    let m : ℕ := 2^(2*j+1)
    3*thueConvolution (m-1)=4*((m:ℤ)+1) ∧ 3*thueConvolution (m+1)=4*((m:ℤ)-2) := by
  let m := 2^(2*j+1)
  have hpos : 0<m := by dsimp [m]; positivity
  have hm : (m:ℤ)=(2:ℤ)^(2*j+1) := by simp [m]
  have h1 := tm_dyad_prev (2*j+1)
  have h2 := tm_dyad_next (2*j+1)
  rw [(show Odd (2*j+1) from ⟨j,rfl⟩).neg_pow (2:ℤ),←hm] at h1 h2
  have hs : thueSign (m-1)= -1 := by
    rw [show m-1=2^(2*j+1)-1 from rfl,sign_last,(show Odd (2*j+1) from ⟨j,rfl⟩).neg_pow (1:ℤ),one_pow]
  have hpow (d : ℕ) : thueSign (2^d)= -1 := by
    induction d with
    | zero => norm_num [thueSign,sign_zero]
    | succ d ih => rw [pow_succ,Nat.mul_comm,sign_even,ih]
  have hp : thuePrefix m=0 := by rw [show m=2*(2^(2*j)) by simp [m,pow_succ,Nat.mul_comm],prefix_even]
  have hp1 : thuePrefix (m-1)=1 := by
    have hh := sum_range_succ thueSign (m-1)
    rw [show m-1+1=m by omega,←thuePrefix,←thuePrefix,hp,hs] at hh
    omega
  have hp2 : thuePrefix (m+1)= -1 := by
    unfold thuePrefix
    rw [sum_range_succ,←thuePrefix,hp,hpow (2*j+1),zero_add]
  change _ ∧ _
  constructor
  · change 3*thueConvolution (m-1)=4*((m:ℤ)+1)
    rw [thueConvolution_formula,hp1,Nat.cast_sub (by omega : 1≤m)]
    change 3*thueSignConvolution (m-1)=_ at h1
    push_cast
    linarith
  · change 3*thueConvolution (m+1)=4*((m:ℤ)-2)
    rw [thueConvolution_formula,hp2,Nat.cast_add,Nat.cast_one]
    change 3*thueSignConvolution (m+1)=_ at h2
    linarith
end GoldbachPartial