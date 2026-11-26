import SignedMajorCharging

/- Arithmetic definitions and proofs in this file were selected from
DFQDZZ/goldbach-proofs, lean/PEqualNP/Outside/L_goldbach_arc_major_floor.lean,
commit e4ab24712555ae8c2c926adf19d368a9fb392c35.
The Pinned316 namespace permits simultaneous imports with the original.
The CRT and prime-power arguments are adapted in the pinned source from
XianWu18 (#207) and wzhxzkk (#203), Apache-2.0. We use the finite geometric
series in place of the additive-character library for two auxiliary steps.
The 9/16 estimate and Fejer floor below are the new results. -/
namespace Pinned316
open Filter Finset MeasureTheory
open scoped Topology
namespace GoldbachMajorArc
noncomputable section
def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def primeSum (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (primeWeight k : ℂ) * phase ((k : ℝ) * t)

def integrand (n : ℕ) (t : ℝ) : ℂ := (primeSum n t) ^ 2 * phase (-(n : ℝ) * t)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2
def arcs (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧
  Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def unitMean (q a : ℕ) : ℂ :=
  (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q), phase ((r : ℝ) * ((a : ℝ) / q))) /
    (q.totient : ℂ)
end
end GoldbachMajorArc
namespace GoldbachMajorArc.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  let z := Complex.exp (2*Real.pi*Complex.I*(h:ℂ)/m)
  have he (k : ℕ) : phase m h k = z^k := by
    unfold phase z
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hmn : (m:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hm : z^m = 1 := by
    unfold z
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_nat_mul_two_pi_mul_I h using 2
    field_simp
  rw [he,he]
  conv_rhs => rw [←Nat.mod_add_div a m]
  rw [pow_add,pow_mul,hm,one_pow,mul_one]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachMajorArc.RamanujanCRT
namespace GoldbachMajorArc.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let z := Complex.exp (2*Real.pi*Complex.I*(h:ℂ)/q)
    have hz (a : ℕ) : E ((h:ℝ)*a/q) = z^a := by
      dsimp only [E,z]
      rw [← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    simp_rw [hz]
    have hone : z=1 ↔ q∣h := Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq.ne'
    by_cases hd : q∣h
    · simp [hone.mpr hd,hd]
    · simp only [hd,↓reduceIte]
      have hqn : (q:ℂ)≠0 := by exact_mod_cast hq.ne'
      have hpow : z^q = 1 := by
        unfold z
        rw [← Complex.exp_nat_mul]
        convert Complex.exp_nat_mul_two_pi_mul_I h using 2
        field_simp
      have hh := geom_sum_mul z q
      rw [hpow,sub_self] at hh
      exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr (fun he => hd (hone.mp he)))
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachMajorArc.RamanujanPower

namespace GoldbachMajorArc

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

theorem ram_unit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [ram_unit_power hp k h hc', ram_unit_power hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

theorem unitMean_eq_ram {q a : ℕ} (h : a.Coprime q) :
    unitMean q a = ram q 1 / (q.totient : ℂ) := by
  calc
    _ = ram q a / (q.totient : ℂ) := by
      apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
      apply sum_congr rfl
      intro k _
      exact congrArg phase (by ring)
    _ = _ := congrArg (fun z : ℂ => z / (q.totient : ℂ)) (ram_unit q a h)

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

theorem sum_centers_eq_coefficient (q n : ℕ) :
    (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      (unitMean q a) ^ 2 * phase (-(n : ℝ) * ((a : ℝ) / q))) = coefficient q n := by
  unfold coefficient ram
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [unitMean_eq_ram (mem_filter.mp ha).2]
  congr 1
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

end
end GoldbachMajorArc
namespace GoldbachMajorArc

open Finset
noncomputable section

private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]

private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos, le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)
def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)
private theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity
def modeledContribution (n : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 (cutoff n), coefficient q n * (kernelMass n (width n q) : ℂ)
private def truncatedMass (n q : ℕ) : ℝ :=
  if q ≤ cutoff n then kernelMass n (width n q) else 0

private theorem truncated_nonneg (n q : ℕ) : 0 ≤ truncatedMass n q := by
  unfold truncatedMass
  split_ifs
  · exact intervalIntegral.integral_nonneg (by linarith [width_nonneg n q]) fun _ _ => sq_nonneg _
  · exact le_rfl

private theorem truncated_mono {n : ℕ} (hn : 0 < n) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j) :
    truncatedMass n j ≤ truncatedMass n i := by
  by_cases hj : j≤cutoff n
  · simp only [truncatedMass, ite_eq_left hj, ite_eq_left (hij.trans hj)]
    apply kernelMass_mono (width_nonneg _ _)
    have hnr : (0:ℝ) < n := by exact_mod_cast hn
    have hir : (0:ℝ) < i := by exact_mod_cast hi
    unfold width
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hir hnr)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hnr.le)
  · rw [truncatedMass, ite_eq_right hj]
    exact truncated_nonneg n i

/-- The precise real part of the pinned, signed model has both denominator 1 and
denominator 2 main contributions for even n. -/
theorem model_nine_sixteenths {n : ℕ} (hn : 0<n) (he : Even n) (hQ : 2≤cutoff n) :
    (9/16:ℝ)*(kernelMass n (width n 1)+kernelMass n (width n 2)) ≤
      (modeledContribution n).re := by
  let P := (range (cutoff n+1)).filter Nat.Prime
  have hp (p:ℕ) (hm : p∈P) : p.Prime := (mem_filter.mp hm).2
  have h2 : 2∈P := mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_two⟩
  have h := GoldbachPartial.signed_major_prime_floor he P hp h2 (truncatedMass n)
    (truncated_nonneg n) (truncated_mono hn)
  have hr : (modeledContribution n).re =
      ∑ q ∈ Icc 1 (cutoff n), (coefficient q n).re * truncatedMass n q := by
    rw [modeledContribution, Complex.re_sum]
    refine sum_congr rfl fun q hq => ?_
    simp [truncatedMass, (mem_Icc.mp hq).2, Complex.mul_re]
  rw [hr,reindex_denominators (cutoff n) n _ (fun q hq => by simp [truncatedMass,not_le.mpr hq])]
  change _ ≤ ∑ t ∈ P.powerset,(∏ p ∈ t,GoldbachPartial.majorPrimeLocal p n)*truncatedMass n (∏ p ∈ t,p)
  exact (show (9/16:ℝ)*(kernelMass n (width n 1)+kernelMass n (width n 2)) =
    (9/16:ℝ)*(truncatedMass n 1+truncatedMass n 2) by
      simp [truncatedMass,show 1≤cutoff n by omega,hQ]).trans_le h

theorem model_asymptotic_explicit {n : ℕ} (hn : 0<n) (he : Even n) (hQ : 2≤cutoff n)
    (hhalf : (cutoff n:ℝ)/n ≤ 1/2) :
    (9/8:ℝ)*((n:ℝ)+2)-(27/32:ℝ)*((n:ℝ)/cutoff n) ≤ (modeledContribution n).re := by
  have hp : (0:ℝ) < cutoff n := by exact_mod_cast (show 0<cutoff n by omega)
  have hw := GoldbachPartial.major_two_window_floor hn hp hhalf
  have hm := model_nine_sixteenths hn he hQ
  have heq₁ : kernelMass n (width n 1) = GoldbachPartial.fejerWindowEnergy n ((cutoff n:ℝ)/n) := by
    simp only [width,Nat.cast_one,one_mul]; rfl
  have heq₂ : kernelMass n (width n 2) = GoldbachPartial.fejerWindowEnergy n ((cutoff n:ℝ)/(2*n)) := by rfl
  rw [heq₁,heq₂] at hm
  rw [show (n:ℝ)/(2*(cutoff n:ℝ))=((n:ℝ)/cutoff n)/2 by ring] at hw
  linarith only [hw,hm]

theorem model_floor_35_over_32 {n : ℕ} (hn : 0<n) (he : Even n)
    (hQ : 27≤cutoff n) (hhalf : (cutoff n:ℝ)/n ≤ 1/2) :
    (35/32:ℝ)*n ≤ (modeledContribution n).re := by
  have hw := model_asymptotic_explicit hn he (by omega) hhalf
  have hQ' : (27:ℝ) ≤ cutoff n := by exact_mod_cast hQ
  have hh : (n:ℝ)/cutoff n ≤ (n:ℝ)/27 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hQ'
  linarith only [hw,hh]

def majorContribution (n : ℕ) : ℂ := ∫ t in (0:ℝ)..1, (arcs n).indicator (integrand n) t

def modelError (n q a : ℕ) (β : ℝ) : ℝ :=
  let r : ℝ := (a : ℝ) / q
  ‖integrand n (r + β) - (unitMean q a * kernel n β) ^ 2 * phase (-(n : ℝ) * (r + β))‖

def totalArcError (n : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ range (q + 1),
    ∫ β in -(width n q)..(width n q), modelError n q a β

theorem cutoff_tendsto : Tendsto cutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2^b)] with n hn
  exact (Nat.le_log_of_pow_le (by decide : 1<2) (show 2^b≤n+2 by omega)).trans
    (Nat.le_self_pow (by decide : 2≠0) _)

/-- The three arguments are the public declarations cutoff_separated, major_error and
totalArcError_sublinear in the pinned source. Every smaller constant than 9/8 works. -/
theorem actual_floor_of_published_estimates
    (hsep : ∀ᶠ n : ℕ in atTop, 2*(cutoff n)^2<n)
    (herr : ∀ {n : ℕ}, 2*(cutoff n)^2<n →
      ‖majorContribution n-modeledContribution n‖ ≤ totalArcError n)
    (hsmall : Tendsto (fun n : ℕ => totalArcError n/n) atTop (𝓝 0))
    {c : ℝ} (hc : c < 9/8) :
    ∀ᶠ n : ℕ in atTop, Even n → c*n ≤ (majorContribution n).re := by
  have hQ : Tendsto (fun n : ℕ => (cutoff n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp cutoff_tendsto
  let ε : ℝ := (9/8-c)/2
  have heps : 0<ε := by dsimp [ε]; linarith only [hc]
  filter_upwards [hsep, cutoff_tendsto.eventually_ge_atTop 2,
    hsmall.eventually_lt_const heps, (hQ.const_div_atTop (27/32:ℝ)).eventually_lt_const heps]
    with n hs h2 hE hW
  intro he
  have hn : 0<n := by omega
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have h2n : 2*cutoff n ≤ n := by
    have hle := Nat.le_self_pow (by decide : 2≠0) (cutoff n)
    omega
  have hhalf : (cutoff n:ℝ)/n ≤ 1/2 := by
    apply (div_le_iff₀ hn').mpr
    have hle : 2*(cutoff n:ℝ) ≤ n := by exact_mod_cast h2n
    linarith only [hle]
  have hm := model_asymptotic_explicit hn he h2 hhalf
  have hWn := mul_le_mul_of_nonneg_right hW.le hn'.le
  have hx : (27/32:ℝ)/(cutoff n:ℝ)*n=(27/32:ℝ)*((n:ℝ)/cutoff n) := by ring
  rw [hx] at hWn
  have hEn := (div_lt_iff₀ hn').mp hE
  have hdist := Complex.re_le_norm (modeledContribution n-majorContribution n)
  rw [Complex.sub_re,norm_sub_rev] at hdist
  have heq : 2*ε=9/8-c := by dsimp [ε]; ring
  have hprod := congrArg (fun x : ℝ => x*n) heq
  linarith only [hm,hWn,hEn,hdist,herr hs,hprod]

end
end GoldbachMajorArc
end Pinned316
