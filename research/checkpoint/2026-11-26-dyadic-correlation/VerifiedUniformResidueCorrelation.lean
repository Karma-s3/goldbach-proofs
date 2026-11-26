import VerifiedResidueWitnessCount
import LocalAdmissibleZCount
namespace GoldbachPartial
open Finset
private theorem admissible_pair_crt {r s : ℕ} (hrs : r.Coprime s) (c : ℕ) :
    admissibleZCount (r*s) c=admissibleZCount r c*admissibleZCount s c := by
  let e := ZMod.chineseRemainder hrs
  let P (n : ℕ) (a : ZMod n) := IsUnit a ∧ IsUnit ((c : ZMod n)-a)
  have he (x : ZMod (r*s)) : P (r*s) x ↔ P r (e x).1 ∧ P s (e x).2 := by
    have hu (z : ZMod (r*s)) : IsUnit z ↔ IsUnit (e z).1 ∧ IsUnit (e z).2 := by
      exact (show IsUnit z ↔ IsUnit (e z) from ⟨fun h => h.map e.toMonoidHom, fun h => by simpa using h.map e.symm.toMonoidHom⟩).trans Prod.isUnit_iff
    dsimp only [P]
    rw [hu,hu,map_sub,map_natCast]
    change (_ ∧ _) ∧ (_ ∧ _) ↔ (_ ∧ _) ∧ (_ ∧ _)
    tauto
  let f := (e.toEquiv.subtypeEquiv he).trans Equiv.subtypeProdEquivProd
  exact (Nat.card_congr f).trans (Nat.card_prod _ _)

private theorem admissible_pair_one (c : ℕ) : admissibleZCount 1 c=1 := by
  have h : ∀ a : ZMod 1, IsUnit a := fun a => Subsingleton.elim (1:ZMod 1) a ▸ isUnit_one
  have he : {a : ZMod 1 // IsUnit a ∧ IsUnit ((c:ZMod 1)-a)} ≃ ZMod 1 :=
    Equiv.subtypeUnivEquiv (fun a => ⟨h a,h _⟩)
  exact (Nat.card_congr he).trans (Nat.card_zmod 1)

private theorem admissible_count_nat {q : ℕ} (hq : 0<q) (c : ℕ) :
    (residueWindowAdmissible q c).card=admissibleZCount q c := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let f : (residueWindowAdmissible q c) ≃
      {a : ZMod q // IsUnit a ∧ IsUnit ((c : ZMod q)-a)} := {
    toFun := fun x => by
      have hx := mem_filter.mp x.property
      have hxq := mem_range.mp hx.1
      have hle : x.val≤c+q := by omega
      have hcast : (((c+q-x.val)%q:ℕ):ZMod q)=(c:ZMod q)-(x.val:ZMod q) := by
        simp [Nat.cast_sub hle]
      exact ⟨(x.val:ZMod q),(ZMod.isUnit_iff_coprime _ _).mpr hx.2.1,
        hcast ▸ (ZMod.isUnit_iff_coprime _ _).mpr hx.2.2⟩
    invFun := fun x => by
      have hxq := ZMod.val_lt x.val
      have hle : x.val.val≤c+q := by omega
      refine ⟨x.val.val,mem_filter.mpr ⟨mem_range.mpr hxq,?_,?_⟩⟩
      · apply (ZMod.isUnit_iff_coprime _ _).mp
        simpa only [ZMod.natCast_zmod_val] using x.property.1
      · apply (ZMod.isUnit_iff_coprime _ _).mp
        simpa [residueWindowPartner,Nat.cast_sub hle] using x.property.2
    left_inv := fun x => by
      apply Subtype.ext
      exact (ZMod.val_natCast _ _).trans (Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp x.property).1))
    right_inv := fun x => Subtype.ext (ZMod.natCast_zmod_val _) }
  simpa only [admissibleZCount,Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr f

private noncomputable def residueEulerLower (p : ℕ) : ℝ :=
  if p=2 then 2 else 1-1/((p:ℝ)-1)^2

private theorem residueEulerLower_nonneg {p : ℕ} (hp : p.Prime) : 0≤residueEulerLower p := by
  unfold residueEulerLower
  split_ifs with he
  · norm_num
  have hlarge : 3≤p := by have := hp.two_le; omega
  have hreal : (3:ℝ)≤p := by exact_mod_cast hlarge
  apply sub_nonneg.mpr
  apply (div_le_one (by nlinarith [sq_nonneg ((p:ℝ)-2)] : 0<((p:ℝ)-1)^2)).mpr
  nlinarith [sq_nonneg ((p:ℝ)-2)]

private theorem normalized_admissible_product (t : ℕ)
    (hodd : ∀ p k c : ℕ, p.Prime → 2<p → 1-1/((p:ℝ)-1)^2 ≤
      ((p^(k+1):ℕ):ℝ)*admissibleZCount (p^(k+1)) c/((p^(k+1)).totient:ℝ)^2)
    (htwo : ∀ k : ℕ, (2:ℝ)≤((2^(k+1):ℕ):ℝ)*admissibleZCount (2^(k+1)) (2*t)/((2^(k+1)).totient:ℝ)^2) :
    ∀ q : ℕ, 0<q → (∏ p∈q.primeFactors,residueEulerLower p) ≤
      (q:ℝ)*admissibleZCount q (2*t)/(q.totient:ℝ)^2 := by
  apply Nat.recOnPosPrimePosCoprime
  · rintro p (_|k) hp hk _
    · omega
    rw [Nat.primeFactors_prime_pow (by omega) hp,prod_singleton]
    by_cases he : p=2
    · subst p
      simpa [residueEulerLower] using htwo k
    · rw [residueEulerLower,ite_eq_right he]
      exact hodd p k (2*t) hp (by have := hp.two_le; omega)
  · omega
  · simp [admissible_pair_one]
  · intro a b ha hb hab hA hB _
    rw [Nat.primeFactors_mul (by omega) (by omega),prod_union hab.disjoint_primeFactors,
      Nat.totient_mul hab,admissible_pair_crt hab]
    push_cast
    have hn : 0≤∏ p∈b.primeFactors,residueEulerLower p :=
      prod_nonneg (fun p hp => residueEulerLower_nonneg (Nat.prime_of_mem_primeFactors hp))
    apply (mul_le_mul (hA (by omega)) (hB (by omega)) hn (by positivity)).trans
    apply le_of_eq
    ring

theorem even_residue_count_floor (q t : ℕ) (hq : 0<q) (he : 2∣q) :
    (9:ℝ)/8 ≤ (q:ℝ)*(residueWindowAdmissible q (2*t)).card/(q.totient:ℝ)^2 := by
  have hprod := normalized_admissible_product t admissibleZCount_odd_power (fun k => admissibleZCount_two_power k t) q hq
  rw [admissible_count_nat hq]
  have hm : 2∈q.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two,he,hq.ne'⟩
  let B := q.primeFactors.erase 2
  have ho (p : ℕ) (hp : p∈B) : p.Prime ∧ 2<p := by
    obtain ⟨hne,mem⟩ := mem_erase.mp hp
    have hprime := Nat.prime_of_mem_primeFactors mem
    exact ⟨hprime,by have := hprime.two_le; omega⟩
  have hid : (∏ p∈q.primeFactors,residueEulerLower p)=2*(∏ p∈B,(1-1/((p:ℝ)-1)^2)) := by
    conv_lhs => rw [←insert_erase hm,prod_insert (notMem_erase 2 _)]
    change residueEulerLower 2 * _ = _
    rw [show residueEulerLower 2 = 2 by norm_num [residueEulerLower]]
    congr 1
    exact prod_congr rfl (fun p hp => ite_eq_right (mem_erase.mp hp).1)
  rw [hid] at hprod
  linarith only [odd_prime_product_lower ho,hprod]

theorem uniform_even_residue_primeCorr_mass :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ N H q t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → 2∣q →
      9*(X:ℝ)*H/(32*q)≤∑ m∈(Ioc N (N+H)).filter (fun m => m%q=(2*t)%q),corr m := by
  filter_upwards [admissible_residue_primeCorr_mass] with X hx
  intro N H q t hn ht hm hh hq hlog he
  apply le_trans _ (hx N H q (2*t) hn ht hm hh hq hlog)
  have h := mul_le_mul_of_nonneg_right (even_residue_count_floor q t hq he) (show 0≤(X:ℝ)*H/(4*q) by positivity)
  have hq' : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  convert h using 1
  · ring
  · field_simp

theorem uniform_even_residue_primeCorr_witness :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ N H q t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → q≤H → 2∣q →
      ∃ m∈Ioc N (N+H), m%q=(2*t)%q ∧ Even m ∧ 3*(m:ℝ)/160≤corr m := by
  filter_upwards [admissible_even_residue_primeCorr_witness] with X hx
  intro N H q t hn ht hm hh hq hlog hqh he
  obtain ⟨m,h1,h2,h3,h4⟩ := hx N H q t hn ht hm hh hq hlog hqh he
  refine ⟨m,h1,h2,h3,le_trans ?_ h4⟩
  have h := mul_le_mul_of_nonneg_left (even_residue_count_floor q t hq he) (show 0≤(m:ℝ)/60 by positivity)
  convert h using 1 <;> ring


theorem uniform_even_residue_primeCorr_count :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ N H q t : ℕ, 3*X≤N → N+H≤5*X → H≤X →
      (X:ℝ)/Real.log X≤H → 0<q → (q:ℝ)≤Real.log X → q≤H → 2∣q →
      (H:ℝ)/(40*Real.log 4*q*Real.log (5*(X:ℝ))) ≤
        (residueAbsoluteWitnesses N H q t).card := by
  filter_upwards [even_residue_absolute_count_of_local_factor] with X h
  intro N H q t h1 h2 h3 h4 hq hL hH he
  apply h N H q t h1 h2 h3 h4 hq hL hH he
  have hp : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hR := (le_div_iff₀ (pow_pos hp 2)).mp (even_residue_count_floor q t hq he)
  exact_mod_cast (show (q.totient:ℝ)^2 ≤ (q:ℝ)*(residueWindowAdmissible q (2*t)).card by
    nlinarith only [hR,sq_nonneg (q.totient:ℝ)])

end GoldbachPartial