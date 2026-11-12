import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Wilson

/-!
# Alternative proof of quadratic reciprocity

This file proves QR with the method we discussed in class.
-/
namespace LeoQuadraticReciprocity

variable (p : ℕ) [instPp : Fact p.Prime]
variable (q : ℕ) [instPq : Fact q.Prime]
variable (hpq : p ≠ q)

/-- Units modulo `p * q` whose canonical representative is strictly below half of `p * q`. -/
def leftSubset : Set (ZMod (p * q))ˣ :=
  {k | (k.val.val : ℚ) < (p * q : ℚ) / 2}

/-- Pairs of units whose first component has canonical representative strictly below `p / 2`. -/
def rightSubset : Set ((ZMod p)ˣ × (ZMod q)ˣ) :=
  {ab | (ab.fst.val.val : ℚ) < (p : ℚ) / 2}

noncomputable def leftFinset : Finset (ZMod (p * q))ˣ :=
  (Set.toFinite (leftSubset p q)).toFinset

noncomputable def rightFinset : Finset ((ZMod p)ˣ × (ZMod q)ˣ) :=
  (Set.toFinite (rightSubset p q)).toFinset

def crt_isomorphism_mul :
    (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv
    (ZMod.chineseRemainder ((Nat.coprime_primes instPp.out instPq.out).2 hpq)).toMulEquiv).trans
      MulEquiv.prodUnits

@[simp]
lemma crt_isomorphism_mul_neg (x : (ZMod (p * q))ˣ) :
    crt_isomorphism_mul p q hpq (-x) = -crt_isomorphism_mul p q hpq x := by
  let crt := ZMod.chineseRemainder ((Nat.coprime_primes instPp.out instPq.out).2 hpq)
  apply Prod.ext <;> apply Units.ext
  · exact congrArg Prod.fst (crt.map_neg x.val)
  · exact congrArg Prod.snd (crt.map_neg x.val)

@[simp]
lemma crt_preimage_uniqueness (a : (ZMod p)ˣ) (b : (ZMod q)ˣ) :
    ∃! k ∈ leftSubset p q,
      crt_isomorphism_mul p q hpq k = (a, b) ∨ crt_isomorphism_mul p q hpq k = -(a, b) := by
  let φ := crt_isomorphism_mul p q hpq
  let k' := φ.symm (a, b)
  have hval_neg : (-k').val.val = p * q - k'.val.val := by
    have hn : 1 < p * q := by nlinarith [instPp.out.one_lt, instPq.out.one_lt]
    let : Fact (1 < p * q) := ⟨hn⟩
    let : NeZero (p * q) :=
      ⟨Nat.mul_ne_zero instPp.out.ne_zero instPq.out.ne_zero⟩
    let : NeZero (k'.val : ZMod (p * q)) := ⟨Units.ne_zero k'⟩
    simpa only [Units.val_neg] using
      (ZMod.val_neg_of_ne_zero (n := p * q) (a := (k'.val : ZMod (p * q))))
  have hval_negQ : ((-k').val.val : ℚ) = (p * q : ℚ) - k'.val.val := by
    rw [hval_neg, Nat.cast_sub (Nat.le_of_lt (ZMod.val_lt _))]
    norm_num
  rcases lt_trichotomy (k'.val.val : ℚ) ((p * q : ℚ) / 2) with hLt|hEq|hGt
  · use k'
    constructor
    · constructor -- existence
      · exact hLt -- k ∈ L
      · left; exact MulEquiv.apply_symm_apply φ (a, b) -- equality
    · rintro y ⟨hymem, hPos | hNeg⟩ -- uniqueness, using isomorphism injectivity
      · apply φ.injective
        rw [hPos, MulEquiv.apply_symm_apply]
      · exfalso -- this case is not possible
        have hy_eq_neg : y = -k' := by
          apply φ.injective
          rw [hNeg, crt_isomorphism_mul_neg, MulEquiv.apply_symm_apply]
        change (y.val.val : ℚ) < (p * q : ℚ) / 2 at hymem
        rw [hy_eq_neg] at hymem
        linarith
  · have hhalfQ : (2 : ℚ) * (k'.val.val : ℚ) = p * q := by linarith [hEq]
    have hneg_eq_self : -k' = (k' : ZMod (p * q)) := by
      apply (ZMod.neg_eq_self_iff (k' : ZMod (p * q))).mpr
      right
      exact_mod_cast hhalfQ
    have hsum_eq_zero : (k' : ZMod (p * q)) + k' = 0 := by
      nth_rw 1 [←hneg_eq_self]
      ring
    have htwo_eq_zero : (2 : ZMod (p * q)) = 0 := by
      calc
        (2 : ZMod (p * q)) = 1 + 1 := by norm_num
        _ = k'.val * k'⁻¹ + k'.val * k'⁻¹ := by rw [←Units.mul_inv]
        _ = 0 := by rw [←right_distrib, hsum_eq_zero, Units.mul_left_eq_zero]
    have hdiv : p * q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p * q)).mp htwo_eq_zero
    have hpq_le_two : p * q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    nlinarith [instPp.out.one_lt, instPq.out.one_lt]
  · use -k'
    dsimp
    constructor
    · constructor
      · change ((-k').val.val : ℚ) < (p * q : ℚ) / 2
        rw [hval_negQ]
        linarith
      · right
        rw [crt_isomorphism_mul_neg, MulEquiv.apply_symm_apply]
        dsimp
    · rintro y ⟨hymem, hPos | hNeg⟩ -- this is the exact mirror of the lt case
      · exfalso
        change (y.val.val : ℚ) < (p * q : ℚ) / 2 at hymem
        have hy_eq_pos : y = k' := by
          apply φ.injective
          rw [hPos, MulEquiv.apply_symm_apply]
        rw [hy_eq_pos] at hymem
        linarith
      · apply φ.injective
        rw [hNeg, crt_isomorphism_mul_neg, MulEquiv.apply_symm_apply]
        dsimp

include hpq in
@[simp]
lemma prod_left_mod_p (hq : q ≠ 2) : (∏ k ∈ leftFinset p q, (k.val.val : ZMod p))
    * (legendreSym p q) = (-1) ^ ((q - 1) / 2) := by
  have hqodd : Odd q := instPq.out.odd_of_ne_two hq
  -- The case p = 2 is immediate: every unit reduces to 1.
  by_cases hp : p = 2
  · subst p
    have hu (k : (ZMod (2 * q))ˣ) :
        (k.val.val : ZMod 2) = 1 := by
      have hc : k.val.val.Coprime 2 :=
        (Nat.coprime_mul_iff_right.mp
          (ZMod.val_coe_unit_coprime k)).1
      exact (Nat.coprime_two_right.mp hc).natCast_zmod_two
    have hleg : (legendreSym 2 (q : ℤ) : ZMod 2) = 1 := by
      rw [legendreSym.eq_pow]
      simpa using hqodd.natCast_zmod_two
    simp [hu, hleg]
  let : NeZero (p * q) :=
    ⟨Nat.mul_ne_zero instPp.out.ne_zero instPq.out.ne_zero⟩
  let h := p / 2
  let m := q / 2
  let N := p * m + h
  have hpmod : p % 2 = 1 :=
    instPp.out.eq_two_or_odd.resolve_left hp
  have hqmod : q % 2 = 1 :=
    instPq.out.eq_two_or_odd.resolve_left hq
  have hpform : p = 2 * h + 1 := by
    dsimp [h]
    omega
  have hqform : q = 2 * m + 1 := by
    dsimp [m]
    omega
  have hN : 2 * N + 1 = p * q := by
    dsimp only [N]
    rw [hqform]
    nlinarith [hpform]
  have hN' : N = q * h + m := by
    dsimp only [N]
    rw [hpform, hqform]
    ring
  have hcut (n : ℕ) :
      (n : ℚ) < (p * q : ℚ) / 2 ↔ n < N + 1 := by
    have hNQ : (2 : ℚ) * N + 1 = (p : ℚ) * q := by
      exact_mod_cast hN
    constructor
    · intro hn
      have hn' : (n : ℚ) < (N : ℚ) + 1 := by linarith
      exact_mod_cast hn'
    · intro hn
      have hn' : n ≤ N := by omega
      have hnQ : (n : ℚ) ≤ N := by exact_mod_cast hn'
      linarith
  let A := (Finset.range (N + 1)).filter
    (fun n => n.Coprime (p * q))
  -- Replace units by their canonical natural representatives.
  have hleft :
      (∏ k ∈ leftFinset p q, (k.val.val : ZMod p)) =
        ∏ n ∈ A, (n : ZMod p) := by
    refine Finset.prod_bij (fun k _ => k.val.val) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : (k.val.val : ℚ) < (p * q : ℚ) / 2 := by
        simpa [leftFinset, leftSubset] using hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((hcut _).mp hk'),
          ZMod.val_coe_unit_coprime k⟩
    · intro x hx y hy hxy
      exact Units.ext ((ZMod.val_injective (p * q)) hxy)
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hn, hc⟩
      have hnN := Finset.mem_range.mp hn
      have hnlt : n < p * q := by omega
      let u := ZMod.unitOfCoprime n hc
      have hu : u.val.val = n := by
        change (n : ZMod (p * q)).val = n
        exact ZMod.val_natCast_of_lt hnlt
      have humem : u ∈ leftFinset p q := by
        simpa only [leftFinset, Set.Finite.mem_toFinset,
          leftSubset, Set.mem_ofPred_eq, hu] using
          (hcut n).mpr hnN
      exact ⟨u, humem, hu⟩
    · intro k hk
      rfl
  have hnz {n : ℕ} (hn0 : 0 < n) (hnp : n < p) :
      (n : ZMod p) ≠ 0 := by
    intro hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    exact Nat.not_dvd_of_pos_of_lt hn0 hnp hz
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff q p).mp hz
    exact hpq
      ((Nat.prime_dvd_prime_iff_eq instPp.out instPq.out).mp hd)
  -- Multiples of p contribute 1 instead of 0.
  let f : ℕ → ZMod p :=
    fun n => if (n : ZMod p) = 0 then 1 else n
  let H : ZMod p :=
    ∏ i ∈ Finset.range h, ((i + 1 : ℕ) : ZMod p)
  have hf0 : f 0 = 1 := by simp [f]
  have hfshift (n : ℕ) : f (p + n) = f n := by
    simp [f]
  have hH : H ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact hnz (by omega) (by omega)
  have hpartial :
      (∏ i ∈ Finset.range (h + 1), f i) = H := by
    rw [Finset.prod_range_succ', hf0, mul_one]
    apply Finset.prod_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hi0 := hnz (n := i + 1) (by omega) (by omega)
    dsimp only [f]
    rw [ite_eq_right hi0]
  -- Each complete interval of length p contributes -1.
  have hblock : (∏ i ∈ Finset.range p, f i) = -1 := by
    rw [Finset.prod_range_eq_mul_Ico f instPp.out.pos,
      hf0, one_mul]
    calc
      (∏ i ∈ Finset.Ico 1 p, f i) =
          ∏ i ∈ Finset.Ico 1 p, (i : ZMod p) := by
        apply Finset.prod_congr rfl
        intro i hi
        rcases Finset.mem_Ico.mp hi with ⟨hi0, hip⟩
        dsimp only [f]
        rw [ite_eq_right (hnz (by omega) hip)]
      _ = -1 := by
        rw [Finset.prod_Ico_eq_prod_range]
        simpa only [Nat.factorial_eq_prod_range_add_one,
          Nat.cast_prod, Nat.add_comm] using
          (ZMod.wilsons_lemma p)
  have hblocks (t : ℕ) :
      (∏ i ∈ Finset.range (p * t + (h + 1)), f i) =
        (-1 : ZMod p) ^ t * H := by
    induction t with
    | zero =>
        simpa using hpartial
    | succ t ih =>
        have ht :
            p * (t + 1) + (h + 1) =
              p + (p * t + (h + 1)) := by ring
        rw [ht, Finset.prod_range_add, hblock]
        simp_rw [hfshift]
        rw [ih, pow_succ]
        ring
  have hfull :
      (∏ i ∈ Finset.range (N + 1), f i) =
        (-1 : ZMod p) ^ m * H := by
    simpa only [N, Nat.add_assoc] using hblocks m
  -- The multiples of q in this range are 0, q, ..., h*q.
  let B := (Finset.range (N + 1)).filter (fun n => q ∣ n)
  have hBindex :
      (∏ n ∈ B, f n) =
        ∏ j ∈ Finset.range (h + 1), f (q * j) := by
    symm
    refine Finset.prod_bij (fun j _ => q * j) ?_ ?_ ?_ ?_
    · intro j hj
      have hj' : j ≤ h := by
        have := Finset.mem_range.mp hj
        omega
      have hjq := Nat.mul_le_mul_left q hj'
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ?_, ⟨j, rfl⟩⟩
      omega
    · intro i hi j hj hij
      exact Nat.eq_of_mul_eq_mul_left instPq.out.pos hij
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hn, hd⟩
      obtain ⟨j, rfl⟩ := hd
      have hn' := Finset.mem_range.mp hn
      have hj : j < h + 1 := by
        by_contra hj
        have hj' : h + 1 ≤ j := by omega
        have hjq := Nat.mul_le_mul_left q hj'
        nlinarith [hN', hqform]
      exact ⟨j, Finset.mem_range.mpr hj, rfl⟩
    · intro j hj
      rfl
  have hB :
      (∏ n ∈ B, f n) = (q : ZMod p) ^ h * H := by
    rw [hBindex, Finset.prod_range_succ']
    simp only [mul_zero, hf0, mul_one]
    calc
      (∏ j ∈ Finset.range h, f (q * (j + 1))) =
          ∏ j ∈ Finset.range h,
            (q : ZMod p) * ((j + 1 : ℕ) : ZMod p) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hj0 := hnz (n := j + 1) (by omega) (by omega)
        have hc : ((q * (j + 1) : ℕ) : ZMod p) ≠ 0 := by
          rw [Nat.cast_mul]
          exact mul_ne_zero hq0 hj0
        dsimp only [f]
        rw [ite_eq_right hc, Nat.cast_mul]
      _ = (q : ZMod p) ^ h * H := by
        rw [Finset.prod_mul_distrib]
        simp [H]
  have hcop (n : ℕ) :
      n.Coprime (p * q) ↔ ¬p ∣ n ∧ ¬q ∣ n := by
    rw [Nat.coprime_comm, Nat.coprime_mul_iff_left,
      instPp.out.coprime_iff_not_dvd,
      instPq.out.coprime_iff_not_dvd]
  -- Separate units from multiples of q; multiples of p contribute 1.
  have hsplit :
      (∏ n ∈ A, (n : ZMod p)) * (∏ n ∈ B, f n) =
        ∏ n ∈ Finset.range (N + 1), f n := by
    simp only [A, B, Finset.prod_filter]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro n hn
    by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n <;>
      simp [f, hcop, ZMod.natCast_eq_zero_iff, hpn, hqn]
  rw [← hleft, hB, hfull] at hsplit
  have hleg :
      (legendreSym p (q : ℤ) : ZMod p) = (q : ZMod p) ^ h := by
    simpa only [Int.cast_natCast] using
      (legendreSym.eq_pow p (q : ℤ))
  have hm : (q - 1) / 2 = m := by omega
  rw [hleg, hm]
  apply mul_right_cancel₀ hH
  simpa only [mul_assoc] using hsplit

include hpq in
@[simp]
lemma prod_left_mod_q (hp : p ≠ 2) : (∏ k ∈ leftFinset p q, (k.val.val : ZMod q))
    * (legendreSym q p) = (-1) ^ ((p - 1) / 2) := by
  convert prod_left_mod_p (p := q) (q := p)
    (hpq := hpq.symm) (hq := hp) using 2
  let F (n : {n : ℕ // n ≠ 0}) : ZMod q := by
    letI : NeZero n.val := ⟨n.property⟩
    exact ∏ k ∈ (Set.toFinite
      {k : (ZMod n.val)ˣ |
        (k.val.val : ℚ) < (n.val : ℚ) / 2}).toFinset,
      (k.val.val : ZMod q)
  simp only [leftFinset, leftSubset, ←Nat.cast_mul]
  change
    F ⟨p * q, Nat.mul_ne_zero instPp.out.ne_zero instPq.out.ne_zero⟩ =
    F ⟨q * p, Nat.mul_ne_zero instPq.out.ne_zero instPp.out.ne_zero⟩
  exact congrArg F (Subtype.ext (Nat.mul_comm p q))

lemma prod_rightFinset_eq {M : Type} [CommMonoid M]
    (hp : p ≠ 2) (f : ZMod p → ZMod q → M) :
    (∏ r ∈ rightFinset p q, f (r.1 : ZMod p) (r.2 : ZMod q)) =
      ∏ i ∈ Finset.Ico 1 (p / 2 + 1),
        ∏ j ∈ Finset.Ico 1 q, f i j := by
  have hodd : p % 2 = 1 :=
    instPp.out.eq_two_or_odd.resolve_left hp
  have hhalf (i : ℕ) :
      (i : ℚ) < (p : ℚ) / 2 ↔ i ≤ p / 2 := by
    rw [lt_div_iff₀ (by norm_num)]
    norm_cast
    omega
  rw [← Finset.prod_product']
  refine Finset.prod_bij
    (fun r _ => (r.1.val.val, r.2.val.val)) ?_ ?_ ?_ ?_
  · intro r hr
    have hr' : (r.1.val.val : ℚ) < (p : ℚ) / 2 := by
      simpa only [rightFinset, Set.Finite.mem_toFinset,
        rightSubset, Set.mem_ofPred_eq] using hr
    have hi := (hhalf _).mp hr'
    have hi0 := ZMod.val_pos.mpr (Units.ne_zero r.1)
    have hj0 := ZMod.val_pos.mpr (Units.ne_zero r.2)
    have hjq := ZMod.val_lt r.2.val
    simp only [Finset.mem_product, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, hjq⟩⟩
  · intro r hr s hs hrs
    apply Prod.ext
    · exact Units.ext
        ((ZMod.val_injective p) (congrArg Prod.fst hrs))
    · exact Units.ext
        ((ZMod.val_injective q) (congrArg Prod.snd hrs))
  · rintro ⟨i, j⟩ hij
    rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
    rcases Finset.mem_Ico.mp hi with ⟨hi0, hi1⟩
    rcases Finset.mem_Ico.mp hj with ⟨hj0, hjq⟩
    have hip : i < p := by omega
    have hci : i.Coprime p :=
      ((instPp.out.coprime_iff_not_dvd).mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) hip)).symm
    have hcj : j.Coprime q :=
      ((instPq.out.coprime_iff_not_dvd).mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) hjq)).symm
    let a := ZMod.unitOfCoprime i hci
    let b := ZMod.unitOfCoprime j hcj
    have ha : a.val.val = i := ZMod.val_natCast_of_lt hip
    have hb : b.val.val = j := ZMod.val_natCast_of_lt hjq
    refine ⟨(a, b), ?_, Prod.ext ha hb⟩
    simp only [rightFinset, Set.Finite.mem_toFinset,
      rightSubset, Set.mem_ofPred_eq]
    change (a.val.val : ℚ) < (p : ℚ) / 2
    rw [ha]
    exact (hhalf i).mpr (by omega)
  · intro r hr
    simp only [ZMod.natCast_zmod_val]

@[simp]
lemma prod_right_fst_mod_p (hp : p ≠ 2) :
    ∏ r ∈ rightFinset p q, (r.1 : ZMod p) =
      ((Nat.factorial (p / 2) : ℕ) : ZMod p) ^ (q - 1) := by
  rw [prod_rightFinset_eq p q hp (fun a _ => a)]
  simp only [Finset.prod_const, Nat.card_Ico, Finset.prod_pow]
  rw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]

@[simp]
lemma prod_right_snd_mod_q (hp : p ≠ 2) :
    ∏ r ∈ rightFinset p q, (r.2 : ZMod q) = (-1) ^ (p / 2) := by
  rw [prod_rightFinset_eq p q hp (fun _ b => b)]
  simp only [ZMod.prod_Ico_one_prime, Finset.prod_const,
    Nat.card_Ico, Nat.add_sub_cancel]

include hpq in
lemma prod_left_right_common_sign (hp : p ≠ 2) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      (∏ k ∈ leftFinset p q, (k.val.val : ZMod p)) =
        (e : ZMod p) * ∏ r ∈ rightFinset p q, (r.1 : ZMod p) ∧
      (∏ k ∈ leftFinset p q, (k.val.val : ZMod q)) =
        (e : ZMod q) * ∏ r ∈ rightFinset p q, (r.2 : ZMod q) := by
  let G := (ZMod p)ˣ × (ZMod q)ˣ
  let isom := crt_isomorphism_mul p q hpq
  let : NeZero (p * q) :=
    ⟨Nat.mul_ne_zero instPp.out.ne_zero instPq.out.ne_zero⟩
  have hodd : p % 2 = 1 :=
    instPp.out.eq_two_or_odd.resolve_left hp
  have hL (k : (ZMod (p * q))ˣ) :
      k ∈ leftFinset p q ↔ k ∈ leftSubset p q := by
    simp only [leftFinset, Set.Finite.mem_toFinset]
  have hR (r : G) :
      r ∈ rightFinset p q ↔ r.1.val.val ≤ p / 2 := by
    simp only [rightFinset, Set.Finite.mem_toFinset]
    change (r.1.val.val : ℚ) < (p : ℚ) / 2 ↔
      r.1.val.val ≤ p / 2
    rw [lt_div_iff₀ (by norm_num)]
    norm_cast
    omega
  have hneg (r : G) :
      -r ∈ rightFinset p q ↔ r ∉ rightFinset p q := by
    simp only [hR]
    change (-r.1.val).val ≤ p / 2 ↔ ¬r.1.val.val ≤ p / 2
    let : NeZero r.1.val := ⟨Units.ne_zero r.1⟩
    rw [ZMod.val_neg_of_ne_zero]
    have hv := ZMod.val_lt r.1.val
    omega
  -- Choose the representative whose first coordinate lies on the left.
  let T (r : G) := if r ∈ rightFinset p q then r else -r
  have hTmem (r : G) : T r ∈ rightFinset p q := by
    by_cases hr : r ∈ rightFinset p q
    · simpa only [T, ite_eq_left hr] using hr
    · simpa only [T, ite_eq_right hr] using (hneg r).mpr hr
  have hTneg (r : G) : T (-r) = T r := by
    by_cases hr : r ∈ rightFinset p q <;> simp [T, hneg, hr]
  have hTsign (r : G) : r = T r ∨ r = -T r := by
    by_cases hr : r ∈ rightFinset p q
    · left
      simp only [T, ite_eq_left hr]
    · right
      simp only [T, ite_eq_right hr, neg_neg]
  -- CRT uniqueness makes this normalization a bijection.
  have hbij {R : Type} [CommMonoid R] (f : G → R) :
      (∏ k ∈ leftFinset p q, f (T (isom k))) =
        ∏ r ∈ rightFinset p q, f r := by
    refine Finset.prod_bij (fun k _ => T (isom k)) ?_ ?_ ?_ ?_
    · intro k hk
      exact hTmem _
    · intro k hk l hl hkl
      obtain ⟨z, hz, huniq⟩ :=
        crt_preimage_uniqueness p q hpq
          (T (isom k)).1 (T (isom k)).2
      have hl' := hTsign (isom l)
      rw [← hkl] at hl'
      exact
        (huniq k ⟨(hL k).mp hk, hTsign (isom k)⟩).trans
          (huniq l ⟨(hL l).mp hl, hl'⟩).symm
    · intro r hr
      obtain ⟨k, ⟨hk, hkr⟩, _⟩ :=
        crt_preimage_uniqueness p q hpq r.1 r.2
      refine ⟨k, (hL k).mpr hk, ?_⟩
      rcases hkr with hkr | hkr
      · rw [hkr]
        exact ite_eq_left hr
      · rw [hkr, hTneg]
        exact ite_eq_left hr
    · intro k hk
      rfl
  let sign (k : (ZMod (p * q))ˣ) : ℤ :=
    if isom k ∈ rightFinset p q then 1 else -1
  let e : ℤ := ∏ k ∈ leftFinset p q, sign k
  have he : e = 1 ∨ e = -1 := by
    apply sq_eq_one_iff.mp
    dsimp only [e]
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro k hk
    dsimp only [sign]
    split_ifs <;> norm_num
  have hprod {R : Type} [CommRing R] (f : G → R)
      (hf : ∀ r, f (-r) = -f r) :
      (∏ k ∈ leftFinset p q, f (isom k)) =
        (e : R) * ∏ r ∈ rightFinset p q, f r := by
    rw [←hbij]
    dsimp only [e]
    rw [Int.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    by_cases hr : isom k ∈ rightFinset p q <;>
      simp [sign, T, hr, hf]
  have hfst (k : (ZMod (p * q))ˣ) :
      ((isom k).1 : ZMod p) = (k.val.val : ZMod p) := by
    change (ZMod.cast k.val : ZMod p × ZMod q).1 = _
    rw [Prod.fst_zmod_cast, ZMod.cast_eq_val]
  have hsnd (k : (ZMod (p * q))ˣ) :
      ((isom k).2 : ZMod q) = (k.val.val : ZMod q) := by
    change (ZMod.cast k.val : ZMod p × ZMod q).2 = _
    rw [Prod.snd_zmod_cast, ZMod.cast_eq_val]
  refine ⟨e, he, ?_, ?_⟩
  · simpa only [hfst] using
      hprod (fun r : G => (r.1 : ZMod p)) (fun _ => rfl)
  · simpa only [hsnd] using
      hprod (fun r : G => (r.2 : ZMod q)) (fun _ => rfl)

private lemma sign_cast_injective (r : ℕ) [Fact r.Prime]
    (hr : r ≠ 2) {a b : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hab : (a : ZMod r) = (b : ZMod r)) : a = b := by
  let : Fact (2 < r) := ⟨by
    have := (Fact.out : r.Prime).two_le
    omega⟩
  have hn : (-1 : ZMod r) ≠ 1 := ZMod.neg_one_ne_one
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp_all [eq_comm]

include hpq in
/-- **The Law of Quadratic Reciprocity**: if `p` and `q` are distinct odd primes, then
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`. -/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by
  let A : ℤ := legendreSym p q
  let B : ℤ := legendreSym q p
  let F : ZMod p := (Nat.factorial (p / 2) : ZMod p)
  have hpodd := instPp.out.eq_two_or_odd.resolve_left hp
  have hqodd := instPq.out.eq_two_or_odd.resolve_left hq
  have hpm : (p - 1) / 2 = p / 2 := by omega
  have hqm : (q - 1) / 2 = q / 2 := by omega
  have hqtw : q - 1 = 2 * (q / 2) := by omega
  have hc : p.Coprime q :=
    (Nat.coprime_primes instPp.out instPq.out).mpr hpq
  have hA : A = 1 ∨ A = -1 :=
    legendreSym.eq_one_or_neg_one p (a := (q : ℤ)) (by
      simpa only [Int.cast_natCast] using
        ((ZMod.isUnit_iff_coprime q p).mpr hc.symm).ne_zero)
  have hB : B = 1 ∨ B = -1 :=
    legendreSym.eq_one_or_neg_one q (a := (p : ℤ)) (by
      simpa only [Int.cast_natCast] using
        ((ZMod.isUnit_iff_coprime p q).mpr hc).ne_zero)
  obtain ⟨e, he, hPe, hQe⟩ :=
    prod_left_right_common_sign p q hpq hp
  rw [prod_right_fst_mod_p p q hp] at hPe
  rw [prod_right_snd_mod_q p q hp] at hQe
  have hLp :
      (e : ZMod p) * F ^ (q - 1) * (A : ZMod p) =
        (-1) ^ (q / 2) := by
    simpa only [hPe, hqm] using
      prod_left_mod_p p q hpq hq
  have hLq :
      (e : ZMod q) * (-1) ^ (p / 2) * (B : ZMod q) =
        (-1) ^ (p / 2) := by
    simpa only [hQe, hpm] using
      prod_left_mod_q p q hpq hp
  -- The q-coordinate identifies the common sign.
  have heq0 : (e : ZMod q) ≠ 0 := by
    rcases he with rfl | rfl <;> norm_num
  have hBe : B = e := by
    apply sign_cast_injective q hq hB he
    apply mul_left_cancel₀ heq0
    apply mul_right_cancel₀
      (pow_ne_zero (p / 2) (by norm_num : (-1 : ZMod q) ≠ 0))
    calc
      ((e : ZMod q) * B) * (-1) ^ (p / 2) =
          (e : ZMod q) * (-1) ^ (p / 2) * B := by ring
      _ = (-1) ^ (p / 2) := hLq
      _ = ((e : ZMod q) * e) * (-1) ^ (p / 2) := by
        rcases he with rfl | rfl <;> simp
  -- Wilson evaluates the first-coordinate right product.
  have hfac :
      (-1 : ZMod p) ^ (p / 2) * F ^ 2 = -1 := by
    simpa only [hpm, ZMod.wilsons_lemma] using
      (ZMod.factorial_eq_neg_one_pow_mul_half_factorial_sq
        (p := p) (instPp.out.odd_of_ne_two hp)).symm
  have hR :
      F ^ (q - 1) * (-1 : ZMod p) ^ (p / 2 * (q / 2)) =
        (-1) ^ (q / 2) := by
    have hw := congrArg (fun x : ZMod p => x ^ (q / 2)) hfac
    simp only [mul_pow, ← pow_mul] at hw
    rw [← hqtw] at hw
    simpa only [mul_comm] using hw
  have hF : F ^ (q - 1) ≠ 0 := by
    intro hz
    have hn : (-1 : ZMod p) ^ (q / 2) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    apply hn
    rw [← hR, hz, zero_mul]
  have hEA :
      (e : ZMod p) * A =
        (-1 : ZMod p) ^ (p / 2 * (q / 2)) := by
    apply mul_left_cancel₀ hF
    calc
      F ^ (q - 1) * ((e : ZMod p) * A) =
          (e : ZMod p) * F ^ (q - 1) * A := by ring
      _ = (-1) ^ (q / 2) := hLp
      _ = F ^ (q - 1) *
          (-1 : ZMod p) ^ (p / 2 * (q / 2)) := hR.symm
  have hBA : B * A = 1 ∨ B * A = -1 := by
    rcases hB with hb | hb <;> rcases hA with ha | ha <;>
      simp [hb, ha]
  apply sign_cast_injective p hp hBA
    (neg_one_pow_eq_or ℤ (p / 2 * (q / 2)))
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, hBe] using hEA

end LeoQuadraticReciprocity
