import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Units

/-!
# This module formalizes HW Exercise 11.5 from Leo Goldmahker's Number Theory class.
-/

open scoped BigOperators NumberTheorySymbols

namespace JacobiCharacterSum

/- The Jacobi symbol, regarded as a function on residue classes modulo n. -/
abbrev jacobiClass (n : ℕ) (x : ZMod n) : ℤ :=
  J((x.val : ℤ) | n)

/-- The sum `∑ a ∈ ZMod n, J(a | n)` from the exercise. -/
abbrev jacobiSum (n : ℕ) [NeZero n] : ℤ :=
  ∑ x : ZMod n, jacobiClass n x

/-!
The first two helper theorems are the main meat for part (a).

* Prove 'jacobiClass_mul' from 'jacobiSym.mul_left' and
  'jacobiSym.mod_left'.
* For 'sum_jacobiClass_mul', use the hypothesis to show that b is a unit
  modulo n; multiplication by a unit permutes ZMod n.
-/

/- Here, a key observation is that multiplication in ZMod n
  corresponds to multiplication modulo n on representatives. -/
private theorem jacobiClass_mul (n : ℕ) [NeZero n] (b x : ZMod n) :
    jacobiClass n (b * x) = jacobiClass n b * jacobiClass n x := by
  calc
    J(((b * x).val : ℤ) | n)
        = J(((b.val : ℤ) * (x.val : ℤ)) | n) := by
            apply jacobiSym.mod_left'
            simp only [ZMod.val_mul]
            norm_cast
            simp
    _ = J((b.val : ℤ) | n) * J((x.val : ℤ) | n) := by
          exact jacobiSym.mul_left b.val x.val n

private theorem sum_jacobiClass_mul (n : ℕ) [NeZero n] (b : ZMod n)
    (hb : jacobiClass n b = -1) :
    ∑ x : ZMod n, jacobiClass n (b * x) = jacobiSum n := by
  have hcoprime : Nat.Coprime b.val n := by
    refine Nat.coprime_iff_gcd_eq_one.mpr ?_
    by_contra h
    unfold jacobiClass at hb
    have hzero : J((b.val : ℤ) | n) = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      exact h
    rw [hzero] at hb
    norm_num at hb
  have hbunit : IsUnit b := by
    rw [←ZMod.natCast_zmod_val b]
    exact (ZMod.isUnit_iff_coprime b.val n).mpr hcoprime
  obtain ⟨u, rfl⟩ := hbunit
  exact Fintype.sum_bijective (fun x : ZMod n => (u : ZMod n) * x) (Units.mulLeft_bijective u)
    (fun x => jacobiClass n ((u : ZMod n) * x)) (fun x => jacobiClass n x) (fun _ => rfl)

/- Exercise 11.5(a). -/
theorem jacobiSum_eq_zero_of_exists_jacobi_neg_one {n : ℕ} [NeZero n]
    (h : ∃ b : ZMod n, jacobiClass n b = -1) :
    jacobiSum n = 0 := by
  -- Get witness 'b' with the hypothesis 'jacobiClass n b = -1'.
  obtain ⟨b, hb⟩ := h
  -- Reindex 'jacobiSum n' by mapping x ↦ b * x using helper theorem.
  have h_reindex : jacobiSum n = ∑ x : ZMod n, jacobiClass n (b * x) :=
    (sum_jacobiClass_mul n b hb).symm
  -- Apply multiplicativity and hb inside the sum.
  have h_neg_summands :
      (∑ x : ZMod n, jacobiClass n (b * x)) = ∑ x : ZMod n, (-1) * jacobiClass n x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [jacobiClass_mul, hb]
  -- Factor -1 out of the finite sum, then rewrite back to 'jacobiSum n'.
  have h_factor_neg :
      (∑ x : ZMod n, (-1) * jacobiClass n x) = -jacobiSum n := by
    simp_rw [neg_one_mul]
    rw [Finset.sum_neg_distrib]
  -- Use a calc block to get 'jacobiSum n = -jacobiSum n'.
  have h_self_neg : jacobiSum n = -jacobiSum n := by
    calc
      jacobiSum n
        = ∑ x : ZMod n, jacobiClass n (b * x) := h_reindex
      _ = ∑ x : ZMod n, (-1) * jacobiClass n x := h_neg_summands
      _ = -jacobiSum n := h_factor_neg
  omega

/-!
For part (b), factor 'n'. Since 'n' is not a square, some prime appears to an
odd exponent. Choose a nonsquare at that prime and squares at every other prime
power, then assemble the residue class with the Chinese remainder theorem.
-/

/- Exercise 11.5(b). -/
theorem exists_jacobi_neg_one_of_not_isSquare {n : ℕ} [NeZero n]
    (hOdd : Odd n) (hNotSquare : ¬ IsSquare n) :
    ∃ b : ZMod n, jacobiClass n b = -1 := by
  -- Find a prime p with odd exponent k = v_p(n), and write n = p^k * m with gcd(p, m) = 1.
  have h_exists_odd_exp : ∃ p ∈ n.primeFactors, Odd (n.factorization p) := by
    by_contra h
    push Not at h
    apply hNotSquare
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← sq, ← Finset.prod_pow]
    conv_lhs => rw [←Nat.prod_factorization_pow_eq_self (NeZero.ne n)]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (h p hp)))]
  rcases h_exists_odd_exp with ⟨p, hp_mem, hk_odd⟩
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hfact : Fact p.Prime := ⟨hp⟩
  let k := n.factorization p
  let m := n / p ^ k
  have hn_eq : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hn_eq
    exact NeZero.ne n hn_eq.symm
  have hNeZerom : NeZero m := ⟨hm_ne_zero⟩
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp (NeZero.ne n)
  -- Since p | n and n is odd, p is odd, so there must exist a quadratic nonresidue c mod p.
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
  have hp_odd : Odd p := by
    rcases hp_dvd with ⟨t, rfl⟩
    exact (Nat.odd_mul.mp hOdd).1
  have hp_ne_two : p ≠ 2 := by
    rintro rfl
    exact Nat.not_odd_iff_even.mpr even_two hp_odd
  have hringChar : ringChar (ZMod p) ≠ 2 := by
    rwa [ZMod.ringChar_zmod_n]
  rcases FiniteField.exists_nonsquare hringChar with ⟨c, hc_nonsq⟩
  have hc_jacobi : jacobiSym (c.val : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    rw [legendreSym.eq_neg_one_iff]
    simpa [ZMod.natCast_zmod_val] using hc_nonsq
  -- Use Chinese remainder theorem to find a with a ≡ c (mod p) and a ≡ 1 (mod m).
  let crt := Nat.chineseRemainder hcop c.val 1
  let a : ℕ := crt.val
  have ha_p : (a : ℤ) ≡ (c.val : ℤ) [ZMOD (p : ℤ)] :=
    Int.natCast_modEq_iff.mpr crt.property.1
  have ha_m : (a : ℤ) ≡ 1 [ZMOD (m : ℤ)] :=
    Int.natCast_modEq_iff.mpr crt.property.2
  -- Evaluate (a / n) = (a / p)^k * (a / m) = (c / p)^k * (1 / m) = (-1)^k * 1 = -1.
  have ha_jacobi : jacobiSym (a : ℤ) n = -1 := by
    rw [←hn_eq, jacobiSym.mul_right, jacobiSym.pow_right]
    rw [jacobiSym.mod_left' ha_p, jacobiSym.mod_left' ha_m]
    rw [hc_jacobi, jacobiSym.one_left, hk_odd.neg_one_pow, mul_one]
  -- Let b be the class of a mod n.
  refine ⟨(a : ZMod n), ?_⟩
  unfold jacobiClass
  have hmod : ((a : ZMod n).val : ℤ) ≡ (a : ℤ) [ZMOD (n : ℤ)] := by
    rw [Int.natCast_modEq_iff, ZMod.val_natCast]
    exact Nat.mod_modEq a n
  rw [jacobiSym.mod_left' hmod, ha_jacobi]

/- Parts (a) and (b) combined. -/
theorem jacobiSum_eq_zero_of_not_isSquare {n : ℕ} [NeZero n]
    (hOdd : Odd n) (hNotSquare : ¬ IsSquare n) :
    jacobiSum n = 0 := by
  exact jacobiSum_eq_zero_of_exists_jacobi_neg_one
    (exists_jacobi_neg_one_of_not_isSquare hOdd hNotSquare)

/-!
For part (c), write `n = m^2`.  `jacobiSym.pow_right` shows that every
coprime summand is `1`; `jacobiSym.eq_zero_iff` shows every non-coprime
summand is `0`.  There are exactly `n.totient` units modulo `n`.
-/

/- Exercise 11.5(c): for a square modulus, the sum is Euler's totient. -/
theorem jacobiSum_eq_totient_of_isSquare {n : ℕ} [NeZero n]
    (hSquare : IsSquare n) :
    jacobiSum n = ((n.totient : ℕ) : ℤ) := by
  -- Write n = m * m and register NeZero m for later use.
  rcases hSquare with ⟨m, rfl⟩
  have hm_ne : m ≠ 0 := fun hm0 => NeZero.ne (m * m) (by simp [hm0])
  have hNeZerom : NeZero m := ⟨hm_ne⟩
  -- Evaluate (v / m²) according to whether gcd(v, m²) = 1.
  have h_term : ∀ v : ℕ,
      jacobiSym (v : ℤ) (m * m) = if Nat.Coprime (m * m) v then 1 else 0 := by
    intro v
    by_cases hv : Nat.Coprime (m * m) v
    · -- gcd(v, m²) = 1 → gcd(v, m) = 1 → (v / m) = ±1 → (v / m²) = (v / m)² = 1
      rw [ite_eq_left hv]
      have hvm : Nat.Coprime v m := (Nat.coprime_mul_iff_left.mp hv).1.symm
      have h_ne_zero : jacobiSym (v : ℤ) m ≠ 0 := by
        rw [ne_eq, jacobiSym.eq_zero_iff]
        rintro ⟨_, hgcd⟩
        apply hgcd
        simpa [Nat.Coprime] using hvm
      have h_sq_one : jacobiSym (v : ℤ) m ^ 2 = 1 := by
        rcases jacobiSym.trichotomy (v : ℤ) m with h0 | h1 | hm1
        · exact absurd h0 h_ne_zero
        · rw [h1]; norm_num
        · rw [hm1]; norm_num
      rw [jacobiSym.mul_right, ← sq, h_sq_one]
    · -- gcd(v, m²) ≠ 1 → (v / m²) = 0
      simp only [hv, ↓reduceIte]
      rw [jacobiSym.eq_zero_iff]
      refine ⟨NeZero.ne (m * m), fun hgcd => hv ?_⟩
      rw [Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast, Nat.gcd_comm] at hgcd
      exact hgcd
  -- Sum over representatives v ∈ {0, ..., n - 1} and count those coprime to n.
  have h_sum_range :
      jacobiSum (m * m) = ∑ v ∈ Finset.range (m * m), jacobiSym (v : ℤ) (m * m) := by
    unfold jacobiSum jacobiClass
    refine Finset.sum_nbij ZMod.val
      (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
      (fun x _ y _ hxy => ZMod.val_injective (m * m) hxy)
      (fun v hv => ⟨(v : ZMod (m * m)), Finset.mem_univ _,
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hv)⟩)
      (fun _ _ => rfl)
  rw [h_sum_range]
  simp_rw [h_term]
  rw [Finset.sum_boole]
  rfl

end JacobiCharacterSum
