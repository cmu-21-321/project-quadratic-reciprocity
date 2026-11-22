import Mathlib.Data.List.Intervals
import QuadraticReciprocityResults.ForMathlib.JacobiSymbol

/-!
# Solovay-Strassen primality test
-/

open scoped NumberTheorySymbols

lemma pow_sub_one_div_two_eq_legendreSym_of_coprime
    {p : ℕ} [inst : Fact p.Prime] {a : ℤ} (hCop : Int.gcd a p = 1) :
      (a : ZMod p) ^ ((p - 1) / 2) = legendreSym p a := by
  by_cases h : p = 2
  · subst p
    have ha : (a : ZMod 2) ≠ 0 := by
      intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      rw_mod_cast [←Int.gcd_emod, Int.emod_eq_zero_of_dvd h] at hCop
      cases hCop
    rcases legendreSym.eq_one_or_neg_one 2 ha with h | h <;> simp [h]
  · obtain ⟨k, hk⟩ := inst.out.odd_of_ne_two h
    have hhalf : (p - 1) / 2 = p / 2 := by omega
    rw [legendreSym.eq_pow, hhalf]


/-- `n` is a *Fermat probable prime* to base `a` if
`gcd(a, n) = 1` and `a ^ (n - 1) ≡ 1 [MOD n]`. -/
@[mk_iff]
structure FermatProbablePrime (n : ℕ) (a : ℤ) : Prop where
  cop : Int.gcd a n = 1
  eq : (a : ZMod n) ^ (n - 1) = 1

namespace FermatProbablePrime

/-- This provides an algorithm for deciding `FermatProbablePrime`. -/
instance instDecidable {n : ℕ} {a : ℤ} : Decidable (FermatProbablePrime n a) :=
  decidable_of_iff' _ (fermatProbablePrime_iff _ _)

end FermatProbablePrime

/- Beware that jacobiSym is written in the opposite way as legendreSym! -/

/--
`n` is an *Euler probable prime* to base `a` if `gcd a n = 1` and
`a ^ ((n - 1) / 2) ≡ J(a|n) [MOD n]`.
-/
@[mk_iff]
structure EulerProbablePrime (n : ℕ) (a : ℤ) : Prop where
  cop : Int.gcd a n = 1
  eq : (a : ZMod n) ^ ((n - 1) / 2) = J(a | n)

namespace EulerProbablePrime

/-- This provides an algorithm for deciding `EulerProbablePrime`. -/
instance instDecidable {n : ℕ} {a : ℤ} : Decidable (EulerProbablePrime n a) :=
  decidable_of_iff' _ (eulerProbablePrime_iff _ _)

/-- Any prime is an Euler probable prime to any coprime base. -/
@[simp]
theorem of_prime {p : ℕ} [Fact p.Prime] {a : ℤ} (hCop : Int.gcd a p = 1) :
    EulerProbablePrime p a where
  cop := hCop
  eq := by
    simp only [pow_sub_one_div_two_eq_legendreSym_of_coprime hCop,
    jacobiSym.legendreSym.to_jacobiSym]

/-- **Solovay Strassen step**: For `a` coprime to `n`,
failing the Euler probable prime criterion proves that `n` is not prime. -/
@[simp]
theorem not_prime {n : ℕ} {a : ℤ} (hCop : Int.gcd a n = 1)
    (ha : ¬EulerProbablePrime n a) : ¬Nat.Prime n := by
  intro hprime
  have := Fact.mk hprime
  exact ha (of_prime hCop)

/-- `1` always yields "probable prime" and thus need not be checked. -/
@[simp]
theorem one (n : ℕ) : EulerProbablePrime n 1 :=
  { cop := by simp, eq := by simp }

/-- `-1` yields "probable prime" for all odd numbers and thus need not be checked. -/
@[simp]
theorem neg_one (n : ℕ) (hOdd : Odd n) : EulerProbablePrime n (-1) where
  cop := by rw [Int.neg_gcd, Int.one_gcd]
  eq := by
    have hOdd' := Nat.odd_iff.mp hOdd
    have hhalf : (n - 1) / 2 = n / 2 := by omega
    rw [jacobiSym.at_neg_one hOdd, ZMod.χ₄_eq_neg_one_pow hOdd',
      Int.cast_pow, Int.cast_neg, Int.cast_one, hhalf]

/-- Exercise 11.6(a): Every Fermat witness is an Euler witness.

We prove the contrapositive due to the way the definitions are set up:
  every Euler PP is a Fermat PP.
-/
theorem fermat {n : ℕ} (hOdd : Odd n) {a : ℤ}
    (ha : EulerProbablePrime n a) : FermatProbablePrime n a := by
  rcases hOdd
  have hpow : (n - 1) / 2 * 2 = n - 1 := by omega
  constructor
  · exact ha.cop
  · rw [←hpow, pow_mul, ha.eq, ←Int.cast_pow, jacobiSym.sq_one ha.cop, Int.cast_one]

/-- A base `a` for which `n` is "probably prime" under the Solovay-Strassen test. -/
abbrev Base (n : ℕ) := {a : (ZMod n)ˣ | EulerProbablePrime n a.val.val}

/-- Exercise 11.6(b): The set of Euler liars forms a subgroup of `(ZMod n)ˣ`.

Note that this works for prime `n` as well, since in that case all test bases
in `(ZMod n)ˣ` answer "probably prime".
-/
def liarSubgroup (n : ℕ) (hOdd : Odd n) : Subgroup (ZMod n)ˣ where
  carrier := Base n
  mul_mem' := by
    rintro a b ⟨_, ha⟩ ⟨_, hb⟩
    constructor
    · exact ZMod.val_coe_unit_coprime (a * b)
    · rw [Units.val_mul, ZMod.val_mul]
      push_cast at ha hb ⊢
      rw [←jacobiSym.mod_left, jacobiSym.mul_left,
        mul_pow, ha, hb]
      norm_cast
  one_mem' := by
    by_cases h : n = 1
    · rw [h]; exact ⟨rfl, by simp⟩
    · have : Fact (1 < n) := ⟨by grind⟩
      dsimp only [Set.mem_ofPred_eq, Units.val_one]
      rw [ZMod.val_one]
      exact EulerProbablePrime.one n
  inv_mem' := by
    rintro a ⟨hcop, heq⟩
    constructor
    · exact (ZMod.val_coe_unit_coprime a⁻¹)
    · have : NeZero n := ⟨Nat.ne_of_odd_add hOdd⟩
      rw [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id, ←ZMod.natCast_val] at ⊢ heq
      have hmul : a.val ^ ((n - 1) / 2) * a⁻¹.val ^ ((n - 1) / 2) = 1 := invOf_eq_iff_right.mp rfl
      rcases jacobiSym.eq_one_or_neg_one hcop with h | h
      <;> have hjainv := (jacobiSym.inv_unit_val_left a).trans h
      <;> have ha := (congrArg (fun (j : ℤ) ↦ a ^ ((n - 1) / 2) = (j : ZMod n)) h).mp heq
      · have hjainv' : (J((a⁻¹.val.val : ℤ) | n) : ZMod n) = 1 := by grind
        rw [ha, Int.cast_one, one_mul] at hmul
        exact hmul.trans hjainv'.symm
      · have hjainv' : (J((a⁻¹.val.val : ℤ) | n) : ZMod n) = -1 := by grind
        rw [ha, Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_eq_iff_eq_neg] at hmul
        exact hmul.trans hjainv'.symm

end EulerProbablePrime

namespace SolovayStrassen

/-- **Solovay-Strassen primality witness search**.
For `a ∈ {1, ..., n - 1}`, either `gcd(a, n) > 1` (sufficient to show that `n` is composite)
or `¬EulerProbablePrime n a` (so `a` is an Euler witness). -/
def findWitness (n : ℕ) : Option (ℤ ×' ¬n.Prime) :=
  if hn : n ≤ 2 then none
  else
    (List.Ico 1 n).attach.findSome? fun ⟨a, ha_mem⟩ =>
      if hCop : Int.gcd a n = 1 then
        if ha : EulerProbablePrime n a then none
        else some ⟨a, EulerProbablePrime.not_prime hCop ha⟩
      else
        have hNp : ¬n.Prime := by
          intro hP
          have ha_range := List.Ico.mem.mp ha_mem
          have hnDvd := Nat.not_dvd_of_pos_of_lt (by linarith) ha_range.2
          have hCop' : Int.gcd n a = 1 := hP.coprime_iff_not_dvd.mpr hnDvd
          rw [Int.gcd_comm] at hCop'
          exact hCop hCop'
        some ⟨a, hNp⟩

end SolovayStrassen
