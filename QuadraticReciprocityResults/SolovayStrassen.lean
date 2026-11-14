import Mathlib.Data.List.Intervals
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import QuadraticReciprocityResults.ForMathlib.JacobiSymbol

/-!
# Solovay-Strassen primality test
-/

open scoped NumberTheorySymbols

@[simp]
lemma pow_sub_one_div_two_eq_legendreSym (p : ℕ) [inst : Fact p.Prime] (hOdd : p ≠ 2) (a : ℤ) :
    (a : ZMod p) ^ ((p - 1) / 2) = legendreSym p a := by
  obtain ⟨k, hk⟩ := inst.out.odd_of_ne_two hOdd
  have hhalf : (p - 1) / 2 = p / 2 := by omega
  rw [legendreSym.eq_pow, hhalf]

/- Beware that jacobiSym is written in the opposite way as legendreSym! -/

/--
`n` is a *Euler probable prime* to base `a` if `gcd a n = 1` and
`a ^ ((n - 1) / 2) ≡ J(a|n) [MOD n]`.
-/
@[simp]
def EulerProbablePrime (n : ℕ) (a : ℤ) : Prop :=
  Int.gcd a n = 1 ∧ (a : ZMod n) ^ ((n - 1) / 2) = J(a | n)

namespace EulerProbablePrime

/-- This provides an algorithm for deciding `EulerProbablePrime`. -/
instance instDecidable {n : ℕ} {a : ℤ} : Decidable (EulerProbablePrime n a) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Any odd prime is a Euler probable prime to any base. -/
@[simp]
theorem of_prime {p : ℕ} [Fact p.Prime] (hOdd : p ≠ 2) {a : ℤ} (hCop : Int.gcd a p = 1) :
    EulerProbablePrime p a := by
  unfold EulerProbablePrime
  constructor
  · exact hCop
  · simp only [pow_sub_one_div_two_eq_legendreSym p hOdd a, jacobiSym.legendreSym.to_jacobiSym]

/-- **Solovay Strassen step**: For `n` odd and `a` coprime to `n`,
failing the Euler probable prime criterion proves that `n` is not prime.

We order the arguments this way so that `not_prime_of_not_eulerProbablePrime n hOdd` is
a "test function" that can be applied to candidate witnesses.
-/
@[simp]
theorem not_prime {n : ℕ} (hOdd : n ≠ 2) {a : ℤ} (hCop : Int.gcd a n = 1)
    (ha : ¬EulerProbablePrime n a) : ¬Nat.Prime n := by
  intro hprime
  have := Fact.mk hprime
  exact ha (of_prime hOdd hCop)

/-- A base `a` for which `n` is "probably prime" under the Solovay-Strassen test. -/
abbrev Base (n : ℕ) := {a : ZMod n | EulerProbablePrime n a.val}

/-- The base and the probable prime have a gcd of one. -/
@[simp]
theorem gcd_eq_one {n : ℕ} {a : ℤ} (h : EulerProbablePrime n a) : Int.gcd a n = 1 := by
  exact h.1

/-- `1` is always an Euler lier and thus need not be checked. -/
theorem one (n : ℕ) : EulerProbablePrime n 1 := by
  simp

/-- `-1` is an Euler lier for all odd numbers and thus need not be checked. -/
@[simp]
theorem neg_one (n : ℕ) (hOdd : Odd n) : EulerProbablePrime n (-1) := by
  have hOdd' := Nat.odd_iff.mp hOdd
  have hhalf : (n - 1) / 2 = n / 2 := by omega
  simp [hhalf, jacobiSym.at_neg_one hOdd, ZMod.χ₄_eq_neg_one_pow hOdd']

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
        else some ⟨a, EulerProbablePrime.not_prime (ne_of_not_le hn) hCop ha⟩
      else
        have hNp: ¬n.Prime := by
          intro hP
          have ha_range := List.Ico.mem.mp ha_mem
          have hnDvd := Nat.not_dvd_of_pos_of_lt (by linarith) ha_range.2
          have hCop' : Int.gcd n a = 1 := hP.coprime_iff_not_dvd.mpr hnDvd
          rw [Int.gcd_comm] at hCop'
          exact hCop hCop'
        some ⟨a, hNp⟩

/-- Exercise 11.6(b): The set of Euler liars forms a subgroup of `(ZMod n)ˣ`.

Note that this works for prime `n` as well, since in that case all test bases
in `(ZMod n)ˣ` answer "probably prime".
-/
def liarSubgroup (n : ℕ) (hOdd : Odd n) : Subgroup (ZMod n)ˣ where
  carrier := { a | EulerProbablePrime n a.val.val }
  mul_mem' {a b} ha hb := by
    dsimp at ha hb ⊢
    constructor
    · rw [ZMod.val_mul, Int.natCast_emod, Int.gcd_emod, Nat.cast_mul]
      exact (Int.gcd_mul_left_left_of_gcd_eq_one hb.1).trans ha.1
    · rw [ZMod.val_mul]
      push_cast at ha hb ⊢
      rw [←jacobiSym.mod_left, jacobiSym.mul_left, mul_pow, ha.2, hb.2]
      norm_cast
  one_mem' := by
    by_cases h : n = 1
    · rw [h]; exact ⟨rfl, by simp⟩
    · have : Fact (1 < n) := ⟨by grind⟩
      dsimp only [Set.mem_ofPred_eq, Units.val_one]
      rw [ZMod.val_one]
      exact EulerProbablePrime.one n
  inv_mem' {a} ha := by
    constructor
    · exact (ZMod.val_coe_unit_coprime a⁻¹)
    · rcases ha with ⟨hCop, hEq⟩
      have : NeZero n := ⟨Nat.ne_of_odd_add hOdd⟩
      rw [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id, ←ZMod.natCast_val] at ⊢ hEq
      have hmul : a.val ^ ((n - 1) / 2) * a⁻¹.val ^ ((n - 1) / 2) = 1 := invOf_eq_iff_right.mp rfl
      rcases jacobiSym.trichotomy (a.val.val : ℤ) n with h | h | h
      <;> have hjainv := (jacobiSym.inv_unit_val_left a).trans h
      <;> have ha := (congrArg (fun (j : ℤ) ↦ a ^ ((n - 1) / 2) = (j : ZMod n)) h).mp hEq
      · rw [ha, Int.cast_zero, zero_mul] at hmul
        have := ZMod.one_eq_zero_iff.mp hmul.symm
        simp_all
      · have hjainv' : (J((a⁻¹.val.val : ℤ) | n) : ZMod n) = 1 := by grind
        rw [ha, Int.cast_one, one_mul] at hmul
        exact hmul.trans hjainv'.symm
      · have hjainv' : (J((a⁻¹.val.val : ℤ) | n) : ZMod n) = -1 := by grind
        rw [ha, Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_eq_iff_eq_neg] at hmul
        exact hmul.trans hjainv'.symm

end SolovayStrassen

namespace Fermat

/-- `n` is a *Fermat probable prime* to base `a` if
`gcd(a, n) = 1` and `a ^ (n - 1) ≡ 1 [MOD n]`. -/
@[simp]
def FermatProbablePrime (n : ℕ) (a : ℤ) : Prop :=
  Int.gcd a n = 1 ∧ (a : ZMod n) ^ (n - 1) = 1

/-- Exercise 11.6(a): Every Fermat witness is a Euler witness.

We prove the contrapositive due to the way the definitions are set up:
  every Euler PP is a Fermat PP.
-/
theorem EulerProbablePrime.fermatProbablePrime {n : ℕ} (hOdd : Odd n) {a : ℤ}
    (ha : EulerProbablePrime n a) : FermatProbablePrime n a := by
  rcases hOdd
  have hpow : (n - 1) / 2 * 2 = n - 1 := by omega
  unfold FermatProbablePrime
  rw [←hpow, pow_mul, ha.2]
  rw_mod_cast [jacobiSym.sq_one ha.1]
  exact ⟨ha.1, mod_cast rfl⟩

end Fermat
