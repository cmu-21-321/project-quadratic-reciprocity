import Mathlib.Data.List.Intervals
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

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
  n.Coprime a.natAbs ∧ (a : ZMod n) ^ ((n - 1) / 2) = J(a | n)

namespace EulerProbablePrime

/-- This provides an algorithm for deciding `EulerProbablePrime`. -/
instance instDecidable {n : ℕ} {a : ℤ} : Decidable (EulerProbablePrime n a) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Any odd prime is a Euler probable prime to any base. -/
@[simp]
theorem of_prime {p : ℕ} [Fact p.Prime] (hOdd : p ≠ 2) {a : ℤ} (hCop : p.Coprime a.natAbs) :
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
theorem not_prime {n : ℕ} (hOdd : n ≠ 2) {a : ℤ} (hCop : n.Coprime a.natAbs)
    (ha : ¬EulerProbablePrime n a) : ¬Nat.Prime n := by
  intro hprime
  have := Fact.mk hprime
  exact ha (of_prime hOdd hCop)

/-- A base `a` for which `n` is "probably prime" under the Solovay-Strassen test. -/
abbrev Base (n : ℕ) := {a : ZMod n | EulerProbablePrime n a.val}

/-- The base and the probable prime have a gcd of one. -/
@[simp]
theorem gcd_eq_one {n : ℕ} {a : ℤ} (h : EulerProbablePrime n a) : gcd a n = 1 := by
  rw [gcd_comm]
  exact Nat.ToInt.of_eq rfl rfl h.1

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
      if hCop : Int.gcd n a = 1 then
        if ha : EulerProbablePrime n a then none
        else some ⟨a, EulerProbablePrime.not_prime (ne_of_not_le hn) hCop ha⟩
      else
        have hNp: ¬n.Prime := by
          intro hP
          have ha_range := List.Ico.mem.mp ha_mem
          have hnDvd := Nat.not_dvd_of_pos_of_lt (by linarith) ha_range.2
          have hCop' := hP.coprime_iff_not_dvd.mpr hnDvd
          exact hCop hCop'
        some ⟨a, hNp⟩

/-- Exercise 11.6(b): The set of Euler liars forms a subgroup of `(ZMod n)ˣ`. -/
def liarSubgroup (n : ℕ) (hOdd : Odd n) (hNotPrime : ¬n.Prime) : Subgroup (ZMod n)ˣ where
  carrier := { a | EulerProbablePrime n a.val.val }
  mul_mem' {a b} ha hb := by
    dsimp at ha hb ⊢
    constructor
    · rw [ZMod.val_mul, Nat.coprime_comm, ZMod.coprime_mod_iff_coprime, ←Nat.coprime_comm]
      exact Nat.Coprime.mul_right ha.1 hb.1
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
    · exact (ZMod.val_coe_unit_coprime a⁻¹).symm
    · rcases ha with ⟨hCop, hEq⟩
      simp
      sorry

end SolovayStrassen
