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
  a.natAbs.Coprime n ∧ (a : ZMod n) ^ ((n - 1) / 2) = J(a | n)

namespace EulerProbablePrime

/-- This provides an algorithm for deciding `EulerProbablePrime`. -/
instance instDecidable {n : ℕ} {a : ℤ} : Decidable (EulerProbablePrime n a) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Any odd prime is a Euler probable prime to any base. -/
@[simp]
theorem of_prime {p : ℕ} [Fact p.Prime] (hOdd : p ≠ 2) {a : ℤ} :
    EulerProbablePrime p a := by
  unfold EulerProbablePrime
  simp only [pow_sub_one_div_two_eq_legendreSym p hOdd a, jacobiSym.legendreSym.to_jacobiSym]

/-- A base `a` for which `n` is "probably prime" under the Solovay-Strassen test. -/
abbrev Base (n : ℕ) := {a : ℤ // EulerProbablePrime n a}

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

/-- **Solovay Strassen step**: if the Euler criterion fails, then `n` is not prime.

We order the arguments this way so that `not_prime_of_not_eulerProbablePrime n hOdd` is
a "test function" that can be applied to candidate witnesses.
-/
theorem not_prime_of_not_eulerProbablePrime (n : ℕ) (hOdd : n ≠ 2) (a : ℤ) :
    ¬EulerProbablePrime n a → ¬Nat.Prime n := by
  intro hneg
  by_contra hprime
  let factPrime := Fact.mk hprime
  have hEPP := @EulerProbablePrime.of_prime n factPrime hOdd a
  exact hneg hEPP

/-- **Solovay Strassen test** -/
def findWitness (n : ℕ) : Option (ℤ ×' ¬Nat.Prime n) :=
  if hn : n = 2 then none
  else
    (List.range n).findSome? fun a =>
      if ha : EulerProbablePrime n a then none
      else some ⟨a, not_prime_of_not_eulerProbablePrime n hn a ha⟩

/- Exercise 11.6b -/

/-- The set of Euler liars coprime to `n` forms a subgroup of `(ZMod n)ˣ`. -/
def liarSubgroup (n : ℕ) (hOdd : Odd n) (hNotPrime : ¬n.Prime) : Subgroup (ZMod n)ˣ := by
  sorry

end SolovayStrassen
