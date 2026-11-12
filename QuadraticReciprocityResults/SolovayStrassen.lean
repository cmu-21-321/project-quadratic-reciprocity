import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Solovay-Strassen primality test
-/

open scoped NumberTheorySymbols

@[simp]
lemma euler_criterion (p : ℕ) [inst : Fact p.Prime] (hOdd : p ≠ 2) (a : ℤ) :
    (a : ZMod p) ^ ((p - 1) / 2) = legendreSym p a := by
  obtain ⟨k, hk⟩ := inst.out.odd_of_ne_two hOdd
  have hhalf : (p - 1) / 2 = p / 2 := by omega
  rw [legendreSym.eq_pow, hhalf]

/- Beware that jacobiSym is written in the opposite way as legendreSym! -/

/--
`n` is a *Euler probable prime* to base `a` if `a ^ ((n - 1) / 2) ≡ J(a|n) (mod n)`.
-/
@[simp]
def EPP (n : ℕ) (a : ℤ) : Prop :=
  (a : ZMod n) ^ ((n - 1) / 2) = J(a | n)

namespace EPP

/-- This provides an algorithm for deciding `EPP`. -/
instance decidable {n : ℕ} {a : ℤ} : Decidable (EPP n a) :=
  decEq _ _

/-- Any odd prime is a Euler probable prime to any base. -/
@[simp]
theorem of_prime {p : ℕ} [Fact p.Prime] (hOdd : p ≠ 2) {a : ℤ} :
    EPP p a := by
  unfold EPP
  simp only [euler_criterion p hOdd a, jacobiSym.legendreSym.to_jacobiSym]

/-- `1` is always an Euler lier and thus need not be checked. -/
theorem one_is_liar (n : ℕ) : EPP n 1 := by
  simp

/-- `-1` is an Euler lier for all odd numbers and thus need not be checked. -/
@[simp]
theorem neg_one_is_liar (n : ℕ) (hOdd : Odd n) : EPP n (-1) := by
  have hOdd' := Nat.odd_iff.mp hOdd
  have hhalf : (n - 1) / 2 = n / 2 := by omega
  simp [hhalf, jacobiSym.at_neg_one hOdd, ZMod.χ₄_eq_neg_one_pow hOdd']

end EPP

namespace SolovayStrassen

/-- **Solovay Strassen step**: if the Euler criterion fails, then `n` is not prime.

We order the arguments this way so that `solovay_strassen' n hOdd` is a "test function"
that can be applied to candidate witnesses.
-/
theorem solovay_strassen' (n : ℕ) (hOdd : n ≠ 2) (a : ℤ) :
    ¬EPP n a → ¬Nat.Prime n := by
  intro hneg
  by_contra hprime
  let factPrime := Fact.mk hprime
  have hEPP := @EPP.of_prime n factPrime hOdd a
  exact hneg hEPP

/-- **Solovay Strassen test** -/
def solovay_strassen (n : ℕ) : Option (ℤ ×' ¬Nat.Prime n) :=
  if hn : n = 2 then none
  else
    (List.range n).findSome? fun a =>
      if ha : EPP n a then none
      else some ⟨a, solovay_strassen' n hn a ha⟩


end SolovayStrassen
