import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Solovay-Strassen primality test
-/

lemma euler_criterion (p : ℕ) [Fact p.Prime] (hOdd : p ≠ 2) (a : ℕ) :
    (a : ZMod p) ^ ((p - 1) / 2) = legendreSym p a := by
  sorry

/- Beware that jacobiSym is written in the opposite way as legendreSym! -/

/-- **Solovay Strassen step**: if the Euler criterion fails, then `n` is not prime. -/
theorem solovay_strassen' (n : ℕ) (hOdd : n ≠ 2) (a : ℕ) :
    (a : ZMod n) ^ ((n - 1) / 2) ≠ jacobiSym a n → ¬Nat.Prime n:= by
  intro hNe
  by_contra hprime
  let factPrime := Fact.mk hprime
  have hEuler := euler_criterion n hOdd a
  have hEq := jacobiSym.legendreSym.to_jacobiSym n a
  rw [hEuler] at hNe
  exact hNe (congrArg Int.cast hEq)

/- TODO: Add a computational version of the test using RNGs -/
