import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# This module formalizes HW Exercise 11.5 from Leo Goldmahker's Number Theory class.
-/

open scoped BigOperators NumberTheorySymbols

namespace JacobiCharacterSum

/-- The Jacobi symbol, regarded as a function on residue classes modulo `n`. -/
def jacobiClass (n : ℕ) (x : ZMod n) : ℤ :=
  J((x.val : ℤ) | n)

/-- The sum `∑ a ∈ ZMod n, J(a | n)` from the exercise. -/
def jacobiSum (n : ℕ) [NeZero n] : ℤ :=
  ∑ x : ZMod n, jacobiClass n x

/-!
The first two helpers are the main work for part (a).

* Prove `jacobiClass_mul` from `jacobiSym.mul_left` and
  `jacobiSym.mod_left'`.
* For `sum_jacobiClass_mul`, use the hypothesis to show that `b` is a unit
  modulo `n`; multiplication by a unit permutes `ZMod n`.
-/

private theorem jacobiClass_mul (n : ℕ) [NeZero n] (b x : ZMod n) :
    jacobiClass n (b * x) = jacobiClass n b * jacobiClass n x := by
  sorry

private theorem sum_jacobiClass_mul (n : ℕ) [NeZero n] (b : ZMod n)
    (hb : jacobiClass n b = -1) :
    ∑ x : ZMod n, jacobiClass n (b * x) = jacobiSum n := by
  sorry

/-- Exercise 11.5(a). -/
theorem jacobiSum_eq_zero_of_exists_jacobi_neg_one {n : ℕ} [NeZero n]
    (h : ∃ b : ZMod n, jacobiClass n b = -1) :
    jacobiSum n = 0 := by
  obtain ⟨b, hb⟩ := h
  -- Reindex by `x ↦ b * x`.
  -- Then each summand becomes `(-1) * jacobiClass n x`.
  -- The sum equals its own negative, hence is zero in `ℤ`.
  sorry

/-!
For part (b), factor `n`. Since `n` is not a square, some prime appears to an
odd exponent. Choose a nonsquare at that prime and squares at every other prime
power, then assemble the residue class with the Chinese remainder theorem.
-/

/-- Exercise 11.5(b). -/
theorem exists_jacobi_neg_one_of_not_isSquare {n : ℕ} [NeZero n]
    (hOdd : Odd n) (hNotSquare : ¬ IsSquare n) :
    ∃ b : ZMod n, jacobiClass n b = -1 := by
  sorry

/-- Parts (a) and (b) combined. -/
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

/-- Exercise 11.5(c): for a square modulus, the sum is Euler's totient. -/
theorem jacobiSum_eq_totient_of_isSquare {n : ℕ} [NeZero n]
    (hSquare : IsSquare n) :
    jacobiSum n = ((n.totient : ℕ) : ℤ) := by
  sorry

end JacobiCharacterSum
