import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Basic quadratic reciprocity results
-/

namespace legendreSym

variable (p : ℕ) [instPp : Fact p.Prime]
variable (q : ℕ) [instPq : Fact q.Prime]
variable (hpq : p ≠ q)

theorem euler1 (hOdd : p ≠ 2 ∧ q ≠ 2) :
    (p % 4 = 1) ∧ (q : ZMod 4) = 1 → legendreSym p q = legendreSym q p := by
  rintro ⟨hp, hq⟩
  exact (legendreSym.quadratic_reciprocity_one_mod_four hp hOdd.2).symm


end legendreSym
