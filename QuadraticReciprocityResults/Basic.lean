import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Basic quadratic reciprocity results
-/

namespace legendreSym

variable (p : ℕ) [instPp : Fact p.Prime]
variable (q : ℕ) [instPq : Fact q.Prime]
variable (hpq : p ≠ q)

theorem euler1 (hOdd : p ≠ 2 ∧ q ≠ 2) :
    (p : ZMod 4) = 1 ∧ (q : ZMod 4) = 1 → legendreSym p q = legendreSym q p := by
  rintro ⟨hp, hq⟩
  unfold legendreSym
  simp
  sorry


end legendreSym
