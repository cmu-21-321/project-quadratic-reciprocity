import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace legendreSym

theorem euler1 (p q : ℕ) [instPp : Fact p.Prime] [instPq : Fact q.Prime] (hOdd : p ≠ 2 ∧ q ≠ 2) :
  (p : ZMod 4) = 1 ∧ (q : ZMod 4) = 1 → legendreSym p q = legendreSym q p := by
  sorry

end legendreSym
