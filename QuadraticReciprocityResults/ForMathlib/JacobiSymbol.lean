import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The Jacobi Symbol

Additional properties for the aJacobi symbol.
-/

open scoped NumberTheorySymbols

namespace jacobiSym

/-- Reducing `a` via `(ZMod n).val` preserves `J(a | n)`. -/
@[simp]
lemma zmod_val_left {n : ℕ} [NeZero n] (a : ℤ) :
    J(((a : ZMod n).val : ℤ) | n) = J(a | n) := by
  rw [ZMod.natCast_val, ZMod.coe_intCast, ←jacobiSym.mod_left]

/-- Inversion in `(ZMod n)ˣ` preserves `J(· | n)`. -/
theorem inv_unit_val_left' {n : ℕ} [Fact (1 < n)] (a : (ZMod n)ˣ) :
    J((a⁻¹.val.val : ℤ) | n) = J((a.val.val : ℤ) | n) := by
  have hmul : J((a.val.val : ℤ) | n) * J((a⁻¹.val.val : ℤ) | n) = 1 := by
    rw [←jacobiSym.mul_left, ←jacobiSym.zmod_val_left]
    simp only [ZMod.natCast_val, Int.cast_mul, ZMod.intCast_cast, ZMod.cast_id]
    rw [Units.mul_inv, ←ZMod.natCast_val, ZMod.val_one, Nat.cast_one]
    exact jacobiSym.one_left n
  rcases jacobiSym.trichotomy (a.val.val : ℤ) n with h | h | h
  <;> rw [h] at hmul
  <;> linarith

/-- Inversion in `(ZMod n)ˣ` preserves `J(· | n)`. -/
theorem inv_unit_val_left {n : ℕ} [NeZero n] (a : (ZMod n)ˣ) :
    J((a⁻¹.val.val : ℤ) | n) = J((a.val.val : ℤ) | n) := by
  by_cases hn : 1 < n
  · have : Fact (1 < n) := ⟨hn⟩
    exact jacobiSym.inv_unit_val_left' a
  · have h1 : n = 1 := (Nat.le_antisymm NeZero.one_le (Nat.le_of_not_lt hn)).symm
    simp_all only [jacobiSym.one_right]

end jacobiSym
