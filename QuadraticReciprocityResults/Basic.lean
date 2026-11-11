import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace legendreSym

variable (p : ℕ) [instPp : Fact p.Prime]
variable (q : ℕ) [instPq : Fact q.Prime]
variable (hpq : p ≠ q)

theorem euler1 (hOdd : p ≠ 2 ∧ q ≠ 2) :
    (p : ZMod 4) = 1 ∧ (q : ZMod 4) = 1 → legendreSym p q = legendreSym q p := by
  sorry

#check (ZMod p)ˣ


def crt_isomorphism_mul :
    (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv
    (ZMod.chineseRemainder ((Nat.coprime_primes instPp.out instPq.out).2 hpq)).toMulEquiv).trans
      MulEquiv.prodUnits

/- Just for practice, this is the QR formalized with the method in class -/
namespace LeoQuadraticReciprocity

/-- Units modulo `p * q` whose canonical representative is strictly below half of `p * q`. -/
def LeftSubset : Set (ZMod (p * q))ˣ :=
  {k | (k.val.val : ℚ) < (p * q : ℚ) / 2}

/-- Pairs of units whose first component has canonical representative strictly below `p / 2`. -/
def RightSubset : Set ((ZMod p)ˣ × (ZMod q)ˣ) :=
  {ab | (ab.fst.val.val : ℚ) < (p : ℚ) / 2}

#check crt_isomorphism_mul p q hpq 1

lemma crt_preimage_uniqueness (a : (ZMod p)ˣ) (b : (ZMod q)ˣ) :
    ∃! k ∈ LeftSubset p q,
      crt_isomorphism_mul p q hpq k = (a, b) ∨ crt_isomorphism_mul p q hpq k = -(a, b) := by
  let e := crt_isomorphism_mul p q hpq
  let x := e.symm (a, b)
  have hNgt : 1 < p * q := by nlinarith [instPp.out.two_le, instPq.out.two_le]
  have hNzero : NeZero (p * q) := ⟨by omega⟩
  have hx0 : (x : ZMod (p * q)) ≠ 0 := by
    intro hx
    have h := x.val_inv
    rw [hx, zero_mul] at h
    have hval := congrArg ZMod.val h
    rw [ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hNgt] at hval
    omega
  have hxpos : 0 < x.val.val := ZMod.val_pos.mpr hx0
  have hxlt : x.val.val < p * q := @ZMod.val_lt (p * q) hNzero x.val
  have hnegval : (-x).val.val = p * q - x.val.val := by
    change (-(x : ZMod (p * q))).val = _
    have hxzero : NeZero (x : ZMod (p * q)) := ⟨hx0⟩
    exact @ZMod.val_neg_of_ne_zero (p * q) hNzero (x : ZMod (p * q)) hxzero
  have hleft_iff (k : (ZMod (p * q))ˣ) :
      k ∈ LeftSubset p q ↔ 2 * k.val.val < p * q := by
    change (k.val.val : ℚ) < (p * q : ℚ) / 2 ↔ _
    rw [lt_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
    norm_cast
    omega
  have hxmap : e x = (a, b) := by
    dsimp [x]
    exact e.apply_symm_apply _
  have hNtwo : 2 < p * q := by nlinarith [instPp.out.two_le, instPq.out.two_le]
  have hnohalf : 2 * x.val.val ≠ p * q := by
    intro hhalf
    have hneg : -(x : ZMod (p * q)) = x :=
      (ZMod.neg_eq_self_iff (x : ZMod (p * q))).2 (Or.inr hhalf)
    have hsum : (x : ZMod (p * q)) + x = 0 := by
      calc
        (x : ZMod (p * q)) + x = x + (-(x : ZMod (p * q))) := by rw [hneg]
        _ = 0 := add_neg_cancel _
    have htwo : (2 : ZMod (p * q)) = 0 := by
      calc
        (2 : ZMod (p * q)) = 1 + 1 := by norm_num
        _ = x.val * x⁻¹ + x.val * x⁻¹ := by simp [Units.mul_inv]
        _ = (x.val + x.val) * x⁻¹ := by ring
        _ = 0 := by rw [hsum]; simp
    have hval := congrArg ZMod.val htwo
    rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt hNtwo, ZMod.val_zero] at hval
    omega
  have hnegMul : (-x : (ZMod (p * q))ˣ) = (-1) * x := by
    apply Units.ext
    change -(x : ZMod (p * q)) = (-1 : ZMod (p * q)) * x
    ring
  have hnegOne : e (-1 : (ZMod (p * q))ˣ) = (-1, -1) := by
    apply Prod.ext
    · apply Units.ext
      change (ZMod.chineseRemainder
        ((Nat.coprime_primes instPp.out instPq.out).2 hpq) (-1 : ZMod (p * q))).1 = -1
      simp
    · apply Units.ext
      change (ZMod.chineseRemainder
        ((Nat.coprime_primes instPp.out instPq.out).2 hpq) (-1 : ZMod (p * q))).2 = -1
      simp
  have hmapneg : e (-x) = -(a, b) := by
    calc
      e (-x) = e ((-1) * x) := congrArg e hnegMul
      _ = e (-1) * e x := map_mul e _ _
      _ = (-1, -1) * (a, b) := by rw [hnegOne, hxmap]
      _ = -(a, b) := by
        apply Prod.ext
        · apply Units.ext
          change (-1 : ZMod p) * (a : ZMod p) = -(a : ZMod p)
          ring
        · apply Units.ext
          change (-1 : ZMod q) * (b : ZMod q) = -(b : ZMod q)
          ring
  by_cases hleft : 2 * x.val.val < p * q
  · have hxmem : x ∈ LeftSubset p q := by
      exact hleft_iff x |>.2 hleft
    refine ⟨x, ⟨hxmem, Or.inl hxmap⟩, ?_⟩
    intro y hy
    rcases hy with ⟨hyLeft, hyPred⟩
    rcases hyPred with hyab | hyneg
    · exact e.injective (hyab.trans hxmap.symm)
    · have hyx : y = -x := e.injective (hyneg.trans hmapneg.symm)
      subst y
      have hnegleft := hleft_iff (-x) |>.1 hyLeft
      rw [hnegval] at hnegleft
      omega
  · have hgt : p * q < 2 * x.val.val := by omega
    have hnegleft : 2 * (p * q - x.val.val) < p * q := by omega
    have hnotleft : x ∉ LeftSubset p q := by
      intro hxmem
      exact hleft (hleft_iff x |>.1 hxmem)
    have hnegmem : -x ∈ LeftSubset p q := by
      apply (hleft_iff (-x)).2
      rw [hnegval]
      exact hnegleft
    refine ⟨-x, ⟨hnegmem, Or.inr hmapneg⟩, ?_⟩
    intro y hy
    rcases hy with ⟨hyLeft, hyPred⟩
    rcases hyPred with hyab | hyneg
    · have hyx : y = x := e.injective (hyab.trans hxmap.symm)
      subst y
      exact (hnotleft hyLeft).elim
    · exact e.injective (hyneg.trans hmapneg.symm)

/-- **The Law of Quadratic Reciprocity**: if `p` and `q` are distinct odd primes, then
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`. -/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by
    sorry

end LeoQuadraticReciprocity


end legendreSym
