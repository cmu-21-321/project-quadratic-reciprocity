import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace legendreSym

variable (p : ℕ) [instPp : Fact p.Prime]
variable (q : ℕ) [instPq : Fact q.Prime]
variable (hpq : p ≠ q)

theorem euler1 (hOdd : p ≠ 2 ∧ q ≠ 2) :
    (p : ZMod 4) = 1 ∧ (q : ZMod 4) = 1 → legendreSym p q = legendreSym q p := by
  sorry

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

noncomputable def leftFinset : Finset (ZMod (p * q))ˣ :=
  (Set.toFinite (LeftSubset p q)).toFinset

noncomputable def rightFinset : Finset ((ZMod p)ˣ × (ZMod q)ˣ) :=
  (Set.toFinite (RightSubset p q)).toFinset

lemma crt_isomorphism_mul_neg (x : (ZMod (p * q))ˣ) :
    crt_isomorphism_mul p q hpq (-x) = -crt_isomorphism_mul p q hpq x := by
  let crt := ZMod.chineseRemainder ((Nat.coprime_primes instPp.out instPq.out).2 hpq)
  apply Prod.ext <;> apply Units.ext
  · exact congrArg Prod.fst (crt.map_neg x.val)
  · exact congrArg Prod.snd (crt.map_neg x.val)

lemma crt_preimage_uniqueness (a : (ZMod p)ˣ) (b : (ZMod q)ˣ) :
    ∃! k ∈ LeftSubset p q,
      crt_isomorphism_mul p q hpq k = (a, b) ∨ crt_isomorphism_mul p q hpq k = -(a, b) := by
  let φ := crt_isomorphism_mul p q hpq
  let k' := φ.symm (a, b)
  have hval_neg : (-k').val.val = p * q - k'.val.val := by
    have hn : 1 < p * q := by nlinarith [instPp.out.one_lt, instPq.out.one_lt]
    let : Fact (1 < p * q) := ⟨hn⟩
    let : NeZero (p * q) :=
      ⟨Nat.mul_ne_zero instPp.out.ne_zero instPq.out.ne_zero⟩
    let : NeZero (k'.val : ZMod (p * q)) := ⟨Units.ne_zero k'⟩
    simpa only [Units.val_neg] using
      (ZMod.val_neg_of_ne_zero (n := p * q) (a := (k'.val : ZMod (p * q))))
  have hval_negQ : ((-k').val.val : ℚ) = (p * q : ℚ) - k'.val.val := by
    rw [hval_neg, Nat.cast_sub (Nat.le_of_lt (ZMod.val_lt _))]
    norm_num
  rcases lt_trichotomy (k'.val.val : ℚ) ((p * q : ℚ) / 2) with hLt|hEq|hGt
  · use k'
    constructor
    · constructor -- existence
      · exact hLt -- k ∈ L
      · left; exact MulEquiv.apply_symm_apply φ (a, b) -- equality
    · rintro y ⟨hymem, hPos | hNeg⟩ -- uniqueness, using isomorphism injectivity
      · apply φ.injective
        rw [hPos, MulEquiv.apply_symm_apply]
      · exfalso -- this case is not possible
        have hy_eq_neg : y = -k' := by
          apply φ.injective
          rw [hNeg, crt_isomorphism_mul_neg, MulEquiv.apply_symm_apply]
        change (y.val.val : ℚ) < (p * q : ℚ) / 2 at hymem
        rw [hy_eq_neg] at hymem
        linarith
  · have hhalfQ : (2 : ℚ) * (k'.val.val : ℚ) = p * q := by linarith [hEq]
    have hneg_eq_self : -k' = (k' : ZMod (p * q)) := by
      apply (ZMod.neg_eq_self_iff (k' : ZMod (p * q))).mpr
      right
      exact_mod_cast hhalfQ
    have hsum_eq_zero : (k' : ZMod (p * q)) + k' = 0 := by
      nth_rw 1 [←hneg_eq_self]
      ring
    have htwo_eq_zero : (2 : ZMod (p * q)) = 0 := by
      calc
        (2 : ZMod (p * q)) = 1 + 1 := by norm_num
        _ = k'.val * k'⁻¹ + k'.val * k'⁻¹ := by rw [←Units.mul_inv]
        _ = 0 := by rw [←right_distrib, hsum_eq_zero, Units.mul_left_eq_zero]
    have hdiv : p * q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p * q)).mp htwo_eq_zero
    have hpq_le_two : p * q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    nlinarith [instPp.out.one_lt, instPq.out.one_lt]
  · use -k'
    dsimp
    constructor
    · constructor
      · change ((-k').val.val : ℚ) < (p * q : ℚ) / 2
        rw [hval_negQ]
        linarith
      · right
        rw [crt_isomorphism_mul_neg, MulEquiv.apply_symm_apply]
        dsimp
    · rintro y ⟨hymem, hPos | hNeg⟩ -- this is the exact mirror of the lt case
      · exfalso
        change (y.val.val : ℚ) < (p * q : ℚ) / 2 at hymem
        have hy_eq_pos : y = k' := by
          apply φ.injective
          rw [hPos, MulEquiv.apply_symm_apply]
        rw [hy_eq_pos] at hymem
        linarith
      · apply φ.injective
        rw [hNeg, crt_isomorphism_mul_neg, MulEquiv.apply_symm_apply]
        dsimp

/-- **The Law of Quadratic Reciprocity**: if `p` and `q` are distinct odd primes, then
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`. -/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by
    sorry

end LeoQuadraticReciprocity


end legendreSym
