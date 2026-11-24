import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# This module formalizes HW Exercise 11.5 from Leo Goldmahker's Number Theory class.
-/

open scoped BigOperators NumberTheorySymbols

namespace JacobiCharacterSum

/- The Jacobi symbol, regarded as a function on residue classes modulo `n`. -/
abbrev jacobiClass (n : ℕ) (x : ZMod n) : ℤ :=
  J((x.val : ℤ) | n)

/- The sum `∑ a ∈ ZMod n, J(a | n)` from the exercise. -/
abbrev jacobiSum (n : ℕ) [NeZero n] : ℤ :=
  ∑ x : ZMod n, jacobiClass n x

/-!
The first two helper theorems are the main meat for part (a).

* Prove `jacobiClass_mul` from `jacobiSym.mul_left` and
  `jacobiSym.mod_left'`.
* For `sum_jacobiClass_mul`, use the hypothesis to show that `b` is a unit
  modulo `n`; multiplication by a unit permutes `ZMod n`.
-/

/- Here, a key observation is that multiplication in ZMod n
  corresponds to multiplication modulo n on representatives. -/
private theorem jacobiClass_mul (n : ℕ) [NeZero n] (b x : ZMod n) :
    jacobiClass n (b * x) = jacobiClass n b * jacobiClass n x := by
  calc
    J(((b * x).val : ℤ) | n)
        = J(((b.val : ℤ) * (x.val : ℤ)) | n) := by
            apply jacobiSym.mod_left'
            simp only [ZMod.val_mul]
            norm_cast
            simp
    _ = J((b.val : ℤ) | n) * J((x.val : ℤ) | n) := by
          exact jacobiSym.mul_left b.val x.val n

private theorem sum_jacobiClass_mul (n : ℕ) [NeZero n] (b : ZMod n)
    (hb : jacobiClass n b = -1) :
    ∑ x : ZMod n, jacobiClass n (b * x) = jacobiSum n := by
  have hcoprime : Nat.Coprime b.val n := by
    refine Nat.coprime_iff_gcd_eq_one.mpr ?_
    by_contra h
    unfold jacobiClass at hb
    have hzero : J((b.val : ℤ) | n) = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      exact h
    rw [hzero] at hb
    norm_num at hb
  have hbunit : IsUnit b := by
    rw [←ZMod.natCast_zmod_val b]
    exact (ZMod.isUnit_iff_coprime b.val n).mpr hcoprime
  obtain ⟨u, rfl⟩ := hbunit
  exact Fintype.sum_bijective (fun x : ZMod n => (u : ZMod n) * x) (Units.mulLeft_bijective u)
    (fun x => jacobiClass n ((u : ZMod n) * x)) (fun x => jacobiClass n x) (fun _ => rfl)


/- Exercise 11.5(a). -/
theorem jacobiSum_eq_zero_of_exists_jacobi_neg_one {n : ℕ} [NeZero n]
    (h : ∃ b : ZMod n, jacobiClass n b = -1) :
    jacobiSum n = 0 := by
  -- Get witness 'b' with the hypothesis 'jacobiClass n b = -1'.
  obtain ⟨b, hb⟩ := h
  -- Reindex 'jacobiSum n' by mapping x ↦ b * x using helper theorem.
  have h_reindex : jacobiSum n = ∑ x : ZMod n, jacobiClass n (b * x) :=
    (sum_jacobiClass_mul n b hb).symm
  -- Apply multiplicativity and hb inside the sum.
  have h_neg_summands :
      (∑ x : ZMod n, jacobiClass n (b * x)) = ∑ x : ZMod n, (-1) * jacobiClass n x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [jacobiClass_mul, hb]
  -- Factor -1 out of the finite sum, then rewrite back to 'jacobiSum n'.
  have h_factor_neg :
      (∑ x : ZMod n, (-1) * jacobiClass n x) = -jacobiSum n := by
    simp_rw [neg_one_mul]
    rw [Finset.sum_neg_distrib]
  -- Use a calc block to get 'jacobiSum n = -jacobiSum n'.
  have h_self_neg : jacobiSum n = -jacobiSum n := by
    calc
      jacobiSum n
        = ∑ x : ZMod n, jacobiClass n (b * x) := h_reindex
      _ = ∑ x : ZMod n, (-1) * jacobiClass n x := h_neg_summands
      _ = -jacobiSum n := h_factor_neg
  omega

#check jacobiSym.eq_zero_iff_not_coprime
