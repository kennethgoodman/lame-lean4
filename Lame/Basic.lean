/-
Copyright (c) 2025 Kenneth Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Goodman
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.IntervalCases

/-!
# Lamé's Theorem

This file formalizes Lamé's theorem (1844), the founding result of computational
complexity theory. It states that the number of division steps in the Euclidean
algorithm is bounded by the Fibonacci sequence.

## Main results

- `Nat.euclidSteps`: counts the number of division steps in the Euclidean algorithm.
- `Nat.lame`: if `euclidSteps a b ≥ n + 1`, then `b ≥ fib (n + 1)` and `a ≥ fib (n + 2)`.
- `Nat.euclidSteps_le`: if `b < fib (n + 1)`, then `euclidSteps a b ≤ n`.

## References

- Gabriel Lamé, *Note sur la limite du nombre des divisions dans la recherche du plus grand
  commun diviseur entre deux nombres entiers*, 1844.
-/

set_option autoImplicit false

namespace Nat

/-- The number of division steps in the Euclidean algorithm on `(a, b)`.
Returns 0 when `b = 0`, and `1 + euclidSteps b (a % b)` otherwise. -/
def euclidSteps (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else 1 + euclidSteps b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero ‹b ≠ 0›)

/-- `euclidSteps a 0 = 0`. -/
@[simp]
theorem euclidSteps_zero_right (a : ℕ) : euclidSteps a 0 = 0 := by
  simp [euclidSteps]

/-- When `b > 0`, `euclidSteps a b = 1 + euclidSteps b (a % b)`. -/
theorem euclidSteps_succ (a : ℕ) {b : ℕ} (hb : 0 < b) :
    euclidSteps a b = 1 + euclidSteps b (a % b) := by
  rw [euclidSteps]
  simp [Nat.not_eq_zero_of_lt (Nat.zero_lt_of_lt hb)]

/-- If the Euclidean algorithm takes at least one step, then `b > 0`. -/
theorem euclidSteps_pos {a b : ℕ} (h : 0 < euclidSteps a b) : 0 < b := by
  by_contra hb
  push_neg at hb
  interval_cases b
  simp at h

/-- Helper lemma: when `0 < b` and `b ≤ a`, we have `b + a % b ≤ a`. -/
theorem add_mod_le {a b : ℕ} (hab : b ≤ a) (hb : 0 < b) : b + a % b ≤ a := by
  have h1 : 1 ≤ a / b := Nat.div_pos hab hb
  -- Set q = a / b, r = a % b, then q * b + r = a and q ≥ 1
  set q := a / b with hq_def
  set r := a % b with hr_def
  have h2 : q * b + r = a := Nat.div_add_mod' a b
  -- Since q ≥ 1, q * b ≥ b, so b + r ≤ q * b + r = a
  have h3 : b ≤ q * b := Nat.le_mul_of_pos_left b h1
  omega

/-- **Lamé's Theorem.** If the Euclidean algorithm on `(a, b)` with `b ≤ a` takes at
least `n + 1` steps, then `b ≥ fib (n + 1)` and `a ≥ fib (n + 2)`.

This is the founding result of computational complexity: it was the first theorem
to bound an algorithm's running time using a mathematical function. -/
theorem lame {a b : ℕ} (hab : b ≤ a) {n : ℕ} (hn : n + 1 ≤ euclidSteps a b) :
    fib (n + 1) ≤ b ∧ fib (n + 2) ≤ a := by
  induction n generalizing a b with
  | zero =>
    constructor
    · -- fib 1 = 1 ≤ b
      simp [fib_one]
      exact euclidSteps_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    · -- fib 2 = 1 ≤ a
      simp [fib_two]
      exact Nat.le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.not_eq_zero_of_lt
        (euclidSteps_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)))) hab
  | succ n ih =>
    have hb : 0 < b := euclidSteps_pos (Nat.lt_of_lt_of_le (Nat.succ_pos _) hn)
    rw [euclidSteps_succ a hb] at hn
    -- So euclidSteps b (a % b) ≥ n + 1
    have hn' : n + 1 ≤ euclidSteps b (a % b) := by omega
    -- a % b < b, so a % b ≤ b (IH precondition)
    have hmod_lt : a % b < b := Nat.mod_lt a hb
    have hmod_le : a % b ≤ b := Nat.le_of_lt hmod_lt
    -- Apply IH to (b, a % b)
    have ⟨ih1, ih2⟩ := ih hmod_le hn'
    -- ih1 : fib (n + 1) ≤ a % b
    -- ih2 : fib (n + 2) ≤ b
    constructor
    · -- fib (n + 2) ≤ b
      exact ih2
    · -- fib (n + 3) ≤ a
      -- Goal: fib (n + 1 + 2) ≤ a
      show fib (n + 1 + 2) ≤ a
      rw [show n + 1 + 2 = (n + 1) + 2 from rfl, @fib_add_two (n + 1)]
      -- Now goal: fib (n + 1) + fib (n + 1 + 1) ≤ a
      -- n + 1 + 1 = n + 2 by definitional equality
      change fib (n + 1) + fib (n + 2) ≤ a
      calc fib (n + 1) + fib (n + 2) ≤ a % b + b := by omega
        _ ≤ a := by have := add_mod_le hab hb; omega

/-- **Contrapositive of Lamé's theorem.** If `b < fib (n + 1)`, then the Euclidean
algorithm on `(a, b)` with `b ≤ a` takes at most `n` steps. -/
theorem euclidSteps_le {a b : ℕ} (hab : b ≤ a) {n : ℕ} (hb : b < fib (n + 1)) :
    euclidSteps a b ≤ n := by
  by_contra h
  push_neg at h
  have ⟨h1, _⟩ := lame hab h
  omega

/-- `euclidSteps` counts the number of recursive calls in the computation of
`Nat.gcd`. They follow the same recursion: `gcd` computes the result,
`euclidSteps` counts the steps. -/
theorem gcd_euclidSteps (a b : ℕ) :
    (euclidSteps a b = 0 ↔ b = 0) ∧
    (0 < b → euclidSteps a b = 1 + euclidSteps b (a % b)) := by
  refine ⟨⟨fun h => ?_, fun h => by subst h; simp⟩,
    fun hb => euclidSteps_succ a hb⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rfl
  · rw [euclidSteps_succ a hb] at h; omega

/-- When `a < b`, one Euclidean step swaps the arguments:
`euclidSteps a b = 1 + euclidSteps b a`. -/
theorem euclidSteps_of_lt {a b : ℕ} (hab : a < b) :
    euclidSteps a b = 1 + euclidSteps b a := by
  rw [euclidSteps_succ a (by omega : 0 < b),
    Nat.mod_eq_of_lt hab]

/-- For `n ≥ 2`, `fib (n + 2) % fib (n + 1) = fib n`. Since
`fib (n + 2) = fib n + fib (n + 1)` and `fib n < fib (n + 1)`
when `n ≥ 2`, the remainder is `fib n`. -/
private theorem fib_mod_fib_succ {n : ℕ} (hn : 2 ≤ n) :
    fib (n + 2) % fib (n + 1) = fib n := by
  rw [fib_add_two, Nat.add_mod_right,
    Nat.mod_eq_of_lt (fib_lt_fib_succ hn)]

/-- **Tightness of Lamé's bound.** Consecutive Fibonacci numbers
are the worst case for the Euclidean algorithm:
`euclidSteps (fib (n + 2)) (fib (n + 1)) = n` for `n ≥ 1`. -/
theorem euclidSteps_fib {n : ℕ} (hn : 0 < n) :
    euclidSteps (fib (n + 2)) (fib (n + 1)) = n := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => native_decide
    | succ n =>
      have hfib_pos : 0 < fib (n + 2 + 1) := by
        simp [fib_pos]
      rw [euclidSteps_succ _ hfib_pos,
        fib_mod_fib_succ (by omega : 2 ≤ n + 2),
        ih (by omega)]
      omega

-- Computational tests: verify euclidSteps on known examples
-- gcd(21, 13) is the classic worst case for Fibonacci inputs: 5 steps
-- 21 = 1*13 + 8, 13 = 1*8 + 5, 8 = 1*5 + 3, 5 = 1*3 + 2, 3 = 1*2 + 1, 2 = 2*1 + 0
example : euclidSteps 21 13 = 6 := by native_decide
-- fib 7 = 13, so Lamé says euclidSteps _ 13 ≤ 6. Our 6 steps is tight.
example : euclidSteps 21 13 ≤ 6 := by native_decide
-- gcd(10, 6): 10 = 1*6 + 4, 6 = 1*4 + 2, 4 = 2*2 + 0 → 3 steps
example : euclidSteps 10 6 = 3 := by native_decide
-- Trivial cases
example : euclidSteps 5 0 = 0 := by native_decide
example : euclidSteps 7 1 = 1 := by native_decide
-- Consecutive Fibonacci numbers are worst case: fib(n+1), fib(n) takes n steps
example : euclidSteps 8 5 = 4 := by native_decide
example : euclidSteps 13 8 = 5 := by native_decide

end Nat
