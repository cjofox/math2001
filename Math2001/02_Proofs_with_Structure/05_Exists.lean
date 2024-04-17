/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- 2.5.1.
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

-- 2.5.2.
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  -- x : ℝ, hxt : x * t < 0
  -- notice that "x" is substituted into "a"
  obtain ⟨x, hxt⟩ := h
  -- H0 : x ≤ 0 ∨ x > 0
  have H0 := le_or_gt x 0
  -- hxle0 : x ≤ 0, hxgt0 : x > 0
  obtain hxle0 | hxgt0 := H0

  -- Case 1: x ≤ 0 (hxle0)
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hxle0]
    cancel -x at hxt'
    -- change goal from t ≠ 0 to 0 < t
    apply ne_of_gt
    apply hxt'

  -- Case 2: x > 0 (hxle0)
  · have hxt'' :=
    calc
      0 < -x*t := by addarith [hxt]
      _ = x*(-t) := by ring
    -- -t > 0
    cancel x at hxt''
    -- change goal from t ≠ 0 to t > 0
    apply ne_of_lt
    -- t < 0
    addarith [hxt'']

-- 2.5.3.
example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers

-- 2.5.4.
example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra

-- 2.5.5.
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

-- 2.5.6.
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring

-- 2.5.7.
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  · calc
      p = (p+p)/2 := by ring
      _ < (p+q)/2 := by addarith [h]
  · calc
      (p+q)/2 < (q+q)/2 := by addarith [h]
      _ = q := by ring

-- 2.5.8.
example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  sorry
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  sorry

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  sorry

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
