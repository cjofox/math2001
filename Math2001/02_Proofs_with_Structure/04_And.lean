/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


-- Alternative proof
example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  -- h1 : 2 * x - y = 4, h2 : y - x + 1 = 2
  obtain ⟨h1, h2⟩ := h
  -- get y in terms of x from h1
  have h1' : y = 2*x - 4 := by addarith [h1]
  -- substitute h3 into h2 to eliminate y
  have h2' :=
  calc
    x = y - 1 := by addarith [h2]
    _ = 2*x - 4 - 1 := by rw [h1']
    _ = 2*x - 5 := by ring
  -- solve for x
  have hx :=
  calc
    5 = 2*x-x := by addarith [h2']
    _ = x := by ring
  -- since 5=x, x=5
  addarith [hx]


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  -- Show that -3 ≤ p ≤ 3 (same as -3 ≤ p ∧ p ≤ 3)
  have hp' : -3 ≤ p ∧ p ≤ 3
  -- Use lemma of absolute value less than a square is less than the square.
  -- Change goal from -3 ≤ p ∧ p ≤ 3 to p ^ 2 ≤ 3 ^ 2
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  -- h_neg3 : -3 ≤ p, h_pos3 : p ≤ 3
  · obtain ⟨h_neg3, h_pos3⟩ := hp'
    addarith [h_neg3]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  -- Show a ^ 2 = 0
  have h2 : a ^ 2 = 0
  -- change goal from a ^ 2 = 0 to a ^ 2 ≤ 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra
  have h3 : b^2 = 0
  · calc
      b^2 = -a^2 := by addarith [h1]
      _ = -0 := by rw [h2]
      _ = 0 := by ring

  -- split goal a = 0 ∧ b = 0 into 2 sub goals
  constructor
  -- Show a = 0
  · cancel 2 at h2
  -- Show b = 0
  · cancel 2 at h3

/-! # 2.4.5. Exercises -/

-- 1.
example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  -- Ha : a ≤ 1, Hb : a + b ≤ 3
  obtain ⟨Ha, Hb⟩ := H
  have Hb' : 1 + a + b ≤ 1 + 3 := by addarith [Hb]
  calc
    2*a + b = a + a + b := by ring
    _ ≤ 1 + a + b := by rel [Ha]
    _ ≤ 1 + 3 := by rel [Hb']
    _ = 4 := by numbers

-- 2.
example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
-- H1 : r + s ≤ 1, H2 : r - s ≤ 5
  obtain ⟨H1, H2⟩ := H
  calc
    2*r = r + s + r - s := by ring
    _ ≤ 1 + 5 := by addarith [H1, H2]
    _ = 6 := by ring

-- 3.
example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  -- H1 : n ≤ 8, H2 : m + 5 ≤ n
  obtain ⟨H1, H2⟩ := H
  calc
    m = m + 5 - 5 := by ring
    _ ≤ n - 5 := by rel [H2]
    _ ≤ 8 - 5 := by rel [H1]
    _ = 3 := by numbers

-- 4.
example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have hp' : p ≥ 7 := by addarith [hp]
  constructor
  · calc
      p^2 ≥ 7^2 := by rel [hp']
      _ = 49 := by numbers
  · addarith [hp']

-- 5.
example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h1 : a ≥ 6 := by addarith [h]
  constructor
  · addarith [h1]
  · calc
      3*a ≥ 3*6 := by rel [h1]
      _ ≥ 10 := by numbers

-- 6.
example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  -- h1 : x + y = 5, h2 : x + 2 * y = 7
  have ⟨h1, h2⟩ := h
  have hy : y = - x + 5 := by addarith [h1]
  -- substitute hy into h2
  have hx :=
  calc
    x = 7 - 2*y := by addarith [h2]
  -- substitute y = - x + 5
    _ = 7 - 2*(- x + 5) := by rw [hy]
    _ = 2*x - 3 := by ring
  have hx' :=
  calc
    3 = 2*x - x := by addarith [hx]
    _ = x := by ring
  constructor
  -- x = 3
  · addarith [hx']
  -- Substutite x = 3 into y = - x + 5, to show y = 3
  · addarith [hy, hx']


-- 7. Prove that if a * b equals both a and b,
--    then a and b must either both be 0 or both be 1.
example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by

  -- show a * (b - 1) = 0
  have h1' :=
  calc
    a * (b-1) = a*b - a := by ring
    _ = 0 := by addarith [h1]

  -- show b * (a - 1) = 0
  have h2' :=
  calc
    b * (a-1) = a*b - b := by ring
    _ = 0 := by addarith [h2]

  -- h1'' : a = 0 ∨ b - 1 = 0
  have h1'' := eq_zero_or_eq_zero_of_mul_eq_zero h1'
  -- ha0 : a = 0, hb1 : b - 1 = 0
  obtain ha0 | hb1 := h1''

  -- Left hand cases: a=0 (ha0) and b=0 (calculated below)
  -- Hypotheses in scope:
  -- h1, h2, h1', h2', ha0

  -- use h2' : b * (a - 1) = 0 and ha0 : a = 0 to show -b = -0 (b=0)
  have hb0' :=
  calc
    0 = b * (a-1) := by addarith [h2']
    _ = b * (0-1) := by rw [ha0]
  have hb0'' :=
  calc
    -0 = b * (-1) := by addarith [hb0']
    _ = -b := by ring

  -- left goal: a = 0 ∧ b = 0
  left
  constructor
  -- a = 0
  · addarith [ha0]
  -- b = 0
  · addarith [hb0'']

  -- Right hand cases: b=1, a=1 (calculated below)
  -- Hypotheses in scope:
  -- h1, h2, h1', h2', hb1

  -- use h2' : b * (a - 1) = 0 and hb1' : b = 1 (hb1 : b - 1 = 0)
  -- to show that ha1' : 0 = 1 * (a - 1)
  have hb1' : b = 1 := by addarith [hb1]
  have ha1'
  calc
    0 = b * (a-1) := by addarith [h2']
    _ = 1 * (a-1) := by rw [hb1']

  -- right goal: a = 1 ∧ b = 1
  right
  constructor
  -- a = 1
  · addarith [ha1']
  -- b = 1
  · addarith [hb1]
