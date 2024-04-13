/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- Proof by Cases
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  -- split hypothesis into 2 cases
  obtain hx | hy := h
  -- prove case 1 given x=1
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  -- prove case 2 given y=-1
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

-- Proof by Natural Number Lemma and spliting into 2 cases
example {n : ℕ} : n ^ 2 ≠ 2 := by
  -- Use lemma that stated n is less than one natural number or greater than or equal to the next
  -- one. In this case, we state that n is either ≤ 1 or ≥ 2.
  have hn := le_or_succ_le n 1
  -- Split the hypothesis into 2 cases.
  -- I think it is easier to read if the hypotheses variables are separated into h1 and h2,
  -- rather than having the same variable hn for both cases.
  obtain h1 | h2 := hn
  -- for the first case, change the goal from n ^ 2 ≠ 2 to n ^ 2 < 2
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [h1]
    _ < 2 := by numbers
  -- for the first case, change the goal from n ^ 2 ≠ 2 to n ^ 2 > 2
  apply ne_of_gt
  calc
    n^2 ≥ 2^2 := by rel [h2]
    _ > 2 := by numbers


example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers

-- Alternative solution
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  have h1 :=
  calc
    2*x = 5 - 1 := by addarith [hx]
    _ = 2*2 := by numbers
  -- cancel the 2 on both sides, leaving x = 2, which is the goal.
  cancel 2 at h1

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  -- show (x-1)(x-2) = 0
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  -- split (x-1)(x-2) = 0 into 2 cases: x-1 = 0 or x-2 = 0
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  -- obtain the 2 cases from h2 so that h3 is x-1 = 0 and h4 is x-2 = 0
  obtain h3 | h4 := h2
  -- prove the left handside goal: x = 1
  left
  addarith [h3]
  -- prove the right handside goal: x = 2
  right
  addarith [h4]

-- 2.3.5. Example: Prove that the square of any integer n is not equal to 2.
example {n : ℤ} : n ^ 2 ≠ 2 := by
  -- Using lemma le_or_succ_le to split the range of ∀ {n : ℤ}.
  -- Consider separately, the cases n ≤ 0 or 1 ≤ n.
  have hn0 := le_or_succ_le n 0
  -- Split the cases of hn0:
  -- case 1: n ≤ 0,
  -- case 2: 1 ≤ n (variable doesn't appear to be used in proof, so using "_").
  obtain hn0_1 | _ := hn0

  --------------------------
  -- CASE 1: where n ≤ 0. --
  --------------------------
  -- Establish that the negation of n is non-negative.
  · have : 0 ≤ -n := by addarith [hn0_1]
    -- Splitting case 1: determine whether -n ≤ 1 or 2 ≤ -n.
    have hn1 := le_or_succ_le (-n) 1
    -- Distinguish the cases based on the value of -n.
    -- Splitting the 2 cases of hn1:
    -- case 1(i): -n ≤ 1
    -- case 1(ii): 2 ≤ -n.
    obtain hn1_i | hn1_ii := hn1

    -- Case 1(i): -n ≤ 1.
    -- Apply a lemma that establishes inequality via a less-than relationship.
    -- i.e. change goal from n ^ 2 ≠ 2 to n ^ 2 < 2
    · apply ne_of_lt
      -- Calculate to show n^2 is less than 2 when -n ≤ 1.
      calc
        n ^ 2 = (-n) ^ 2 := by ring -- Equality due to squaring eliminating sign.
        _ ≤ 1 ^ 2 := by rel [hn1_i] -- Apply the established bound on -n.
        _ < 2 := by numbers -- Conclude n^2 is less than 2.

    -- Case 1(ii) 2 ≤ -n.
    -- Apply a lemma that establishes inequality via a greater-than relationship.
    -- i.e. change goal from n ^ 2 ≠ 2 to n ^ 2 > 2
    · apply ne_of_gt
      -- Calculate to show n^2 is greater than 2 when 2 ≤ -n.
      calc
        (2:ℤ) < 2 ^ 2 := by numbers -- Establish that 2 is less than 4.
        _ ≤ (-n) ^ 2 := by rel [hn1_ii] -- Apply the established bound on -n.
        _ = n ^ 2 := by ring -- Equality due to squaring eliminating sign.

  --------------------
  -- CASE 2: 1 ≤ n. --
  --------------------
  -- Determine whether n ≤ 1 or 2 ≤ n.
  · have hn2 := le_or_succ_le n 1
    -- Split the 2 cases of hn2:
    -- Case 2(i): n ≤ 1
    -- Case 2(ii): 2 ≤ n
    obtain hn2_i | hn2_ii := hn2

    -- Case 2(i): n ≤ 1.
    -- Apply a lemma that establishes inequality via a less-than relationship.
    -- i.e. change goal from n ^ 2 ≠ 2 to n ^ 2 < 2.
    · apply ne_of_lt
      -- Calculate to show n^2 is less than 2 for case where n ≤ 1.
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn2_i] -- Apply the established bound on n.
        _ < 2 := by numbers -- Conclude n^2 is less than 2.

    -- Case 2(ii): 2 ≤ n.
    -- Apply a lemma that establishes inequality via a greater-than relationship.
    -- i.e. change goal from n ^ 2 ≠ 2 to n ^ 2 > 2.
    · apply ne_of_gt
      -- Calculate to show n^2 is greater than 2.
      calc
        (2:ℤ) < 2 ^ 2 := by numbers -- Establish that 2 is less than 4.
        _ ≤ n ^ 2 := by rel [hn2_ii] -- Apply the established bound on n.
-- 2.3.5. End

/-! # 2.3.6. Exercises -/

-- 1.
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h1 | h2 := h
  calc
    x^2 + 1 = 4^2 + 1 := by rw [h1]
    _ = 17 := by numbers
  calc
    x^2 + 1 = (-4)^2 + 1 := by rw [h2]
    _ = 17 := by numbers

-- 2.
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h2 := h
  calc
    x^2 - 3*x + 2 = 1^2 - 3*1 + 2 := by rw [h1]
    _ = 0 := by numbers
  calc
    x^2 - 3*x + 2 = 2^2 - 3*2 + 2 := by rw [h2]
    _ = 0 := by numbers

-- 3.
example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h2 := h
  calc
    t^2 - t - 6 = (-2)^2 - (-2) - 6 := by rw [h1]
    _ = 0 := by numbers
  calc
    t^2 - t - 6 = (3)^2 - (3) - 6 := by rw [h2]
    _ = 0 := by numbers

-- 4.
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h1 | h2 := h
  calc
    x*y + 2*x = 2*y + 2*2 := by rw [h1]
    _ = 2*y + 4 := by ring
  calc
    x*y + 2*x = x*(-2) + 2*x := by rw [h2]
    _ = 0  := by ring
    _ = 2*(-2) + 4 := by numbers
    _ = 2*y + 4 := by rw [h2]

-- 5.
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc
    s + t = 3 := by addarith [h]

-- 6.
example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  calc
    b = (a + 2*b - a)/2 := by ring
    _ < (0 - a)/2 := by rel [h]
    _ = -a/2 := by ring

-- 7.
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  calc
    y/2 = (2*x + 1)/2 := by rw [h]
    _ = x + 1/2 := by ring
    _ > x := by extra

-- 8. Solving a quadratic
example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  -- show (x+3)*(x-1) = 0
  have h2 :=
  calc
    (x+3)*(x-1) = x^2 + 2*x - 3 := by ring
    _ = 0 := by rw [hx]
  -- (x+3)*(x-1)=0 implies: x+3=0 or x-1=0
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  -- split the 2 cases, h4: x+3=0, h5: x-1=0
  obtain h4 | h5 := h3
  -- prove the left goal, x = -3
  left
  addarith [h4]
  -- prove the right goal, x = 1
  right
  addarith [h5]

-- 9.
example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h1 :=
  calc
    0 = a^2 - 3*a*b + 2*b^2 := by addarith [hab]
    _ = (a - b)*(a - 2*b) := by ring
  have h2 :=
  calc
    (a - b)*(a - 2*b) = 0 := by addarith [h1]
    _ = 0 := by ring
  -- h3 : a - b = 0 ∨ a - 2 * b = 0
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  -- h4 : a - b = 0, h5 : a - 2*b = 0
  obtain h4 | h5 := h3
  left
  addarith [h4]
  right
  addarith [h5]

-- 10.
example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 :=
  calc
    (t-1)*t^2 = t^3 - t^2 := by ring
    _ = 0 := by addarith [ht]
  -- h2 : t - 1 = 0 ∨ t ^ 2 = 0
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  -- h3 : t - 1 = 0, h4 : t ^ 2 = 0
  obtain h3 | h4 := h2
  left
  addarith [h3]
  right
  cancel 2 at h4

-- 11.
example {n : ℕ} : n ^ 2 ≠ 7 := by
  -- Step 1 is to split the set of n natural numbers into 2 sets.
  -- Splitting around 7, so ≤6 and ≥7, or ≤7 and ≥8 wouldn't help as none of these are squares.
  -- Splitting on ≤2 and ≥3 gives squares of 4 and 9,
  -- which is more useful, since they are either side of 7, so 4<7 and 9>7.
  -- So, hn: n ≤ 2 ∨ 3 ≤ n
  have hn := le_or_succ_le n 2
  -- h2 : n ≤ 2, h3 : 3 ≤ n
  obtain h2 | h3 := hn
  -- change goal from n ^ 2 ≠ 7 to n ^ 2 < 7
  apply ne_of_lt
  calc
    n^2 ≤ 2^2 := by rel [h2]
    _ < 7 := by numbers
  -- change goal from n ^ 2 ≠ 7 to 7 < n ^ 2
  apply ne_of_gt
  calc
    7 < 3^2 := by numbers
    _ ≤ n^2 := by rel [h3]

-- 12.
example {x : ℤ} : 2 * x ≠ 3 := by
  -- Step 1: again, we want successive values of x that give us 2*x < 3 and 2*x > 3.
  -- We split all of x into ≤ 1 and ≥ 2.
  -- hx : x ≤ 1 ∨ 2 ≤ x
  have hx := le_or_succ_le x 1
  -- h1 : x ≤ 1, h2 : 2 ≤ x
  obtain h1 | h2 := hx
  -- change goal from 2 * x ≠ 3 to 2 * x < 3
  apply ne_of_lt
  calc
    2*x ≤ 2*1 := by rel [h1]
    _ < 3 := by numbers
  -- change goal from 2 * x ≠ 3 to 3 < 2 * x
  apply ne_of_gt
  calc
    3 < 2*2 := by numbers
    _ ≤ 2*x := by rel [h2]

-- 13.
example {t : ℤ} : 5 * t ≠ 18 := by
  -- Split t into values ≤ 3 (giving 5*3 < 18) and values ≥ 4 (giving 5*4 > 18)
  -- ht : t ≤ 3 ∨ 4 ≤ t
  have ht := le_or_succ_le t 3
  -- h3 : t ≤ 3, h4 : 4 ≤ t
  obtain h3 | h4 := ht
  -- prove cases of t where 5 * t < 18
  apply ne_of_lt
  calc
    5*t ≤ 5*3 := by rel [h3]
    _ < 18 := by numbers
  -- prove cases of t where 18 < 5 * t
  apply ne_of_gt
  calc
    18 < 5*4 := by numbers
    _ ≤ 5*t := by rel [h4]

-- 14.
example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  -- We need to find consecutive numbers of m giving the first case < 46 and second case > 46.
  -- Since m is a Natural Number, we only need cases ≥ 0.
  -- Case 1: m = 5, so m^2 + 4*m = 45 < 46
  -- Case 2: m = 6, so m^2 + 4*m = 60 > 46
  -- hm : m ≤ 5 ∨ 6 ≤ m
  have hm := le_or_succ_le m 5
  -- h5 : m ≤ 5, h6 : 6 ≤ m
  obtain h5 | h6 := hm
  -- For m ≤ 5, show m^2 + 4*m < 46
  apply ne_of_lt
  calc
    m^2 + 4*m ≤ 5^2 + 4*5 := by rel [h5]
    _ < 46 := by numbers
  -- For 6 ≤ m, show 46 < m^2 + 4*m
  apply ne_of_gt
  calc
    46 < 6^2 + 4*6 := by numbers
    _ ≤ m^2 + 4*m := by rel [h6]
