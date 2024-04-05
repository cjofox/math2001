/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.2: Proving equalities in Lean

This file should be worked through in parallel with the corresponding section of the book:
https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#proving-equalities-in-lean

I recommend splitting your screen to display the code and the book side by side! -/


-- Example 1.2.1
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring

-- Example 1.2.1.a: Demonstrating algebraic manipulation in Lean with verbose steps
-- Problem Statement:
-- Let a and b be rational numbers,
-- suppose that a - b = 4 and ab = 1,
-- show that (a + b)^2 = 20.
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
-- Solution
  calc
    -- Step 1: Expand (a + b)^2 using the binomial theorem.
    (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
    -- Step 2: Introduce 4ab by adding and subtracting 2ab.
    _ = a^2 - 2*a*b + b^2 + 4*a*b := by ring
    -- Step 3: Recognize (a - b)^2 and factor it out.
    _ = (a - b)^2 + 4*(a*b) := by ring
    -- Step 4: Substitute given values from hypotheses h1 (a - b = 4) and h2 (ab = 1).
    _ = (4)^2 + 4*(1) := by rw [h1, h2]
    -- Conclusion: Simplify to show (a + b)^2 equals 20.
    _ = 20 := by ring

-- Example 1.2.2.
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by ring

-- Example 1.2.3
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
    _ = 2 := by ring

-- Example 1.2.3.a: Alternative solution with more verbose intermediate steps.
example {a b n m : ℤ} (h1 : a*m + b*n = 1) (h2 : b^2 = 2*a^2) : (2*a*n + b*m)^2 = 2 :=
  calc
    -- Expand the square of the sum
    (2*a*n + b*m)^2 = 4*a^2*n^2 + 4*a*b*m*n + (b^2)*m^2 := by ring
    -- Apply the second hypothesis to replace b^2 with 2*a^2
    _               = 4*a^2*n^2 + 4*a*b*m*n + (2*a^2)*m^2 := by rw [h2]
    -- Factor out the common term 2*a^2 from the first and last terms
    _               = 2*(2*a^2)*n^2 + 4*a*b*m*n + 2*a^2*m^2 := by ring
    -- Use the reverse of the second hypothesis to replace 2*a^2 with b^2 in the first term
    _               = 2*(b^2)*n^2 + 4*a*b*m*n + 2*a^2*m^2 := by rw [←h2]
    -- Recognize and rewrite the entire expression as twice the square of (b*n + a*m)
    _               = 2*(b*n + a*m)^2 := by ring
    -- Commutativity of addition in the square term
    _               = 2*(a*m + b*n)^2 := by ring
    -- Apply the first hypothesis where a*m + b*n equals 1
    _               = 2*(1)^2 := by rw [h1]
    -- Simplify to complete the proof
    _               = 2 := by ring


-- Example 1.2.4.
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e)
      = (a*d)*f - d*b*e := by ring
      _ = (b*c)*f - d*b*e := by rw[h1]
      _ = b*(c*f) - d*b*e := by ring
      _ = b*(d*e) - d*b*e := by rw[h2]
      _ = 0 := by ring
