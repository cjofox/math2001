/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/

-- Example 1.3.1: Proving a = 11 with given conditions
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2*b + 5 := by rw [h1]  -- Substitute for a using h1
    _ = 2*3 + 5 := by rw [h2]  -- Substitute for b using h2
    _ = 11 := by ring         -- Simplify arithmetic

-- Example 1.3.2: Solving for x
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = (x + 4) - 4 := by ring  -- Rearrange to isolate x
    _ = 2 - 4 := by rw [h1]     -- Substitute for x + 4 using h1
    _ = -2 := by ring           -- Simplify arithmetic

-- Example 1.3.3: Finding a with given a and b conditions
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = (a - 5*b) + 5*b := by ring  -- Add and subtract 5b to isolate a
    _ = 4 + 5*b := by rw [h1]       -- Substitute for a - 5b using h1
    _ = 4 + 5*(b + 2 - 2) := by ring  -- Manipulate b for substitution
    _ = 4 + 5*(b+2) - 10 := by ring  -- Expand to separate b+2
    _ = 4 + 5*3 - 10 := by rw [h2]  -- Substitute for b+2 using h2
    _ = 9 := by ring                 -- Simplify arithmetic

-- Example 1.3.4: Determining w from given equation
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = ((3*w + 1) - 1)/3 := by ring  -- Isolate w
    _ = (4 - 1)/3 := by rw [h1]       -- Substitute for 3w + 1 using h1
    _ = 1 := by ring                  -- Simplify arithmetic

-- Example 1.3.5: Isolating x in the given equation
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
    x = (2*x + 3) - x - 3 := by ring  -- Rearrange to isolate x
    _ = x - x - 3 := by rw [h1]       -- Substitute for 2x + 3 using h1
    _ = -3 := by ring                 -- Simplify arithmetic

-- Example 1.3.6: Solving for x using two given equations
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x = (2*x - y) + (y - x + 1) - 1 := by ring  -- Combine and rearrange equations
    _ = 4 + 2 - 1 := by rw [h1, h2]  -- Substitute using h1 and h2
    _ = 5 := by ring                -- Simplify arithmetic

-- Example 1.3.7: Finding u from two equations involving u and v
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = ((u + 2 * v)  + (u - 2 * v))/2 := by ring  -- Average expressions for u
    _ = (4 + 6)/2 := by rw [h1, h2]     -- Substitute using h1 and h2
    _ = 5 := by ring                    -- Simplify arithmetic

-- Example 1.3.8: Using two conditions to solve for x
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x = ((5*x - 3*y) + 3*(x + y))/8 := by ring  -- Manipulate equations to isolate x
    _ = (4 + 3*4)/8 := by rw [h1, h2]  -- Substitute using h1 and h2
    _ = 2 := by ring                  -- Simplify arithmetic

-- Example 1.3.9: Relating a^2 - a + 3 to a function of b
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a^2 - a + 3 = ((a-3) + 3)^2 - (a-3) := by ring  -- Expand a^2 - a + 3
    _ = ((2*b) + 3)^2 - (2*b) := by rw [h1]  -- Substitute for a - 3 using h1
    _ = 4*b^2 + 12*b + 9 - 2*b := by ring  -- Expand and simplify
    _ = 4*b^2 + 10*b + 9 := by ring        -- Further simplify arithmetic

-- Example 1.3.10: Deriving a complex expression using z^2 - 2 = 0
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    -- Rearrange terms to facilitate substitution
    z^4 - z^3 - z^2 + 2*z + 1 = (z^4 - 4*z^2 + 4) + 3*(z^2 - 2 + 1) - z*(z^2 - 2) := by ring
    -- Simplify using polynomial identities and distribute z
    _ = (z^2 - 2)^2 + 3*((z^2 - 2) + 1) - z*(z^2 - 2) := by ring
    -- Apply the hypothesis h1 to substitute z^2 - 2 with 0
    _ = (0)^2 + 3*((0) + 1) - z*(0) := by rw [h1]
    -- Simplify the expression to conclude
    _ = 3 := by ring

/-! # 1.3.11. Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y = 4*(x) - 3 := by rw [h2]
    _ = 4*(3) - 3 := by rw [h1]
    _ = 9 := by ring

example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a = (a - b) + b := by ring
    _ = (0) + b := by rw [h]
    _ = b := by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x = (x - 3*y) + 3*(y) := by ring
    _ = (5) + 3*(3) := by rw [h1, h2]
    _ = 14 := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
    p = (p - 2*q) + 2*(q) := by ring
    _ = (1) + 2*(-1) := by rw [h1, h2]
    _ = -1 := by ring

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  calc
    x = (x + 2*y) - 2*((y + 1) - 1) := by ring
    _ = (3) - 2*((3) - 1) := by rw [h2, h1]
    _ = -1 := by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
    p = (p + 4*q) - 4*((q - 1) + 1) := by ring
    _ = (1) - 4*((2) + 1) := by rw [h1, h2]
    _ = -11 := by ring

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
    a = (a + 2*b + 3*c) -(2*(b + 2*c) - (c)) := by ring
    _ = (7) -(2*(3) - (1)) := by rw [h1, h2, h3]
    _ = 2 := by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
    u = ((4*u + v) - (v))/4 := by ring
    _ = ((3) - (2))/4 := by rw [h1, h2]
    _ = 1/4 := by ring

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  calc
    c = (4*c + 1) - 3*c - 1 := by ring
    _ = (3*c - 2) - 3*c - 1 := by rw [h1]
    _ = -3 := by ring

example {p : ℝ} (h1 : 5*p - 3 = 3*p + 1) : p = 2 :=
  sorry

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  calc
    x = (2*x + y) - (x + y) := by ring
    _ = (4) - (1) := by rw [h1, h2]
    _ = 3 := by ring

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  calc
    a = ((a + 2*b) + 2*(a - b))/3  := by ring
    _ = ((4) + 2*(1))/3 := by rw [h1, h2]
    _ = 2 := by ring

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
    u^2 + 3*u + 1 = ((u + 1) - 1)^2 + 3*((u + 1) - 1) + 1 := by ring
    _ = ((v) - 1)^2 + 3*((v) - 1) + 1 := by rw [h1]
    _ = v^2 - 2*v + 1 + 3*v - 2 := by ring
    _ = v^2 + v - 1 := by ring

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  calc
    t^4 + 3*t^3 - 3*t^2 - 2*t - 2
    = (t^4 - 8*t^2 + 16) - 16 + 8*((t^2 - 4) + 4) + t*(3*(t^2 - 4 + 4) - 2) - 3*((t^2 - 4) + 4) - 2 := by ring
    _ = (t^2 - 4)^2  + 8*(t^2 - 4)  + t*(3*(t^2 - 4) + 10) - 3*(t^2 - 4) + 2 := by ring
    _ = (0)^2  + 8*(0)  + t*(3*(0) + 10) - 3*(0) + 2 := by rw [ht]
    _ = 10*t + 2 := by ring

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  sorry

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  calc
    p^2 + q^2 + r^2 = (p + q + r)^2 -2*(p*q + p*r + q*r) := by ring
    _ = (0)^2 -2*(2) := by rw [h1, h2]
    _ = -4 := by ring
