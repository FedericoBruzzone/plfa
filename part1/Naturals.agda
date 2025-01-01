{-# OPTIONS --exact-split #-}

module part1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ →  ℕ

-- Exercise `seven` (practice)
-- Write out 7 in longhand.
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

_+_ : ℕ →  ℕ →  ℕ
zero    + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

-- Exercise `+-example`
-- Compute 3 + 4, writing out your reasoning as a chain of equations, using the equations for +.
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    suc (suc 5)
  ≡⟨⟩
    suc 6
  ≡⟨⟩
    7
  ∎

_*_ : ℕ →  ℕ →  ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

-- Exercise *-example (practice)
-- Compute 3 * 4, writing out your reasoning as a chain of equations, using the equations for *. (You do not need to step through the evaluation of +.)
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + ( 4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    4 + (4 + 4)
  ≡⟨⟩
    4 + 8
  ≡⟨⟩
    12
  ∎

-- Exercise _^_ (recommended)
-- Define exponentiation, which is given by the following equations:
-- m ^ 0        =  1
-- m ^ (1 + n)  =  m * (m ^ n)
-- Check that 3 ^ 4 is 81.
_^_ : ℕ →  ℕ →  ℕ
m ^ zero    =  suc zero
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    3 * (3 * 9)
  ≡⟨⟩
    3 * 27
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ →  ℕ →  ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ = 3 ∸ 2 ≡ 1
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- Exercise ∸-example₁ and ∸-example₂ (recommended)
-- Compute 5 ∸ 3 and 3 ∸ 5, writing out your reasoning as a chain of equations.
_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩ -- inductive case
    4 ∸ 2
  ≡⟨⟩ -- inductive case
    3 ∸ 1
  ≡⟨⟩ -- base case
    2 ∸ 0
  ≡⟨⟩ -- simplify
    2
  ∎

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩ -- inductive case
    2 ∸ 4
  ≡⟨⟩ -- inductive case
    1 ∸ 3
  ≡⟨⟩ -- base case
    0 ∸ 2
  ≡⟨⟩ -- simplify
    0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise Bin (stretch)
-- A more efficient representation of natural numbers uses a binary rather than a unary system. We represent a number as a bitstring:
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin →  Bin
  _I : Bin →  Bin
-- For instance, the bitstring
-- 1011
-- standing for the number eleven is encoded as
-- ⟨⟩ I O I I
-- Representations are not unique due to leading zeros. Hence, eleven is also represented by 001011, encoded as:
-- ⟨⟩ O O I O I I
-- Define a function
-- inc : Bin →  Bin
-- that converts a bitstring to the bitstring for the next higher number. For example, since 1100 encodes twelve, we should have:
-- inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
inc : Bin →  Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ =
  begin
    inc (⟨⟩ I O I I)
  ≡⟨⟩
    inc (⟨⟩ I O I) O
  ≡⟨⟩
    inc (⟨⟩ I O) O O
  ≡⟨⟩
    ⟨⟩ I I O O
  ∎
-- Using the above, define a pair of functions to convert between the two representations.
-- to : ℕ →  Bin
-- from : Bin →  ℕ
-- For the former, choose the bitstring to have no leading zeros if it represents a positive natural, and represent zero by ⟨⟩ O. Confirm that these both give the correct answer for zero through four.

to : ℕ →  Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 0 ≡ ⟨⟩ O;     _ = refl
_ : to 1 ≡ ⟨⟩ I;     _ = refl
_ : to 2 ≡ ⟨⟩ I O;   _ = refl
_ : to 3 ≡ ⟨⟩ I I;   _ = refl
_ : to 4 ≡ ⟨⟩ I O O; _ = refl

from : Bin →  ℕ
from (⟨⟩ O) = 0
from (⟨⟩ I) = 1
from (b O) = 2 * (from b)
from (b I) = suc (2 * (from b))

_ : from (⟨⟩ O) ≡ zero;  _ = refl
_ : from (⟨⟩ I) ≡ 1;     _ = refl
_ : from (⟨⟩ I O) ≡ 2;   _ = refl
_ : from (⟨⟩ I I) ≡ 3;   _ = refl
_ : from (⟨⟩ I O O) ≡ 4; _ = refl

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

-- Unicode characters used in this file:
-- ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\bN)
-- →  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
-- ∸  U+2238  DOT MINUS (\.-)
-- ≡  U+2261  IDENTICAL TO (\==)
-- ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
-- ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
-- ∎  U+220E  END OF PROOF (\qed)
