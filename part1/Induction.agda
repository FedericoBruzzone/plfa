module part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Exercise operators (practice)
-- Give another example of a pair of operators that have an identity and are associative, commutative, and distribute over one another. (You do not have to prove these properties.)
-- _*_
-- 2. Give an example of an operator that has an identity and is associative but is not commutative. (You do not have to prove these properties.)
-- _∸_

-- Associativity of addition
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- Proof: Associativity of addition
+-assoc : ∀ (m n p : ℕ) →  (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    ((suc m) + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    (suc m) + (n + p)
  ∎

-- Lemma: Right identity of addition
+-identityʳ : ∀ (m : ℕ) →  m + zero ≡ m
+-identityʳ zero =
    begin
        zero + zero
    ≡⟨⟩
        zero
    ∎
+-identityʳ (suc n) =
    begin
      suc n + zero
    ≡⟨⟩
      suc (n + zero)
    ≡⟨ cong suc (+-identityʳ n) ⟩
      suc n
    ∎

-- Lemma: `suc` as second argument
+-suc : ∀ (m n : ℕ) →  m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- Proof: Commutativity of addition
+-comm : ∀ (m n : ℕ) →  m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) →  (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ∎

-- Commutativity with rewrite
+-identity′ : ∀ (n : ℕ) →  n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) →  m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) →  m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

+-assoc′ : ∀ (m n p : ℕ) →  (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

-- Exercise +-swap (recommended)
-- Show
-- m + (n + p) ≡ n + (m + p)
-- for all naturals m, n, and p. No induction is needed, just apply the previous results which show addition is associative and commutative.
+-swap : ∀ (m n p : ℕ) →  m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p) ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

-- Exercise *-distrib-+ (recommended)
-- Show multiplication distributes over addition, that is,
-- (m + n) * p ≡ m * p + n * p
-- for all naturals m, n, and p.
*-distrib-+ : ∀ (m n p : ℕ) →  (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    ((suc m) + n) * p     ≡⟨⟩
    (suc (m + n)) * p     ≡⟨⟩
    p + ((m + n) * p)     ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)   ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + (m * p)) + n * p ≡⟨⟩
    (suc m * p) + n * p
  ∎

-- Exercise *-assoc (recommended)
-- Show multiplication is associative, that is,
-- (m * n) * p ≡ m * (n * p)
-- for all naturals m, n, and p.
*-assoc : ∀ (m n p : ℕ) →  (m * n) * p ≡ m * (n * p)
*-assoc zero n p =
  begin
    (zero * n) * p ≡⟨⟩
    zero * p       ≡⟨⟩
    zero           ≡⟨⟩
    zero * (n * p)
  ∎
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p     ≡⟨⟩
    (suc m) * n * p       ≡⟨⟩
    (n + m * n) * p       ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + m * n * p   ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + m * (n * p) ≡⟨⟩
    suc m  * (n * p)
  ∎

-- Exercise *-comm (practice)
-- Show multiplication is commutative, that is,
-- m * n ≡ n * m
-- for all naturals m and n. As with commutativity of addition, you will need to formulate and prove suitable lemmas.
*-mul-zero : ∀ (n : ℕ) →  n * zero ≡ zero
*-mul-zero zero = refl
*-mul-zero (suc n) =
  begin
    suc n * zero ≡⟨ *-mul-zero n ⟩
    zero
  ∎

*-comm : ∀ (m n : ℕ) →  m * n ≡ n * m
*-comm zero zero = refl
*-comm (suc m) zero rewrite *-mul-zero m = refl
*-comm zero (suc n) rewrite *-mul-zero n = refl
*-comm (suc m) (suc n) =
  begin
   begin
      begin
    (suc m) * (suc n) ≡⟨⟩
    (suc n) + (m * (suc n)) ≡⟨ cong ((suc n) +_) (*-comm m (suc n)) ⟩
    (suc n) + ((suc n) * m) ≡⟨⟩
    (suc n) + (m + (n * m)) ≡⟨ +-swap (suc n) m (n * m) ⟩
    m + ((suc n) + (n * m)) ≡⟨ sym (+-assoc m (suc n) (n * m)) ⟩
    (m + (suc n)) + (n * m) ≡⟨ cong (_+ (n * m)) (+-suc m n) ⟩
    suc (m + n) + (n * m)   ≡⟨ cong suc (+-assoc m n (n * m)) ⟩
    (suc m) + (n + (n * m)) ≡⟨ cong (λ m*n → (suc m) + (n + m*n)) (*-comm n m) ⟩
    (suc m) + (n + (m * n)) ≡⟨⟩
    (suc m) + ((suc m) * n) ≡⟨ cong ((suc m) +_) (*-comm ((suc m)) n) ⟩
    (suc m) + (n * (suc m)) ≡⟨⟩
    (suc n) * (suc m)
  ∎

