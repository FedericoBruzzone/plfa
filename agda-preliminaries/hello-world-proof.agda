module agda-preliminaries.hello-world-proof where

open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

+-assoc : Set
+-assoc = ∀ (x y z : ℕ) →  x + (y + z) ≡ (x + y) + z
