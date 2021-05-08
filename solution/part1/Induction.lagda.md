# Induction


```agda
module solution.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
```

---

Exercise `operators`

1. ∧ and ∨ over `true` and `false`. They are associative, commutative, and distributive over the other.

1. Matrix multiplication. It is not commutative, but does have an identity.
---

## Proof by induction

---

Exercise `finite-∣-assoc`

```agda
-- omitted
```
---

## Building proofs interactively

Let us introduce some results first.

```agda
+-identity^r : ∀ ( n : ℕ ) → n + 0 ≡ n
+-identity^r zero = refl
+-identity^r (suc n) rewrite +-identity^r n = refl 

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity^r m = refl
+-comm m (suc n) rewrite +-comm n m | +-suc m n = refl
```

---

Exercise `+-swap`

```agda
+-swap : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-swap m n p rewrite +-assoc m n p = refl
```

---

Exercise `*-distrib-+`

```agda
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m zero p rewrite +-identity^r m | +-comm (m * p) 0 = refl
*-distrib-+ m (suc n) p rewrite +-suc m n 
                              | *-distrib-+ (suc m) n p 
                              | +-comm p (m * p)   
                              | +-assoc (m * p) p (n * p)
                              = refl
```