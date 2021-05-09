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

---

Exercise `*-assoc`

```agda
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl
```

---

Exercise `*-comm`

```agda
*-rzero : ∀ (m : ℕ) → m * 0 ≡ 0
*-rzero zero = refl
*-rzero (suc m) rewrite *-rzero m = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-rzero m = refl
*-comm zero (suc n) rewrite *-rzero (suc n) = refl
*-comm (suc m) (suc n) rewrite *-comm n (suc m) 
                             | *-comm m (suc n) 
                             | *-comm n m 
                             | sym (+-assoc n m (m * n)) 
                             | sym (+-assoc m n (m * n)) 
                             | +-comm n m 
                             = refl
```

---

Exercise `0∸n≡0`

```agda
zero-monus-n : ∀ (n : ℕ) →  0 ∸ n ≡ 0
zero-monus-n zero = refl
zero-monus-n (suc n) rewrite zero-monus-n n = refl
```

---

Exercise `∸-|-assoc`

```agda
monus-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
monus-|-assoc zero n p rewrite zero-monus-n n | zero-monus-n (n + p) | zero-monus-n p = refl
monus-|-assoc (suc m) zero p rewrite +-suc 0 p = refl
monus-|-assoc (suc m) (suc n) p rewrite +-suc n p | monus-|-assoc m n p = refl
```

---

Exercise `+*^`

Import `_^_` frist.

```agda
open import Data.Nat using (_^_)
```

And we prove a lemma for future use:

```agda
*-swap : ∀ (k m n p : ℕ) → k * m * (n * p) ≡ k * n * (m * p)
*-swap k m n p rewrite *-assoc k m (n * p) 
                     | *-assoc k n (m * p) 
                     | sym (*-assoc m n p)
                     | *-comm m n
                     | *-assoc n m p
                     = refl
```

This exercise includes three parts:

```agda
^-distrib-l-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distrib-l-|-* m n zero rewrite +-identity^r n | *-comm (m ^ n) 1 | +-identity^r (m ^ n)  = refl
^-distrib-l-|-* m zero (suc p) rewrite +-identity^r (m * (m ^ p)) = refl
^-distrib-l-|-* m (suc n) (suc p) rewrite +-suc n p 
                                         | ^-distrib-l-|-* m n p  
                                         | sym (*-assoc m (m ^ n) (m ^ p))
                                         | *-assoc m (m ^ n) (m * (m ^ p))
                                         | *-comm m (m ^ n)
                                         | sym (*-assoc (m ^ n) m (m ^ p))
                                         = refl
```

and

```agda
^-distrib-r-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distrib-r-* m n zero = refl
^-distrib-r-* m n (suc p) rewrite ^-distrib-r-* m n p | *-swap m n (m ^ p) (n ^ p) = refl
```
, and 

```agda
lemma : ∀ (m n : ℕ) → m * suc n ≡ m + n * m
lemma m n rewrite *-comm m (suc n) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-rzero n = refl
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p | lemma n p | ^-distrib-l-|-* m n (p * n) | *-comm n p = refl
```
