# Relations

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)
```

## Defining relations

```agda
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ} → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    → suc m ≤ suc n

infix 4 _≤_
```

Exercise `orderings`

1. R = ℕ² is a preorder (reflexive + transitive), but not anti-symmetric, hence not a partial order.

1. The set-theoretic "subseteq" relation ⊆. It is a partial order but not total.

---

Example code:

```agda
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s ((≤-trans m≤n n≤p))

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)
```

Exercise `≤-antisym-cases`

Because there are unnecessary cases involving the equation `suc n = zero`, which has no solution, hence omitted.

```agda

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
```

Exercise `*-mono-≤`

We import `*` and it properties first:
```agda
open import Data.Nat using (_*_)
open import Data.Nat.Properties using (*-comm)
```

```agda
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → (n + p) ≤ (n + q)
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → (m + p) ≤ (n + p)
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → (m + p) ≤ (n + q)
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ) 
    → p ≤ q 
    → (n * p) ≤ (n * q)
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = ≤-trans (+-monoˡ-≤ p q (n * p) p≤q) (+-mono-≤ q q (n * p) (n * q) ≤-refl (*-monoʳ-≤ n p q p≤q))

*-monoˡ-≤ : ∀ (p q n : ℕ) 
    → p ≤ q 
    → (p * n) ≤ (q * n)
*-monoˡ-≤ p q zero p≤q rewrite *-comm p 0 = z≤n
*-monoˡ-≤ p q (suc n) p≤q rewrite *-comm p (suc n) | *-comm q (suc n) = *-monoʳ-≤ (suc n) p q p≤q

*-mono-≤ : ∀ (m n p q : ℕ) 
    → m ≤ n 
    → p ≤ q 
    → (m * p) ≤ (n * q)
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)
```

Notice that it will be some unnecessary boring steps if you to define `*-monoˡ-≤` before `*-monoʳ-≤`.