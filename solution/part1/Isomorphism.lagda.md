# Isomorphism

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; *-distrib-+; +-assoc)
```

## Lambda expressions

Example code:

```agda
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)
```

## Extensionality

Example code:

```agda
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)
same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))
```

## Isomorphism

Example code:

```agda
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_
```

## Isomorphism is an equivalence

```agda
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl = record { 
    to = λ z → z ;
    from = λ z → z ;
    from∘to = λ x → refl ;
    to∘from = λ y → refl }

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B = record {
            to = from A≃B ;
            from = to A≃B ;
            from∘to = to∘from A≃B ;
            to∘from = from∘to A≃B }


≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C = record {
    to = λ z → to B≃C (to A≃B z) ;
    from = λ z → from A≃B (from B≃C z) ;
    from∘to = λ{x →
            begin
                (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
            ≡⟨⟩
                from A≃B (from B≃C (to B≃C (to A≃B x)))
            ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
                from A≃B (to A≃B x)
            ≡⟨ from∘to A≃B x ⟩
                x
            ∎} ;
    to∘from = λ{y →
        begin 
            to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong ((to B≃C)) (to∘from A≃B (from B≃C y)) ⟩
            to∘from B≃C y
        }
 }
```

## Equational reasoning for isomorphism

Example code:

```agda
module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning
```

## Embedding

Example code:

```agda
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl = record { to = λ z → z ; from = λ z → z ; from∘to = λ x → refl }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C = record {
                to = λ z → to B≲C (to A≲B z) ;
                from = λ z → from A≲B (from B≲C z) ;
                from∘to = λ x → begin 
                                    from A≲B (from B≲C (to B≲C (to A≲B x))) 
                                ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x ) ) ⟩
                                    from∘to A≲B x
                }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to = record { to = to A≲B ;
 from = from A≲B ;
 from∘to = from∘to A≲B ;
 to∘from = λ y → begin 
                    to A≲B (from A≲B y)
                ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
                    to A≲B (to B≲A y)
                ≡⟨ cong-app to≡from (to B≲A y ) ⟩
                    from∘to B≲A y
  } 
```

---

Exercise `≃-implies-≲`

```agda
≃-implies-≲ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≲ B
≃-implies-≲ = λ x → record { to = to x ; from = from x ; from∘to = from∘to x }
```

---

Exercise `_⇔_`

```agda
record _⇔_ (A B : Set) : Set where
    field
        to   : A → B
        from : B → A

⇔-refl : ∀ {A B : Set} → A ⇔ B → A ⇔ B
⇔-refl = λ x → record { to = _⇔_.to x ; from = _⇔_.from x }

⇔-sym : ∀ {A B : Set} → A ⇔ B → B ⇔ A
⇔-sym = λ x → record { to = _⇔_.from x ; from = _⇔_.to x }

⇔-trans : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans = λ x x₁ → record { to = λ z → _⇔_.to x₁ (_⇔_.to x z) ; from = λ z → _⇔_.from x (_⇔_.from x₁ z) }
```

---

Exercise `Bin-embedding`

```agda
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to-bin : ℕ → Bin
to-bin zero = ⟨⟩
to-bin (suc x) = inc (to-bin x)

from-bin : Bin → ℕ
from-bin ⟨⟩ = 0
from-bin (b O) = 2 * from-bin b
from-bin (b I) = 1 + 2 * from-bin b

law1 : ∀ (b : Bin) → from-bin (inc b) ≡ suc (from-bin b)
law1 ⟨⟩ = refl
law1 (b O) rewrite +-comm (from-bin b) 0 | +-comm (from-bin b + (from-bin b)) 1 = refl
law1 (b I) rewrite +-comm (from-bin b) 0 | +-comm (from-bin (inc b)) 0 | +-assoc (from-bin b) (from-bin b) 1 | +-comm (from-bin b) 1 | law1 b | +-comm (suc (from-bin b)) (from-bin b) = refl

law3 : ∀ (n : ℕ) → from-bin (to-bin n) ≡ n
law3 zero = refl
law3 (suc n) rewrite law1 (to-bin n) | law3 n = refl

≲-Bin : ℕ ≲ Bin
≲-Bin = record { to = to-bin; from = from-bin ; from∘to = λ (x : ℕ) → law3 x }
```