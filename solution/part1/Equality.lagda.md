# Equality


```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

```

## Equality is an equivalence relation

Example code:

```agda
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl  =  refl
```

## Congruence and substitution

Example code:

```agda
cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px
```

## Chains of equations

Example code:

```agda
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning
```

---

Exercise `trans` and `≡-Reasoning`

Because the `­≡-Reasoning` includes `trans`, as the definition of `_≡⟨_⟩_` shown.


## Chains of equations, another example

Exercise

```agda
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-comm; ≤-trans; ≤-refl)

module ≤-Reasoning where

    infix  1 begin≤_

    infixr 2 _≤⟨⟩_ _≤⟨_⟩_

    infix  3 _∎≤

    begin≤_ : ∀ {x y : ℕ}
        → x ≤ y
        -----
        → x ≤ y

    begin≤ x = x

    _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
        → x ≤ y
        -----
        → x ≤ y

    x ≤⟨⟩ y = y

    _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
        → x ≤ y
        → y ≤ z
        -----
        → x ≤ z
    x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

    _∎≤ : ∀ (x : ℕ)
        -----
        → x ≤ x
    x ∎≤  = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ {p n m} → n ≤ m → p + n ≤ p + m
+-monoʳ-≤ {zero} x = x
+-monoʳ-≤ {suc p} {n} {m} x = begin≤ 
                                 suc p + n 
                              ≤⟨ (s≤s (+-monoʳ-≤ x)) ⟩
                                 suc p + m
                              ∎≤

+-monoˡ-≤ : ∀ {n m p} → n ≤ m → n + p ≤ m + p
+-monoˡ-≤ {n} {m} {p} x rewrite +-comm n p | +-comm m p  = begin≤ 
                            p + n
                          ≤⟨ +-monoʳ-≤ x ⟩
                            p + m
                          ∎≤
+-mono-≤ : ∀ {n m p q} → n ≤ m → p ≤ q → n + p ≤ m + q
+-mono-≤ {n} {m} {p} {q} x x₁ = begin≤ 
                                    n + p
                                ≤⟨ +-monoʳ-≤ {n} {p} {q} x₁ ⟩ 
                                    n + q
                                ≤⟨ +-monoˡ-≤ {n} {m} {q} x ⟩ 
                                    m + q
                                ∎≤
```

## Rewriting

Example code:

```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev rewrite +-comm n m  = ev

```

## Lebniz equality


Example code:

```agda
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P  = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx
```

## Universe polymorphism


Example code:

```agda

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x
sym′ refl′ = refl′

```