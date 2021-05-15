# Connectives

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning
```

## Conjunction is product

Example code:

```agda
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }
```

---

Exercise `⇔≃×`

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

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record { 
    to = λ x → ⟨ _⇔_.to x , _⇔_.from x ⟩ 
    ; from = λ x → record { 
            to = proj₁ x
            ; from = proj₂ x 
            } 
    ; from∘to = λ x → refl 
    ; to∘from = λ y → η-× y 
    }
```

## Truth is unit

Example code:

```agda
data ⊤ : Set where

  tt :
    --
    ⊤
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record { 
    to = λ x → proj₂ x 
    ; from = λ x → ⟨ tt , x ⟩ 
    ; from∘to = λ { ⟨ tt , x ⟩  →  refl }
    ; to∘from =  λ y → refl
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

```

## Disjunction is sum

Example code:

```agda
data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_


```

---

Exercise `⊎-comm`

```agda
⊎-comm : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-comm {A} {B} (inj₁ x) = inj₂ x
⊎-comm {A} {B} (inj₂ x) = inj₁ x
```

--

Exercise `⊎-assoc`

```agda
⊎-assoc : ∀ {A B C : Set} → A ⊎ B ⊎ C → (A ⊎ B) ⊎ C
⊎-assoc (inj₁ x) = inj₁ (inj₁ x)
⊎-assoc (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
⊎-assoc (inj₂ (inj₂ x)) = inj₂ x
```

## False is empty

Example code:

```agda
data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()
```

---

Exercise `⊥-identityˡ`

-- ⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A


```agda
empty-body-app : ∀ {A : ⊥} { B : Set } {f : ⊥ → ⊥} → (f A) ≡ A
empty-body-app {()} {f}

⊥-identityˡ : ∀ {A : Set} → ⊥ × A ≃ ⊥
⊥-identityˡ = record { 
                    to = λ { ⟨ () , a ⟩ }
                    ; from = λ ()
                    ; from∘to = λ { ⟨ () , x₁ ⟩ }
                    ; to∘from = λ y → ⊥-elim y
                }

⊥-identityʳ : ∀ {A : Set} → A × ⊥ ≃ ⊥
⊥-identityʳ = record { 
                to = λ { ⟨ a , () ⟩ }
                ; from = λ () 
                ; from∘to = λ { ⟨ x , () ⟩ }
                ; to∘from = λ y → ⊥-elim y
                }
```

## Implication is function

Example code:

```agda
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
```

## Distribution

Exercise `⊎-weak-×`

```agda
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , x₁ ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , x₁ ⟩ = inj₂ ⟨ x , x₁ ⟩
```

And the distributive law is :

```agda
⊎-disrtib-× : ∀ {A B C : Set} → (A ⊎ B) × C → (A × C) ⊎ (B × C)
⊎-disrtib-× ⟨ inj₁ x , x₁ ⟩ = inj₁ ⟨ x , x₁ ⟩
⊎-disrtib-× ⟨ inj₂ x , x₁ ⟩ = inj₂ ⟨ x , x₁ ⟩ 
```

As one can observe in the proof, the only subtle difference is at each proof's second line.
The stronger property also employs the fact about `C`, but the weaker version does not.

--- 

Exercise `⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)`

```agda
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , x₁ ⟩) = ⟨ inj₁ x , inj₁ x₁ ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , x₁ ⟩) = ⟨ inj₂ x , inj₂ x₁ ⟩

```
We could try to prove it, but will encounter ab obstacle to show that to prove `A × B ⊎ C × D` given only `A` and `D`, 
which is obviously impossible.

```agda
-- ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- ×⊎-implies-⊎× ⟨ inj₁ a , inj₁ b ⟩ = inj₁ ⟨ a , b ⟩
-- ×⊎-implies-⊎× ⟨ inj₁ a , inj₂ d ⟩  = {!   !}
-- ×⊎-implies-⊎× ⟨ inj₂ c , inj₁ b ⟩ = {!   !}
-- ×⊎-implies-⊎× ⟨ inj₂ c , inj₂ d ⟩ = inj₂ ⟨ c , d ⟩
```