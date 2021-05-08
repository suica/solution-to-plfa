# solution-to-plfa

My solution to _Programming Language Foundations in Agda_ (available at [plfa.github.io](plfa.github.io))

## TODOs

### Part I

- [x] Naturals: Natural numbers
- [ ] Induction: Proof by Induction
- [ ] Relations: Inductive definition of relations
- [ ] Equality: Equality and equational reasoning
- [ ] Isomorphism: Isomorphism and Embedding
- [ ] Connectives: Conjunction, disjunction, and implication
- [ ] Negation: Negation, with intuitionistic and classical logic
- [ ] Quantifiers: Universals and existentials
- [ ] Decidable: Booleans and decision procedures
- [ ] Lists: Lists and higher-order functions

### Part II

- [ ] Lambda: Introduction to Lambda Calculus
- [ ] Properties: Progress and Preservation
- [ ] DeBruijn: Intrinsically-typed de Bruijn representation
- [ ] More: Additional constructs of simply-typed lambda calculus
- [ ] Bisimulation: Relating reduction systems
- [ ] Inference: Bidirectional type inference
- [ ] Untyped: Untyped lambda calculus with full normalisation
- [ ] Confluence: Confluence of untyped lambda calculus
- [ ] BigStep: Big-step semantics of untyped lambda calculus

### Part III

- [ ] Denotational: Denotational semantics of untyped lambda calculus
- [ ] Compositional: The denotational semantics is compositional
- [ ] Soundness: Soundness of reduction with respect to denotational semantics
- [ ] Adequacy: Adequacy of denotational semantics with respect to operational semantics
- [ ] ContextualEquivalence: Denotational equality implies contextual equivalence

## Part I

### Naturals

```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

seven = suc (suc (suc ( suc (suc (suc zero)))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

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

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ =
    begin
      3 ^ 4
    ≡⟨⟩
      81
    ∎

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ : 5 ∸ 3 ≡ 2
_ =
    begin
      5 ∸ 3
    ≡⟨⟩
      4 ∸ 2
    ≡⟨⟩
      3 ∸ 1
    ≡⟨⟩
      2 ∸ 0
    ≡⟨⟩
      2
    ∎

_ : 3 ∸ 5 ≡ 0
_ =
    begin
      3 ∸ 5
    ≡⟨⟩
      2 ∸ 4
    ≡⟨⟩
      1 ∸ 3
    ≡⟨⟩
      0 ∸ 2
    ≡⟨⟩
      0
    ∎

```

```agda
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

_ : to 11 ≡ (⟨⟩ I O I I)
_ = refl

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * from b
from (b I) = (2 * from b) + 1

_ : from (⟨⟩ I O I I) ≡ 11
_ = refl
```
