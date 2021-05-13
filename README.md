# solution-to-plfa

My solution to _Programming Language Foundations in Agda_ (available at [https://plfa.github.io](https://plfa.github.io/))

## Getting Started

The `template` branch contains a bare solution scaffold. You could fork this repo and use it to write your own solutions to PLFA.

### Setup

[WIP]

#### Install Haskell

We recommend to use ghcup to install Haskell and the package manager `cabal`.

Just follow the instructions on [ghcup](https://www.haskell.org/ghcup/).

After the installation, you may be able to call `cabal` from your terminal. If you are not, consider adding following statements to your shell config file ( e.g., `~/.bashrc`, `~/.zshrc`).

```
export PATH=$HOME/.ghcup/bin:$PATH
export PATH=$HOME/.cabal/bin:$PATH
```

Note that it is for mac users. If you are installing Haskell on a Windows / Linux, you should modify your environment variables accordingly.

#### Install Agda

```
cabal v2-install --lib ieee754
cabal v2-install Agda
```

After a long period of compilation, you can call `agda` in your terminal.

#### Tunning your editor

- VSCode [WIP]

## TODOs

### Part 1: Logical Foundations

- [x] [Naturals](https://plfa.github.io/Naturals/)([solution](./solution/part1/Naturals.lagda.md)): Natural numbers
- [x] [Induction](https://plfa.github.io/Induction/)([solution](./solution/part1/Induction.lagda.md)): Proof by Induction
- [ ] [Relations](https://plfa.github.io/Relations/)([solution](./solution/part1/Relations.lagda.md)): Inductive definition of relations
- [x] [Equality](https://plfa.github.io/Equality/)([solution](./solution/part1/Equality.lagda.md)): Equality and equational reasoning
- [ ] [Isomorphism](https://plfa.github.io/Isomorphism/): Isomorphism and Embedding
- [ ] [Connectives](https://plfa.github.io/Connectives/): Conjunction, disjunction, and implication
- [ ] [Negation](https://plfa.github.io/Negation/): Negation, with intuitionistic and classical logic
- [ ] [Quantifiers](https://plfa.github.io/Quantifiers/): Universals and existentials
- [ ] [Decidable](https://plfa.github.io/Decidable/): Booleans and decision procedures
- [ ] [Lists](https://plfa.github.io/Lists/): Lists and higher-order functions

### Part 2: Programming Language Foundations

- [ ] [Lambda](https://plfa.github.io/Lambda/): Introduction to Lambda Calculus
- [ ] [Properties](https://plfa.github.io/Properties/): Progress and Preservation
- [ ] [DeBruijn](https://plfa.github.io/DeBruijn/): Intrinsically-typed de Bruijn representation
- [ ] [More](https://plfa.github.io/More/): Additional constructs of simply-typed lambda calculus
- [ ] [Bisimulation](https://plfa.github.io/Bisimulation/): Relating reduction systems
- [ ] [Inference](https://plfa.github.io/Inference/): Bidirectional type inference
- [ ] [Untyped](https://plfa.github.io/Untyped/): Untyped lambda calculus with full normalisation
- [ ] [Confluence](https://plfa.github.io/Confluence/): Confluence of untyped lambda calculus
- [ ] [BigStep](https://plfa.github.io/BigStep/): Big-step semantics of untyped lambda calculus

### Part 3: Denotational Semantics

- [ ] [Denotational](https://plfa.github.io/Denotational/): Denotational semantics of untyped lambda calculus
- [ ] [Compositional](https://plfa.github.io/Compositional/): The denotational semantics is compositional
- [ ] [Soundness](https://plfa.github.io/Soundness/): Soundness of reduction with respect to denotational semantics
- [ ] [Adequacy](https://plfa.github.io/Adequacy/): Adequacy of denotational semantics with respect to operational semantics
- [ ] [ContextualEquivalence](https://plfa.github.io/ContextualEquivalence/): Denotational equality implies contextual equivalence