{-# OPTIONS --safe --without-K #-}
module Language.Context where

open import Level

-- A context can be thought of as a list of things.
-- We don't use sets or multisets to make the proofs easier.
-- We also use snoc lists for nicer notation.
data Context {a} (A : Set a) : Set a where
  ∅ : Context A
  _,_ : Context A → A → Context A

-- A proof that some element 'x' is part of a context 'Γ'
data _∈_ {a} {A : Set a} (x : A) : Context A → Set a where
  here : ∀ {Γ} → x ∈ (Γ , x)
  there : ∀ {y} {Γ} → x ∈ Γ → x ∈ (Γ , y)

infixl 4 _,_
infix 5 _∈_

-- Concatenation of contexts.
_++_ : ∀ {a} {A : Set a} → Context A → Context A → Context A
Γ ++ ∅ = Γ
Γ ++ (Γ′ , x) = (Γ ++ Γ′) , x

--------------------------------------------------------------------------------
-- Lemmas
--------------------------------------------------------------------------------

private
  variable
    a : Level
    A : Set a
    x y z : A
    Γ Γ′ : Context A

-- If x ∈ Γ implies that x ∈ Γ′, then this is also true for larger contexts
-- In more categorical terms, '_, x' is an endofunctor on the category of contexts.
∈-extend : (x ∈ Γ → x ∈ Γ′) → x ∈ (Γ , y) → x ∈ (Γ′ , y)
∈-extend {Γ = Γ} {Γ′ = Γ′} f here = here
∈-extend {Γ = Γ} {Γ′ = Γ′} f (there mem) = there (f mem)

-- If 'x' is a member of some context, then we can concatenate any context
-- to it and 'x' will still be a member.
∈-concat : x ∈ Γ → x ∈ Γ ++ Γ′
∈-concat {Γ′ = ∅} mem = mem
∈-concat {Γ′ = Γ′ , x} mem = there (∈-concat mem)

-- If 'x' is a member of some context, then it is also a member of that context
-- with an extra 'y' inserted at any arbitrary point.
∈-weaken : x ∈ (Γ ++ Γ′) → x ∈ (Γ , y) ++ Γ′
∈-weaken {Γ′ = ∅} mem = there mem
∈-weaken {Γ′ = Γ′ , x} here = here
∈-weaken {Γ′ = Γ′ , x} (there mem) = there (∈-weaken mem)

-- If 'x' is a member of some context, then it is also a member of that context
-- even if we permute the elements.
∈-exchange : x ∈ (Γ , y , z) ++ Γ′ → x ∈ (Γ , z , y) ++ Γ′
∈-exchange {Γ′ = ∅} here = there here
∈-exchange {Γ′ = ∅} (there here) = here
∈-exchange {Γ′ = ∅} (there (there mem)) = there (there mem)
∈-exchange {Γ′ = Γ′ , x} here = here
∈-exchange {Γ′ = Γ′ , x} (there mem) = there (∈-exchange mem)

-- Generalizes ∈-exchange. Not only can we swap the positions of two elements, but
-- we can also bring an element to the front of the context while preserving membership.
∈-reorder : x ∈ (Γ , y) ++ Γ′ → x ∈ ((Γ ++ Γ′) , y)
∈-reorder {Γ′ = ∅} mem = mem
∈-reorder {Γ′ = Γ′ , z} here = there here
∈-reorder {Γ = Γ} {Γ′ = Γ′ , z} (there mem) = ∈-exchange {Γ′ = ∅} (there (∈-reorder mem))

-- If 'x' is a member of some context with duplicates, then it is still a member of that context
-- without duplicates
∈-contract : x ∈ (Γ , y , y) ++ Γ′ → x ∈ (Γ , y) ++ Γ′
∈-contract {Γ′ = ∅} here = here
∈-contract {Γ′ = ∅} (there mem) = mem
∈-contract {Γ′ = Γ′ , x} here = here
∈-contract {Γ′ = Γ′ , x} (there mem) = there (∈-contract mem)

