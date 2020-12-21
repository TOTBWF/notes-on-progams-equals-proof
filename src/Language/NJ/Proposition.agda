{-# OPTIONS --safe --without-K #-}
module Language.NJ.Proposition where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

import Data.Fin.Properties as Finᴾ

open import Relation.Nullary

-- An Proposition in NJ, with at most n free variables
-- FIXME Perhaps I should be more clever with variable binding...
data Proposition (n : ℕ) : Set where
  _′ : Fin n → Proposition n
  _∧_ : Proposition n → Proposition n → Proposition n
  _∨_ : Proposition n → Proposition n → Proposition n
  _⇒_ : Proposition n → Proposition n → Proposition n
  ⊥ : Proposition n
  ⊤ : Proposition n

infixr 6 _⇒_ 
infixr 5 _∨_
infixr 4 _∧_

-- Substitution in Propositions. 'A [ B / x ]' means that every occurance of 'x'
-- in 'A' is replaced by 'B'.
_[_/_] : ∀ {n} → Proposition n → Proposition n → Fin n → Proposition n
(y ′) [ B / x ] with y Finᴾ.≟ x
... | yes _ = B
... | no _ = y ′
(L ∧ R) [ B / x ] = (L [ B / x ]) ∧ (R [ B / x ])
(L ∨ R) [ B / x ] = (L [ B / x ]) ∨ (R [ B / x ])
(L ⇒ R) [ B / x ] = (L [ B / x ]) ⇒ (R [ B / x ])
⊥ [ B / x ] = ⊥
⊤ [ B / x ] = ⊤
