{-# OPTIONS --safe --without-K #-}
module Language.NJ.Sequent.WithCut.Properties where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality

open import Language.Context
open import Language.NJ.Proposition
open import Language.NJ.Sequent
open import Language.NJ.Sequent.WithCut

private
  variable
    n : ℕ
    A B C : Proposition n
    Γ Γ′ : Context (Proposition n)

cut-elim : Γ ⊢⁺ A → Γ ⊢ A
cut-elim (ax⁺ x) = {!!}
cut-elim (⇒ᴱ⁺ p p₁) = {!!}
cut-elim (⇒ᴵ⁺ p) = {!!}
cut-elim (∧ᴱₗ⁺ p) = {!!}
cut-elim (∧ᴱᵣ⁺ p) = {!!}
cut-elim (∧ᴵ⁺ p p₁) = {!!}
cut-elim (∨ᴱ⁺ p p₁ p₂) = {!!}
cut-elim (∨ᴵₗ⁺ p) = {!!}
cut-elim (∨ᴵᵣ⁺ p) = {!!}
cut-elim (⊥ᴱ⁺ p) = {!!}
cut-elim ⊤ᴵ⁺ = {!!}
cut-elim (cut refl pa pb) = cut-admissable (cut-elim pa) (cut-elim pb)
