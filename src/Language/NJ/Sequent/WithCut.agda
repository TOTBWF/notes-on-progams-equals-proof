{-# OPTIONS --safe --without-K #-}
module Language.NJ.Sequent.WithCut where

open import Data.Nat using (ℕ)

open import Relation.Binary.PropositionalEquality

open import Language.Context
open import Language.NJ.Proposition

private
  variable
    n : ℕ
    A B C : Proposition n
    Γ Γ′ : Context (Proposition n)

-- Sequents in NJ, augmented with the cut rule.
data _⊢⁺_ (Γ : Context (Proposition n)) : Proposition n → Set where
  ax⁺ : ∀ {A} → A ∈ Γ → Γ ⊢⁺ A
  ⇒ᴱ⁺ : ∀ {A B} → Γ ⊢⁺ (A ⇒ B) → Γ ⊢⁺ A → Γ ⊢⁺ B
  ⇒ᴵ⁺ : ∀ {A B} → (Γ , A) ⊢⁺ B → Γ ⊢⁺ (A ⇒ B)
  ∧ᴱₗ⁺ : ∀ {A B} → Γ ⊢⁺ (A ∧ B) → Γ ⊢⁺ A
  ∧ᴱᵣ⁺ : ∀ {A B} → Γ ⊢⁺ (A ∧ B) → Γ ⊢⁺ B
  ∧ᴵ⁺  : ∀ {A B} → Γ ⊢⁺ A → Γ ⊢⁺ B → Γ ⊢⁺ (A ∧ B)
  ∨ᴱ⁺  : ∀ {A B C} → Γ ⊢⁺ (A ∨ B) → (Γ , A) ⊢⁺ C → (Γ , B) ⊢⁺ C → Γ ⊢⁺ C
  ∨ᴵₗ⁺ : ∀ {A B} → Γ ⊢⁺ A → Γ ⊢⁺ (A ∨ B)
  ∨ᴵᵣ⁺ : ∀ {A B} → Γ ⊢⁺ B → Γ ⊢⁺ (A ∨ B)
  ⊥ᴱ⁺  : ∀ {A} → Γ ⊢⁺ ⊥ → Γ ⊢⁺ A
  ⊤ᴵ⁺  : Γ ⊢⁺ ⊤
  -- We need to do this silly hack with the equality to make this a parameterized datatype.
  cut : ∀ {Γ′ Γ″} {A B} → (Γ′ ++ Γ″) ≡ Γ → (Γ′ ⊢⁺ A) → ((Γ′ , A) ++ Γ″) ⊢⁺ B → Γ ⊢⁺ B
