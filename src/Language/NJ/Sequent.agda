{-# OPTIONS --safe --without-K #-}
module Language.NJ.Sequent where

open import Data.Nat using (ℕ)

open import Language.Context
open import Language.NJ.Proposition

private
  variable
    n : ℕ
    A B C : Proposition n
    Γ Γ′ : Context (Proposition n)

data _⊢_ (Γ : Context (Proposition n)) : Proposition n → Set where
  ax : ∀ {A} → A ∈ Γ → Γ ⊢ A
  ⇒ᴱ : ∀ {A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
  ⇒ᴵ : ∀ {A B} → (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
  ∧ᴱₗ : ∀ {A B} → Γ ⊢ (A ∧ B) → Γ ⊢ A
  ∧ᴱᵣ : ∀ {A B} → Γ ⊢ (A ∧ B) → Γ ⊢ B
  ∧ᴵ  : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A ∧ B)
  ∨ᴱ  : ∀ {A B C} → Γ ⊢ (A ∨ B) → (Γ , A) ⊢ C → (Γ , B) ⊢ C → Γ ⊢ C
  ∨ᴵₗ : ∀ {A B} → Γ ⊢ A → Γ ⊢ (A ∨ B)
  ∨ᴵᵣ : ∀ {A B} → Γ ⊢ B → Γ ⊢ (A ∨ B)
  ⊥ᴱ  : ∀ {A} → Γ ⊢ ⊥ → Γ ⊢ A
  ⊤ᴵ  : Γ ⊢ ⊤

-- If a rule is purely structural, then it is admissable.
-- That is to say, we can lift lemmas about membership to admissable rules.
structural : (∀ {B} → B ∈ Γ → B ∈ Γ′) → Γ ⊢ A → Γ′ ⊢ A
structural mem-implies (ax mem) = ax (mem-implies mem)
structural mem-implies (⇒ᴱ p q) = ⇒ᴱ (structural mem-implies p) (structural mem-implies q)
structural mem-implies (⇒ᴵ {A} p) = ⇒ᴵ (structural (∈-extend mem-implies) p)
structural mem-implies (∧ᴱₗ p) = ∧ᴱₗ (structural mem-implies p)
structural mem-implies (∧ᴱᵣ p) = ∧ᴱᵣ (structural mem-implies p)
structural mem-implies (∧ᴵ p q) = ∧ᴵ (structural mem-implies p) (structural mem-implies q)
structural mem-implies (∨ᴱ p q u) = ∨ᴱ (structural mem-implies p) (structural (∈-extend mem-implies) q) (structural (∈-extend mem-implies) u)
structural mem-implies (∨ᴵₗ p) = ∨ᴵₗ (structural mem-implies p)
structural mem-implies (∨ᴵᵣ p) = ∨ᴵᵣ (structural mem-implies p)
structural mem-implies (⊥ᴱ p) = ⊥ᴱ (structural mem-implies p)
structural mem-implies ⊤ᴵ = ⊤ᴵ

-- If we have a proof of 'A' in some context 'Γ', and a proof of 'B'
-- that relies on 'A' and also provides the context 'Γ', then we can
-- produce a proof of 'B' without assuming 'A'.
cut-admissable : Γ ⊢ A → ((Γ , A) ++ Γ′) ⊢ B → (Γ ++ Γ′) ⊢ B
cut-admissable pa pb = ⇒ᴱ (⇒ᴵ (structural ∈-reorder pb)) (structural ∈-concat pa)
