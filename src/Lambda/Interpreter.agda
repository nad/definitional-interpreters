------------------------------------------------------------------------
-- A definitional interpreter
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Interpreter where

import Equality.Propositional as E
open import Prelude

open import Maybe E.equality-with-J
open import Monad E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Monad

open import Lambda.Syntax

open Closure Tm

------------------------------------------------------------------------
-- An interpreter monad

-- The interpreter monad.

M : ∀ {ℓ} → Size → Set ℓ → Set ℓ
M i = MaybeT (λ A → Delay A i)

-- A variant of the interpreter monad.

M′ : ∀ {ℓ} → Size → Set ℓ → Set ℓ
M′ i = MaybeT (λ A → Delay′ A i)

-- A lifted variant of later.

laterM : ∀ {i a} {A : Set a} → M′ i A → M i A
run (laterM x) = later (run x)

-- A lifted variant of weak bisimilarity.

infix 4 _≈M_

_≈M_ : ∀ {a} {A : Set a} → M ∞ A → M ∞ A → Set a
x ≈M y = run x ≈ run y

------------------------------------------------------------------------
-- The interpreter

infix 10 _∙_

mutual

  ⟦_⟧ : ∀ {i n} → Tm n → Env n → M i Value
  ⟦ con i ⟧   ρ = return (con i)
  ⟦ var x ⟧   ρ = return (index x ρ)
  ⟦ ƛ t ⟧     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧ ρ = ⟦ t₁ ⟧ ρ >>= λ v₁ →
                  ⟦ t₂ ⟧ ρ >>= λ v₂ →
                  v₁ ∙ v₂

  _∙_ : ∀ {i} → Value → Value → M i Value
  con i  ∙ v₂ = fail
  ƛ t₁ ρ ∙ v₂ = laterM (⟦ t₁ ⟧′ (v₂ ∷ ρ))

  ⟦_⟧′ : ∀ {i n} → Tm n → Env n → M′ i Value
  force (run (⟦ t ⟧′ ρ)) = run (⟦ t ⟧ ρ)

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

Ω-loops : ∀ {i} → [ i ] run (⟦ Ω ⟧ []) ∼ never
Ω-loops =
  run (⟦ Ω ⟧ [])                                     ∼⟨⟩
  run (⟦ ω · ω ⟧ [])                                 ∼⟨⟩
  run (ƛ (v0 · v0) [] ∙ ƛ (v0 · v0) [])              ∼⟨⟩
  run (laterM (⟦ v0 · v0 ⟧′ (ƛ (v0 · v0) [] ∷ [])))  ∼⟨ later (λ { .force →

      run (⟦ v0 · v0 ⟧ (ƛ (v0 · v0) [] ∷ []))             ∼⟨⟩
      run (ƛ (v0 · v0) [] ∙ ƛ (v0 · v0) [])               ∼⟨⟩
      run (⟦ Ω ⟧ [])                                      ∼⟨ Ω-loops ⟩∼
      never                                               ∎ }) ⟩∼

  never                                              ∎
  where
  v0 = var fzero