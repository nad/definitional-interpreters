------------------------------------------------------------------------
-- A definitional interpreter
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

import Lambda.Syntax

module Lambda.Interpreter
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

import Equality.Propositional as E
open import Prelude

open import Maybe E.equality-with-J
open import Monad E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Monad

open import Lambda.Delay-crash

open Closure Tm

------------------------------------------------------------------------
-- The interpreter

infix 10 _∙_

mutual

  ⟦_⟧ : ∀ {i n} → Tm n → Env n → Delay-crash Value i
  ⟦ var x ⟧       ρ = return (index x ρ)
  ⟦ ƛ t ⟧         ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧     ρ = do v₁ ← ⟦ t₁ ⟧ ρ
                         v₂ ← ⟦ t₂ ⟧ ρ
                         v₁ ∙ v₂
  ⟦ call f t ⟧    ρ = do v ← ⟦ t ⟧ ρ
                         ƛ (def f) [] ∙ v
  ⟦ con b ⟧       ρ = return (con b)
  ⟦ if t₁ t₂ t₃ ⟧ ρ = do v₁ ← ⟦ t₁ ⟧ ρ
                         ⟦if⟧ v₁ t₂ t₃ ρ

  _∙_ : ∀ {i} → Value → Value → Delay-crash Value i
  ƛ t₁ ρ ∙ v₂ = laterDC (⟦ t₁ ⟧′ (v₂ ∷ ρ))
  con _  ∙ _  = fail

  ⟦if⟧ : ∀ {i n} → Value → Tm n → Tm n → Env n → Delay-crash Value i
  ⟦if⟧ (ƛ _ _)     _  _  _ = fail
  ⟦if⟧ (con true)  t₂ t₃ ρ = ⟦ t₂ ⟧ ρ
  ⟦if⟧ (con false) t₂ t₃ ρ = ⟦ t₃ ⟧ ρ

  ⟦_⟧′ : ∀ {i n} → Tm n → Env n → Delay-crash′ Value i
  force (run (⟦ t ⟧′ ρ)) = run (⟦ t ⟧ ρ)

------------------------------------------------------------------------
-- An example

-- The semantics of Ω is the non-terminating computation never.

Ω-loops : ∀ {i} → [ i ] run (⟦ Ω ⟧ []) ∼ never
Ω-loops =
  run (⟦ Ω ⟧ [])                                  ∼⟨⟩
  run (⟦ ω · ω ⟧ [])                              ∼⟨⟩
  run (ƛ ω-body [] ∙ ƛ ω-body [])                 ∼⟨⟩
  run (laterDC (⟦ ω-body ⟧′ (ƛ ω-body [] ∷ [])))  ∼⟨ later (λ { .force →

      run (⟦ ω-body ⟧ (ƛ ω-body [] ∷ []))              ∼⟨⟩
      run (ƛ ω-body [] ∙ ƛ ω-body [])                  ∼⟨⟩
      run (⟦ Ω ⟧ [])                                   ∼⟨ Ω-loops ⟩∼
      never                                            ∎ }) ⟩∼

  never                                           ∎
