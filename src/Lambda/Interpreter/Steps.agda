------------------------------------------------------------------------
-- A definitional interpreter that is instrumented with information
-- about the number of steps required to run the compiled program
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Prelude

import Lambda.Syntax

module Lambda.Interpreter.Steps
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

import Equality.Propositional as E

open import Monad E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity

open import Lambda.Delay-crash
import Lambda.Interpreter def as I

open Closure Tm

------------------------------------------------------------------------
-- The interpreter

-- A step annotation.

infix 1 √_

√_ : ∀ {A i} → Delay-crash A i → Delay-crash A i
√ x = later λ { .force → x }

-- The instrumented interpreter.

infix 10 _∙_

mutual

  ⟦_⟧ : ∀ {i n} → Tm n → Env n → Delay-crash Value i
  ⟦ var x ⟧       ρ = √ return (index x ρ)
  ⟦ lam t ⟧       ρ = √ return (lam t ρ)
  ⟦ t₁ · t₂ ⟧     ρ = do v₁ ← ⟦ t₁ ⟧ ρ
                         v₂ ← ⟦ t₂ ⟧ ρ
                         v₁ ∙ v₂
  ⟦ call f t ⟧    ρ = do v ← ⟦ t ⟧ ρ
                         lam (def f) [] ∙ v
  ⟦ con b ⟧       ρ = √ return (con b)
  ⟦ if t₁ t₂ t₃ ⟧ ρ = do v₁ ← ⟦ t₁ ⟧ ρ
                         ⟦if⟧ v₁ t₂ t₃ ρ

  _∙_ : ∀ {i} → Value → Value → Delay-crash Value i
  lam t₁ ρ ∙ v₂ = later λ { .force → ⟦ t₁ ⟧ (v₂ ∷ ρ) }
  con _    ∙ _  = crash

  ⟦if⟧ : ∀ {i n} →
         Value → Tm n → Tm n → Env n → Delay-crash Value i
  ⟦if⟧ (lam _ _)   _  _  _ = crash
  ⟦if⟧ (con true)  t₂ t₃ ρ = √ ⟦ t₂ ⟧ ρ
  ⟦if⟧ (con false) t₂ t₃ ρ = √ ⟦ t₃ ⟧ ρ

------------------------------------------------------------------------
-- The semantics given above gives the same (uninstrumented) result as
-- the one in Lambda.Interpreter

mutual

  -- The result of the instrumented interpreter is an expansion of
  -- that of the uninstrumented interpreter.

  ⟦⟧≳⟦⟧ :
    ∀ {i n} (t : Tm n) {ρ : Env n} →
    [ i ] ⟦ t ⟧ ρ ≳ I.⟦ t ⟧ ρ
  ⟦⟧≳⟦⟧ (var x)       = laterˡ (reflexive _)
  ⟦⟧≳⟦⟧ (lam t)       = laterˡ (reflexive _)
  ⟦⟧≳⟦⟧ (t₁ · t₂)     = ⟦⟧≳⟦⟧ t₁ >>=-cong λ _ →
                        ⟦⟧≳⟦⟧ t₂ >>=-cong λ _ →
                        ∙≳∙ _
  ⟦⟧≳⟦⟧ (call f t)    = ⟦⟧≳⟦⟧ t >>=-cong λ _ →
                        ∙≳∙ _
  ⟦⟧≳⟦⟧ (con b)       = laterˡ (reflexive _)
  ⟦⟧≳⟦⟧ (if t₁ t₂ t₃) = ⟦⟧≳⟦⟧ t₁ >>=-cong λ _ →
                        ⟦if⟧≳⟦if⟧ _ t₂ t₃

  ∙≳∙ :
    ∀ {i} (v₁ {v₂} : Value) →
    [ i ] v₁ ∙ v₂ ≳ v₁ I.∙ v₂
  ∙≳∙ (lam t₁ ρ) = later λ { .force → ⟦⟧≳⟦⟧ t₁ }
  ∙≳∙ (con _)    = reflexive _

  ⟦if⟧≳⟦if⟧ :
    ∀ {i n} v₁ (t₂ t₃ : Tm n) {ρ} →
    [ i ] ⟦if⟧ v₁ t₂ t₃ ρ ≳ I.⟦if⟧ v₁ t₂ t₃ ρ
  ⟦if⟧≳⟦if⟧ (lam _ _)   _  _  = reflexive _
  ⟦if⟧≳⟦if⟧ (con true)  t₂ t₃ = laterˡ (⟦⟧≳⟦⟧ t₂)
  ⟦if⟧≳⟦if⟧ (con false) t₂ t₃ = laterˡ (⟦⟧≳⟦⟧ t₃)
