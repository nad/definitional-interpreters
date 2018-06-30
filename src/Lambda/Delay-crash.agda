------------------------------------------------------------------------
-- A delay monad with the possibility of crashing
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Delay-crash where

import Equality.Propositional as E
open import Prelude

open import Maybe E.equality-with-J
open import Monad E.equality-with-J using (return; _>>=_)

open import Delay-monad
open import Delay-monad.Bisimilarity
import Delay-monad.Monad as DM

------------------------------------------------------------------------
-- Types and operations

-- The monad.

Delay-crash : Set → Size → Set
Delay-crash A i = MaybeT (λ X → Delay X i) A

Delay-crash′ : Set → Size → Set
Delay-crash′ A i = MaybeT (λ X → Delay′ X i) A

-- A lifted variant of later.

laterDC : ∀ {i A} → Delay-crash′ A i → Delay-crash A i
run (laterDC x) = later (run x)

------------------------------------------------------------------------
-- Some properties

-- Bind preserves strong bisimilarity.

infixl 5 _>>=-cong_

_>>=-cong_ :
  ∀ {i} {A B : Set}
    {x y : Delay-crash A ∞} {f g : A → Delay-crash B ∞} →
  [ i ] run x ∼ run y →
  (∀ z → [ i ] run (f z) ∼ run (g z)) →
  [ i ] run (x >>= f) ∼ run (y >>= g)
p >>=-cong q = p DM.>>=-cong [ (λ _ → run fail ∎) , q ]

-- The monad laws.

left-identity :
  ∀ {A B : Set} x (f : A → Delay-crash B ∞) →
  [ ∞ ] run (return x >>= f) ∼ run (f x)
left-identity x f =
  run (f x)  ∎

right-identity :
  ∀ {A : Set} (x : Delay-crash A ∞) →
  [ ∞ ] run (x >>= return) ∼ run x
right-identity x =
  run (x >>= return)                                ∼⟨⟩
  run x >>= maybe (return ∘ just) (return nothing)  ∼⟨ (run x ∎) DM.>>=-cong [ (λ _ → run fail ∎) , (λ x → run (return x) ∎) ] ⟩
  run x >>= return                                  ∼⟨ DM.right-identity′ _ ⟩
  run x                                             ∎

associativity :
  {A B C : Set}
  (x : Delay-crash A ∞)
  (f : A → Delay-crash B ∞) (g : B → Delay-crash C ∞) →
  run (x >>= (λ x → f x >>= g)) ∼ run (x >>= f >>= g)
associativity x f g =
  run (x >>= λ x → f x >>= g)                               ∼⟨⟩

  run x >>= maybe (λ x → run (f x >>= g)) (return nothing)  ∼⟨ (run x ∎) DM.>>=-cong [ (λ _ → run fail ∎) , (λ x → run (f x >>= g) ∎) ] ⟩

  run x >>= (λ x → maybe (run ∘ f) (return nothing) x >>=
                   maybe (run ∘ g) (return nothing))        ∼⟨ DM.associativity′ (run x) _ _ ⟩

  run x >>= maybe (run ∘ f) (return nothing)
        >>= maybe (run ∘ g) (return nothing)                ∼⟨⟩

  run (x >>= f >>= g)                                       ∎
