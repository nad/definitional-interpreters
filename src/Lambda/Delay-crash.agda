------------------------------------------------------------------------
-- A delay monad with the possibility of crashing
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Delay-crash where

import Conat
import Equality.Propositional as E
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Maybe E.equality-with-J as Maybe hiding (raw-monad)
open import Monad E.equality-with-J as M
  using (Raw-monad; return; _>>=_)

open import Delay-monad
open import Delay-monad.Bisimilarity
import Delay-monad.Monad as DM

------------------------------------------------------------------------
-- Types and operations

-- The monad.

Delay-crash : Set → Size → Set
Delay-crash A i = Delay (Maybe A) i

-- A crashing computation.

crash : ∀ {A i} → Delay-crash A i
crash = now nothing

-- A raw-monad instance. (This definition is turned into an actual
-- instance at the end of this module, to avoid problems with instance
-- resolution.)

private

  raw-monad′ : ∀ {i} → Raw-monad (λ A → Delay-crash A i)
  raw-monad′ {i} =
    _⇔_.to (M.⇔→raw⇔raw {F = MaybeT (λ A → Delay A i)}
              (λ _ → record { to = run; from = wrap }))
      it

  module DC {i} = Raw-monad (raw-monad′ {i = i})

------------------------------------------------------------------------
-- Some properties

-- Bind preserves strong and weak bisimilarity and the expansion
-- relation.

infixl 5 _>>=-cong_

_>>=-cong_ :
  ∀ {i k} {A B : Set}
    {x y : Delay-crash A ∞} {f g : A → Delay-crash B ∞} →
  [ i ] x ⟨ k ⟩ y →
  (∀ z → [ i ] f z ⟨ k ⟩ g z) →
  [ i ] x DC.>>= f ⟨ k ⟩ y DC.>>= g
p >>=-cong q = p DM.>>=-cong [ (λ _ → run fail ∎) , q ]

-- The monad laws.

left-identity :
  ∀ {A B : Set} x (f : A → Delay-crash B ∞) →
  [ ∞ ] DC.return x DC.>>= f ∼ f x
left-identity x f =
  f x  ∎

right-identity :
  ∀ {A : Set} (x : Delay-crash A ∞) →
  [ ∞ ] x DC.>>= DC.return ∼ x
right-identity x =
  x DC.>>= DC.return                            ∼⟨⟩
  x >>= maybe (return ∘ just) (return nothing)  ∼⟨ (x ∎) DM.>>=-cong [ (λ _ → run fail ∎) , (λ x → run (return x) ∎) ] ⟩
  x >>= return                                  ∼⟨ DM.right-identity′ _ ⟩
  x                                             ∎

associativity :
  {A B C : Set}
  (x : Delay-crash A ∞)
  (f : A → Delay-crash B ∞) (g : B → Delay-crash C ∞) →
  x DC.>>= (λ x → f x DC.>>= g) ∼ x DC.>>= f DC.>>= g
associativity x f g =
  x DC.>>= (λ x → f x DC.>>= g)                      ∼⟨⟩

  x >>= maybe (λ x → f x DC.>>= g) (return nothing)  ∼⟨ (x ∎) DM.>>=-cong [ (λ _ → run fail ∎) , (λ x → f x DC.>>= g ∎) ] ⟩

  x >>= (λ x → maybe f (return nothing) x >>=
                   maybe g (return nothing))         ∼⟨ DM.associativity′ x _ _ ⟩

  x >>= maybe f (return nothing)
        >>= maybe g (return nothing)                 ∼⟨⟩

  x DC.>>= f DC.>>= g                                ∎

-- Use of _⟨$⟩_ does not affect the number of steps in the
-- computation.

steps-⟨$⟩ :
  ∀ {i A B} {f : A → B} {x : Delay-crash A ∞} →
  Conat.[ i ] steps (f DC.⟨$⟩ x) ∼ steps x
steps-⟨$⟩ {f = f} {x} =
  steps (f DC.⟨$⟩ x)                                        Conat.≡⟨⟩∼
  steps (x DC.>>= DC.return ∘ f)                            Conat.≡⟨⟩∼
  steps (x >>= maybe (return ∘ just ∘ f) (return nothing))  Conat.∼⟨ steps-cong ((x ∎) DM.>>=-cong [ (λ _ → run fail ∎)
                                                                                                   , (λ x → return (just (f x)) ∎)
                                                                                                   ]) ⟩
  steps (x >>= return ∘ maybe (just ∘ f) nothing)           Conat.∼⟨ DM.steps-⟨$⟩ _ ⟩
  steps x                                                   Conat.∎∼

------------------------------------------------------------------------
-- The instance declaration

-- A raw-monad instance.

instance

  raw-monad : ∀ {i} → Raw-monad (λ A → Delay-crash A i)
  raw-monad = raw-monad′
