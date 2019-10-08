------------------------------------------------------------------------
-- A delay monad with the possibility of crashing
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Lambda.Delay-crash where

import Equality.Propositional as E
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Prelude.Size

import Conat E.equality-with-J as Conat
open import Maybe E.equality-with-J as Maybe hiding (raw-monad)
open import Monad E.equality-with-J as M
  using (Raw-monad; return; _>>=_)

open import Delay-monad
open import Delay-monad.Bisimilarity
import Delay-monad.Monad as DM
import Delay-monad.Parallel as DP
import Delay-monad.Sequential as DS

------------------------------------------------------------------------
-- Types and operations

-- The monad.

Delay-crash : Set → Size → Set
Delay-crash A i = Delay (Maybe A) i

-- A crashing computation.

crash : ∀ {A i} → Delay-crash A i
crash = now nothing

-- Sequential composition of computations.
--
-- Note that non-termination trumps crashes, in the sense that if one
-- computation crashes and the other fails to terminate, then the
-- combination fails to terminate.

infixl 6 _⊛ˢ_

_⊛ˢ_ :
  ∀ {A B i} →
  Delay-crash (A → B) i → Delay-crash A i → Delay-crash B i
f ⊛ˢ x = M._⊛_ M.⟨$⟩ f DS.⊛ x

-- Parallel composition of computations.
--
-- Note that non-termination trumps crashes, in the sense that if one
-- computation crashes and the other fails to terminate, then the
-- combination fails to terminate.

infixl 6 _⊛ᵖ_

_⊛ᵖ_ :
  ∀ {A B i} →
  Delay-crash (A → B) i → Delay-crash A i → Delay-crash B i
f ⊛ᵖ x = M._⊛_ M.⟨$⟩ f DP.⊛ x

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

-- Sequential composition preserves strong and weak bisimilarity and
-- the expansion relation.

infixl 6 _⊛ˢ-cong_

_⊛ˢ-cong_ :
  ∀ {i k} {A B : Set}
    {f g : Delay-crash (A → B) ∞} {x y : Delay-crash A ∞} →
  [ i ] f ⟨ k ⟩ g →
  [ i ] x ⟨ k ⟩ y →
  [ i ] f ⊛ˢ x ⟨ k ⟩ g ⊛ˢ y
p ⊛ˢ-cong q = (p DM.>>=-cong λ _ → now) DS.⊛-cong q

-- Parallel composition preserves strong and weak bisimilarity and the
-- expansion relation.

infixl 6 _⊛ᵖ-cong_

_⊛ᵖ-cong_ :
  ∀ {i k} {A B : Set}
    {f g : Delay-crash (A → B) ∞} {x y : Delay-crash A ∞} →
  [ i ] f ⟨ k ⟩ g →
  [ i ] x ⟨ k ⟩ y →
  [ i ] f ⊛ᵖ x ⟨ k ⟩ g ⊛ᵖ y
p ⊛ᵖ-cong q = (p DM.>>=-cong λ _ → now) DP.⊛-cong q

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

-- Sequential composition is an expansion of parallel composition.

⊛ˢ≳⊛ᵖ :
  ∀ {i} {A B : Set} {x} (f : Delay-crash (A → B) ∞) →
  [ i ] f ⊛ˢ x ≳ f ⊛ᵖ x
⊛ˢ≳⊛ᵖ {x = x} f =
  f ⊛ˢ x                ∼⟨⟩
  M._⊛_ M.⟨$⟩ f DS.⊛ x  ≳⟨ DP.⊛≳⊛ ⟩
  M._⊛_ M.⟨$⟩ f DP.⊛ x  ∼⟨⟩
  f ⊛ᵖ x                ∎

------------------------------------------------------------------------
-- The instance declaration

-- A raw-monad instance.

instance

  raw-monad : ∀ {i} → Raw-monad (λ A → Delay-crash A i)
  raw-monad = raw-monad′
