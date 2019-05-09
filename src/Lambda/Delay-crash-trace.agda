------------------------------------------------------------------------
-- A combination of the delay monad (with the possibility of crashing)
-- and a kind of writer monad yielding colists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Lambda.Delay-crash-trace where

open import Colist as C using (Colist; []; _∷_; force)
open import Equality.Propositional as E using (_≡_; refl)
open import Prelude
open import Prelude.Size

open import Monad E.equality-with-J
  using (Raw-monad; return; _>>=_; _⟨$⟩_)

open import Delay-monad using (now; later; force)
open import Delay-monad.Bisimilarity as D using (now; later; force)

open import Lambda.Delay-crash using (Delay-crash)

------------------------------------------------------------------------
-- The monad

mutual

  -- A kind of delay monad with the possibility of crashing that also
  -- yields a trace (colist) of values.

  data Delay-crash-trace (A B : Set) (i : Size) : Set where

    -- A result is returned now.

    now : B → Delay-crash-trace A B i

    -- The computation crashes now.

    crash : Delay-crash-trace A B i

    -- A result is possibly returned later. This constructor also
    -- functions as a coinductive cons constructor for the resulting
    -- trace.

    later : A → Delay-crash-trace′ A B i → Delay-crash-trace A B i

    -- An inductive cons constructor for the resulting trace.

    tell : A → Delay-crash-trace A B i → Delay-crash-trace A B i

  record Delay-crash-trace′ (A B : Set) (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay-crash-trace A B j

open Delay-crash-trace′ public

------------------------------------------------------------------------
-- Extracting or deleting the trace

-- Returns the trace.

trace : ∀ {A B i} → Delay-crash-trace A B i → Colist A i
trace (now x)     = []
trace crash       = []
trace (later x m) = x ∷ λ { .force → trace (m .force) }
trace (tell x m)  = x ∷ λ { .force → trace m }

-- Erases the trace.

delay-crash :
  ∀ {A B i} → Delay-crash-trace A B i → Delay-crash B i
delay-crash (now x)     = now (just x)
delay-crash crash       = now nothing
delay-crash (later x m) = later λ { .force → delay-crash (m .force) }
delay-crash (tell x m)  = delay-crash m

------------------------------------------------------------------------
-- Delay-crash-trace is a raw monad

-- Bind.

bind : ∀ {i A B C} →
       Delay-crash-trace A B i →
       (B → Delay-crash-trace A C i) →
       Delay-crash-trace A C i
bind (now x)     f = f x
bind crash       f = crash
bind (later x m) f = later x λ { .force → bind (force m) f }
bind (tell x m)  f = tell x (bind m f)

-- Delay-crash-trace is a raw monad.

instance

  raw-monad : ∀ {A i} → Raw-monad (λ B → Delay-crash-trace A B i)
  Raw-monad.return raw-monad = now
  Raw-monad._>>=_  raw-monad = bind

------------------------------------------------------------------------
-- Strong bisimilarity for Delay-crash-trace

module _ {A B : Set} where

  mutual

    -- Strong bisimilarity.

    infix 4 [_]_∼_ [_]_∼′_

    data [_]_∼_ (i : Size) :
           Delay-crash-trace A B ∞ →
           Delay-crash-trace A B ∞ → Set where
      now   : ∀ {x} → [ i ] now x ∼ now x
      crash : [ i ] crash ∼ crash
      later : ∀ {v x y} →
              [ i ] force x ∼′ force y →
              [ i ] later v x ∼ later v y
      tell  : ∀ {v x y} →
              [ i ] x ∼ y →
              [ i ] tell v x ∼ tell v y

    record [_]_∼′_ (i : Size)
             (x : Delay-crash-trace A B ∞)
             (y : Delay-crash-trace A B ∞) : Set where
      coinductive
      field
        force : {j : Size< i} → [ j ] x ∼ y

  open [_]_∼′_ public

  -- Reflexivity.

  reflexive : ∀ {i} x → [ i ] x ∼ x
  reflexive (now _)     = now
  reflexive crash       = crash
  reflexive (later v x) = later λ { .force → reflexive (force x) }
  reflexive (tell v x)  = tell (reflexive x)

  -- Symmetry.

  symmetric : ∀ {i x y} → [ i ] x ∼ y → [ i ] y ∼ x
  symmetric now       = now
  symmetric crash     = crash
  symmetric (later p) = later λ { .force → symmetric (force p) }
  symmetric (tell p)  = tell (symmetric p)

  -- Transitivity.

  transitive : ∀ {i x y z} → [ i ] x ∼ y → [ i ] y ∼ z → [ i ] x ∼ z
  transitive now       now       = now
  transitive crash     crash     = crash
  transitive (later p) (later q) = later λ { .force →
                                     transitive (force p) (force q) }
  transitive (tell p)  (tell q)  = tell (transitive p q)

  -- Equational reasoning combinators.

  infix  -1 _∎
  infixr -2 step-∼ step-≡ _∼⟨⟩_

  _∎ : ∀ {i} x → [ i ] x ∼ x
  _∎ = reflexive

  step-∼ : ∀ {i} x {y z} → [ i ] y ∼ z → [ i ] x ∼ y → [ i ] x ∼ z
  step-∼ _ y∼z x∼y = transitive x∼y y∼z

  syntax step-∼ x y∼z x∼y = x ∼⟨ x∼y ⟩ y∼z

  step-≡ : ∀ {i} x {y z} → [ i ] y ∼ z → x ≡ y → [ i ] x ∼ z
  step-≡ _ y∼z refl = y∼z

  syntax step-≡ x y∼z x≡y = x ≡⟨ x≡y ⟩ y∼z

  _∼⟨⟩_ : ∀ {i} x {y} → [ i ] x ∼ y → [ i ] x ∼ y
  _ ∼⟨⟩ x∼y = x∼y

----------------------------------------------------------------------
-- Monad laws

left-identity :
  ∀ {A B C : Set} x (f : B → Delay-crash-trace A C ∞) →
  [ ∞ ] return x >>= f ∼ f x
left-identity x f = reflexive (f x)

right-identity :
  ∀ {i} {A B : Set} (x : Delay-crash-trace A B ∞) →
  [ i ] x >>= return ∼ x
right-identity (now x)     = now
right-identity crash       = crash
right-identity (later v x) = later λ { .force →
                               right-identity (force x) }
right-identity (tell v x)  = tell (right-identity x)

associativity :
  ∀ {i} {A B C D : Set} →
  (x : Delay-crash-trace A B ∞)
  (f : B → Delay-crash-trace A C ∞)
  (g : C → Delay-crash-trace A D ∞) →
  [ i ] x >>= (λ x → f x >>= g) ∼ x >>= f >>= g
associativity (now x)     f g = reflexive (f x >>= g)
associativity crash       f g = crash
associativity (later v x) f g = later λ { .force →
                                  associativity (force x) f g }
associativity (tell v x)  f g = tell (associativity x f g)

----------------------------------------------------------------------
-- Some preservation lemmas

infixl 5 _>>=-cong_

_>>=-cong_ :
  ∀ {i} {A B C : Set}
    {x y : Delay-crash-trace A B ∞}
    {f g : B → Delay-crash-trace A C ∞} →
  [ i ] x ∼ y → (∀ z → [ i ] f z ∼ g z) →
  [ i ] x >>= f ∼ y >>= g
now     >>=-cong q = q _
crash   >>=-cong q = crash
later p >>=-cong q = later λ { .force → force p >>=-cong q }
tell p  >>=-cong q = tell (p >>=-cong q)

trace-cong :
  ∀ {i} {A B : Set} {x y : Delay-crash-trace A B ∞} →
  [ i ] x ∼ y → C.[ i ] trace x ∼ trace y
trace-cong now       = []
trace-cong crash     = []
trace-cong (later p) = refl ∷ λ { .force → trace-cong (force p) }
trace-cong (tell p)  = refl ∷ λ { .force → trace-cong p }

delay-crash-cong :
  ∀ {i} {A B : Set} {x y : Delay-crash-trace A B ∞} →
  [ i ] x ∼ y → D.[ i ] delay-crash x ∼ delay-crash y
delay-crash-cong now       = now
delay-crash-cong crash     = now
delay-crash-cong (later p) = later λ { .force →
                               delay-crash-cong (force p) }
delay-crash-cong (tell p)  = delay-crash-cong p

------------------------------------------------------------------------
-- More lemmas

-- The delay-crash function commutes with _>>=_ (in a certain sense).

delay-crash->>= :
  ∀ {i A B C} (x : Delay-crash-trace A B ∞)
    {f : B → Delay-crash-trace A C ∞} →
  D.[ i ] delay-crash (x >>= f) ∼
          delay-crash x >>= delay-crash ∘ f
delay-crash->>= (now x)     = D.reflexive _
delay-crash->>= crash       = D.reflexive _
delay-crash->>= (later x m) = later λ { .force →
                                delay-crash->>= (force m) }
delay-crash->>= (tell x m)  = delay-crash->>= m

-- Use of _⟨$⟩_ does not affect the trace.

trace-⟨$⟩ :
  ∀ {i} {A B C : Set} {f : B → C}
  (x : Delay-crash-trace A B ∞) →
  C.[ i ] trace (f ⟨$⟩ x) ∼ trace x
trace-⟨$⟩ (now x)     = []
trace-⟨$⟩ crash       = []
trace-⟨$⟩ (later _ x) = refl ∷ λ { .force → trace-⟨$⟩ (force x) }
trace-⟨$⟩ (tell _ x)  = refl ∷ λ { .force → trace-⟨$⟩ x }
