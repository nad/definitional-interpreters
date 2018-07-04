------------------------------------------------------------------------
-- A combination of the delay monad (with the possibility of crashing)
-- and a kind of writer monad yielding colists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Delay-crash-colist where

open import Colist as C using (Colist; []; _∷_; force)
open import Equality.Propositional as E using (_≡_; refl)
open import Prelude

open import Maybe E.equality-with-J using (maybe; run)
open import Monad E.equality-with-J
  using (Raw-monad; return; _>>=_; _⟨$⟩_)

open import Delay-monad using (now; later; force)
open import Delay-monad.Bisimilarity as D using (now; later; force)
import Delay-monad.Monad

open import Lambda.Delay-crash using (Delay-crash; Delay-crash′)

------------------------------------------------------------------------
-- The monad

mutual

  -- A kind of delay monad with the possibility of crashing that also
  -- yields a colist of values.

  data Delay-crash-colist (A B : Set) (i : Size) : Set where

    -- A result is returned now.

    now : B → Delay-crash-colist A B i

    -- The computation crashes now.

    crash : Delay-crash-colist A B i

    -- A result is possibly returned later. This constructor also
    -- functions as a coinductive cons constructor for the resulting
    -- colist.

    later : A → Delay-crash-colist′ A B i → Delay-crash-colist A B i

    -- An inductive cons constructor for the resulting colist.

    tell : A → Delay-crash-colist A B i → Delay-crash-colist A B i

  record Delay-crash-colist′ (A B : Set) (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay-crash-colist A B j

open Delay-crash-colist′ public

------------------------------------------------------------------------
-- Extracting or deleting the colist

-- Returns the colist.

colist : ∀ {A B i} → Delay-crash-colist A B i → Colist A i
colist (now x)     = []
colist crash       = []
colist (later x m) = x ∷ λ { .force → colist (force m) }
colist (tell x m)  = x ∷ λ { .force → colist m }

mutual

  -- Erases the colist.

  delay-crash :
    ∀ {A B i} → Delay-crash-colist A B i → Delay-crash B i
  delay-crash (now x)     .run = now (just x)
  delay-crash crash       .run = now nothing
  delay-crash (later x m) .run = later (delay-crash′ m .run)
  delay-crash (tell x m)  .run = delay-crash m .run

  delay-crash′ :
    ∀ {A B i} → Delay-crash-colist′ A B i → Delay-crash′ B i
  delay-crash′ m .run .force = delay-crash (m .force) .run

------------------------------------------------------------------------
-- Delay-crash-colist is a raw monad

-- Bind.

bind : ∀ {i A B C} →
       Delay-crash-colist A B i →
       (B → Delay-crash-colist A C i) →
       Delay-crash-colist A C i
bind (now x)     f = f x
bind crash       f = crash
bind (later x m) f = later x λ { .force → bind (force m) f }
bind (tell x m)  f = tell x (bind m f)

-- Delay-crash-colist is a raw monad.

instance

  raw-monad : ∀ {A i} → Raw-monad (λ B → Delay-crash-colist A B i)
  Raw-monad.return raw-monad = now
  Raw-monad._>>=_  raw-monad = bind

------------------------------------------------------------------------
-- Strong bisimilarity for Delay-crash-colist

module _ {A B : Set} where

  mutual

    -- Strong bisimilarity.

    infix 4 [_]_∼_ [_]_∼′_

    data [_]_∼_ (i : Size) :
           Delay-crash-colist A B ∞ →
           Delay-crash-colist A B ∞ → Set where
      now   : ∀ {x} → [ i ] now x ∼ now x
      crash : [ i ] crash ∼ crash
      later : ∀ {v x y} →
              [ i ] force x ∼′ force y →
              [ i ] later v x ∼ later v y
      tell  : ∀ {v x y} →
              [ i ] x ∼ y →
              [ i ] tell v x ∼ tell v y

    record [_]_∼′_ (i : Size)
             (x : Delay-crash-colist A B ∞)
             (y : Delay-crash-colist A B ∞) : Set where
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
  ∀ {A B C : Set} x (f : B → Delay-crash-colist A C ∞) →
  [ ∞ ] return x >>= f ∼ f x
left-identity x f = reflexive (f x)

right-identity :
  ∀ {A B : Set} (x : Delay-crash-colist A B ∞) →
  [ ∞ ] x >>= return ∼ x
right-identity (now x)     = now
right-identity crash       = crash
right-identity (later v x) = later λ { .force →
                               right-identity (force x) }
right-identity (tell v x)  = tell (right-identity x)

associativity :
  ∀ {A B C D : Set} →
  (x : Delay-crash-colist A B ∞)
  (f : B → Delay-crash-colist A C ∞)
  (g : C → Delay-crash-colist A D ∞) →
  [ ∞ ] x >>= (λ x → f x >>= g) ∼ x >>= f >>= g
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
    {x y : Delay-crash-colist A B ∞}
    {f g : B → Delay-crash-colist A C ∞} →
  [ i ] x ∼ y → (∀ z → [ i ] f z ∼ g z) →
  [ i ] x >>= f ∼ y >>= g
now     >>=-cong q = q _
crash   >>=-cong q = crash
later p >>=-cong q = later λ { .force → force p >>=-cong q }
tell p  >>=-cong q = tell (p >>=-cong q)

colist-cong :
  ∀ {i} {A B : Set} {x y : Delay-crash-colist A B ∞} →
  [ i ] x ∼ y → C.[ i ] colist x ∼ colist y
colist-cong now       = []
colist-cong crash     = []
colist-cong (later p) = refl ∷ λ { .force → colist-cong (force p) }
colist-cong (tell p)  = refl ∷ λ { .force → colist-cong p }

delay-crash-cong :
  ∀ {i} {A B : Set} {x y : Delay-crash-colist A B ∞} →
  [ i ] x ∼ y → D.[ i ] run (delay-crash x) ∼ run (delay-crash y)
delay-crash-cong now       = now
delay-crash-cong crash     = now
delay-crash-cong (later p) = later λ { .force →
                               delay-crash-cong (force p) }
delay-crash-cong (tell p)  = delay-crash-cong p

------------------------------------------------------------------------
-- More lemmas

-- The delay-crash function commutes with _>>=_ (in a certain sense).

delay-crash->>= :
  ∀ {i A B C} (x : Delay-crash-colist A B ∞)
    {f : B → Delay-crash-colist A C ∞} →
  D.[ i ] run (delay-crash (x >>= f)) ∼
          run (delay-crash x >>= delay-crash ∘ f)
delay-crash->>= (now x)     = D.reflexive _
delay-crash->>= crash       = D.reflexive _
delay-crash->>= (later x m) = later λ { .force →
                                delay-crash->>= (force m) }
delay-crash->>= (tell x m)  = delay-crash->>= m

-- Use of _⟨$⟩_ does not affect the colist.

colist-⟨$⟩ :
  ∀ {i} {A B C : Set} {f : B → C}
  (x : Delay-crash-colist A B ∞) →
  C.[ i ] colist (f ⟨$⟩ x) ∼ colist x
colist-⟨$⟩ (now x)     = []
colist-⟨$⟩ crash       = []
colist-⟨$⟩ (later _ x) = refl ∷ λ { .force → colist-⟨$⟩ (force x) }
colist-⟨$⟩ (tell _ x)  = refl ∷ λ { .force → colist-⟨$⟩ x }
