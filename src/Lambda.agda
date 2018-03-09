------------------------------------------------------------------------
-- A small language with lambdas, general recursion, natural numbers,
-- references and IO
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Fin equality-with-J
open import Monad equality-with-J
open import Monad.Reader equality-with-J
open import Monad.State equality-with-J
open import Nat equality-with-J as Nat hiding (pred)
open import Vec equality-with-J as Vec hiding (_[_≔_])

------------------------------------------------------------------------
-- Syntax

-- Variables.

Var : Set
Var = ℕ

-- Expressions.

data Exp : Set where
  -- Lambdas.
  var : Var → Exp
  lam : Var → Exp → Exp
  app : Exp → Exp → Exp

  -- General recursion.
  fix : Var → Var → Exp → Exp → Exp

  -- Natural numbers.
  zero             : Exp
  suc pred         : Exp → Exp
  if_=0-then_else_ : Exp → Exp → Exp → Exp

  -- References.
  ref : Exp → Exp        -- Allocate a new reference with the given
                         -- initial value.
  !_  : Exp → Exp        -- Dereference a reference.
  _≔_ : Exp → Exp → Exp  -- Assign a value to a reference.

  -- IO.
  read  : Var → Exp → Exp  -- Read input (natural numbers) into the given
                           -- variable and continue executing.
  write : Exp → Exp        -- Write output (only natural numbers).

-- References.

Ref : Set
Ref = ℕ

------------------------------------------------------------------------
-- Values and environments

mutual

  -- Values.

  data Value : Set where
    unit    : Value
    nat     : ℕ → Value
    ref     : Ref → Value
    closure : Var → Exp → Env → Value

  -- Environments.

  Env : Set
  Env = ℕ → Maybe Value

-- An empty environment.

ε : Env
ε = λ _ → nothing

-- Extends an environment with a new binding.

_[_≔_] : Env → ℕ → Value → Env
(ρ [ x ≔ v ]) y = if x ≟ y then just v else ρ y

------------------------------------------------------------------------
-- Heaps

-- Heaps.

record Heap : Set where
  field
    size     : ℕ
    contents : Vec Value size

open Heap public

-- An empty heap.

∅ : Heap
size     ∅ = 0
contents ∅ = _

-- Extends a heap with a new binding. The freshly allocated reference
-- is returned along with the new heap.

extend : Heap → Value → Heap × Ref
extend σ v =
    record { size     = 1 + size σ
           ; contents = v , contents σ
           }
  , size σ

-- Dereferences a reference.

dereference : Heap → Ref → Maybe Value
dereference σ r =
  ⊎-map _
        (λ r → index r (contents σ))
        (from-ℕ r)

-- Updates the value pointed to by a reference. (Returns nothing if
-- the reference is unallocated.)

update : Heap → Ref → Value → Maybe Heap
update σ r v =
  ⊎-map _
        (λ r → record σ { contents = contents σ Vec.[ r ≔ v ]})
        (from-ℕ r)

------------------------------------------------------------------------
-- The result type

-- The result type uses resumptions to handle IO, following Nakata and
-- Uustalu ("Resumptions, Weak Bisimilarity and Big-Step Semantics for
-- While with Interactive I/O: An Exercise in Mixed
-- Induction-Coinduction").

mutual

  data Result (A : Set) (i : Size) : Set where
    now   : A → Result A i
    crash : Result A i
    read  : (ℕ → Result′ A i) → Result A i
    write : ℕ → Result′ A i → Result A i
    later : Result′ A i → Result A i

  record Result′ (A : Set) (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Result A j

open Result′ public

-- Removes a later constructor, if possible.

drop-later : ∀ {i} {j : Size< i} {A} → Result A i → Result A j
drop-later r@(now _)     = r
drop-later r@crash       = r
drop-later r@(read _)    = r
drop-later r@(write _ _) = r
drop-later (later r)     = force r

-- Strong and weak bisimilarity and expansion for Result ∞.

data Not-strong-kind : Set where
  weak expansion : Not-strong-kind

data Kind : Set where
  strong : Kind
  other  : Not-strong-kind → Kind

mutual

  infix 4 [_]_⟨_⟩_ [_]_∼_ [_]_≳_ [_]_≈_

  [_]_∼_ : {A : Set} → Size → Result A ∞ → Result A ∞ → Set
  [_]_∼_ = [_]_⟨ strong ⟩_

  [_]_≳_ : {A : Set} → Size → Result A ∞ → Result A ∞ → Set
  [_]_≳_ = [_]_⟨ other expansion ⟩_

  [_]_≈_ : {A : Set} → Size → Result A ∞ → Result A ∞ → Set
  [_]_≈_ = [_]_⟨ other weak ⟩_

  data [_]_⟨_⟩_
         {A : Set} (i : Size) :
         Result A ∞ → Kind → Result A ∞ → Set where
    now    : ∀ {k x} → [ i ] now x ⟨ k ⟩ now x
    crash  : ∀ {k} → [ i ] crash ⟨ k ⟩ crash
    read   : ∀ {k f₁ f₂} →
             (∀ n → [ i ] force (f₁ n) ⟨ k ⟩′ force (f₂ n)) →
             [ i ] read f₁ ⟨ k ⟩ read f₂
    write  : ∀ {k n r₁ r₂} →
             [ i ] force r₁ ⟨ k ⟩′ force r₂ →
             [ i ] write n r₁ ⟨ k ⟩ write n r₂
    later  : ∀ {k r₁ r₂} →
             [ i ] force r₁ ⟨ k ⟩′ force r₂ →
             [ i ] later r₁ ⟨ k ⟩ later r₂
    laterˡ : ∀ {k r₁ r₂} →
             [ i ] force r₁ ⟨ other k ⟩ r₂ →
             [ i ] later r₁ ⟨ other k ⟩ r₂
    laterʳ : ∀ {r₁ r₂} →
             [ i ] r₁ ≈ force r₂ →
             [ i ] r₁ ≈ later r₂

  record [_]_⟨_⟩′_
           {A : Set} (i : Size)
           (r₁ : Result A ∞) (k : Kind) (r₂ : Result A ∞) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] r₁ ⟨ k ⟩ r₂

open [_]_⟨_⟩′_ public

-- Strong bisimilarity is contained in the other relations (and
-- itself).

∼→ : ∀ {k i A} {r₁ r₂ : Result A ∞} →
     [ i ] r₁ ∼ r₂ → [ i ] r₁ ⟨ k ⟩ r₂
∼→ now       = now
∼→ crash     = crash
∼→ (read p)  = read λ { n .force → ∼→ (force (p n)) }
∼→ (write p) = write λ { .force → ∼→ (force p) }
∼→ (later p) = later λ { .force → ∼→ (force p) }

-- Expansion is contained in weak bisimilarity (and expansion).

≳→ : ∀ {k i A} {r₁ r₂ : Result A ∞} →
     [ i ] r₁ ≳ r₂ → [ i ] r₁ ⟨ other k ⟩ r₂
≳→ now        = now
≳→ crash      = crash
≳→ (read p)   = read λ { n .force → ≳→ (force (p n)) }
≳→ (write p)  = write λ { .force → ≳→ (force p) }
≳→ (later p)  = later λ { .force → ≳→ (force p) }
≳→ (laterˡ p) = laterˡ (≳→ p)

-- Later constructors can sometimes be removed.

laterʳ⁻¹ : ∀ {k i} {j : Size< i} {A} {r₁ : Result A ∞} {r₂} →
           [ i ] r₁ ⟨ other k ⟩ later r₂ →
           [ j ] r₁ ⟨ other k ⟩ force r₂
laterʳ⁻¹ (later  p) = laterˡ (force p)
laterʳ⁻¹ (laterʳ p) = p
laterʳ⁻¹ (laterˡ p) = laterˡ (laterʳ⁻¹ p)

laterˡ⁻¹ : ∀ {i} {j : Size< i} {A r₁} {r₂ : Result A ∞} →
           [ i ] later r₁ ≈ r₂ →
           [ j ] force r₁ ≈ r₂
laterˡ⁻¹ (later  p) = laterʳ (force p)
laterˡ⁻¹ (laterʳ p) = laterʳ (laterˡ⁻¹ p)
laterˡ⁻¹ (laterˡ p) = p

later⁻¹ : ∀ {i} {j : Size< i} {A} {r₁ r₂ : Result′ A ∞} →
          [ i ] later r₁ ≈ later r₂ →
          [ j ] force r₁ ≈ force r₂
later⁻¹ (later  p) = force p
later⁻¹ (laterʳ p) = laterˡ⁻¹ p
later⁻¹ (laterˡ p) = laterʳ⁻¹ p

-- All three relations are reflexive.

reflexive : ∀ {k i A} (r : Result A ∞) → [ i ] r ⟨ k ⟩ r
reflexive (now _)     = now
reflexive crash       = crash
reflexive (read r)    = read λ { n .force → reflexive (force (r n)) }
reflexive (write n r) = write λ { .force → reflexive (force r) }
reflexive (later r)   = later λ { .force → reflexive (force r) }

-- Strong and weak bisimilarity are symmetric.

symmetric-∼ :
  ∀ {i A} {r₁ r₂ : Result A ∞} →
  [ i ] r₁ ∼ r₂ → [ i ] r₂ ∼ r₁
symmetric-∼ now        = now
symmetric-∼ crash      = crash
symmetric-∼ (read p)   = read λ { n .force → symmetric-∼ (force (p n)) }
symmetric-∼ (write p)  = write λ { .force → symmetric-∼ (force p) }
symmetric-∼ (later p)  = later λ { .force → symmetric-∼ (force p) }

symmetric-≈ :
  ∀ {i A} {r₁ r₂ : Result A ∞} →
  [ i ] r₁ ≈ r₂ → [ i ] r₂ ≈ r₁
symmetric-≈ now        = now
symmetric-≈ crash      = crash
symmetric-≈ (read p)   = read λ { n .force → symmetric-≈ (force (p n)) }
symmetric-≈ (write p)  = write λ { .force → symmetric-≈ (force p) }
symmetric-≈ (later p)  = later λ { .force → symmetric-≈ (force p) }
symmetric-≈ (laterˡ p) = laterʳ (symmetric-≈ p)
symmetric-≈ (laterʳ p) = laterˡ (symmetric-≈ p)

-- Several variants of transitivity.

transitive-∼ :
  ∀ {i A} {r₁ r₂ r₃ : Result A ∞} →
  [ i ] r₁ ∼ r₂ → [ i ] r₂ ∼ r₃ → [ i ] r₁ ∼ r₃
transitive-∼ now       now       = now
transitive-∼ crash     crash     = crash
transitive-∼ (read p)  (read q)  = read λ { n .force →
                                     transitive-∼ (force (p n)) (force (q n)) }
transitive-∼ (write p) (write q) = write λ { .force →
                                     transitive-∼ (force p) (force q) }
transitive-∼ (later p) (later q) = later λ { .force →
                                     transitive-∼ (force p) (force q) }

transitive-∼ˡ :
  ∀ {k i A} {r₁ r₂ r₃ : Result A ∞} →
  [ ∞ ] r₁ ∼ r₂ → [ i ] r₂ ⟨ k ⟩ r₃ → [ i ] r₁ ⟨ k ⟩ r₃
transitive-∼ˡ now       now        = now
transitive-∼ˡ crash     crash      = crash
transitive-∼ˡ (read p)  (read q)   = read λ { n .force →
                                       transitive-∼ˡ (force (p n)) (force (q n)) }
transitive-∼ˡ (write p) (write q)  = write λ { .force →
                                       transitive-∼ˡ (force p) (force q) }
transitive-∼ˡ (later p) (later q)  = later λ { .force →
                                       transitive-∼ˡ (force p) (force q) }
transitive-∼ˡ (later p) (laterˡ q) = laterˡ (transitive-∼ˡ (force p) q)
transitive-∼ˡ p         (laterʳ q) = laterʳ (transitive-∼ˡ p q)

transitive-∼ʳ :
  ∀ {k i A} {r₁ r₂ r₃ : Result A ∞} →
  [ i ] r₁ ⟨ k ⟩ r₂ → [ ∞ ] r₂ ∼ r₃ → [ i ] r₁ ⟨ k ⟩ r₃
transitive-∼ʳ now        now       = now
transitive-∼ʳ crash      crash     = crash
transitive-∼ʳ (read p)   (read q)  = read λ { n .force →
                                       transitive-∼ʳ (force (p n)) (force (q n)) }
transitive-∼ʳ (write p)  (write q) = write λ { .force →
                                       transitive-∼ʳ (force p) (force q) }
transitive-∼ʳ (later p)  (later q) = later λ { .force →
                                       transitive-∼ʳ (force p) (force q) }
transitive-∼ʳ (laterˡ p) q         = laterˡ (transitive-∼ʳ p q)
transitive-∼ʳ (laterʳ p) (later q) = laterʳ (transitive-∼ʳ p (force q))

transitive-≳ :
  ∀ {k i A} {r₁ r₂ r₃ : Result A ∞} →
  [ ∞ ] r₁ ≳ r₂ → [ i ] r₂ ⟨ other k ⟩ r₃ → [ i ] r₁ ⟨ other k ⟩ r₃
transitive-≳ now        now        = now
transitive-≳ crash      crash      = crash
transitive-≳ (read p)   (read q)   = read λ { n .force →
                                       transitive-≳ (force (p n)) (force (q n)) }
transitive-≳ (write p)  (write q)  = write λ { .force →
                                       transitive-≳ (force p) (force q) }
transitive-≳ (later p)  (later q)  = later λ { .force →
                                       transitive-≳ (force p) (force q) }
transitive-≳ (later p)  (laterˡ q) = laterˡ (transitive-≳ (force p) q)
transitive-≳ (laterˡ p) q          = laterˡ (transitive-≳ p q)
transitive-≳ p          (laterʳ q) = laterʳ (transitive-≳ p q)

transitive-≈-now :
  ∀ {i A x} {r₂ r₃ : Result A ∞} →
  let r₁ = now x in
  [ i ] r₁ ≈ r₂ → [ ∞ ] r₂ ≈ r₃ → [ i ] r₁ ≈ r₃
transitive-≈-now now        now        = now
transitive-≈-now (laterʳ p) q          = transitive-≈-now p (laterˡ⁻¹ q)
transitive-≈-now p          (laterʳ q) = laterʳ (transitive-≈-now p q)

transitive-≈-crash :
  ∀ {i A} {r₂ r₃ : Result A ∞} →
  let r₁ = crash in
  [ i ] r₁ ≈ r₂ → [ ∞ ] r₂ ≈ r₃ → [ i ] r₁ ≈ r₃
transitive-≈-crash crash      crash      = crash
transitive-≈-crash (laterʳ p) q          = transitive-≈-crash p (laterˡ⁻¹ q)
transitive-≈-crash p          (laterʳ q) = laterʳ (transitive-≈-crash p q)

mutual

  transitive-≈-read :
    ∀ {i A r₁} {r₂ r₃ : Result A ∞} →
    let r₁ = read r₁ in
    [ ∞ ] r₁ ≈ r₂ → [ ∞ ] r₂ ≈ r₃ → [ i ] r₁ ≈ r₃
  transitive-≈-read (read p)   (read q)   = read λ { n .force →
                                            transitive-≈ (force (p n)) (force (q n)) }
  transitive-≈-read (laterʳ p) q          = transitive-≈-read p (laterˡ⁻¹ q)
  transitive-≈-read p          (laterʳ q) = laterʳ (transitive-≈-read p q)

  transitive-≈-write :
    ∀ {i n A r₁} {r₂ r₃ : Result A ∞} →
    let r₁ = write n r₁ in
    [ ∞ ] r₁ ≈ r₂ → [ ∞ ] r₂ ≈ r₃ → [ i ] r₁ ≈ r₃
  transitive-≈-write (write p)  (write q)  = write λ { .force →
                                             transitive-≈ (force p) (force q) }
  transitive-≈-write (laterʳ p) q          = transitive-≈-write p (laterˡ⁻¹ q)
  transitive-≈-write p          (laterʳ q) = laterʳ (transitive-≈-write p q)

  transitive-≈-later :
    ∀ {i A r₁} {r₂ r₃ : Result A ∞} →
    let r₁ = later r₁ in
    [ ∞ ] r₁ ≈ r₂ → [ ∞ ] r₂ ≈ r₃ → [ i ] r₁ ≈ r₃
  transitive-≈-later p          (laterʳ q) = laterʳ (transitive-≈-later p q)
  transitive-≈-later p          (later q)  = later λ { .force →
                                             transitive-≈ (later⁻¹ p) (force q) }
  transitive-≈-later (later p)  (laterˡ q) = laterˡ (transitive-≈ (force p) q)
  transitive-≈-later (laterʳ p) (laterˡ q) = transitive-≈-later p q
  transitive-≈-later (laterˡ p) q          = laterˡ (transitive-≈ p q)

  transitive-≈ :
    ∀ {i A} {r₁ r₂ r₃ : Result A ∞} →
    [ ∞ ] r₁ ≈ r₂ → [ ∞ ] r₂ ≈ r₃ → [ i ] r₁ ≈ r₃
  transitive-≈ {r₁ = now _}     p q = transitive-≈-now   p q
  transitive-≈ {r₁ = crash}     p q = transitive-≈-crash p q
  transitive-≈ {r₁ = read _}    p q = transitive-≈-read p q
  transitive-≈ {r₁ = write _ _} p q = transitive-≈-write p q
  transitive-≈ {r₁ = later _}   p q = transitive-≈-later p q

-- Equational reasoning combinators.

module Result-reasoning {i A} where

  infix  -1 finally-∼ _□
  infixr -2 step-∼ step-∼ˡ step-∼ʳ step-≳ step-≈ _≳⟨⟩_ _≡⟨⟩∼_

  _□ : ∀ {k} (r : Result A ∞) → [ i ] r ⟨ k ⟩ r
  _□ = reflexive

  step-∼ : ∀ (r₁ : Result A ∞) {r₂ r₃} →
           [ i ] r₂ ∼ r₃ → [ i ] r₁ ∼ r₂ → [ i ] r₁ ∼ r₃
  step-∼ _ r₂∼r₃ r₁∼r₂ = transitive-∼ r₁∼r₂ r₂∼r₃

  syntax step-∼ r₁ r₂∼r₃ r₁∼r₂ = r₁ ∼⟨ r₁∼r₂ ⟩ r₂∼r₃

  step-∼ˡ : ∀ {k} (r₁ : Result A ∞) {r₂ r₃} →
            [ i ] r₂ ⟨ k ⟩ r₃ → [ ∞ ] r₁ ∼ r₂ → [ i ] r₁ ⟨ k ⟩ r₃
  step-∼ˡ _ r₂≈r₃ r₁∼r₂ = transitive-∼ˡ r₁∼r₂ r₂≈r₃

  syntax step-∼ˡ r₁ r₂≈r₃ r₁∼r₂ = r₁ ∼⟨ r₁∼r₂ ⟩≈ r₂≈r₃

  step-∼ʳ : ∀ {k} (r₁ : Result A ∞) {r₂ r₃} →
            [ ∞ ] r₂ ∼ r₃ → [ i ] r₁ ⟨ k ⟩ r₂ → [ i ] r₁ ⟨ k ⟩ r₃
  step-∼ʳ _ r₂∼r₃ r₁≈r₂ = transitive-∼ʳ r₁≈r₂ r₂∼r₃

  syntax step-∼ʳ r₁ r₂∼r₃ r₁≈r₂ = r₁ ≈⟨ r₁≈r₂ ⟩∼ r₂∼r₃

  step-≳ : ∀ {k} (r₁ : Result A ∞) {r₂ r₃} →
           [ i ] r₂ ⟨ other k ⟩ r₃ → [ ∞ ] r₁ ≳ r₂ →
           [ i ] r₁ ⟨ other k ⟩ r₃
  step-≳ _ r₂≈r₃ r₁≳r₂ = transitive-≳ r₁≳r₂ r₂≈r₃

  syntax step-≳ r₁ r₂≈r₃ r₁≳r₂ = r₁ ≳⟨ r₁≳r₂ ⟩ r₂≈r₃

  step-≈ : ∀ (r₁ : Result A ∞) {r₂ r₃} →
           [ ∞ ] r₂ ≈ r₃ → [ ∞ ] r₁ ≈ r₂ → [ i ] r₁ ≈ r₃
  step-≈ _ r₂≈r₃ r₁≈r₂ = transitive-≈ r₁≈r₂ r₂≈r₃

  syntax step-≈ r₁ r₂≈r₃ r₁≈r₂ = r₁ ≈⟨ r₁≈r₂ ⟩ r₂≈r₃

  _≳⟨⟩_ : ∀ {k} (r₁ : Result A ∞) {r₂} →
          [ i ] drop-later r₁ ⟨ other k ⟩ r₂ → [ i ] r₁ ⟨ other k ⟩ r₂
  now _     ≳⟨⟩ p = p
  crash     ≳⟨⟩ p = p
  read _    ≳⟨⟩ p = p
  write _ _ ≳⟨⟩ p = p
  later _   ≳⟨⟩ p = laterˡ p

  _≡⟨⟩∼_ : ∀ {k} (r₁ : Result A ∞) {r₂} →
           [ i ] r₁ ⟨ k ⟩ r₂ → [ i ] r₁ ⟨ k ⟩ r₂
  _ ≡⟨⟩∼ r₁≈r₂ = r₁≈r₂

  finally-∼ : ∀ {k} (r₁ r₂ : Result A ∞) →
              [ i ] r₁ ⟨ k ⟩ r₂ → [ i ] r₁ ⟨ k ⟩ r₂
  finally-∼ _ _ r₁≈r₂ = r₁≈r₂

  syntax finally-∼ r₁ r₂ r₁≈r₂ = r₁ ∼⟨ r₁≈r₂ ⟩□ r₂ □

-- An alternative formulation of weak bisimilarity.

module Alternative-weak-bisimilarity where

  -- If r₁ ↓ r₂, then r₂ does not start with a later constructor, and
  -- one can get r₂ from r₁ by peeling off a finite number of later
  -- constructors.

  infix 4 _↓_

  data _↓_ {A : Set} : Result A ∞ → Result A ∞ → Set where
    now    : ∀ {x} → now x ↓ now x
    crash  : crash ↓ crash
    read   : ∀ {f} → read f ↓ read f
    write  : ∀ {n r} → write n r ↓ write n r
    later  : ∀ {r₁ r₂} → force r₁ ↓ r₂ → later r₁ ↓ r₂

  -- The alternative formulation of weak bisimilarity.

  mutual

    infix 4 [_]_≈₂_ [_]_≈₂′_

    data [_]_≈₂_ {A : Set} (i : Size) :
                 Result A ∞ → Result A ∞ → Set where
      now    : ∀ {r₁ r₂ x} →
               r₁ ↓ now x → r₂ ↓ now x → [ i ] r₁ ≈₂ r₂
      crash  : ∀ {r₁ r₂} →
               r₁ ↓ crash → r₂ ↓ crash → [ i ] r₁ ≈₂ r₂
      read   : ∀ {r₁ r₂ f₁ f₂} →
               r₁ ↓ read f₁ → r₂ ↓ read f₂ →
               (∀ n → [ i ] force (f₁ n) ≈₂′ force (f₂ n)) →
               [ i ] r₁ ≈₂ r₂
      write  : ∀ {r₁ r₂ n r₁′ r₂′} →
               r₁ ↓ write n r₁′ → r₂ ↓ write n r₂′ →
               [ i ] force r₁′ ≈₂′ force r₂′ →
               [ i ] r₁ ≈₂ r₂
      later  : ∀ {r₁ r₂} →
               [ i ] force r₁ ≈₂′ force r₂ → [ i ] later r₁ ≈₂ later r₂

    record [_]_≈₂′_ {A : Set} (i : Size)
                    (r₁ r₂ : Result A ∞) : Set where
      coinductive
      field
        force : {j : Size< i} → [ j ] r₁ ≈₂ r₂

  open [_]_≈₂′_ public

  -- Emulations of laterˡ and laterʳ.

  laterˡ₂ : ∀ {i A r₁} {r₂ : Result A ∞} →
            [ i ] force r₁ ≈₂ r₂ → [ i ] later r₁ ≈₂ r₂
  laterˡ₂ {i} {r₁ = r₁} {r₂} = helper refl
    where
    helper :
      ∀ {r₁′} → r₁′ ≡ force r₁ → [ i ] r₁′ ≈₂ r₂ → [ i ] later r₁ ≈₂ r₂
    helper eq (now   r₁↓ r₂↓)   = now   (later (subst (_↓ _) eq r₁↓)) r₂↓
    helper eq (crash r₁↓ r₂↓)   = crash (later (subst (_↓ _) eq r₁↓)) r₂↓
    helper eq (read  r₁↓ r₂↓ p) = read  (later (subst (_↓ _) eq r₁↓)) r₂↓ p
    helper eq (write r₁↓ r₂↓ p) = write (later (subst (_↓ _) eq r₁↓)) r₂↓ p
    helper eq (later p)         = later λ { .force {j} →
      subst ([ j ]_≈₂ _) eq (laterˡ₂ (force p)) }

  laterʳ₂ : ∀ {i A} {r₁ : Result A ∞} {r₂} →
            [ i ] r₁ ≈₂ force r₂ → [ i ] r₁ ≈₂ later r₂
  laterʳ₂ {i} {r₁ = r₁} {r₂} = helper refl
    where
    helper :
      ∀ {r₂′} → r₂′ ≡ force r₂ → [ i ] r₁ ≈₂ r₂′ → [ i ] r₁ ≈₂ later r₂
    helper eq (now   r₁↓ r₂↓)   = now   r₁↓ (later (subst (_↓ _) eq r₂↓))
    helper eq (crash r₁↓ r₂↓)   = crash r₁↓ (later (subst (_↓ _) eq r₂↓))
    helper eq (read  r₁↓ r₂↓ p) = read  r₁↓ (later (subst (_↓ _) eq r₂↓)) p
    helper eq (write r₁↓ r₂↓ p) = write r₁↓ (later (subst (_↓ _) eq r₂↓)) p
    helper eq (later p)         = later λ { .force {j} →
      subst ([ j ] _ ≈₂_) eq (laterʳ₂ (force p)) }

  -- Lots of later constructors can be prepended to the left and right
  -- sides.

  laterˡ⋆ :
    ∀ {i A} {r₁ r₁′ r₂ : Result A ∞} →
    r₁ ↓ r₁′ → [ i ] r₁′ ≈ r₂ → [ i ] r₁ ≈ r₂
  laterˡ⋆ now       = id
  laterˡ⋆ crash     = id
  laterˡ⋆ read      = id
  laterˡ⋆ write     = id
  laterˡ⋆ (later p) = laterˡ ∘ laterˡ⋆ p

  laterʳ⋆ :
    ∀ {i A} {r₁ r₂ r₂′ : Result A ∞} →
    r₂ ↓ r₂′ → [ i ] r₁ ≈ r₂′ → [ i ] r₁ ≈ r₂
  laterʳ⋆ p = symmetric-≈ ∘ laterˡ⋆ p ∘ symmetric-≈

  laterˡʳ⋆ :
    ∀ {i A} {r₁ r₁′ r₂ r₂′ : Result A ∞} →
    r₁ ↓ r₁′ → r₂ ↓ r₂′ → [ i ] r₁′ ≈ r₂′ → [ i ] r₁ ≈ r₂
  laterˡʳ⋆ p q = laterˡ⋆ p ∘ laterʳ⋆ q

  -- The two formulations of weak bisimilarity are pointwise logically
  -- equivalent, in a size-preserving way.

  ≈⇔≈₂ : ∀ {i A} {r₁ r₂ : Result A ∞} →
         [ i ] r₁ ≈ r₂ ⇔ [ i ] r₁ ≈₂ r₂
  ≈⇔≈₂ = record { to = ≈→≈₂; from = ≈₂→≈ }
    where
    ≈→≈₂ : ∀ {i r₁ r₂} → [ i ] r₁ ≈ r₂ → [ i ] r₁ ≈₂ r₂
    ≈→≈₂ now        = now now now
    ≈→≈₂ crash      = crash crash crash
    ≈→≈₂ (read p)   = read read read λ { n .force → ≈→≈₂ (force (p n)) }
    ≈→≈₂ (write p)  = write write write λ { .force → ≈→≈₂ (force p) }
    ≈→≈₂ (later p)  = later λ { .force → ≈→≈₂ (force p) }
    ≈→≈₂ (laterˡ p) = laterˡ₂ (≈→≈₂ p)
    ≈→≈₂ (laterʳ p) = laterʳ₂ (≈→≈₂ p)

    ≈₂→≈ : ∀ {i r₁ r₂} → [ i ] r₁ ≈₂ r₂ → [ i ] r₁ ≈ r₂
    ≈₂→≈ (now   r₁↓ r₂↓)   = laterˡʳ⋆ r₁↓ r₂↓ now
    ≈₂→≈ (crash r₁↓ r₂↓)   = laterˡʳ⋆ r₁↓ r₂↓ crash
    ≈₂→≈ (read  r₁↓ r₂↓ p) = laterˡʳ⋆ r₁↓ r₂↓ (read λ { n .force →
                                                 ≈₂→≈ (force (p n)) })
    ≈₂→≈ (write r₁↓ r₂↓ p) = laterˡʳ⋆ r₁↓ r₂↓ (write λ { .force →
                                                 ≈₂→≈ (force p) })
    ≈₂→≈ (later p)         = later λ { .force → ≈₂→≈ (force p) }

-- Bind.

bind : ∀ {i A B} → Result A i → (A → Result B i) → Result B i
bind (now x)     f = f x
bind crash       f = crash
bind (read r)    f = read λ { n .force → bind (force (r n)) f }
bind (write o r) f = write o λ { .force → bind (force r) f }
bind (later r)   f = later λ { .force → bind (force r) f }

-- Result is a raw monad.

instance

  result-monad : ∀ {i} → Raw-monad (λ A → Result A i)
  Raw-monad.return result-monad = now
  Raw-monad._>>=_  result-monad = bind

-- Bind preserves strong and weak bisimilarity and expansion.

infixl 5 _>>=-cong_

_>>=-cong_ :
  ∀ {A B r₁ r₂} {f₁ f₂ : A → Result B ∞} {k i} →
  [ i ] r₁ ⟨ k ⟩ r₂ →
  (∀ x → [ i ] f₁ x ⟨ k ⟩ f₂ x) →
  [ i ] r₁ >>= f₁ ⟨ k ⟩ r₂ >>= f₂
now      >>=-cong q = q _
crash    >>=-cong q = crash
read p   >>=-cong q = read λ { n .force → force (p n) >>=-cong q }
write p  >>=-cong q = write λ { .force → force p >>=-cong q }
later p  >>=-cong q = later λ { .force → force p >>=-cong q }
laterˡ p >>=-cong q = laterˡ (p >>=-cong q)
laterʳ p >>=-cong q = laterʳ (p >>=-cong q)

-- The monad laws hold up to strong bisimilarity.

return->>= :
  ∀ {i A B x} (f : A → Result B ∞) →
  [ i ] return x >>= f ∼ f x
return->>= _ = reflexive _

>>=-return :
  ∀ {i A} (r : Result A ∞) →
  [ i ] r >>= return ∼ r
>>=-return (now _)     = now
>>=-return crash       = crash
>>=-return (read r)    = read λ { n .force → >>=-return (force (r n)) }
>>=-return (write _ r) = write λ { .force → >>=-return (force r) }
>>=-return (later r)   = later λ { .force → >>=-return (force r) }

>>=-associative :
  ∀ {i A B C} r {f : A → Result B ∞} {g : B → Result C ∞} →
  [ i ] r >>= f >>= g ∼ r >>= λ p → f p >>= g
>>=-associative (now _)     = reflexive _
>>=-associative crash       = crash
>>=-associative (read r)    = read λ { n .force → >>=-associative (force (r n)) }
>>=-associative (write _ r) = write λ { .force → >>=-associative (force r) }
>>=-associative (later r)   = later λ { .force → >>=-associative (force r) }

------------------------------------------------------------------------
-- The monad used by the definitional interpreter

-- The monad.

M : Set → Size → Set
M A i = ReaderT Env (StateT Heap (λ A → Result A i)) A

-- The monad's run function.

runM : ∀ {A i} → M A i → Env → Heap → Result (A × Heap) i
runM m ρ σ = run (run m ρ) σ

-- The inverse of the monad's run function.

runM⁻¹ : ∀ {A i} → (Env → Heap → Result (A × Heap) i) → M A i
run (run (runM⁻¹ m) ρ) σ = m ρ σ

-- Lifts results into the M monad.

liftM : ∀ {A i} → Result (A × Heap) i → M A i
liftM r = runM⁻¹ (λ _ _ → r)

-- A variant of drop-later.

drop-laterM : ∀ {i} {j : Size< i} {A} → M A i → M A j
drop-laterM m = runM⁻¹ λ ρ σ → drop-later (runM m ρ σ)

-- A crashing computation.

crashM : ∀ {A i} → M A i
crashM = liftʳ (liftʳ crash)

-- Looks up a variable in the environment.

lookup : ∀ {i} → Var → M Value i
lookup x = do
  ρ ← ask
  case ρ x of λ where
    nothing  → crashM
    (just v) → return v

-- Modifies the environment locally in the given computation.

with-env : ∀ {A i} → (Env → Env) → M A i → M A i
with-env = local

-- Allocates a new reference with the given initial value.

extendM : ∀ {i} → Value → M Ref i
extendM v = do
  σ ← liftʳ get
  let σ , r = extend σ v
  liftʳ (set σ)
  return r

-- Tries to dereference the given reference.

dereferenceM : ∀ {i} → Ref → M Value i
dereferenceM r = do
  σ ← liftʳ get
  case dereference σ r of λ where
    nothing  → crashM
    (just v) → return v

-- Tries to update the given reference with the given value.

updateM : ∀ {i} → Ref → Value → M ⊤ i
updateM r v = do
  σ ← liftʳ get
  case update σ r v of λ where
    nothing  → crashM
    (just σ) → do
      liftʳ (set σ)
      return _

-- Reads a natural number and continues.

readM : ∀ {A i} → (ℕ → M A i) → M A i
readM f =
  runM⁻¹ λ ρ σ →
    read λ { n .force → runM (f n) ρ σ }

-- Writes a natural number and continues.

writeM : ∀ {A i} → ℕ → M A i → M A i
writeM n m =
  runM⁻¹ λ ρ σ →
    write n λ { .force → runM m ρ σ }

-- Strong and weak bisimilarity and expansion can be lifted to the M
-- monad.

infix 4 [_]_⟨_⟩M_ [_]_∼M_ [_]_≳M_ [_]_≈M_

record [_]_⟨_⟩M_⟨_,_⟩
         {A : Set} (i : Size) (m₁ : M A ∞) (k : Kind) (m₂ : M A ∞)
         (ρ : Env) (σ : Heap) : Set where
  constructor wrap
  field
    run : [ i ] runM m₁ ρ σ ⟨ k ⟩ runM m₂ ρ σ

open [_]_⟨_⟩M_⟨_,_⟩ public

[_]_∼M_⟨_,_⟩ : {A : Set} → Size → M A ∞ → M A ∞ → Env → Heap → Set
[_]_∼M_⟨_,_⟩ = [_]_⟨ strong ⟩M_⟨_,_⟩

[_]_≳M_⟨_,_⟩ : {A : Set} → Size → M A ∞ → M A ∞ → Env → Heap → Set
[_]_≳M_⟨_,_⟩ = [_]_⟨ other expansion ⟩M_⟨_,_⟩

[_]_≈M_⟨_,_⟩ : {A : Set} → Size → M A ∞ → M A ∞ → Env → Heap → Set
[_]_≈M_⟨_,_⟩ = [_]_⟨ other weak ⟩M_⟨_,_⟩

[_]_⟨_⟩M_ : {A : Set} → Size → M A ∞ → Kind → M A ∞ → Set
[ i ] m₁ ⟨ k ⟩M m₂ = ∀ {ρ σ} → [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩

[_]_∼M_ : {A : Set} → Size → M A ∞ → M A ∞ → Set
[_]_∼M_ = [_]_⟨ strong ⟩M_

[_]_≳M_ : {A : Set} → Size → M A ∞ → M A ∞ → Set
[_]_≳M_ = [_]_⟨ other expansion ⟩M_

[_]_≈M_ : {A : Set} → Size → M A ∞ → M A ∞ → Set
[_]_≈M_ = [_]_⟨ other weak ⟩M_

-- Equational reasoning combinators.

module M-reasoning {A : Set} (ρ : Env) (σ : Heap) where

  infix  -1 finally-∼ _□
  infixr -2 step-∼ step-∼ˡ step-∼ʳ step-≳ step-≈ _≳⟨⟩_ _≡⟨⟩∼_

  _□ : ∀ {i k} (m : M A ∞) → [ i ] m ⟨ k ⟩M m ⟨ ρ , σ ⟩
  _ □ = wrap (_ Result-reasoning.□)

  step-∼ : ∀ {i} (m₁ : M A ∞) {m₂ m₃} →
           [ i ] m₂ ∼M m₃ ⟨ ρ , σ ⟩ →
           [ i ] m₁ ∼M m₂ ⟨ ρ , σ ⟩ →
           [ i ] m₁ ∼M m₃ ⟨ ρ , σ ⟩
  step-∼ _ m₂∼m₃ m₁∼m₂ =
    wrap (Result-reasoning.step-∼ _ (run m₂∼m₃) (run m₁∼m₂))

  syntax step-∼ m₁ m₂∼m₃ m₁∼m₂ = m₁ ∼⟨ m₁∼m₂ ⟩ m₂∼m₃

  step-∼ˡ : ∀ {i k} (m₁ : M A ∞) {m₂ m₃} →
            [ i ] m₂ ⟨ k ⟩M m₃ ⟨ ρ , σ ⟩ →
            [ ∞ ] m₁ ∼M m₂ ⟨ ρ , σ ⟩ →
            [ i ] m₁ ⟨ k ⟩M m₃ ⟨ ρ , σ ⟩
  step-∼ˡ _ m₂≈m₃ m₁∼m₂ =
    wrap (Result-reasoning.step-∼ˡ _ (run m₂≈m₃) (run m₁∼m₂))

  syntax step-∼ˡ m₁ m₂≈m₃ m₁∼m₂ = m₁ ∼⟨ m₁∼m₂ ⟩≈ m₂≈m₃

  step-∼ʳ : ∀ {k i} (m₁ : M A ∞) {m₂ m₃} →
            [ ∞ ] m₂ ∼M m₃ ⟨ ρ , σ ⟩ →
            [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩ →
            [ i ] m₁ ⟨ k ⟩M m₃ ⟨ ρ , σ ⟩
  step-∼ʳ _ m₂∼m₃ m₁≈m₂ =
    wrap (Result-reasoning.step-∼ʳ _ (run m₂∼m₃) (run m₁≈m₂))

  syntax step-∼ʳ m₁ m₂∼m₃ m₁≈m₂ = m₁ ≈⟨ m₁≈m₂ ⟩∼ m₂∼m₃

  step-≳ : ∀ {k i} (m₁ : M A ∞) {m₂ m₃} →
           [ i ] m₂ ⟨ other k ⟩M m₃ ⟨ ρ , σ ⟩ →
           [ ∞ ] m₁ ≳M m₂ ⟨ ρ , σ ⟩ →
           [ i ] m₁ ⟨ other k ⟩M m₃ ⟨ ρ , σ ⟩
  step-≳ _ m₂≈m₃ m₁≳m₂ =
    wrap (Result-reasoning.step-≳ _ (run m₂≈m₃) (run m₁≳m₂))

  syntax step-≳ m₁ m₂≈m₃ m₁≳m₂ = m₁ ≳⟨ m₁≳m₂ ⟩ m₂≈m₃

  step-≈ : ∀ {i} (m₁ : M A ∞) {m₂ m₃} →
           [ ∞ ] m₂ ≈M m₃ ⟨ ρ , σ ⟩ →
           [ ∞ ] m₁ ≈M m₂ ⟨ ρ , σ ⟩ →
           [ i ] m₁ ≈M m₃ ⟨ ρ , σ ⟩
  step-≈ _ m₂≈m₃ m₁≈m₂ =
    wrap (Result-reasoning.step-≈ _ (run m₂≈m₃) (run m₁≈m₂))

  syntax step-≈ m₁ m₂≈m₃ m₁≈m₂ = m₁ ≈⟨ m₁≈m₂ ⟩ m₂≈m₃

  _≳⟨⟩_ : ∀ {k i} (m₁ : M A ∞) {m₂} →
          [ i ] drop-laterM m₁ ⟨ other k ⟩M m₂ ⟨ ρ , σ ⟩ →
          [ i ] m₁ ⟨ other k ⟩M m₂ ⟨ ρ , σ ⟩
  _ ≳⟨⟩ p =
    wrap (Result-reasoning._≳⟨⟩_ _ (run p))

  _≡⟨⟩∼_ : ∀ {k i} (m₁ : M A ∞) {m₂} →
           [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩ →
           [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩
  _ ≡⟨⟩∼ m₁≈m₂ =
    wrap (Result-reasoning._≡⟨⟩∼_ _ (run m₁≈m₂))

  finally-∼ : ∀ {k i} (m₁ m₂ : M A ∞) →
              [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩ →
              [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩
  finally-∼ _ _ m₁≈m₂ =
    wrap (Result-reasoning.finally-∼ _ _ (run m₁≈m₂))

  syntax finally-∼ m₁ m₂ m₁≈m₂ = m₁ ∼⟨ m₁≈m₂ ⟩□ m₂ □

-- Conversions.

∼→M : ∀ {k i A} {m₁ m₂ : M A ∞} {ρ σ} →
      [ i ] m₁ ∼M m₂ ⟨ ρ , σ ⟩ → [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩
run (∼→M p) = ∼→ (run p)

≳→M : ∀ {k i A} {m₁ m₂ : M A ∞} {ρ σ} →
      [ i ] m₁ ≳M m₂ ⟨ ρ , σ ⟩ → [ i ] m₁ ⟨ other k ⟩M m₂ ⟨ ρ , σ ⟩
run (≳→M p) = ≳→ (run p)

-- Reflexivity and symmetry.

reflM : ∀ {A i k} (m : M A ∞) → [ i ] m ⟨ k ⟩M m
run (reflM _) = reflexive _

sym-∼M :
  ∀ {i A} {m₁ m₂ : M A ∞} {ρ σ} →
  [ i ] m₁ ∼M m₂ ⟨ ρ , σ ⟩ → [ i ] m₂ ∼M m₁ ⟨ ρ , σ ⟩
run (sym-∼M p) = symmetric-∼ (run p)

sym-≈M :
  ∀ {i A} {m₁ m₂ : M A ∞} {ρ σ} →
  [ i ] m₁ ≈M m₂ ⟨ ρ , σ ⟩ → [ i ] m₂ ≈M m₁ ⟨ ρ , σ ⟩
run (sym-≈M p) = symmetric-≈ (run p)

-- Some laws related to return and bind for M.

infixl 5 _>>=-congM_

_>>=-congM_ :
  ∀ {A B m₁ m₂} {f₁ f₂ : A → M B ∞} {k i ρ σ} →
  [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩ →
  (∀ {σ} x → [ i ] f₁ x ⟨ k ⟩M f₂ x ⟨ ρ , σ ⟩) →
  [ i ] m₁ >>= f₁ ⟨ k ⟩M m₂ >>= f₂ ⟨ ρ , σ ⟩
p >>=-congM q = wrap (run p >>=-cong λ _ → run (q _))

return->>=M :
  ∀ {i A B x} (f : A → M B ∞) →
  [ i ] return x >>= f ∼M f x
return->>=M f = wrap (return->>= (λ x → runM (f x) _ _))

>>=-returnM :
  ∀ {i A} (m : M A ∞) →
  [ i ] m >>= return ∼M m
>>=-returnM _ = wrap (>>=-return _)

>>=-associativeM :
  ∀ {i A B C} (m : M A ∞) {f : A → M B ∞} {g : B → M C ∞} →
  [ i ] m >>= f >>= g ∼M m >>= λ p → f p >>= g
>>=-associativeM m = wrap (>>=-associative (runM m _ _))

-- The with-env function preserves strong and weak bisimilarity and
-- expansion.

with-env-cong :
  ∀ {k i A f ρ σ} {m₁ m₂ : M A ∞} →
  [ i ] m₁ ⟨ k ⟩M m₂ ⟨ f ρ , σ ⟩ →
  [ i ] with-env f m₁ ⟨ k ⟩M with-env f m₂ ⟨ ρ , σ ⟩
run (with-env-cong p) = run p

-- A fusion lemma for with-env.

with-env-∘ :
  ∀ {i A} f g (m : M A ∞) →
  [ i ] with-env f (with-env g m) ∼M with-env (g ∘ f) m
run (with-env-∘ _ _ _) = reflexive _

-- The readM and writeM functions preserve strong and weak
-- bisimilarity and expansion.

readM-cong :
  ∀ {k i A ρ σ} {f₁ f₂ : ℕ → M A ∞} →
  (∀ n → [ i ] f₁ n ⟨ k ⟩M f₂ n ⟨ ρ , σ ⟩) →
  [ i ] readM f₁ ⟨ k ⟩M readM f₂ ⟨ ρ , σ ⟩
run (readM-cong p) = read λ { n .force → run (p n) }

writeM-cong :
  ∀ {k i A n ρ σ} {m₁ m₂ : M A ∞} →
  [ i ] m₁ ⟨ k ⟩M m₂ ⟨ ρ , σ ⟩ →
  [ i ] writeM n m₁ ⟨ k ⟩M writeM n m₂ ⟨ ρ , σ ⟩
run (writeM-cong p) = write λ { .force → run p }

------------------------------------------------------------------------
-- Semantics

mutual

  -- A definitional interpreter.

  ⟦_⟧ : ∀ {i} → Exp → M Value i
  ⟦ var x ⟧ = lookup x

  ⟦ lam x e ⟧ = do
    ρ ← ask
    return (closure x e ρ)

  ⟦ app e₁ e₂ ⟧ = apply ⟦ e₁ ⟧ ⟦ e₂ ⟧

  ⟦ fix rec x₂ e₁ e₂ ⟧ =
    let e = app (app (lam rec (lam x₂ e₁))
                     (lam x₂ (fix rec x₂ e₁ (var x₂))))
                e₂
    in
    runM⁻¹ λ ρ σ → later λ { .force → runM ⟦ e ⟧ ρ σ }

  ⟦ zero ⟧ = return (nat 0)

  ⟦ suc e ⟧ = do
    nat n ← ⟦ e ⟧
      where _ → crashM
    return (nat (1 + n))

  ⟦ pred e ⟧ = do
    nat n ← ⟦ e ⟧
      where _ → crashM
    return (nat (n ∸ 1))

  ⟦ if e =0-then e₁ else e₂ ⟧ = do
    nat n ← ⟦ e ⟧
      where _ → crashM
    case n of λ where
      zero    → ⟦ e₁ ⟧
      (suc _) → ⟦ e₂ ⟧

  ⟦ ref e ⟧ = do
    v ← ⟦ e ⟧
    r ← extendM v
    return (ref r)

  ⟦ ! e ⟧ = do
    ref r ← ⟦ e ⟧
      where _ → crashM
    dereferenceM r

  ⟦ e₁ ≔ e₂ ⟧ = do
    ref r ← ⟦ e₁ ⟧
      where _ → crashM
    v ← ⟦ e₂ ⟧
    updateM r v
    return unit

  ⟦ read x e ⟧ =
    readM λ n → with-env (_[ x ≔ nat n ]) ⟦ e ⟧

  ⟦ write e ⟧ = do
    nat n ← ⟦ e ⟧
      where _ → crashM
    writeM n (return unit)

  -- A function that is used to define the app case of ⟦_⟧.

  apply : ∀ {i} → M Value i → M Value i → M Value i
  apply m₁ m₂ = do
    closure x e ρ ← m₁
      where _ → crashM
    v ← m₂
    with-env (λ _ → ρ [ x ≔ v ])
      (runM⁻¹ λ ρ σ → later λ { .force → runM ⟦ e ⟧ ρ σ })

------------------------------------------------------------------------
-- Some lemmas related to the semantics

-- The apply function preserves strong and weak bisimilarity and
-- expansion.

apply-cong :
  ∀ {k i m₁₁ m₁₂ m₂₁ m₂₂ ρ σ} →
  [ i ] m₁₁ ⟨ k ⟩M m₁₂ ⟨ ρ , σ ⟩ →
  (∀ {σ} → [ i ] m₂₁ ⟨ k ⟩M m₂₂ ⟨ ρ , σ ⟩) →
  [ i ] apply m₁₁ m₂₁ ⟨ k ⟩M apply m₁₂ m₂₂ ⟨ ρ , σ ⟩
apply-cong {k} {m₁₁ = m₁₁} {m₁₂} {m₂₁} {m₂₂} {ρ} {σ} p q =
  wrap (helper {m₁₁ = m₁₁} {m₁₂} refl refl (run p) q)
  where
  helper :
    ∀ {i r₁ r₂ m₁₁ m₁₂} →
    runM m₁₁ ρ σ ≡ r₁ → runM m₁₂ ρ σ ≡ r₂ →
    [ i ] r₁ ⟨ k ⟩ r₂ →
    (∀ {σ} → [ i ] m₂₁ ⟨ k ⟩M m₂₂ ⟨ ρ , σ ⟩) →
    [ i ] runM (apply m₁₁ m₂₁) ρ σ ⟨ k ⟩ runM (apply m₁₂ m₂₂) ρ σ
  helper eq₁ eq₂ (now {x = unit , _})          _ rewrite eq₁ | eq₂ = crash
  helper eq₁ eq₂ (now {x = nat _ , _})         _ rewrite eq₁ | eq₂ = crash
  helper eq₁ eq₂ (now {x = ref _ , _})         _ rewrite eq₁ | eq₂ = crash
  helper eq₁ eq₂ (now {x = closure _ _ _ , _}) q rewrite eq₁ | eq₂ = run q >>=-cong λ _ → reflexive _
  helper eq₁ eq₂ crash                         _ rewrite eq₁ | eq₂ = crash
  helper eq₁ eq₂ (read p)                      q rewrite eq₁ | eq₂ = read λ { n .force → helper refl refl (force (p n)) q }
  helper eq₁ eq₂ (write p)                     q rewrite eq₁ | eq₂ = write λ { .force → helper refl refl (force p) q }
  helper eq₁ eq₂ (later p)                     q rewrite eq₁ | eq₂ = later λ { .force → helper refl refl (force p) q }
  helper eq₁ eq₂ (laterˡ p)                    q rewrite eq₁ | eq₂ = laterˡ (helper refl refl p q)
  helper eq₁ eq₂ (laterʳ p)                    q rewrite eq₁ | eq₂ = laterʳ (helper refl refl p q)

-- Some rearrangement/simplification lemmas for apply.

apply->>= :
  ∀ {A} (m : M A ∞) {f g i} →
  [ i ] apply (m >>= f) g ∼M
        m >>= λ x → apply (f x) g
run (apply->>= m) = >>=-associative (runM m _ _)

apply-closure :
  ∀ m₁ {x e ρ} m₂ {ρ₀ σ k i} →
  [ i ] m₁ ⟨ other k ⟩M return (closure x e ρ) ⟨ ρ₀ , σ ⟩ →
  [ i ] apply m₁ m₂ ⟨ other k ⟩M
        (do v ← m₂
            with-env (λ _ → ρ [ x ≔ v ]) ⟦ e ⟧) ⟨ ρ₀ , σ ⟩
apply-closure m₁ {x} {e} {ρ} m₂ {ρ₀} {σ} m₁≈ =
  apply m₁ m₂                                 ≳⟨ reflM m₁ >>=-congM (λ where
                                                   (unit         ) → wrap crash
                                                   (nat _        ) → wrap crash
                                                   (ref _        ) → wrap crash
                                                   (closure _ _ _) →
                                                     reflM m₂ >>=-congM λ _ → wrap (laterˡ (reflexive _))) ⟩
  (do closure x e ρ ← m₁
        where _ → crashM
      v ← m₂
      with-env (λ _ → ρ [ x ≔ v ]) ⟦ e ⟧)     ≈⟨ m₁≈ >>=-congM (λ _ → reflM _) ⟩∼

  (do closure x e ρ ← return (closure x e ρ)
        where _ → crashM
      v ← m₂
      with-env (λ _ → ρ [ x ≔ v ]) ⟦ e ⟧)     ≡⟨⟩∼

  (do v ← m₂
      with-env (λ _ → ρ [ x ≔ v ]) ⟦ e ⟧)     □
  where
  open M-reasoning ρ₀ σ

with-env-apply :
  ∀ {f} (m₁ : M Value ∞) {m₂ i} →
  [ i ] with-env f (apply m₁ m₂) ∼M
        apply (with-env f m₁) (with-env f m₂)
run (with-env-apply m₁) =
  (runM m₁ _ _ □) >>=-cong λ where
    (unit          , _) → crash
    (nat _         , _) → crash
    (ref _         , _) → crash
    (closure _ _ _ , _) → reflexive _
  where
  open Result-reasoning

-- A rearrangement/simplification lemma for fix.

unfold-fix :
  ∀ {rec x₂ e₁} e₂ {ρ σ i} →
  [ i ] ⟦ fix rec x₂ e₁ e₂ ⟧ ≳M
        (do v₂ ← ⟦ e₂ ⟧
            with-env (λ _ → ρ [ rec ≔ closure x₂
                                        (fix rec x₂ e₁ (var x₂)) ρ ]
                              [ x₂ ≔ v₂ ])
              ⟦ e₁ ⟧) ⟨ ρ , σ ⟩
unfold-fix {rec} {x₂} {e₁} e₂ {ρ} {σ} =
  ⟦ fix rec x₂ e₁ e₂ ⟧                                                   ≳⟨⟩

  ⟦ app (app (lam rec (lam x₂ e₁))
             (lam x₂ (fix rec x₂ e₁ (var x₂))))
        e₂ ⟧                                                             ∼⟨ wrap (reflexive _) ⟩≈

  apply (apply (return (closure rec (lam x₂ e₁) ρ))
               (return (closure x₂ (fix rec x₂ e₁ (var x₂)) ρ)))
        ⟦ e₂ ⟧                                                           ≳⟨ apply-cong (apply-closure (return (closure rec _ _)) (return _)
                                                                                                      (reflM _))
                                                                                       (reflM _) ⟩
  apply (do v ← return (closure x₂ (fix rec x₂ e₁ (var x₂)) ρ)
            with-env (λ _ → ρ [ rec ≔ v ]) ⟦ lam x₂ e₁ ⟧)
        ⟦ e₂ ⟧                                                           ≡⟨⟩∼

  apply (with-env (λ _ → ρ′) ⟦ lam x₂ e₁ ⟧) ⟦ e₂ ⟧                       ≳⟨ apply-closure (with-env _ ⟦ lam x₂ _ ⟧) ⟦ e₂ ⟧ (reflM _) ⟩

  (do v₂ ← ⟦ e₂ ⟧
      with-env (λ _ → ρ′ [ x₂ ≔ v₂ ]) ⟦ e₁ ⟧)                            □
  where
  open M-reasoning ρ σ
  ρ′ = ρ [ rec ≔ closure x₂ (fix rec x₂ e₁ (var x₂)) ρ ]

------------------------------------------------------------------------
-- Sequencing

-- Sequencing of expressions.

_⨾_ : Exp → Exp → Exp
e₁ ⨾ e₂ = app (app (lam 0 (lam 0 (var 0))) e₁) e₂

-- Sequencing is correctly implemented.

⨾-correct :
  ∀ {i} e₁ e₂ →
  [ i ] ⟦ e₁ ⨾ e₂ ⟧ ≳M do ⟦ e₁ ⟧; ⟦ e₂ ⟧
⨾-correct e₁ e₂ {ρ} {σ} =
  ⟦ app (app (lam 0 (lam 0 (var 0))) e₁) e₂ ⟧                 ≡⟨⟩∼

  apply (apply ⟦ lam 0 (lam 0 (var 0)) ⟧ ⟦ e₁ ⟧) ⟦ e₂ ⟧       ≳⟨ apply-cong (apply-closure ⟦ lam 0 _ ⟧ ⟦ e₁ ⟧ (wrap now)) (reflM _) ⟩

  apply (do v₁ ← ⟦ e₁ ⟧
            with-env (λ _ → ρ [ 0 ≔ v₁ ]) ⟦ lam 0 (var 0) ⟧)
        ⟦ e₂ ⟧                                                ≡⟨⟩∼

  apply (do v₁ ← ⟦ e₁ ⟧
            return (closure 0 (var 0) (ρ [ 0 ≔ v₁ ])))
        ⟦ e₂ ⟧                                                ∼⟨ apply->>= ⟦ e₁ ⟧ ⟩≈

  (do v₁ ← ⟦ e₁ ⟧
      apply (return (closure 0 (var 0) (ρ [ 0 ≔ v₁ ])))
            ⟦ e₂ ⟧)                                           ≳⟨ (⟦ e₁ ⟧ □) >>=-congM (λ _ →
                                                                 apply-closure (return (closure 0 _ _)) ⟦ e₂ ⟧ (reflM _)) ⟩
  (do v₁ ← ⟦ e₁ ⟧
      v₂ ← ⟦ e₂ ⟧
      with-env (λ ρ → ρ [ 0 ≔ v₁ ] [ 0 ≔ v₂ ]) ⟦ var 0 ⟧)     ≡⟨⟩∼

  (do v₁ ← ⟦ e₁ ⟧
      v₂ ← ⟦ e₂ ⟧
      return v₂)                                              ∼⟨ (⟦ e₁ ⟧ □) >>=-congM (λ _ → >>=-returnM _) ⟩≈

  (do ⟦ e₁ ⟧; ⟦ e₂ ⟧)                                         □
  where
  open M-reasoning ρ σ

------------------------------------------------------------------------
-- A fixed-point combinator

-- A call-by-value fixed-point combinator that doesn't quite work as
-- the one above.

fix′ : Exp
fix′ = lam 0 (app t t)
  module Fix where
  body₂ = app (app (var 1) (var 1)) (var 2)
  body₁ = app (var 0) (lam 2 body₂)
  t     = lam 1 body₁

-- This combinator does not satisfy (a variant of) the defining
-- equation of fix.
--
-- Note that the weak bisimilarity used here is rather syntactical.
-- Perhaps an equation like this holds for some notion of contextual
-- equivalence or applicative bisimilarity.

fix′-is-not-fix :
  ¬ (∀ {rec x₂ e₁} e₂ →
     [ ∞ ] ⟦ app (app fix′ (lam rec (lam x₂ e₁))) e₂ ⟧ ≈M
           ⟦ app (app (lam rec (lam x₂ e₁))
                      (lam x₂ (app (app fix′ (lam rec (lam x₂ e₁)))
                                   (var x₂))))
                 e₂ ⟧)
fix′-is-not-fix hyp = contradiction
  where
  fix′-lemma₁ :
    ∀ {i} e {ρ σ} →
    [ i ] ⟦ app fix′ e ⟧ ≳M
          (do v₀ ← ⟦ e ⟧
              let ρ₀ = ρ  [ 0 ≔ v₀ ]
                  ρ₁ = ρ₀ [ 1 ≔ closure 1 Fix.body₁ ρ₀ ]
              apply (return v₀)
                    (return (closure 2 Fix.body₂ ρ₁))) ⟨ ρ , σ ⟩
  fix′-lemma₁ e {ρ} {σ} =
    ⟦ app fix′ e ⟧                                     ≡⟨⟩∼

    apply ⟦ fix′ ⟧ ⟦ e ⟧                               ≳⟨ apply-closure ⟦ fix′ ⟧ ⟦ e ⟧ (wrap now) ⟩

    (do v₀ ← ⟦ e ⟧
        with-env (λ _ → ρ₀ v₀) ⟦ app Fix.t Fix.t ⟧)    ≡⟨⟩∼

    (do v₀ ← ⟦ e ⟧
        with-env (λ _ → ρ₀ v₀)
          (apply ⟦ Fix.t ⟧ ⟦ Fix.t ⟧))                 ≳⟨ reflM ⟦ e ⟧ >>=-congM (λ _ → with-env-cong $
                                                          apply-closure ⟦ Fix.t ⟧ ⟦ Fix.t ⟧ (wrap now)) ⟩
    (do v₀ ← ⟦ e ⟧
        with-env (λ _ → ρ₀ v₀) do
          v₁ ← ⟦ Fix.t ⟧
          with-env (λ _ → ρ₁ v₀ v₁) ⟦ Fix.body₁ ⟧)     ≡⟨⟩∼

    (do v₀ ← ⟦ e ⟧
        with-env (λ _ → ρ₂ v₀) ⟦ Fix.body₁ ⟧)          ≡⟨⟩∼

    (do v₀ ← ⟦ e ⟧
        with-env (λ _ → ρ₂ v₀)
          (apply (return v₀) ⟦ lam 2 Fix.body₂ ⟧))     ∼⟨ reflM ⟦ e ⟧ >>=-congM (λ v₀ →
                                                          with-env-apply (return v₀)) ⟩≈
    (do v₀ ← ⟦ e ⟧
        apply (return v₀)
              (return (closure 2 Fix.body₂ (ρ₂ v₀))))  □
    where
    open M-reasoning ρ σ

    ρ₀ = λ v₀ → ρ [ 0 ≔ v₀ ]
    ρ₁ = λ v₀ v₁ → ρ₀ v₀ [ 1 ≔ v₁ ]
    ρ₂ = λ v₀ → ρ₁ v₀ (closure 1 Fix.body₁ (ρ₀ v₀))

  fix′-lemma₂ :
    ∀ {rec x e ρ σ i} →
    let ρ₀ = ρ  [ 0 ≔ closure rec (lam x e) ρ ]
        ρ₁ = ρ₀ [ 1 ≔ closure 1 Fix.body₁ ρ₀ ]
    in
    [ i ] ⟦ app fix′ (lam rec (lam x e)) ⟧ ≳M
          return (closure x e (ρ [ rec ≔ closure 2 Fix.body₂ ρ₁ ]))
          ⟨ ρ , σ ⟩
  fix′-lemma₂ {rec} {x} {e} {ρ} {σ} =
    ⟦ app fix′ (lam rec (lam x e)) ⟧                                 ≳⟨ fix′-lemma₁ (lam _ (lam _ _)) ⟩

    (do v₀ ← ⟦ lam rec (lam x e) ⟧
        let ρ₀ = ρ  [ 0 ≔ v₀ ]
            ρ₁ = ρ₀ [ 1 ≔ closure 1 Fix.body₁ ρ₀ ]
        apply (return v₀) (return (closure 2 Fix.body₂ ρ₁)))         ∼⟨ wrap (reflexive _) ⟩≈

    apply (return v₀) (return (closure 2 Fix.body₂ ρ₁))              ≳⟨ apply-closure (return v₀) (return (closure 2 _ _)) (reflM _) ⟩

    with-env (λ _ → ρ [ rec ≔ closure 2 Fix.body₂ ρ₁ ]) ⟦ lam x e ⟧  ≡⟨⟩∼
    return (closure x e (ρ [ rec ≔ closure 2 Fix.body₂ ρ₁ ]))        □
    where
    open M-reasoning ρ σ

    v₀ = closure rec (lam x e) ρ
    ρ₀ = ρ  [ 0 ≔ v₀ ]
    ρ₁ = ρ₀ [ 1 ≔ closure 1 Fix.body₁ ρ₀ ]

  consequence :
    ∀ rec x₂ e₁ e₂ ρ σ →
    let ρ′   = ρ  [ 0 ≔ closure rec (lam x₂ e₁) ρ ]
        rec₁ = closure x₂ (app (app fix′ (lam rec (lam x₂ e₁)))
                               (var x₂))
                          ρ
        rec₂ = closure 2 Fix.body₂
                         (ρ′ [ 1 ≔ closure 1 Fix.body₁ ρ′ ])
    in
    [ ∞ ] (do v₂ ← ⟦ e₂ ⟧
              with-env (λ _ → ρ [ rec ≔ rec₁ ] [ x₂ ≔ v₂ ]) ⟦ e₁ ⟧) ≈M
          (do v₂ ← ⟦ e₂ ⟧
              with-env (λ _ → ρ [ rec ≔ rec₂ ] [ x₂ ≔ v₂ ]) ⟦ e₁ ⟧)
          ⟨ ρ , σ ⟩
  consequence rec x₂ e₁ e₂ ρ σ =
    (do v₂ ← ⟦ e₂ ⟧
        with-env (λ _ → ρ [ rec ≔ rec₁ ] [ x₂ ≔ v₂ ]) ⟦ e₁ ⟧)         ≈⟨ wrap (run (sym-≈M (apply-closure (return (closure x₂ _ _)) ⟦ e₂ ⟧ (reflM _)))) ⟩

    apply (return (closure x₂ e₁ (ρ [ rec ≔ rec₁ ]))) ⟦ e₂ ⟧          ∼⟨ wrap (reflexive _) ⟩≈

    apply (do v ← ⟦ ηf ⟧
              with-env (λ _ → ρ [ rec ≔ v ]) ⟦ lam x₂ e₁ ⟧)
          ⟦ e₂ ⟧                                                      ≈⟨ apply-cong
                                                                           (sym-≈M (apply-closure (return (closure rec _ _)) ⟦ ηf ⟧ (reflM _)))
                                                                           (reflM _) ⟩

    apply (apply (return (closure rec (lam x₂ e₁) ρ)) ⟦ ηf ⟧) ⟦ e₂ ⟧  ∼⟨ wrap (reflexive _) ⟩≈

    ⟦ app (app (lam rec (lam x₂ e₁)) ηf) e₂ ⟧                         ≈⟨ sym-≈M (hyp e₂) ⟩

    ⟦ app f e₂ ⟧                                                      ≡⟨⟩∼

    apply ⟦ f ⟧ ⟦ e₂ ⟧                                                ≳⟨ apply-cong (fix′-lemma₂) (reflM _) ⟩

    apply (return (closure x₂ e₁ (ρ [ rec ≔ rec₂ ]))) ⟦ e₂ ⟧          ≳⟨ apply-closure (return (closure x₂ _ _)) ⟦ e₂ ⟧ (reflM _) ⟩

    (do v₂ ← ⟦ e₂ ⟧
        with-env (λ _ → ρ [ rec ≔ rec₂ ] [ x₂ ≔ v₂ ]) ⟦ e₁ ⟧)         □
    where
    open M-reasoning ρ σ

    f    = app fix′ (lam rec (lam x₂ e₁))
    ηf   = lam x₂ (app f (var x₂))
    ρ′   = ρ [ 0 ≔ closure rec (lam x₂ e₁) ρ ]
    rec₁ = closure x₂ (app f (var x₂)) ρ
    rec₂ = closure 2 Fix.body₂ (ρ′ [ 1 ≔ closure 1 Fix.body₁ ρ′ ])

  consequence₂ :
    let e = lam 1 (var 0)
        ρ = ε [ 0 ≔ closure 0 e ε ]
    in
    [ ∞ ]
      now (closure 1 (app (app fix′ (lam 0 e)) (var 1)) ε , ∅) ≈
      now (closure 2 Fix.body₂ (ρ [ 1 ≔ closure 1 Fix.body₁ ρ ]) , ∅)
  consequence₂ = run (consequence 0 1 (var 0) zero ε ∅)

  contradiction : ⊥
  contradiction with consequence₂
  ... | ()

------------------------------------------------------------------------
-- An echo program

-- A program that echoes the input to the output.

echo : Exp
echo = app (lam 1 body) zero
  module Echo where
  body = fix 0 1 (read 1 (write (var 1) ⨾ app (var 0) zero)) (var 1)

-- The intended semantics of echo.

echo-sem : ∀ {i A} → Result A i
echo-sem = read λ { n .force → write n λ { .force → echo-sem }}

-- The echo program has the intended semantics.

echo-correct : ∀ {i} → [ i ] ⟦ echo ⟧ ≳M liftM echo-sem
echo-correct {ρ = ρ} {σ} =
  ⟦ echo ⟧                                        ≡⟨⟩∼
  apply ⟦ lam 1 Echo.body ⟧ (return (nat 0))      ≳⟨ apply-closure ⟦ lam 1 Echo.body ⟧ (return (nat 0)) (wrap now) ⟩
  with-env (λ _ → ρ [ 1 ≔ nat 0 ]) ⟦ Echo.body ⟧  ≳⟨ echo-body-correct ⟩
  liftM echo-sem                                  □
  where
  echo-body-correct :
    ∀ {ρ₀ v i} →
    [ i ] with-env (λ _ → ρ₀ [ 1 ≔ v ]) ⟦ Echo.body ⟧ ≳M liftM echo-sem
  echo-body-correct {ρ₀} {v} {ρ = ρ} {σ} =
    with-env (λ _ → ρ₀ [ 1 ≔ v ]) ⟦ Echo.body ⟧                 ≳⟨ with-env-cong (unfold-fix _) ⟩

    with-env (λ _ → ρ₀ [ 1 ≔ v ]) (with-env (λ _ → ρ₂)
       ⟦ read 1 (write (var 1) ⨾ app (var 0) zero) ⟧)           ∼⟨ with-env-∘ (λ _ → ρ₀ [ 1 ≔ v ]) (λ _ → ρ₂)
                                                                     ⟦ read 1 (write (var 1) ⨾ app (var 0) zero) ⟧ ⟩≈
    with-env (λ _ → ρ₂)
      ⟦ read 1 (write (var 1) ⨾ app (var 0) zero) ⟧             ∼⟨ with-env-cong (readM-cong λ _ → reflM _) ⟩≈

    with-env (λ _ → ρ₂) (readM λ n → with-env (_[ 1 ≔ nat n ])
      ⟦ write (var 1) ⨾ app (var 0) zero ⟧)                     ∼⟨ wrap (read λ { _ .force → reflexive _ }) ⟩≈

    (readM λ n → with-env (λ _ → ρ₃ n)
       ⟦ write (var 1) ⨾ app (var 0) zero ⟧)                    ≳⟨ (readM-cong λ _ → with-env-cong {f = λ _ → ρ₃ _} $
                                                                      ⨾-correct (write (var 1)) (app (var 0) zero)) ⟩
    (readM λ n → with-env (λ _ → ρ₃ n)
       (do ⟦ write (var 1) ⟧; ⟦ app (var 0) zero ⟧))            ∼⟨ (readM-cong λ n →
                                                                    with-env-cong {m₁ = do ⟦ write (var 1) ⟧; ⟦ app (var 0) zero ⟧}
                                                                                  {m₂ = writeM _ _} $
                                                                      wrap (write λ { .force → reflexive _ })) ⟩≈
    (readM λ n → with-env (λ _ → ρ₃ n) $ writeM n
       (apply (return (closure 1 Echo.body ρ₁))
              (return (nat 0))))                                ≳⟨ (readM-cong λ n → with-env-cong $ writeM-cong $
                                                                      apply-closure (return (closure 1 _ _)) (return _) (reflM _)) ⟩
    (readM λ n → with-env (λ _ → ρ₃ n) $ writeM n do
       v ← return (nat 0)
       with-env (λ _ → ρ₁ [ 1 ≔ v ]) ⟦ Echo.body ⟧)             ∼⟨ wrap (read λ { _ .force → write λ { .force → reflexive _ }}) ⟩≈

    (readM λ n → writeM n $
       with-env (λ _ → ρ₁ [ 1 ≔ nat 0 ]) ⟦ Echo.body ⟧)         ∼⟨ wrap (read λ { _ .force → write λ { .force →
                                                                     run (echo-body-correct {ρ = ρ}) }}) ⟩□
    liftM echo-sem                                              □
    where
    ρ₁ = ρ₀ [ 1 ≔ v ]
    ρ₂ = ρ₁ [ 0 ≔ closure 1 Echo.body ρ₁ ] [ 1 ≔ v ]
    ρ₃ = λ n → ρ₂ [ 1 ≔ nat n ]

    open M-reasoning ρ σ

  open M-reasoning ρ σ
