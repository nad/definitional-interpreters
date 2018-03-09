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

infix  -1 finally-∼ _□
infixr -2 step-∼ step-∼ˡ step-∼ʳ step-≳ step-≈ _≳⟨⟩_ _≡⟨⟩∼_

_□ : ∀ {k i A} (r : Result A ∞) → [ i ] r ⟨ k ⟩ r
_□ = reflexive

step-∼ : ∀ {i A} (r₁ : Result A ∞) {r₂ r₃} →
         [ i ] r₂ ∼ r₃ → [ i ] r₁ ∼ r₂ → [ i ] r₁ ∼ r₃
step-∼ _ r₂∼r₃ r₁∼r₂ = transitive-∼ r₁∼r₂ r₂∼r₃

syntax step-∼ r₁ r₂∼r₃ r₁∼r₂ = r₁ ∼⟨ r₁∼r₂ ⟩ r₂∼r₃

step-∼ˡ : ∀ {k i A} (r₁ : Result A ∞) {r₂ r₃} →
          [ i ] r₂ ⟨ k ⟩ r₃ → [ ∞ ] r₁ ∼ r₂ → [ i ] r₁ ⟨ k ⟩ r₃
step-∼ˡ _ r₂≈r₃ r₁∼r₂ = transitive-∼ˡ r₁∼r₂ r₂≈r₃

syntax step-∼ˡ r₁ r₂≈r₃ r₁∼r₂ = r₁ ∼⟨ r₁∼r₂ ⟩≈ r₂≈r₃

step-∼ʳ : ∀ {k i A} (r₁ : Result A ∞) {r₂ r₃} →
          [ ∞ ] r₂ ∼ r₃ → [ i ] r₁ ⟨ k ⟩ r₂ → [ i ] r₁ ⟨ k ⟩ r₃
step-∼ʳ _ r₂∼r₃ r₁≈r₂ = transitive-∼ʳ r₁≈r₂ r₂∼r₃

syntax step-∼ʳ r₁ r₂∼r₃ r₁≈r₂ = r₁ ≈⟨ r₁≈r₂ ⟩∼ r₂∼r₃

step-≳ : ∀ {k i A} (r₁ : Result A ∞) {r₂ r₃} →
         [ i ] r₂ ⟨ other k ⟩ r₃ → [ ∞ ] r₁ ≳ r₂ →
         [ i ] r₁ ⟨ other k ⟩ r₃
step-≳ _ r₂≈r₃ r₁≳r₂ = transitive-≳ r₁≳r₂ r₂≈r₃

syntax step-≳ r₁ r₂≈r₃ r₁≳r₂ = r₁ ≳⟨ r₁≳r₂ ⟩ r₂≈r₃

step-≈ : ∀ {i A} (r₁ : Result A ∞) {r₂ r₃} →
         [ ∞ ] r₂ ≈ r₃ → [ ∞ ] r₁ ≈ r₂ → [ i ] r₁ ≈ r₃
step-≈ _ r₂≈r₃ r₁≈r₂ = transitive-≈ r₁≈r₂ r₂≈r₃

syntax step-≈ r₁ r₂≈r₃ r₁≈r₂ = r₁ ≈⟨ r₁≈r₂ ⟩ r₂≈r₃

_≳⟨⟩_ : ∀ {k i A} (r₁ : Result A ∞) {r₂} →
        [ i ] drop-later r₁ ⟨ other k ⟩ r₂ → [ i ] r₁ ⟨ other k ⟩ r₂
now _     ≳⟨⟩ p = p
crash     ≳⟨⟩ p = p
read _    ≳⟨⟩ p = p
write _ _ ≳⟨⟩ p = p
later _   ≳⟨⟩ p = laterˡ p

_≡⟨⟩∼_ : ∀ {k i A} (r₁ : Result A ∞) {r₂} →
         [ i ] r₁ ⟨ k ⟩ r₂ → [ i ] r₁ ⟨ k ⟩ r₂
_ ≡⟨⟩∼ r₁≈r₂ = r₁≈r₂

finally-∼ : ∀ {k i A} (r₁ r₂ : Result A ∞) →
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

-- Bind. (The do notation below is desugared using this operator.)

infixl 5 _>>=_

_>>=_ : ∀ {i A B} → Result A i → (A → Result B i) → Result B i
now x     >>= f = f x
crash     >>= f = crash
read r    >>= f = read λ { n .force → force (r n) >>= f }
write o r >>= f = write o λ { .force → force r >>= f }
later r   >>= f = later λ { .force → force r >>= f }

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

now->>= : ∀ {i A B x} {f : A → Result B ∞} → [ i ] now x >>= f ∼ f x
now->>= = _ □

>>=-now : ∀ {i A} (r : Result A ∞) → [ i ] r >>= now ∼ r
>>=-now (now _)     = now
>>=-now crash       = crash
>>=-now (read r)    = read λ { n .force → >>=-now (force (r n)) }
>>=-now (write _ r) = write λ { .force → >>=-now (force r) }
>>=-now (later r)   = later λ { .force → >>=-now (force r) }

>>=-associative :
  ∀ {i A B C} r {f : A → Result B ∞} {g : B → Result C ∞} →
  [ i ] r >>= f >>= g ∼ r >>= λ p → f p >>= g
>>=-associative (now _)     = _ □
>>=-associative crash       = crash
>>=-associative (read r)    = read λ { n .force → >>=-associative (force (r n)) }
>>=-associative (write _ r) = write λ { .force → >>=-associative (force r) }
>>=-associative (later r)   = later λ { .force → >>=-associative (force r) }

------------------------------------------------------------------------
-- Semantics

mutual

  -- A definitional interpreter.

  ⟦_⟧ : ∀ {i} → Exp → Env → Heap → Result (Value × Heap) i
  ⟦ var x ⟧ ρ σ = case ρ x of λ where
    nothing  → crash
    (just v) → now (v , σ)

  ⟦ lam x e ⟧ ρ σ = now (closure x e ρ , σ)

  ⟦ app e₁ e₂ ⟧ ρ σ = apply (⟦ e₁ ⟧ ρ σ) (⟦ e₂ ⟧ ρ)

  ⟦ fix rec x₂ e₁ e₂ ⟧ ρ σ =
    later λ { .force →
      ⟦ app (app (lam rec (lam x₂ e₁))
                 (lam x₂ (fix rec x₂ e₁ (var x₂))))
            e₂ ⟧ ρ σ }

  ⟦ zero ⟧ ρ σ = now (nat 0 , σ)

  ⟦ suc e ⟧ ρ σ = do
    nat n , σ ← ⟦ e ⟧ ρ σ
      where _ → crash
    now (nat (1 + n) , σ)

  ⟦ pred e ⟧ ρ σ = do
    nat n , σ ← ⟦ e ⟧ ρ σ
      where _ → crash
    now (nat (n ∸ 1) , σ)

  ⟦ if e =0-then e₁ else e₂ ⟧ ρ σ = do
    nat n , σ ← ⟦ e ⟧ ρ σ
      where _ → crash
    case n of λ where
      zero    → ⟦ e₁ ⟧ ρ σ
      (suc _) → ⟦ e₂ ⟧ ρ σ

  ⟦ ref e ⟧ ρ σ = do
    v , σ ← ⟦ e ⟧ ρ σ
    let σ , r = extend σ v
    now (ref r , σ)

  ⟦ ! e ⟧ ρ σ = do
    ref r , σ ← ⟦ e ⟧ ρ σ
      where _ → crash
    case dereference σ r of λ where
      nothing  → crash
      (just v) → now (v , σ)

  ⟦ e₁ ≔ e₂ ⟧ ρ σ = do
    ref r , σ ← ⟦ e₁ ⟧ ρ σ
      where _ → crash
    v , σ ← ⟦ e₂ ⟧ ρ σ
    case update σ r v of λ where
      nothing  → crash
      (just σ) → now (unit , σ)

  ⟦ read x e ⟧ ρ σ =
    read λ { n .force →
    ⟦ e ⟧ (ρ [ x ≔ nat n ]) σ }

  ⟦ write e ⟧ ρ σ = do
    nat n , σ ← ⟦ e ⟧ ρ σ
      where _ → crash
    write n λ { .force → now (unit , σ) }

  -- A function that is used to define the app case of ⟦_⟧.

  apply : ∀ {i} →
          Result (Value × Heap) i →
          (Heap → Result (Value × Heap) i) →
          Result (Value × Heap) i
  apply r f = do
    closure x e ρ , σ ← r
      where _ → crash
    v , σ ← f σ
    later λ { .force → ⟦ e ⟧ (ρ [ x ≔ v ]) σ }

------------------------------------------------------------------------
-- Some lemmas related to the semantics

-- The apply function preserves strong and weak bisimilarity and
-- expansion.

apply-cong :
  ∀ {k i r₁ r₂ f₁ f₂} →
  [ i ] r₁ ⟨ k ⟩ r₂ →
  (∀ σ → [ i ] f₁ σ ⟨ k ⟩ f₂ σ) →
  [ i ] apply r₁ f₁ ⟨ k ⟩ apply r₂ f₂
apply-cong (now {x = unit , _})          _ = crash
apply-cong (now {x = nat _ , _})         _ = crash
apply-cong (now {x = ref _ , _})         _ = crash
apply-cong (now {x = closure _ _ _ , _}) q = q _ >>=-cong λ _ → _ □
apply-cong crash                         _ = crash
apply-cong (read p)                      q = read λ { n .force → apply-cong (force (p n)) q }
apply-cong (write p)                     q = write λ { .force → apply-cong (force p) q }
apply-cong (later p)                     q = later λ { .force → apply-cong (force p) q }
apply-cong (laterˡ p)                    q = laterˡ (apply-cong p q)
apply-cong (laterʳ p)                    q = laterʳ (apply-cong p q)

-- Some rearrangement/simplification lemmas for apply.

apply->>= :
  ∀ {A} (r : Result A ∞) {f g i} →
  [ i ] apply (r >>= f) g ∼
        r >>= λ x → apply (f x) g
apply->>= r = >>=-associative r

apply-closure :
  ∀ {r x e ρ σ k i} f →
  [ i ] r ⟨ other k ⟩ now (closure x e ρ , σ) →
  [ i ] apply r f ⟨ other k ⟩
        do v , σ ← f σ
           ⟦ e ⟧ (ρ [ x ≔ v ]) σ
apply-closure {r} {x} {e} {ρ} {σ} f r≈now =
  apply r f                                         ≳⟨ (r □) >>=-cong (λ where
                                                         (unit          , _) → crash
                                                         (nat _         , _) → crash
                                                         (ref _         , _) → crash
                                                         (closure _ _ _ , _) → (f _ □) >>=-cong λ _ → laterˡ (_ □)) ⟩
  (do closure x e ρ , σ ← r
        where _ → crash
      v , σ ← f σ
      ⟦ e ⟧ (ρ [ x ≔ v ]) σ)                        ≈⟨ r≈now >>=-cong (λ _ → _ □) ⟩∼

  (do closure x e ρ , σ ← now (closure x e ρ ,′ σ)
        where _ → crash
      v₂ , σ ← f σ
      ⟦ e ⟧ (ρ [ x ≔ v₂ ]) σ)                       ≡⟨⟩∼

  (do v , σ ← f σ
      ⟦ e ⟧ (ρ [ x ≔ v ]) σ)                        □

-- A rearrangement/simplification lemma for fix.

unfold-fix :
  ∀ {rec x₂ e₁} e₂ {ρ σ i} →
  [ i ] ⟦ fix rec x₂ e₁ e₂ ⟧ ρ σ ≳
        (do v₂ , σ ← ⟦ e₂ ⟧ ρ σ
            ⟦ e₁ ⟧ (ρ [ rec ≔ closure x₂ (fix rec x₂ e₁ (var x₂)) ρ ]
                      [ x₂ ≔ v₂ ]) σ)
unfold-fix {rec} {x₂} {e₁} e₂ {ρ} {σ} =
  ⟦ fix rec x₂ e₁ e₂ ⟧ ρ σ                                               ≳⟨⟩

  ⟦ app (app (lam rec (lam x₂ e₁))
             (lam x₂ (fix rec x₂ e₁ (var x₂))))
        e₂ ⟧ ρ σ                                                         ≡⟨⟩∼

  apply (apply (now (closure rec (lam x₂ e₁) ρ , σ))
               (λ σ → now (closure x₂ (fix rec x₂ e₁ (var x₂)) ρ , σ)))
        (⟦ e₂ ⟧ ρ)                                                       ≳⟨ apply-cong (apply-closure (λ σ → now (_ , σ)) now)
                                                                                       (λ σ → ⟦ e₂ ⟧ ρ σ □) ⟩
  apply (do v , σ ← now (closure x₂ (fix rec x₂ e₁ (var x₂)) ρ , σ)
            ⟦ lam x₂ e₁ ⟧ (ρ [ rec ≔ v ]) σ)
        (⟦ e₂ ⟧ ρ)                                                       ≡⟨⟩∼

  apply (⟦ lam x₂ e₁ ⟧ ρ′ σ) (⟦ e₂ ⟧ ρ)                                  ≳⟨ apply-closure (⟦ e₂ ⟧ ρ) now ⟩

  (do v₂ , σ ← ⟦ e₂ ⟧ ρ σ
      ⟦ e₁ ⟧ (ρ′ [ x₂ ≔ v₂ ]) σ)                                         □
  where
  ρ′ = ρ [ rec ≔ closure x₂ (fix rec x₂ e₁ (var x₂)) ρ ]

------------------------------------------------------------------------
-- Sequencing

-- Sequencing of expressions.

_⨾_ : Exp → Exp → Exp
e₁ ⨾ e₂ = app (app (lam 0 (lam 0 (var 0))) e₁) e₂

-- Sequencing is correctly implemented.

⨾-correct :
  ∀ {i} e₁ e₂ ρ {σ} →
  [ i ] ⟦ e₁ ⨾ e₂ ⟧ ρ σ ≳
        do _ , σ ← ⟦ e₁ ⟧ ρ σ
           ⟦ e₂ ⟧ ρ σ
⨾-correct e₁ e₂ ρ {σ} =
  ⟦ app (app (lam 0 (lam 0 (var 0))) e₁) e₂ ⟧ ρ σ           ≡⟨⟩∼

  apply (apply (⟦ lam 0 (lam 0 (var 0)) ⟧ ρ σ) (⟦ e₁ ⟧ ρ))
        (⟦ e₂ ⟧ ρ)                                          ≳⟨ apply-cong (apply-closure (⟦ e₁ ⟧ ρ) now) (λ _ → _ □) ⟩

  apply (do v₁ , σ ← ⟦ e₁ ⟧ ρ σ
            ⟦ lam 0 (var 0) ⟧ (ρ [ 0 ≔ v₁ ]) σ)
        (⟦ e₂ ⟧ ρ)                                          ≡⟨⟩∼

  apply (do v₁ , σ ← ⟦ e₁ ⟧ ρ σ
            now (closure 0 (var 0) (ρ [ 0 ≔ v₁ ]) , σ))
        (⟦ e₂ ⟧ ρ)                                          ∼⟨ apply->>= (⟦ e₁ ⟧ ρ σ) ⟩≈

  (do v₁ , σ ← ⟦ e₁ ⟧ ρ σ
      apply (now (closure 0 (var 0) (ρ [ 0 ≔ v₁ ]) , σ))
            (⟦ e₂ ⟧ ρ))                                     ≳⟨ (⟦ e₁ ⟧ ρ σ □) >>=-cong (λ _ → apply-closure (⟦ e₂ ⟧ ρ) now) ⟩

  (do v₁ , σ ← ⟦ e₁ ⟧ ρ σ
      v₂ , σ ← ⟦ e₂ ⟧ ρ σ
      ⟦ var 0 ⟧ (ρ [ 0 ≔ v₁ ] [ 0 ≔ v₂ ]) σ)                ≡⟨⟩∼

  (do _  , σ ← ⟦ e₁ ⟧ ρ σ
      v₂ , σ ← ⟦ e₂ ⟧ ρ σ
      now (v₂ , σ))                                         ∼⟨ (⟦ e₁ ⟧ ρ σ □) >>=-cong (λ _ → >>=-now _) ⟩≈

  (do _ , σ ← ⟦ e₁ ⟧ ρ σ
      ⟦ e₂ ⟧ ρ σ)                                           □

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
  ¬ (∀ {rec x₂ e₁} e₂ {ρ σ} →
     [ ∞ ] ⟦ app (app fix′ (lam rec (lam x₂ e₁))) e₂ ⟧ ρ σ ≈
           ⟦ app (app (lam rec (lam x₂ e₁))
                      (lam x₂ (app (app fix′ (lam rec (lam x₂ e₁)))
                                   (var x₂))))
                 e₂ ⟧ ρ σ)
fix′-is-not-fix hyp = contradiction
  where
  fix′-lemma₁ :
    ∀ {i} e {ρ σ} →
    [ i ] ⟦ app fix′ e ⟧ ρ σ ≳
          do v₀ , σ ← ⟦ e ⟧ ρ σ
             let ρ₀ = ρ  [ 0 ≔ v₀ ]
                 ρ₁ = ρ₀ [ 1 ≔ closure 1 Fix.body₁ ρ₀ ]
             apply (now (v₀ , σ))
                   (λ σ → now (closure 2 Fix.body₂ ρ₁ , σ))
  fix′-lemma₁ e {ρ} {σ} =
    ⟦ app fix′ e ⟧ ρ σ                                        ≡⟨⟩∼

    apply (⟦ fix′ ⟧ ρ σ) (⟦ e ⟧ ρ)                            ≳⟨ apply-closure (⟦ e ⟧ ρ) now ⟩

    (do v₀ , σ ← ⟦ e ⟧ ρ σ
        ⟦ app Fix.t Fix.t ⟧ (ρ₀ v₀) σ)                        ≡⟨⟩∼

    (do v₀ , σ ← ⟦ e ⟧ ρ σ
        apply (⟦ Fix.t ⟧ (ρ₀ v₀) σ) (⟦ Fix.t ⟧ (ρ₀ v₀)))      ≳⟨ (⟦ e ⟧ ρ σ □) >>=-cong (λ _ → apply-closure (⟦ Fix.t ⟧ _) now) ⟩

    (do v₀ , σ ← ⟦ e ⟧ ρ σ
        v₁ , σ ← ⟦ Fix.t ⟧ (ρ₀ v₀) σ
        ⟦ Fix.body₁ ⟧ (ρ₁ v₀ v₁) σ)                           ≡⟨⟩∼

    (do v₀ , σ ← ⟦ e ⟧ ρ σ
        apply (now (v₀ , σ))
              (λ σ → now (closure 2 Fix.body₂ (ρ₂ v₀) , σ)))  □
    where
    ρ₀ = λ v₀ → ρ [ 0 ≔ v₀ ]
    ρ₁ = λ v₀ v₁ → ρ₀ v₀ [ 1 ≔ v₁ ]
    ρ₂ = λ v₀ → ρ₁ v₀ (closure 1 Fix.body₁ (ρ₀ v₀))

  fix′-lemma₂ :
    ∀ {rec x e ρ σ i} →
    [ i ] ⟦ app fix′ (lam rec (lam x e)) ⟧ ρ σ ≳
          let ρ₀ = ρ  [ 0 ≔ closure rec (lam x e) ρ ]
              ρ₁ = ρ₀ [ 1 ≔ closure 1 Fix.body₁ ρ₀ ]
          in
          now (closure x e (ρ [ rec ≔ closure 2 Fix.body₂ ρ₁ ]) , σ)
  fix′-lemma₂ {rec} {x} {e} {ρ} {σ} =
    ⟦ app fix′ (lam rec (lam x e)) ⟧ ρ σ                        ≳⟨ fix′-lemma₁ (lam _ (lam _ _)) ⟩

    apply (now (v₀ , σ))
          (λ σ → now (closure 2 Fix.body₂ ρ₁ , σ))              ≳⟨ apply-closure (λ σ → now (closure _ _ ρ₁ , σ)) now ⟩

    ⟦ lam x e ⟧ (ρ [ rec ≔ closure 2 Fix.body₂ ρ₁ ]) σ          ≡⟨⟩∼

    now (closure x e (ρ [ rec ≔ closure 2 Fix.body₂ ρ₁ ]) , σ)  □
    where
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
    [ ∞ ] (do v₂ , σ ← ⟦ e₂ ⟧ ρ σ
              ⟦ e₁ ⟧ (ρ [ rec ≔ rec₁ ] [ x₂ ≔ v₂ ]) σ) ≈
          (do v₂ , σ ← ⟦ e₂ ⟧ ρ σ
              ⟦ e₁ ⟧ (ρ [ rec ≔ rec₂ ] [ x₂ ≔ v₂ ]) σ)
  consequence rec x₂ e₁ e₂ ρ σ =
    (do v₂ , σ ← ⟦ e₂ ⟧ ρ σ
        ⟦ e₁ ⟧ (ρ [ rec ≔ rec₁ ] [ x₂ ≔ v₂ ]) σ)                    ≈⟨ symmetric-≈ (apply-closure (⟦ e₂ ⟧ ρ) now) ⟩

    apply (now (closure x₂ e₁ (ρ [ rec ≔ rec₁ ]) , σ)) (⟦ e₂ ⟧ ρ)   ≡⟨⟩∼

    apply (do v , σ ← ⟦ ηf ⟧ ρ σ
              ⟦ lam x₂ e₁ ⟧ (ρ [ rec ≔ v ]) σ)
          (⟦ e₂ ⟧ ρ)                                                ≈⟨ apply-cong (symmetric-≈ (apply-closure (⟦ ηf ⟧ ρ) now)) (λ _ → _ □) ⟩

    apply (apply (now (closure rec (lam x₂ e₁) ρ , σ)) (⟦ ηf ⟧ ρ))
          (⟦ e₂ ⟧ ρ)                                                ≡⟨⟩∼

    ⟦ app (app (lam rec (lam x₂ e₁)) ηf) e₂ ⟧ ρ σ                   ≈⟨ symmetric-≈ (hyp e₂) ⟩

    ⟦ app f e₂ ⟧ ρ σ                                                ≡⟨⟩∼

    apply (⟦ f ⟧ ρ σ) (⟦ e₂ ⟧ ρ)                                    ≳⟨ apply-cong fix′-lemma₂ (λ _ → _ □) ⟩

    apply (now (closure x₂ e₁ (ρ [ rec ≔ rec₂ ]) , σ))
          (⟦ e₂ ⟧ ρ)                                                ≳⟨ apply-closure (⟦ e₂ ⟧ ρ) now ⟩

    (do v₂ , σ ← ⟦ e₂ ⟧ ρ σ
        ⟦ e₁ ⟧ (ρ [ rec ≔ rec₂ ] [ x₂ ≔ v₂ ]) σ)                    □
    where
    f    = app fix′ (lam rec (lam x₂ e₁))
    ηf   = lam x₂ (app f (var x₂))
    ρ′   = ρ  [ 0 ≔ closure rec (lam x₂ e₁) ρ ]
    rec₁ = closure x₂ (app f (var x₂)) ρ
    rec₂ = closure 2 Fix.body₂ (ρ′ [ 1 ≔ closure 1 Fix.body₁ ρ′ ])

  consequence₂ :
    let e = lam 1 (var 0)
        ρ = ε [ 0 ≔ closure 0 e ε ]
    in
    [ ∞ ]
      now (closure 1 (app (app fix′ (lam 0 e)) (var 1)) ε , ∅) ≈
      now (closure 2 Fix.body₂ (ρ [ 1 ≔ closure 1 Fix.body₁ ρ ]) , ∅)
  consequence₂ = consequence 0 1 (var 0) zero ε ∅

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

echo-correct : ∀ {ρ σ i} → [ i ] ⟦ echo ⟧ ρ σ ≳ echo-sem
echo-correct {ρ} {σ} =
  ⟦ echo ⟧ ρ σ                                             ≡⟨⟩∼
  apply (⟦ lam 1 Echo.body ⟧ ρ σ) (λ σ → now (nat 0 , σ))  ≳⟨ apply-closure (λ σ → now (_ , σ)) now ⟩
  ⟦ Echo.body ⟧ (ρ [ 1 ≔ nat 0 ]) σ                        ≳⟨ echo-body-correct ⟩
  echo-sem                                                 □
  where
  echo-body-correct :
    ∀ {ρ v σ i} →
    [ i ] ⟦ Echo.body ⟧ (ρ [ 1 ≔ v ]) σ ≳ echo-sem
  echo-body-correct {ρ} {v} {σ} =
    ⟦ Echo.body ⟧ ρ₁ σ                                   ≳⟨ unfold-fix (var 1) ⟩

    ⟦ read 1 (write (var 1) ⨾ app (var 0) zero) ⟧ ρ₂ σ   ∼⟨ (read λ { _ .force → _ □ }) ⟩≈

    (read λ { n .force →
       ⟦ write (var 1) ⨾ app (var 0) zero ⟧ (ρ₃ n) σ })  ≳⟨ (read λ { _ .force → ⨾-correct (write (var 1)) (app (var 0) zero) (ρ₃ _) }) ⟩

    (read λ { n .force → do
       _ , σ ← ⟦ write (var 1) ⟧ (ρ₃ n) σ
       ⟦ app (var 0) zero ⟧ (ρ₃ n) σ })                  ∼⟨ (read λ { _ .force → write λ { .force → _ □ }}) ⟩≈

    (read λ { n .force → write n λ { .force →
       apply (now (closure 1 Echo.body ρ₁ , σ))
             (λ σ → now (nat 0 , σ)) }})                 ≳⟨ (read λ { _ .force → write λ { .force → apply-closure (λ σ → now (_ , σ)) now }}) ⟩

    (read λ { n .force → write n λ { .force → do
       v , σ ← now (nat 0 , σ)
       ⟦ Echo.body ⟧ (ρ₁ [ 1 ≔ v ]) σ }})                ∼⟨ (read λ { _ .force → write λ { .force → _ □ }}) ⟩≈

    (read λ { n .force → write n λ { .force →
       ⟦ Echo.body ⟧ (ρ₁ [ 1 ≔ nat 0 ]) σ }})            ∼⟨ (read λ { _ .force → write λ { .force → echo-body-correct }}) ⟩□

    echo-sem                                             □
    where
    ρ₁ = ρ [ 1 ≔ v ]
    ρ₂ = ρ₁ [ 0 ≔ closure 1 Echo.body ρ₁ ] [ 1 ≔ v ]
    ρ₃ = λ n → ρ₂ [ 1 ≔ nat n ]
