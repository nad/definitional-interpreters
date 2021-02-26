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
open import Function-universe E.equality-with-J hiding (_∘_)
open import Maybe E.equality-with-J as Maybe hiding (raw-monad)
open import Monad E.equality-with-J as M
  using (Raw-monad; _>>=_)

open import Delay-monad
open import Delay-monad.Bisimilarity
open import Delay-monad.Bisimilarity.Kind
import Delay-monad.Monad as DM
import Delay-monad.Parallel as DP
import Delay-monad.Sequential as DS
open import Delay-monad.Termination

private

  variable
    A B C     : Type
    i         : Size
    f g k x y : A

------------------------------------------------------------------------
-- Types and operations

-- The monad.

Delay-crash : Type → Size → Type
Delay-crash A i = Delay (Maybe A) i

-- A raw-monad instance. (This definition is turned into an actual
-- instance at the end of this module, to avoid problems with instance
-- resolution.)

private

  raw-monad′ : Raw-monad (λ A → Delay-crash A i)
  raw-monad′ {i = i} =
    _⇔_.to (M.⇔→raw⇔raw {F = MaybeT (λ A → Delay A i)}
              (λ _ → record { to = run; from = wrap }))
      it

  module DC {i} = Raw-monad (raw-monad′ {i = i})

-- A crashing computation.

pattern crash = now nothing

private

  -- A computation that terminates now.

  pattern return x = now (just x)

-- Sequential composition of computations.
--
-- Note that if the first argument fails to terminate, and the other
-- one crashes, then the computation fails to terminate. However, if
-- the first argument crashes, then the computation always crashes.

infixl 6 _⊛ˢ_

_⊛ˢ_ : Delay-crash (A → B) i → Delay-crash A i → Delay-crash B i
f ⊛ˢ x = f DC.>>= λ f → x DC.>>= λ x → DC.return (f x)

-- Parallel composition of computations.
--
-- Note that if the first argument fails to terminate, and the other
-- one crashes, then the computation fails to terminate. However, if
-- the first argument crashes, then the computation always crashes.

infixl 6 _⊛ᵖ_

_⊛ᵖ_ : Delay-crash (A → B) i → Delay-crash A i → Delay-crash B i
crash    ⊛ᵖ _            = crash
return f ⊛ᵖ return x     = return (f x)
return f ⊛ᵖ crash        = crash
return f ⊛ᵖ later x      = later λ { .force → return f ⊛ᵖ x .force }
later f  ⊛ᵖ later x      = later λ { .force → f .force ⊛ᵖ x .force }
later f  ⊛ᵖ x            = later λ { .force → f .force ⊛ᵖ x }

------------------------------------------------------------------------
-- Some properties

-- Bind preserves strong and weak bisimilarity and the expansion
-- relation.

infixl 5 _>>=-cong_

_>>=-cong_ :
  [ i ] x ⟨ k ⟩ y →
  (∀ z → [ i ] f z ⟨ k ⟩ g z) →
  [ i ] x DC.>>= f ⟨ k ⟩ y DC.>>= g
p >>=-cong q = p DM.>>=-cong [ (λ _ → run fail ∎) , q ]

-- Sequential composition preserves strong and weak bisimilarity and
-- the expansion relation.

infixl 6 _⊛ˢ-cong_

_⊛ˢ-cong_ :
  [ i ] f ⟨ k ⟩ g →
  [ i ] x ⟨ k ⟩ y →
  [ i ] f ⊛ˢ x ⟨ k ⟩ g ⊛ˢ y
p ⊛ˢ-cong q = p >>=-cong λ _ → q >>=-cong λ _ → now

-- Parallel composition preserves strong and weak bisimilarity and the
-- expansion relation.

infixl 6 _⊛ᵖ-cong_

_⊛ᵖ-cong_ :
  [ i ] f ⟨ k ⟩ g →
  [ i ] x ⟨ k ⟩ y →
  [ i ] f ⊛ᵖ x ⟨ k ⟩ g ⊛ᵖ y
_⊛ᵖ-cong_ = λ p q → ⊛ᵖ-cong-helper _ _ p _ _ q
  where
  crash-lemma :
    [ i ] f ⟨ other k ⟩ crash → ∀ x → [ i ] f ⊛ᵖ x ⟨ other k ⟩ crash
  crash-lemma now        x         = now
  crash-lemma (laterˡ p) (now x)   = laterˡ (crash-lemma p _)
  crash-lemma (laterˡ p) (later x) = laterˡ (crash-lemma p _)

  ⊛ᵖ-cong-helper :
    (f g : Delay-crash (A → B) ∞) → [ i ] f ⟨ k ⟩ g →
    (x y : Delay-crash A ∞) →       [ i ] x ⟨ k ⟩ y →
    [ i ] f ⊛ᵖ x ⟨ k ⟩ g ⊛ᵖ y
  ⊛ᵖ-cong-helper crash crash now = λ _ _ _ → now

  ⊛ᵖ-cong-helper (return f) .(return f) now = λ where
    (later x)  (later y)   q          → later λ { .force → now ⊛ᵖ-cong later⁻¹ q }
    crash      crash       now        → now
    (return x) .(return x) now        → now
    _          _           (laterˡ q) → laterˡ (now ⊛ᵖ-cong q)
    _          _           (laterʳ q) → laterʳ (now ⊛ᵖ-cong q)

  ⊛ᵖ-cong-helper (later f) (later g) p = λ where
    crash      crash       now        → later λ { .force → later⁻¹ p ⊛ᵖ-cong now }
    (return x) .(return x) now        → later λ { .force → later⁻¹ p ⊛ᵖ-cong now }
    (later x)  (later y)   q          → later λ { .force → later⁻¹ p ⊛ᵖ-cong later⁻¹ q }
    _          crash       (laterˡ q) → later λ { .force → later⁻¹ p ⊛ᵖ-cong q }
    _          (return y)  (laterˡ q) → later λ { .force → later⁻¹ p ⊛ᵖ-cong q }
    crash      _           (laterʳ q) → later λ { .force → later⁻¹ p ⊛ᵖ-cong q }
    (return x) _           (laterʳ q) → later λ { .force → later⁻¹ p ⊛ᵖ-cong q }

  ⊛ᵖ-cong-helper _ (return g) (laterˡ p) = λ where
    crash      crash       now        → laterˡ (p ⊛ᵖ-cong now)
    (return x) .(return x) now        → laterˡ (p ⊛ᵖ-cong now)
    (later x)  (later y)   q          → later λ { .force → p ⊛ᵖ-cong later⁻¹ q }
    _          crash       (laterˡ q) → laterˡ (p ⊛ᵖ-cong q)
    _          (return y)  (laterˡ q) → laterˡ (p ⊛ᵖ-cong q)
    crash      _           (laterʳ q) → later λ { .force → p ⊛ᵖ-cong q }
    (return x) _           (laterʳ q) → later λ { .force → p ⊛ᵖ-cong q }

  ⊛ᵖ-cong-helper (return f) _ (laterʳ p) = λ where
    crash      crash       now        → laterʳ (p ⊛ᵖ-cong now)
    (return x) .(return x) now        → laterʳ (p ⊛ᵖ-cong now)
    (later x)  (later y)   q          → later λ { .force → p ⊛ᵖ-cong later⁻¹ q }
    _          crash       (laterˡ q) → later λ { .force → p ⊛ᵖ-cong q }
    _          (return y)  (laterˡ q) → later λ { .force → p ⊛ᵖ-cong q }
    crash      _           (laterʳ q) → laterʳ (p ⊛ᵖ-cong q)
    (return x) _           (laterʳ q) → laterʳ (p ⊛ᵖ-cong q)

  ⊛ᵖ-cong-helper _ crash p@(laterˡ _) = λ _ _ _ → crash-lemma p _

  ⊛ᵖ-cong-helper crash _ p@(laterʳ _) =
    λ _ _ _ → symmetric (crash-lemma (symmetric p) _)

-- The monad laws.

left-identity :
  ∀ x (f : A → Delay-crash B ∞) →
  [ ∞ ] DC.return x DC.>>= f ∼ f x
left-identity x f =
  f x  ∎

right-identity :
  (x : Delay-crash A ∞) →
  [ ∞ ] x DC.>>= DC.return ∼ x
right-identity x =
  x DC.>>= DC.return        ∼⟨⟩
  x >>= maybe return crash  ∼⟨ (x ∎) DM.>>=-cong [ (λ _ → run fail ∎) , (λ x → run (M.return x) ∎) ] ⟩
  x >>= M.return            ∼⟨ DM.right-identity′ _ ⟩
  x                         ∎

associativity :
  (x : Delay-crash A ∞)
  (f : A → Delay-crash B ∞) (g : B → Delay-crash C ∞) →
  x DC.>>= (λ x → f x DC.>>= g) ∼ x DC.>>= f DC.>>= g
associativity x f g =
  x DC.>>= (λ x → f x DC.>>= g)                      ∼⟨⟩
  x >>= maybe (λ x → f x DC.>>= g) crash             ∼⟨ (x ∎) DM.>>=-cong [ (λ _ → run fail ∎) , (λ x → f x DC.>>= g ∎) ] ⟩
  x >>= (λ x → maybe f crash x >>= maybe g crash)    ∼⟨ DM.associativity′ x _ _ ⟩
  x >>= maybe f crash >>= maybe g crash              ∼⟨⟩
  x DC.>>= f DC.>>= g                                ∎

-- Use of _⟨$⟩_ does not affect the number of steps in the
-- computation.

steps-⟨$⟩ : Conat.[ i ] steps (f DC.⟨$⟩ x) ∼ steps x
steps-⟨$⟩ {f = f} {x = x} =
  steps (f DC.⟨$⟩ x)                                 Conat.≡⟨⟩∼
  steps (x DC.>>= DC.return ∘ f)                     Conat.≡⟨⟩∼
  steps (x >>= maybe (return ∘ f) crash)             Conat.∼⟨ steps-cong ((x ∎) DM.>>=-cong [ (λ _ → run fail ∎)
                                                                                            , (λ x → return (f x) ∎)
                                                                                            ]) ⟩
  steps (x >>= M.return ∘ maybe (just ∘ f) nothing)  Conat.∼⟨ DM.steps-⟨$⟩ _ ⟩
  steps x                                            Conat.∎∼

-- Sequential composition is an expansion of parallel composition.

⊛ˢ≳⊛ᵖ : [ i ] f ⊛ˢ x ≳ f ⊛ᵖ x
⊛ˢ≳⊛ᵖ {f = return f} {x = return x} = now
⊛ˢ≳⊛ᵖ {f = return f} {x = crash}    = now
⊛ˢ≳⊛ᵖ {f = return f} {x = later x}  = later λ { .force → ⊛ˢ≳⊛ᵖ }
⊛ˢ≳⊛ᵖ {f = crash}                   = now
⊛ˢ≳⊛ᵖ {f = later f}  {x = now x}    = later λ { .force → ⊛ˢ≳⊛ᵖ }
⊛ˢ≳⊛ᵖ {f = later f}  {x = later x}  = later λ { .force →
  (f .force DC.>>= λ f → later x DC.>>= λ x → DC.return (f x))  ≳⟨ ((f .force ∎) >>=-cong λ _ → laterˡ (_ ∎)) ⟩
  f .force ⊛ˢ x .force                                          ≳⟨ ⊛ˢ≳⊛ᵖ ⟩∼
  f .force ⊛ᵖ x .force                                          ∎ }

-- The computation crash is a left zero for _⊛ˢ_ and _⊛ᵖ_.

crash-⊛ˢ : [ i ] crash ⊛ˢ x ∼ (crash ⦂ Delay-crash B ∞)
crash-⊛ˢ = reflexive _

crash-⊛ᵖ : [ i ] crash ⊛ᵖ x ∼ (crash ⦂ Delay-crash B ∞)
crash-⊛ᵖ = reflexive _

-- The computation never is a left zero for _⊛ˢ_ and _⊛ᵖ_.

never-⊛ˢ :
  (x : Delay-crash A ∞) →
  [ i ] never ⊛ˢ x ∼ (never ⦂ Delay-crash B ∞)
never-⊛ˢ x = later λ { .force → never-⊛ˢ x }

never-⊛ᵖ :
  (x : Delay-crash A ∞) →
  [ i ] never ⊛ᵖ x ∼ (never ⦂ Delay-crash B ∞)
never-⊛ᵖ (now x)   = later λ { .force → never-⊛ᵖ (now x) }
never-⊛ᵖ (later x) = later λ { .force → never-⊛ᵖ _ }

-- The computation never is a right zero for _⊛ˢ_ and _⊛ᵖ_ if the left
-- computation does not crash.

⊛ˢ-never : ¬ f ≈ crash → [ i ] f ⊛ˢ never ∼ never
⊛ˢ-never {f = return _} p = later λ { .force → ⊛ˢ-never p }
⊛ˢ-never {f = later _}  p = later λ { .force → ⊛ˢ-never (p ∘ laterˡ) }
⊛ˢ-never {f = crash}    p = ⊥-elim (p (_ ∎))

⊛ᵖ-never : ¬ f ≈ crash → [ i ] f ⊛ᵖ never ∼ never
⊛ᵖ-never {f = return _} p = later λ { .force → ⊛ᵖ-never p }
⊛ᵖ-never {f = later _}  p = later λ { .force → ⊛ᵖ-never (p ∘ laterˡ) }
⊛ᵖ-never {f = crash}    p = ⊥-elim (p (_ ∎))

-- The computation crash is a right zero for _⊛ˢ_ and _⊛ᵖ_ (up to
-- expansion) if the left computation terminates.

⊛ˢ-crash : f ⇓ g → [ i ] f ⊛ˢ crash ≳ crash
⊛ˢ-crash (now {x = nothing}) = now
⊛ˢ-crash (now {x = just _})  = now
⊛ˢ-crash (laterʳ p)          = laterˡ (⊛ˢ-crash p)

⊛ᵖ-crash : f ⇓ g → [ i ] f ⊛ᵖ crash ≳ crash
⊛ᵖ-crash (now {x = nothing}) = now
⊛ᵖ-crash (now {x = just _})  = now
⊛ᵖ-crash (laterʳ p)          = laterˡ (⊛ᵖ-crash p)

-- The _⊛ᵖ_ and _⊛ˢ_ operators are not (kind of) commutative.

¬-⊛ᵖ-comm :
  ¬ (∀ {f : Delay-crash (A → B) ∞} {x} →
     f ⊛ᵖ x ≈ flip _$_ DC.⟨$⟩ x ⊛ᵖ f)
¬-⊛ᵖ-comm {A = A} {B = B} =
  (∀ {f : Delay-crash (A → B) ∞} {x} → f ⊛ᵖ x ≈ flip _$_ DC.⟨$⟩ x ⊛ᵖ f)  ↝⟨ (λ hyp → hyp {f = crash} {x = never}) ⟩
  crash ≈ flip _$_ DC.⟨$⟩ never ⊛ᵖ crash                                 ↝⟨ flip transitive-∞∼ʳ lemma ⟩
  crash ≈ never                                                          ↝⟨ now≉never ⟩□
  ⊥                                                                      □
  where
  lemma : [ i ] flip _$_ DC.⟨$⟩ never ⊛ᵖ crash ∼ never
  lemma = later λ { .force → lemma }

¬-⊛ˢ-comm :
  ¬ (∀ {f : Delay-crash (A → B) ∞} {x} →
     f ⊛ˢ x ≈ flip _$_ DC.⟨$⟩ x ⊛ˢ f)
¬-⊛ˢ-comm {A = A} {B = B} =
  (∀ {f : Delay-crash (A → B) ∞} {x} → f ⊛ˢ x ≈ flip _$_ DC.⟨$⟩ x ⊛ˢ f)  ↝⟨ (λ hyp {f x} →

      f ⊛ᵖ x                                                                   ≈⟨ symmetric (≳→ ⊛ˢ≳⊛ᵖ) ⟩
      f ⊛ˢ x                                                                   ≈⟨ hyp {f = f} {x = x} ⟩
      flip _$_ DC.⟨$⟩ x ⊛ˢ f                                                   ≳⟨ ⊛ˢ≳⊛ᵖ ⟩
      flip _$_ DC.⟨$⟩ x ⊛ᵖ f                                                   ∎) ⟩

  (∀ {f : Delay-crash (A → B) ∞} {x} → f ⊛ᵖ x ≈ flip _$_ DC.⟨$⟩ x ⊛ᵖ f)  ↝⟨ ¬-⊛ᵖ-comm ⟩□
  ⊥                                                                      □

------------------------------------------------------------------------
-- The instance declaration

-- A raw-monad instance.

instance

  raw-monad : Raw-monad (λ A → Delay-crash A i)
  raw-monad = raw-monad′
