------------------------------------------------------------------------
-- A definitional interpreter that is annotated with information about
-- the stack size of the compiled program
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Interpreter.Annotated where

open import Colist as C
open import Conat using (infinity)
import Equality.Propositional as E
open import Prelude

open import Function-universe E.equality-with-J hiding (_∘_)
open import Maybe E.equality-with-J
open import Monad E.equality-with-J
open import Nat E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity as D using (later; force)
import Delay-monad.Monad

open import Upper-bounds

open import Lambda.Delay-crash as DC
open import Lambda.Delay-crash-colist as DCC
import Lambda.Interpreter as I
open import Lambda.Syntax

open Closure Tm

------------------------------------------------------------------------
-- The interpreter

infix 10 _∙_

mutual

  -- The semantics annotated with stack size changes (functions of
  -- type ℕ → ℕ).

  ⟦_⟧⁺ : ∀ {i n} → Tm n → Env n → Delay-crash-colist (ℕ → ℕ) Value i
  ⟦ con i ⟧⁺   ρ = tell suc (return (con i))
  ⟦ var x ⟧⁺   ρ = tell suc (return (index x ρ))
  ⟦ ƛ t ⟧⁺     ρ = tell suc (return (ƛ t ρ))
  ⟦ t₁ · t₂ ⟧⁺ ρ = do v₁ ← ⟦ t₁ ⟧⁺ ρ
                      v₂ ← ⟦ t₂ ⟧⁺ ρ
                      v₁ ∙⁺ v₂

  _∙⁺_ : ∀ {i} → Value → Value → Delay-crash-colist (ℕ → ℕ) Value i
  con i  ∙⁺ v₂ = crash
  ƛ t₁ ρ ∙⁺ v₂ = later pred λ { .force → do
                   v ← ⟦ t₁ ⟧⁺ (v₂ ∷ ρ)
                   tell pred (return v) }

-- The unannotated semantics.

⟦_⟧ : ∀ {i n} → Tm n → Env n → Delay-crash Value i
⟦ t ⟧ ρ = delay-crash (⟦ t ⟧⁺ ρ)

_∙_ : ∀ {i} → Value → Value → Delay-crash Value i
t₁ ∙ t₂ = delay-crash (t₁ ∙⁺ t₂)

-- Applies the functions, one after another, to the starting value
-- (that is also the first value in the resulting list).

apply : ∀ {i} → Colist (ℕ → ℕ) i → (ℕ → Colist ℕ i)
apply = flip (scanl (flip _$_))

-- The natural numbers produced by a given computation, for a given
-- initial number.

numbers : ∀ {i A} → Delay-crash-colist (ℕ → ℕ) A i → ℕ → Colist ℕ i
numbers = apply ∘ colist

-- The stack sizes, for an empty initial stack.

stack-sizes : ∀ {i n} → Tm n → Env n → Colist ℕ i
stack-sizes t ρ = numbers (⟦ t ⟧⁺ ρ) 0

------------------------------------------------------------------------
-- The unannotated semantics given above matches the one in
-- Lambda.Interpreter

mutual

  -- The annotated and the unannotated semantics yield strongly
  -- bisimilar results.

  ⟦⟧∼⟦⟧ :
    ∀ {i n} (t : Tm n) (ρ : Env n) →
    D.[ i ] run (⟦ t ⟧ ρ) ∼ run (I.⟦ t ⟧ ρ)
  ⟦⟧∼⟦⟧ (con i)   ρ = D.reflexive _
  ⟦⟧∼⟦⟧ (var x)   ρ = D.reflexive _
  ⟦⟧∼⟦⟧ (ƛ t)     ρ = D.reflexive _
  ⟦⟧∼⟦⟧ (t₁ · t₂) ρ =
    run (delay-crash
           (⟦ t₁ ⟧⁺ ρ >>= λ v₁ → ⟦ t₂ ⟧⁺ ρ >>= λ v₂ → v₁ ∙⁺ v₂))  D.∼⟨ delay-crash->>= (⟦ t₁ ⟧⁺ _) ⟩

    run (⟦ t₁ ⟧ ρ >>= λ v₁ →
         delay-crash (⟦ t₂ ⟧⁺ ρ >>= λ v₂ → v₁ ∙⁺ v₂))             D.∼⟨ ((run (⟦ t₁ ⟧ _) D.∎) DC.>>=-cong λ _ → delay-crash->>= (⟦ t₂ ⟧⁺ _)) ⟩

    run (⟦ t₁ ⟧ ρ >>= λ v₁ → ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂)         D.∼⟨ (⟦⟧∼⟦⟧ t₁ _ DC.>>=-cong λ v₁ → ⟦⟧∼⟦⟧ t₂ _ DC.>>=-cong λ v₂ → ∙∼∙ v₁ v₂) ⟩∼

    run (I.⟦ t₁ ⟧ ρ >>= λ v₁ → I.⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ I.∙ v₂)   D.∎

  ∙∼∙ :
    ∀ {i} (v₁ v₂ : Value) →
    D.[ i ] run (v₁ ∙ v₂) ∼ run (v₁ I.∙ v₂)
  ∙∼∙ (con i)  v₂ = D.reflexive _
  ∙∼∙ (ƛ t₁ ρ) v₂ = later λ { .force →
    run (delay-crash (⟦ t₁ ⟧⁺ (v₂ ∷ ρ) >>=
                      Delay-crash-colist.tell pred ∘ return))  D.∼⟨ delay-crash->>= (⟦ t₁ ⟧⁺ _) ⟩

    run (⟦ t₁ ⟧ (v₂ ∷ ρ) >>=
         delay-crash ∘ Delay-crash-colist.tell pred ∘ return)  D.∼⟨ ((run (⟦ t₁ ⟧ _) D.∎) DC.>>=-cong λ _ → D.reflexive _) ⟩

    run (⟦ t₁ ⟧ (v₂ ∷ ρ) >>= return)                           D.∼⟨ DC.right-identity _ ⟩

    run (⟦ t₁ ⟧ (v₂ ∷ ρ))                                      D.∼⟨ ⟦⟧∼⟦⟧ t₁ _ ⟩∼

    run (I.⟦ t₁ ⟧ (v₂ ∷ ρ))                                    D.∎ }

------------------------------------------------------------------------
-- A lemma

-- The function numbers preserves strong bisimilarity.

numbers-cong :
  ∀ {i A} {x y : Delay-crash-colist (ℕ → ℕ) A ∞} {n} →
  DCC.[ i ] x ∼ y → C.[ i ] numbers x n ∼ numbers y n
numbers-cong = scanl-cong ∘ colist-cong

------------------------------------------------------------------------
-- An example: An analysis of the semantics of Ω

-- The semantics of Ω is the non-terminating computation never.

Ω-loops : ∀ {i} → D.[ i ] run (⟦ Ω ⟧ []) ∼ never
Ω-loops =
  run (⟦ Ω ⟧ [])    D.∼⟨ ⟦⟧∼⟦⟧ Ω _ ⟩
  run (I.⟦ Ω ⟧ [])  D.∼⟨ I.Ω-loops ⟩
  never             D.∎

-- A colist used in an analysis of the stack space usage of Ω.

Ω-sizes : ∀ {i} → ℕ → Colist ℕ i
Ω-sizes n =
  n ∷′ 1 + n ∷′ 2 + n ∷ λ { .force → Ω-sizes (1 + n) }

private

  -- An abbreviation.

  cong₃ :
    ∀ {i x y z} {xs ys : Colist′ ℕ ∞} →
    C.[ i ] force xs ∼′ force ys →
    C.[ i ] x ∷′ y ∷′ z ∷ xs ∼ x ∷′ y ∷′ z ∷ ys
  cong₃ p = E.refl ∷ λ { .force → E.refl ∷ λ { .force → E.refl ∷ p }}

-- The colist Ω-sizes n is an "upper bound" of nats-from n.

nats-from≲Ω-sizes : ∀ {i} n → [ i ] nats-from n ≲ Ω-sizes n
nats-from≲Ω-sizes n =
  nats-from n                             ∼⟨ ∷∼∷′ ⟩≲
  n ∷′ nats-from (suc n)                  ≲⟨ (cons′-≲ λ { .force → nats-from≲Ω-sizes (suc n) }) ⟩
  n ∷′ Ω-sizes (suc n)                    ≲⟨ (cons′-≲ λ { .force → consʳ-≲ (_ □≲) }) ⟩
  n ∷′ 1 + n ∷′ Ω-sizes (suc n)           ≲⟨ (cons′-≲ λ { .force → cons′-≲ λ { .force → consʳ-≲ (_ □≲) }}) ⟩
  n ∷′ 1 + n ∷′ 2 + n ∷′ Ω-sizes (suc n)  ∼⟨ (cong₃ λ { .force → C.reflexive-∼ _ }) ⟩≲
  Ω-sizes n                               □≲

-- The colist Ω-sizes n is a "lower bound" of nats-from n.

Ω-sizes≲nats-from : ∀ {i} n → [ i ] Ω-sizes n ≲ nats-from n
Ω-sizes≲nats-from n =
  Ω-sizes n                               ∼⟨ (cong₃ λ { .force → C.reflexive-∼ _ }) ⟩≲
  n ∷′ 1 + n ∷′ 2 + n ∷′ Ω-sizes (suc n)  ≲⟨ (cons′-≲ λ { .force → inj₂ (here ≤-refl) ∷ λ { .force → inj₂ (there (here ≤-refl)) ∷ λ { .force →
                                              Ω-sizes≲nats-from (suc n) }}}) ⟩
  n ∷′ nats-from (suc n)                  ∼⟨ C.symmetric-∼ ∷∼∷′ ⟩≲
  nats-from n                             □≲

-- The least upper bound of Ω-sizes 0 is infinity.

lub-Ω-sizes-0-infinity :
  Least-upper-bound (Ω-sizes 0) infinity
lub-Ω-sizes-0-infinity =                    $⟨ lub-nats-infinity ⟩
  Least-upper-bound nats          infinity  ↝⟨ Least-upper-bound-∼ nats∼nats-from-0 (Conat.reflexive-∼ _) ⟩
  Least-upper-bound (nats-from 0) infinity  ↝⟨ Least-upper-bound-≲≳ (nats-from≲Ω-sizes 0) (Ω-sizes≲nats-from 0) ⟩□
  Least-upper-bound (Ω-sizes 0)   infinity  □

-- When Ω is interpreted (starting with an empty stack) the stack
-- sizes that are encountered match the sizes in the colist Ω-sizes 0.

stack-sizes-Ω∼Ω-sizes-0 :
  ∀ {i} → C.[ i ] stack-sizes Ω [] ∼ Ω-sizes 0
stack-sizes-Ω∼Ω-sizes-0 =
  stack-sizes Ω []                                                  C.∼⟨⟩

  numbers (⟦ Ω ⟧⁺ []) 0                                             C.∼⟨ (E.refl ∷ λ { .force → E.refl ∷ λ { .force → E.refl ∷ λ { .force →
                                                                          C.reflexive-∼ _ }}}) ⟩
  0 ∷′ 1 ∷′ 2 ∷′ numbers (⟦ ω-body ⟧⁺ (ƛ ω-body [] ∷ []) >>=
                          Delay-crash-colist.tell pred ∘ return) 1  C.∼⟨ (cong₃ λ { .force → lemma 1 }) ⟩

  0 ∷′ 1 ∷′ 2 ∷′ Ω-sizes 1                                          C.∼⟨ (cong₃ λ { .force → C.reflexive-∼ _ }) ⟩

  Ω-sizes 0                                                         C.∎
  where
  lemma :
    ∀ {i} n {k : Value → Delay-crash-colist (ℕ → ℕ) Value ∞} →
    C.[ i ] numbers (⟦ ω-body ⟧⁺ (ƛ ω-body [] ∷ []) >>= k) n ∼ Ω-sizes n
  lemma n {k} =
    numbers (⟦ ω-body ⟧⁺ (ƛ ω-body [] ∷ []) >>= k) n                    C.∼⟨⟩

    numbers (tell suc (tell suc (ƛ ω-body [] ∙⁺ ƛ ω-body [])) >>= k) n  C.∼⟨ (E.refl ∷ λ { .force → E.refl ∷ λ { .force → E.refl ∷ λ { .force →
                                                                              C.reflexive-∼ _ }}}) ⟩
    n ∷′ 1 + n ∷′ 2 + n ∷′
    numbers (⟦ ω-body ⟧⁺ (ƛ ω-body [] ∷ []) >>=
             Delay-crash-colist.tell pred ∘ return >>= k) (1 + n)       C.∼⟨ (cong₃ λ { .force → C.symmetric-∼ $
                                                                              numbers-cong (DCC.associativity (⟦ ω-body ⟧⁺ (ƛ _ _ ∷ [])) _ _) }) ⟩
    n ∷′ 1 + n ∷′ 2 + n ∷′
    numbers (⟦ ω-body ⟧⁺ (ƛ ω-body [] ∷ []) >>= λ v →
             Delay-crash-colist.tell pred (return v) >>= k) (1 + n)     C.∼⟨ (cong₃ λ { .force → lemma (1 + n) }) ⟩

    n ∷′ 1 + n ∷′ 2 + n ∷′ Ω-sizes (1 + n)                              C.∼⟨ (cong₃ λ { .force → C.reflexive-∼ _ }) ⟩

    Ω-sizes n                                                           C.∎

-- The computation Ω requires unbounded space.

Ω-requires-unbounded-space :
  Least-upper-bound (stack-sizes Ω []) infinity
Ω-requires-unbounded-space =
  Least-upper-bound-∼
    (C.symmetric-∼ stack-sizes-Ω∼Ω-sizes-0)
    (Conat.reflexive-∼ _)
    lub-Ω-sizes-0-infinity
