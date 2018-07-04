------------------------------------------------------------------------
-- A definitional interpreter that is annotated with information about
-- the stack size of the compiled program
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Prelude

import Lambda.Syntax

module Lambda.Interpreter.Annotated
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

open import Colist as C
open import Conat using (infinity)
import Equality.Propositional as E

open import Function-universe E.equality-with-J hiding (id; _∘_)
open import Maybe E.equality-with-J
open import Monad E.equality-with-J
open import Nat E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity as D using (later; force)
import Delay-monad.Monad

open import Upper-bounds

open import Lambda.Compiler def
open import Lambda.Delay-crash as DC
open import Lambda.Delay-crash-colist as DCC
import Lambda.Interpreter def as I

open Closure Tm

------------------------------------------------------------------------
-- The interpreter

-- Stack size change functions used in the interpreter's call case.

δ₁ : In-tail-context → ℕ → ℕ
δ₁ true  = pred
δ₁ false = id

δ₂ : In-tail-context → Maybe (ℕ → ℕ)
δ₂ true  = nothing
δ₂ false = just pred

infix 10 [_,_]_∙_

mutual

  -- The semantics annotated with stack size changes (functions of
  -- type ℕ → ℕ). The semantics takes an argument of type
  -- In-tail-context, so that it can produce annotations matching
  -- those produced by the compiler + virtual machine.

  ⟦_⟧ :
    ∀ {i n} →
    Tm n → Env n → In-tail-context →
    Delay-crash-colist (ℕ → ℕ) Value i
  ⟦ var x ⟧          ρ _  = tell suc (return (index x ρ))
  ⟦ ƛ t ⟧            ρ _  = tell suc (return (ƛ t ρ))
  ⟦ t₁ · t₂ ⟧        ρ _  = do v₁ ← ⟦ t₁ ⟧ ρ false
                               v₂ ← ⟦ t₂ ⟧ ρ false
                               [ pred , just pred ] v₁ ∙ v₂
  ⟦ call f t ⟧       ρ tc = do v ← ⟦ t ⟧ ρ false
                               [ δ₁ tc , δ₂ tc ] ƛ (def f) [] ∙ v
  ⟦ con b ⟧          ρ _  = tell suc (return (con b))
  ⟦ if t₁ t₂ t₃ ⟧    ρ tc = do v₁ ← ⟦ t₁ ⟧ ρ false
                               ⟦if⟧ v₁ t₂ t₃ ρ tc

  [_,_]_∙_ :
    ∀ {i} →
    (ℕ → ℕ) → Maybe (ℕ → ℕ) →
    Value → Value → Delay-crash-colist (ℕ → ℕ) Value i
  [ f₁ , f₂ ] ƛ t₁ ρ ∙ v₂ = later f₁ λ { .force → do
                              v ← ⟦ t₁ ⟧ (v₂ ∷ ρ) true
                              maybe-tell f₂ (return v) }
  [ _  , _  ] con _  ∙ _  = crash

  ⟦if⟧ :
    ∀ {i n} →
    Value → Tm n → Tm n → Env n → In-tail-context →
    Delay-crash-colist (ℕ → ℕ) Value i
  ⟦if⟧ (ƛ _ _)     _  _  _ _  = crash
  ⟦if⟧ (con true)  t₂ t₃ ρ tc = tell pred (⟦ t₂ ⟧ ρ tc)
  ⟦if⟧ (con false) t₂ t₃ ρ tc = tell pred (⟦ t₃ ⟧ ρ tc)

-- Applies the functions, one after another, to the starting value
-- (that is also the first value in the resulting list).

apply : ∀ {i} → Colist (ℕ → ℕ) i → (ℕ → Colist ℕ i)
apply = flip (scanl (flip _$_))

-- The natural numbers produced by a given computation, for a given
-- initial number.

numbers : ∀ {i A} → Delay-crash-colist (ℕ → ℕ) A i → ℕ → Colist ℕ i
numbers = apply ∘ colist

-- The stack sizes, for an empty initial stack, with false as the
-- In-tail-context argument.

stack-sizes : ∀ {i} → Tm 0 → Colist ℕ i
stack-sizes t = numbers (⟦ t ⟧ [] false) 0

------------------------------------------------------------------------
-- The semantics given above gives the same (unannotated) result as
-- the one in Lambda.Interpreter

mutual

  -- The annotated and the unannotated semantics yield strongly
  -- bisimilar results.

  ⟦⟧∼⟦⟧ :
    ∀ {i n} (t : Tm n) {ρ : Env n} tc →
    D.[ i ] run (delay-crash (⟦ t ⟧ ρ tc)) ∼ run (I.⟦ t ⟧ ρ)
  ⟦⟧∼⟦⟧ (var x) _ = D.reflexive _

  ⟦⟧∼⟦⟧ (ƛ t) _ = D.reflexive _

  ⟦⟧∼⟦⟧ (t₁ · t₂) {ρ} _ =
    run (delay-crash
           (⟦ t₁ ⟧ ρ false >>= λ v₁ → ⟦ t₂ ⟧ ρ false >>= λ v₂ →
            [ pred , just pred ] v₁ ∙ v₂))                       D.∼⟨ delay-crash->>= (⟦ t₁ ⟧ _ _) ⟩

    run (delay-crash (⟦ t₁ ⟧ ρ false) >>= λ v₁ →
         delay-crash (⟦ t₂ ⟧ ρ false >>= λ v₂ →
                      [ pred , just pred ] v₁ ∙ v₂))             D.∼⟨ ((run (delay-crash (⟦ t₁ ⟧ _ _)) D.∎) DC.>>=-cong λ _ →
                                                                       delay-crash->>= (⟦ t₂ ⟧ _ _)) ⟩
    run (delay-crash (⟦ t₁ ⟧ ρ false) >>= λ v₁ →
         delay-crash (⟦ t₂ ⟧ ρ false) >>= λ v₂ →
         delay-crash ([ pred , just pred ] v₁ ∙ v₂))             D.∼⟨ (⟦⟧∼⟦⟧ t₁ _ DC.>>=-cong λ v₁ → ⟦⟧∼⟦⟧ t₂ _ DC.>>=-cong λ _ → ∙∼∙ pred v₁) ⟩∼

    run (I.⟦ t₁ ⟧ ρ >>= λ v₁ → I.⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ I.∙ v₂)  D.∎

  ⟦⟧∼⟦⟧ (call f t) {ρ} tc =
    run (delay-crash (⟦ t ⟧ ρ false >>= λ v →
                      [ _ , _ ] ƛ (def f) [] ∙ v))      D.∼⟨ delay-crash->>= (⟦ t ⟧ _ _) ⟩

    run (delay-crash (⟦ t ⟧ ρ false) >>= λ v →
         delay-crash ([ δ₁ tc , _ ] ƛ (def f) [] ∙ v))  D.∼⟨ (⟦⟧∼⟦⟧ t _ DC.>>=-cong λ _ → ∙∼∙ (δ₁ tc) (ƛ (def f) [])) ⟩∼

    run (I.⟦ t ⟧ ρ >>= λ v → ƛ (def f) [] I.∙ v)        D.∎

  ⟦⟧∼⟦⟧ (con b) _ = D.reflexive _

  ⟦⟧∼⟦⟧ (if t₁ t₂ t₃) {ρ} tc =
    run (delay-crash (⟦ t₁ ⟧ ρ false >>= λ v₁ → ⟦if⟧ v₁ t₂ t₃ ρ tc))  D.∼⟨ delay-crash->>= (⟦ t₁ ⟧ _ _) ⟩

    run (delay-crash (⟦ t₁ ⟧ ρ false) >>= λ v₁ →
         delay-crash (⟦if⟧ v₁ t₂ t₃ ρ tc))                            D.∼⟨ (⟦⟧∼⟦⟧ t₁ _ DC.>>=-cong λ v₁ → ⟦if⟧∼⟦if⟧ v₁ t₂ t₃ _) ⟩∼

    run (I.⟦ t₁ ⟧ ρ >>= λ v₁ → I.⟦if⟧ v₁ t₂ t₃ ρ)                     D.∎

  ∙∼∙ :
    ∀ {i} f₁ {f₂} (v₁ {v₂} : Value) →
    D.[ i ] run (delay-crash ([ f₁ , f₂ ] v₁ ∙ v₂)) ∼ run (v₁ I.∙ v₂)
  ∙∼∙ f₁ {nothing} (ƛ t₁ ρ) {v₂} = later λ { .force →
    run (delay-crash (⟦ t₁ ⟧ (v₂ ∷ ρ) true >>= return))  D.∼⟨ delay-crash->>= (⟦ t₁ ⟧ _ _) ⟩
    run (delay-crash (⟦ t₁ ⟧ (v₂ ∷ ρ) true) >>= return)  D.∼⟨ DC.right-identity _ ⟩
    run (delay-crash (⟦ t₁ ⟧ (v₂ ∷ ρ) true))             D.∼⟨ ⟦⟧∼⟦⟧ t₁ _ ⟩∼
    run (I.⟦ t₁ ⟧ (v₂ ∷ ρ))                              D.∎ }

  ∙∼∙ f₁ {just f₂} (ƛ t₁ ρ) {v₂} = later λ { .force →
    run (delay-crash (⟦ t₁ ⟧ (v₂ ∷ ρ) true >>=
                      Delay-crash-colist.tell f₂ ∘ return))  D.∼⟨ delay-crash->>= (⟦ t₁ ⟧ _ _) ⟩

    run (delay-crash (⟦ t₁ ⟧ (v₂ ∷ ρ) true) >>=
         delay-crash ∘ Delay-crash-colist.tell f₂ ∘ return)  D.∼⟨ ((run (delay-crash (⟦ t₁ ⟧ _ _)) D.∎) DC.>>=-cong λ _ → D.reflexive _) ⟩

    run (delay-crash (⟦ t₁ ⟧ (v₂ ∷ ρ) true) >>= return)      D.∼⟨ DC.right-identity _ ⟩

    run (delay-crash (⟦ t₁ ⟧ (v₂ ∷ ρ) true))                 D.∼⟨ ⟦⟧∼⟦⟧ t₁ _ ⟩∼

    run (I.⟦ t₁ ⟧ (v₂ ∷ ρ))                                  D.∎ }

  ∙∼∙ _ (con _) = D.reflexive _

  ⟦if⟧∼⟦if⟧ :
    ∀ {i n} v₁ (t₂ t₃ : Tm n) {ρ} tc →
    D.[ i ] run (delay-crash (⟦if⟧ v₁ t₂ t₃ ρ tc)) ∼
            run (I.⟦if⟧ v₁ t₂ t₃ ρ)
  ⟦if⟧∼⟦if⟧ (ƛ _ _)     _  _  _ = D.reflexive _
  ⟦if⟧∼⟦if⟧ (con true)  t₂ t₃ _ = ⟦⟧∼⟦⟧ t₂ _
  ⟦if⟧∼⟦if⟧ (con false) t₂ t₃ _ = ⟦⟧∼⟦⟧ t₃ _

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

Ω-loops : ∀ {i} → D.[ i ] run (delay-crash (⟦ Ω ⟧ [] false)) ∼ never
Ω-loops =
  run (delay-crash (⟦ Ω ⟧ [] false))  D.∼⟨ ⟦⟧∼⟦⟧ Ω false ⟩
  run (I.⟦ Ω ⟧ [])                    D.∼⟨ I.Ω-loops ⟩
  never                               D.∎

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

-- The colist Ω-sizes n has the same upper bounds as nats-from n.

Ω-sizes≲≳nats-from : ∀ {i} n → [ i ] Ω-sizes n ≲≳ nats-from n
Ω-sizes≲≳nats-from n =
  Ω-sizes n                               ∼⟨ (cong₃ λ { .force → C.reflexive-∼ _ }) ⟩≲≳
  n ∷′ 1 + n ∷′ 2 + n ∷′ Ω-sizes (suc n)  ≲≳⟨ ⌊ cons′-≲≳D (λ { .force → ⌈
                                                consˡ-≲≳ (inj₁ (here ≤-refl)) (
                                                consˡ-≲≳ (inj₁ (there (here ≤-refl))) (
                                                Ω-sizes≲≳nats-from (suc n))) ⌉ }) ⌋≲≳ ⟩∼
  n ∷′ nats-from (suc n)                  C.∼⟨ C.symmetric-∼ ∷∼∷′ ⟩
  nats-from n                             C.∎

-- The least upper bound of Ω-sizes 0 is infinity.

lub-Ω-sizes-0-infinity :
  Least-upper-bound (Ω-sizes 0) infinity
lub-Ω-sizes-0-infinity =                    $⟨ lub-nats-infinity ⟩
  Least-upper-bound nats          infinity  ↝⟨ Least-upper-bound-∼ nats∼nats-from-0 (Conat.reflexive-∼ _) ⟩
  Least-upper-bound (nats-from 0) infinity  ↝⟨ Least-upper-bound-≲≳ (symmetric-≲≳ (Ω-sizes≲≳nats-from 0)) ⟩□
  Least-upper-bound (Ω-sizes 0)   infinity  □

-- When Ω is interpreted (starting with an empty stack) the stack
-- sizes that are encountered match the sizes in the colist Ω-sizes 0.

stack-sizes-Ω∼Ω-sizes-0 :
  ∀ {i} → C.[ i ] stack-sizes Ω ∼ Ω-sizes 0
stack-sizes-Ω∼Ω-sizes-0 =
  stack-sizes Ω                                                     C.∼⟨⟩

  numbers (⟦ Ω ⟧ [] false) 0                                        C.∼⟨ (E.refl ∷ λ { .force → E.refl ∷ λ { .force → E.refl ∷ λ { .force →
                                                                          C.reflexive-∼ _ }}}) ⟩
  0 ∷′ 1 ∷′ 2 ∷′ numbers (⟦ ω-body ⟧ (ƛ ω-body [] ∷ []) true >>=
                          Delay-crash-colist.tell pred ∘ return) 1  C.∼⟨ (cong₃ λ { .force → lemma 1 }) ⟩

  0 ∷′ 1 ∷′ 2 ∷′ Ω-sizes 1                                          C.∼⟨ (cong₃ λ { .force → C.reflexive-∼ _ }) ⟩

  Ω-sizes 0                                                         C.∎
  where
  lemma :
    ∀ {i} n {k : Value → Delay-crash-colist (ℕ → ℕ) Value ∞} →
    C.[ i ] numbers (⟦ ω-body ⟧ (ƛ ω-body [] ∷ []) true >>= k) n ∼
            Ω-sizes n
  lemma n {k} =
    numbers (⟦ ω-body ⟧ (ƛ ω-body [] ∷ []) true >>= k) n                 C.∼⟨⟩

    numbers (tell suc (tell suc
               ([ pred , just pred ] ƛ ω-body [] ∙ ƛ ω-body []) >>= k))
            n                                                            C.∼⟨ (E.refl ∷ λ { .force → E.refl ∷ λ { .force → E.refl ∷ λ { .force →
                                                                               C.reflexive-∼ _ }}}) ⟩
    n ∷′ 1 + n ∷′ 2 + n ∷′
    numbers (⟦ ω-body ⟧ (ƛ ω-body [] ∷ []) true >>=
             Delay-crash-colist.tell pred ∘ return >>= k) (1 + n)        C.∼⟨ (cong₃ λ { .force → C.symmetric-∼ $ numbers-cong $
                                                                               DCC.associativity (⟦ ω-body ⟧ (ƛ _ _ ∷ []) true) _ _ }) ⟩
    n ∷′ 1 + n ∷′ 2 + n ∷′
    numbers (⟦ ω-body ⟧ (ƛ ω-body [] ∷ []) true >>= λ v →
             Delay-crash-colist.tell pred (return v) >>= k) (1 + n)      C.∼⟨ (cong₃ λ { .force → lemma (1 + n) }) ⟩

    n ∷′ 1 + n ∷′ 2 + n ∷′ Ω-sizes (1 + n)                               C.∼⟨ (cong₃ λ { .force → C.reflexive-∼ _ }) ⟩

    Ω-sizes n                                                            C.∎

-- The computation Ω requires unbounded space.

Ω-requires-unbounded-space :
  Least-upper-bound (stack-sizes Ω) infinity
Ω-requires-unbounded-space =
  Least-upper-bound-∼
    (C.symmetric-∼ stack-sizes-Ω∼Ω-sizes-0)
    (Conat.reflexive-∼ _)
    lub-Ω-sizes-0-infinity
