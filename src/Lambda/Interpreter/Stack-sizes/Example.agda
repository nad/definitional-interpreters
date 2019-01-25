------------------------------------------------------------------------
-- An example: A non-terminating program that runs in bounded stack
-- space
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Lambda.Interpreter.Stack-sizes.Example where

open import Colist as C
open import Conat hiding (pred)
open import Equality.Propositional as E using (refl)
open import Prelude
open import Size

open import Function-universe E.equality-with-J hiding (id; _∘_)
open import Monad E.equality-with-J
open import Nat E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity as D using (later; force)

open import Upper-bounds

import Lambda.Delay-crash-trace as DCT
import Lambda.Interpreter
import Lambda.Interpreter.Stack-sizes

open DCT.Delay-crash-trace

-- This module uses a name type with a single inhabitant, allowing
-- (and requiring) the definition and use of one named definition.

open import Lambda.Syntax ⊤

open Closure Tm

-- A definition that calls itself repeatedly using a tail call.

def : ⊤ → Tm 1
def tt = call tt (con true)

-- The two interpreters are instantiated with this definition.

open Lambda.Interpreter def
module I = Lambda.Interpreter.Stack-sizes def

-- A top-level term to get things going.

go : Tm 0
go = call tt (con true)

-- The semantics of go is the non-terminating computation never.

go-loops : ∀ {i} → D.[ i ] ⟦ go ⟧ [] ∼ never
go-loops = later λ { .force → go-loops }

-- Colists used to analyse the stack space usage of go.

loop-sizes : ∀ {i} → Colist ℕ i
loop-sizes = 1 ∷′ 2 ∷ λ { .force → loop-sizes }

go-sizes : Colist ℕ ∞
go-sizes = 0 ∷′ 1 ∷′ loop-sizes

-- When go is interpreted (starting with an empty stack) the stack
-- sizes that are encountered match the sizes in go-sizes.

stack-sizes-go∼go-sizes : ∀ {i} → C.[ i ] I.stack-sizes go ∼ go-sizes
stack-sizes-go∼go-sizes =
  I.numbers (I.⟦ go ⟧ [] false) 0                                     C.∼⟨ ∷∼∷′ ⟩
  0 ∷′ I.numbers (I.[ id , pred ] lam (def tt) [] ∙ con true) 1       C.∼⟨ (refl ∷ λ { .force → ∷∼∷′ }) ⟩
  0 ∷′ 1 ∷′ I.numbers (I.⟦ def tt ⟧ ρ true >>= tell pred ∘ return) 1  C.∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force → numbers-loop∼loop-sizes _ }}) ⟩
  0 ∷′ 1 ∷′ loop-sizes                                                C.∼⟨⟩
  go-sizes                                                            C.∎
  where
  ρ = con true ∷ []

  numbers-loop∼loop-sizes :
    ∀ {i} k → C.[ i ] I.numbers (I.⟦ def tt ⟧ ρ true >>= k) 1 ∼ loop-sizes
  numbers-loop∼loop-sizes k =
    I.numbers (I.⟦ def tt ⟧ ρ true >>= k) 1                                 C.∼⟨ ∷∼∷′ ⟩
    1 ∷′ I.numbers (I.[ pred , id ] lam (def tt) [] ∙ con true >>= k) 2     C.∼⟨ (refl ∷ λ { .force → ∷∼∷′ }) ⟩
    1 ∷′ 2 ∷′ I.numbers (I.⟦ def tt ⟧ ρ true >>= tell id ∘ return >>= k) 1  C.∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force → I.numbers-cong (
                                                                                  DCT.symmetric (DCT.associativity (I.⟦ def tt ⟧ ρ true) _ _)) }}) ⟩
    1 ∷′ 2 ∷′ I.numbers (I.⟦ def tt ⟧ ρ true >>= tell id ∘ k) 1             C.∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force →
                                                                                  numbers-loop∼loop-sizes _ }}) ⟩
    1 ∷′ 2 ∷′ loop-sizes                                                    C.∼⟨ (refl ∷ λ { .force → C.symmetric-∼ ∷∼∷′ }) ⟩
    loop-sizes                                                              C.∎

-- The least upper bound of go-sizes is 2.

lub-go-sizes-2 : LUB go-sizes ⌜ 2 ⌝
lub-go-sizes-2 =
  lub-∷ʳ zero (lub-∷ʳ 1≤2 lub-loop-sizes-2)
  where
  1≤2 = suc λ { .force → zero }

  2∷[] = λ { .force → 2 ∷′ [] }

  cycle-1-2∷[]∼loop-sizes :
    ∀ {i} → C.[ i ] cycle 1 2∷[] ∼ loop-sizes
  cycle-1-2∷[]∼loop-sizes =
    refl ∷ λ { .force → refl ∷ λ { .force → cycle-1-2∷[]∼loop-sizes }}

  lub-loop-sizes-2 : LUB loop-sizes ⌜ 2 ⌝
  lub-loop-sizes-2 =          $⟨ lub-∷ʳ 1≤2 (lub-∷ˡ zero lub-[]) ⟩
    LUB (1 ∷ 2∷[]) ⌜ 2 ⌝      ↝⟨ lub-cycle ⟩
    LUB (cycle 1 2∷[]) ⌜ 2 ⌝  ↝⟨ LUB-∼ cycle-1-2∷[]∼loop-sizes (Conat.reflexive-∼ _) ⟩□
    LUB loop-sizes ⌜ 2 ⌝      □

-- The maximum stack size encountered when running go (starting with
-- an empty stack) is 2.

go-bounded-stack : LUB (I.stack-sizes go) ⌜ 2 ⌝
go-bounded-stack =
  LUB-∼ (C.symmetric-∼ stack-sizes-go∼go-sizes)
        (Conat.reflexive-∼ _)
        lub-go-sizes-2
