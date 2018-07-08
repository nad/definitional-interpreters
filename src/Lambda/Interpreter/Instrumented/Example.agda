------------------------------------------------------------------------
-- An example: A non-terminating program that runs in bounded stack
-- space
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Interpreter.Instrumented.Example where

open import Colist as C
open import Conat hiding (pred)
open import Equality.Propositional as E using (refl)
open import Prelude

open import Function-universe E.equality-with-J hiding (id; _∘_)
open import Monad E.equality-with-J
open import Nat E.equality-with-J
open import Vec.Data E.equality-with-J

open import Delay-monad
open import Delay-monad.Bisimilarity as D using (later; force)

open import Upper-bounds

import Lambda.Delay-crash-colist as DCC
import Lambda.Interpreter
import Lambda.Interpreter.Instrumented

-- This module uses a name type with a single inhabitant, allowing
-- (and requiring) the definition and use of one named definition.

open import Lambda.Syntax ⊤

open Closure Tm

-- A term that calls itself repeatedly using a tail call.

loop : Tm 1
loop = call tt (con true)

def : ⊤ → Tm 1
def _ = loop

-- The two interpreters are instantiated with this definition.

module I = Lambda.Interpreter              def
module A = Lambda.Interpreter.Instrumented def

-- A top-level term to get things going.

go : Tm 0
go = call tt (con true)

-- The semantics of go is the non-terminating computation never.

go-loops : ∀ {i} → D.[ i ] I.⟦ go ⟧ [] ∼ never
go-loops = later λ { .force → go-loops }

-- Colists used to analyse the stack space usage of go.

loop-sizes : ∀ {i} → Colist ℕ i
loop-sizes = 1 ∷′ 2 ∷ λ { .force → loop-sizes }

go-sizes : Colist ℕ ∞
go-sizes = 0 ∷′ 1 ∷′ loop-sizes

-- When go is interpreted (starting with an empty stack) the stack
-- sizes that are encountered match the sizes in go-sizes.

stack-sizes-go∼go-sizes : ∀ {i} → C.[ i ] A.stack-sizes go ∼ go-sizes
stack-sizes-go∼go-sizes =
  A.numbers (A.⟦ go ⟧ [] false) 0                                   C.∼⟨ ∷∼∷′ ⟩
  0 ∷′ A.numbers (A.[ id , pred ] lam loop [] ∙ con true) 1         C.∼⟨ (refl ∷ λ { .force → ∷∼∷′ }) ⟩
  0 ∷′ 1 ∷′ A.numbers (A.⟦ loop ⟧ ρ true >>= tell pred ∘ return) 1  C.∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force → numbers-loop∼loop-sizes _ }}) ⟩
  0 ∷′ 1 ∷′ loop-sizes                                              C.∼⟨⟩
  go-sizes                                                          C.∎
  where
  ρ    = con true ∷ []
  tell = DCC.Delay-crash-colist.tell

  numbers-loop∼loop-sizes :
    ∀ {i} k → C.[ i ] A.numbers (A.⟦ loop ⟧ ρ true >>= k) 1 ∼ loop-sizes
  numbers-loop∼loop-sizes k =
    A.numbers (A.⟦ loop ⟧ ρ true >>= k) 1                                 C.∼⟨ ∷∼∷′ ⟩
    1 ∷′ A.numbers (A.[ pred , id ] lam loop [] ∙ con true >>= k) 2       C.∼⟨ (refl ∷ λ { .force → ∷∼∷′ }) ⟩
    1 ∷′ 2 ∷′ A.numbers (A.⟦ loop ⟧ ρ true >>= tell id ∘ return >>= k) 1  C.∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force → A.numbers-cong (
                                                                                DCC.symmetric (DCC.associativity (A.⟦ loop ⟧ ρ true) _ _)) }}) ⟩
    1 ∷′ 2 ∷′ A.numbers (A.⟦ loop ⟧ ρ true >>= tell id ∘ k) 1             C.∼⟨ (refl ∷ λ { .force → refl ∷ λ { .force →
                                                                                numbers-loop∼loop-sizes _ }}) ⟩
    1 ∷′ 2 ∷′ loop-sizes                                                  C.∼⟨ (refl ∷ λ { .force → C.symmetric-∼ ∷∼∷′ }) ⟩
    loop-sizes                                                            C.∎

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

go-bounded-stack : LUB (A.stack-sizes go) ⌜ 2 ⌝
go-bounded-stack =
  LUB-∼ (C.symmetric-∼ stack-sizes-go∼go-sizes)
        (Conat.reflexive-∼ _)
        lub-go-sizes-2
