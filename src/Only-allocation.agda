------------------------------------------------------------------------
-- The syntax of a toy programming language that only supports
-- allocation and deallocation of memory
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Only-allocation where

open import Colist
open import Prelude

------------------------------------------------------------------------
-- Programs

-- Statements.

data Stmt : Set where
  alloc dealloc : Stmt

-- Programs are potentially infinite sequences of statements.

Program : Size → Set
Program i = Colist Stmt i

------------------------------------------------------------------------
-- Some examples

-- A program that runs in bounded space.

bounded : ∀ {i} → Program i
bounded = alloc ∷′ dealloc ∷ λ { .force → bounded }

-- Another program that runs in bounded space.

bounded₂ : ∀ {i} → Program i
bounded₂ =
  alloc   ∷′ alloc   ∷′
  dealloc ∷′ dealloc ∷ λ { .force → bounded₂ }

-- A program that does not run in bounded space.

unbounded : ∀ {i} → Program i
unbounded = alloc ∷ λ { .force → unbounded }
