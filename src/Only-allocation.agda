------------------------------------------------------------------------
-- The syntax of a toy programming language that only supports
-- allocation and deallocation of memory
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Only-allocation where

open import Colist
open import Prelude

------------------------------------------------------------------------
-- Programs

-- Statements.

data Stmt : Set where
  allocate deallocate : Stmt

-- Programs are potentially infinite sequences of statements.

Program : Size → Set
Program i = Colist Stmt i

------------------------------------------------------------------------
-- Some examples

-- A program that runs in constant space.

constant-space : ∀ {i} → Program i
constant-space = allocate ∷′ deallocate ∷ λ { .force → constant-space }

-- Another program that runs in constant space.

constant-space₂ : ∀ {i} → Program i
constant-space₂ =
  allocate   ∷′ allocate   ∷′
  deallocate ∷′ deallocate ∷ λ { .force → constant-space₂ }

-- A program that does not run in bounded space.

unbounded-space : ∀ {i} → Program i
unbounded-space = allocate ∷ λ { .force → unbounded-space }
