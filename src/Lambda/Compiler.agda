------------------------------------------------------------------------
-- A compiler
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Prelude

import Lambda.Syntax

module Lambda.Compiler
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm 1)
  where

open import Equality.Propositional
open import Tactic.By

open import List equality-with-J using (_++_)
open import Vec.Data equality-with-J

open import Lambda.Virtual-machine.Instructions Name

private
  module C = Closure Code
  module T = Closure Tm

-- The compiler takes an argument of type In-tail-context. The value
-- "true" means that the term is in a tail context. (I have based the
-- definition of tail context on the one in Section 4.5 of "Revised⁵
-- Report on the Algorithmic Language Scheme" by Abelson et al.) The
-- value "false" means that no such information is present.
--
-- The compiler compiles calls claimed to be in a tail context in a
-- special way.

In-tail-context : Set
In-tail-context = Bool

-- The compiler (which takes a code continuation).

comp : ∀ {n} → In-tail-context → Tm n → Code n → Code n
comp _     (var x)       c = var x ∷ c
comp _     (ƛ t)         c = clo (comp true t (ret ∷ [])) ∷ c
comp _     (t₁ · t₂)     c = comp false t₁ (comp false t₂ (app ∷ c))
comp true  (call f t)    c = comp false t (tcl f ∷ c)
comp false (call f t)    c = comp false t (cal f ∷ c)
comp _     (con b)       c = con b ∷ c
comp tc    (if t₁ t₂ t₃) c =
  comp false t₁ (bra (comp tc t₂ []) (comp tc t₃ []) ∷ c)

-- Compiler for named definitions.

comp-name : Name → Code 1
comp-name f = comp true (def f) (ret ∷ [])

-- Top-level compiler.
--
-- Note that the top-level expression is not assumed to be in a tail
-- context. Tail calls do not push a return frame on the stack. The
-- idea is to reuse an existing return frame, and the virtual machine
-- starts with an empty stack (which does not contain any return
-- frames).

comp₀ : Tm 0 → Code 0
comp₀ t = comp false t []

-- Environments and values can also be compiled.

mutual

  comp-env : ∀ {n} → T.Env n → C.Env n
  comp-env []      = []
  comp-env (v ∷ ρ) = comp-val v ∷ comp-env ρ

  comp-val : T.Value → C.Value
  comp-val (T.ƛ t ρ) = C.ƛ (comp true t (ret ∷ [])) (comp-env ρ)
  comp-val (T.con b) = C.con b

-- Indexing commutes with compilation.

comp-index : ∀ {n} (x : Fin n) (ρ : T.Env n) →
             index x (comp-env ρ) ≡ comp-val (index x ρ)
comp-index ()       []
comp-index fzero    (v ∷ ρ) = refl
comp-index (fsuc i) (v ∷ ρ) = comp-index i ρ

-- The function comp tc t commutes with _++ c₂.

comp-++ :
  ∀ {n} tc (t : Tm n) {c₁ c₂ : Code n} →
  comp tc t c₁ ++ c₂ ≡ comp tc t (c₁ ++ c₂)
comp-++ _     (var x)             = refl
comp-++ _     (ƛ t)               = refl
comp-++ true  (call f t)          = comp-++ _ t
comp-++ false (call f t)          = comp-++ _ t
comp-++ _     (con b)             = refl
comp-++ _     (if t₁ t₂ t₃)       = comp-++ _ t₁
comp-++ _     (t₁ · t₂) {c₁} {c₂} =
  comp false t₁ (comp false t₂ (app ∷ c₁)) ++ c₂  ≡⟨ comp-++ _ t₁ ⟩
  comp false t₁ (comp false t₂ (app ∷ c₁) ++ c₂)  ≡⟨ by (comp-++ _ t₂) ⟩∎
  comp false t₁ (comp false t₂ (app ∷ c₁ ++ c₂))  ∎
