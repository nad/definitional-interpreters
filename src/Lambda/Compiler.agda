------------------------------------------------------------------------
-- A compiler
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Prelude

import Lambda.Syntax

module Lambda.Compiler
  {Name : Set}
  (open Lambda.Syntax Name)
  (def : Name → Tm true 1)
  where

open import Equality.Propositional
open import Tactic.By

open import List equality-with-J using (_++_)
open import Vec.Data equality-with-J

open import Lambda.Virtual-machine.Instructions Name

private
  module C = Closure (const Code)
  module T = Closure Tm

-- The compiler (which takes a code continuation).

comp : ∀ {p n} → Tm p n → Code n → Code n
comp         (var x)       c = var x ∷ c
comp         (ƛ t)         c = clo (comp t (ret ∷ [])) ∷ c
comp         (t₁ · t₂)     c = comp t₁ (comp t₂ (app ∷ c))
comp {true}  (call f t)    c = comp t (tcl f ∷ c)
comp {false} (call f t)    c = comp t (cal f ∷ c)
comp         (con b)       c = con b ∷ c
comp         (if t₁ t₂ t₃) c = comp t₁ (bra (comp t₂ []) (comp t₃ []) ∷ c)

-- Compiler for named definitions.

comp-name : Name → Code 1
comp-name f = comp (def f) (ret ∷ [])

-- Environments and values can also be compiled.

mutual

  comp-env : ∀ {n} → T.Env n → C.Env n
  comp-env []      = []
  comp-env (v ∷ ρ) = comp-val v ∷ comp-env ρ

  comp-val : T.Value → C.Value
  comp-val (T.ƛ t ρ) = C.ƛ {p = true} (comp t (ret ∷ [])) (comp-env ρ)
  comp-val (T.con b) = C.con b

-- Indexing commutes with compilation.

comp-index : ∀ {n} (x : Fin n) (ρ : T.Env n) →
             index x (comp-env ρ) ≡ comp-val (index x ρ)
comp-index ()       []
comp-index fzero    (v ∷ ρ) = refl
comp-index (fsuc i) (v ∷ ρ) = comp-index i ρ

-- The function comp t commutes with _++ c₂.

comp-++ :
  ∀ {p n} (t : Tm p n) {c₁ c₂ : Code n} →
  comp t c₁ ++ c₂ ≡ comp t (c₁ ++ c₂)
comp-++         (var x)             = refl
comp-++         (ƛ t)               = refl
comp-++ {true}  (call f t)          = comp-++ t
comp-++ {false} (call f t)          = comp-++ t
comp-++         (con b)             = refl
comp-++         (if t₁ t₂ t₃)       = comp-++ t₁
comp-++         (t₁ · t₂) {c₁} {c₂} =
  comp t₁ (comp t₂ (app ∷ c₁)) ++ c₂  ≡⟨ comp-++ t₁ ⟩
  comp t₁ (comp t₂ (app ∷ c₁) ++ c₂)  ≡⟨ by (comp-++ t₂) ⟩∎
  comp t₁ (comp t₂ (app ∷ c₁ ++ c₂))  ∎
