------------------------------------------------------------------------
-- The syntax of, and a type system for, an untyped λ-calculus with
-- booleans and recursive unary function calls
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Syntax (Name : Set) where

open import Equality.Propositional
open import Prelude

open import Vec.Data equality-with-J

------------------------------------------------------------------------
-- Terms

-- Variables are represented using de Bruijn indices.

infixl 9 _·_

data Tm (n : ℕ) : Set where
  var  : Fin n → Tm n
  lam  : Tm (suc n) → Tm n
  _·_  : Tm n → Tm n → Tm n
  call : Name → Tm n → Tm n
  con  : Bool → Tm n
  if   : Tm n → Tm n → Tm n → Tm n

------------------------------------------------------------------------
-- Closure-based definition of values

-- Environments and values. Defined in a module parametrised by the
-- type of terms.

module Closure (Tm : ℕ → Set) where

  mutual

    -- Environments.

    Env : ℕ → Set
    Env n = Vec Value n

    -- Values. Lambdas are represented using closures, so values do
    -- not contain any free variables.

    data Value : Set where
      lam : ∀ {n} → Tm (suc n) → Env n → Value
      con : Bool → Value

------------------------------------------------------------------------
-- Type system

-- Recursive, simple types, defined coinductively.

infixr 8 _⇾_ _⇾′_

mutual

  data Ty (i : Size) : Set where
    bool : Ty i
    _⇾′_ : (σ τ : Ty′ i) → Ty i

  record Ty′ (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Ty j

open Ty′ public

-- Some type formers.

_⇾_ : ∀ {i} → Ty i → Ty i → Ty i
σ ⇾ τ = (λ { .force → σ }) ⇾′ (λ { .force → τ })

-- Contexts.

Ctxt : ℕ → Set
Ctxt n = Vec (Ty ∞) n

-- Type system.

infix 4 _,_⊢_∈_

data _,_⊢_∈_ (Σ : Name → Ty ∞ × Ty ∞) {n} (Γ : Ctxt n) :
             Tm n → Ty ∞ → Set where
  var  : ∀ {x} → Σ , Γ ⊢ var x ∈ index x Γ
  lam  : ∀ {t σ τ} →
         Σ , force σ ∷ Γ ⊢ t ∈ force τ →
         Σ , Γ ⊢ lam t ∈ σ ⇾′ τ
  _·_  : ∀ {t₁ t₂ σ τ} →
         Σ , Γ ⊢ t₁ ∈ σ ⇾′ τ →
         Σ , Γ ⊢ t₂ ∈ force σ →
         Σ , Γ ⊢ t₁ · t₂ ∈ force τ
  call : ∀ {f t} →
         Σ , Γ ⊢ t ∈ proj₁ (Σ f) →
         Σ , Γ ⊢ call f t ∈ proj₂ (Σ f)
  con  : ∀ {b} → Σ , Γ ⊢ con b ∈ bool
  if   : ∀ {t₁ t₂ t₃ σ} →
         Σ , Γ ⊢ t₁ ∈ bool →
         Σ , Γ ⊢ t₂ ∈ σ →
         Σ , Γ ⊢ t₃ ∈ σ →
         Σ , Γ ⊢ if t₁ t₂ t₃ ∈ σ

------------------------------------------------------------------------
-- Examples

-- A non-terminating term.

ω-body : Tm 1
ω-body = var fzero · var fzero

ω : Tm 0
ω = lam ω-body

Ω : Tm 0
Ω = ω · ω

-- Ω is well-typed.

Ω-well-typed : ∀ {Σ} (τ : Ty ∞) → Σ , [] ⊢ Ω ∈ τ
Ω-well-typed τ =
  _·_ {σ = σ} {τ = λ { .force → τ }} (lam (var · var)) (lam (var · var))
  where
  σ : ∀ {i} → Ty′ i
  force σ = σ ⇾′ λ { .force → τ }

-- A call-by-value fixpoint combinator.

Z : Tm 0
Z = lam (t · t)
  where
  t = lam (var (fsuc fzero) ·
         lam (var (fsuc fzero) · var (fsuc fzero) · var fzero))

-- This combinator is also well-typed.

Z-well-typed :
  ∀ {Σ} {σ τ : Ty ∞} →
  Σ , [] ⊢ Z ∈ ((σ ⇾ τ) ⇾ (σ ⇾ τ)) ⇾ (σ ⇾ τ)
Z-well-typed {σ = σ} {τ = τ} =
  lam (_·_ {σ = υ} {τ = λ { .force → σ ⇾ τ }}
           (lam (var · lam (var · var · var)))
           (lam (var · lam (var · var · var))))
  where
  υ : ∀ {i} → Ty′ i
  force υ = υ ⇾′ λ { .force → σ ⇾ τ }
