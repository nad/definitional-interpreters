------------------------------------------------------------------------
-- The syntax of, and a type system for, an untyped λ-calculus with
-- booleans and recursive unary function calls
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Lambda.Syntax (Name : Set) where

open import Equality.Propositional
open import Prelude

open import Maybe equality-with-J
open import Vec.Data equality-with-J

------------------------------------------------------------------------
-- Terms

-- The term type is parametrised by In-tail-context. The value "true"
-- means that the term is in a tail context. (I have based the
-- definition of tail context on the one in Section 4.5 of "Revised⁵
-- Report on the Algorithmic Language Scheme" by Abelson et al.) The
-- value "false" means that no such information is present.
--
-- The compiler compiles calls known to be in a tail context in a
-- special way.

In-tail-context : Set
In-tail-context = Bool

-- Variables are represented using de Bruijn indices.

infixl 9 _·_

data Tm (p : In-tail-context) (n : ℕ) : Set where
  var  : (x : Fin n) → Tm p n
  ƛ    : Tm true (suc n) → Tm p n
  _·_  : Tm false n → Tm false n → Tm p n
  call : (f : Name) → Tm false n → Tm p n
  con  : Bool → Tm p n
  if   : Tm false n → Tm p n → Tm p n → Tm p n

------------------------------------------------------------------------
-- Closure-based definition of values

-- Environments and values. Defined in a module parametrised by the
-- type of terms.

module Closure (Tm : In-tail-context → ℕ → Set) where

  mutual

    -- Environments.

    Env : ℕ → Set
    Env n = Vec Value n

    -- Values. Lambdas are represented using closures, so values do
    -- not contain any free variables.

    data Value : Set where
      ƛ   : ∀ {p n} (t : Tm p (suc n)) (ρ : Env n) → Value
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

data _,_⊢_∈_ (Σ : Name → Ty ∞ × Ty ∞) {p n} (Γ : Ctxt n) :
             Tm p n → Ty ∞ → Set where
  var  : ∀ {x} → Σ , Γ ⊢ var x ∈ index x Γ
  ƛ    : ∀ {t σ τ} →
         Σ , force σ ∷ Γ ⊢ t ∈ force τ →
         Σ , Γ ⊢ ƛ t ∈ σ ⇾′ τ
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

ω-body : Tm true 1
ω-body = var fzero · var fzero

ω : Tm false 0
ω = ƛ ω-body

Ω : Tm true 0
Ω = ω · ω

-- Ω is well-typed.

Ω-well-typed : ∀ {Σ} (τ : Ty ∞) → Σ , [] ⊢ Ω ∈ τ
Ω-well-typed τ =
  _·_ {σ = σ} {τ = λ { .force → τ }} (ƛ (var · var)) (ƛ (var · var))
  where
  σ : ∀ {i} → Ty′ i
  force σ = σ ⇾′ λ { .force → τ }

-- A call-by-value fixpoint combinator.

Z : Tm true 0
Z = ƛ (t · t)
  where
  t = ƛ (var (fsuc fzero) ·
         ƛ (var (fsuc fzero) · var (fsuc fzero) · var fzero))

-- This combinator is also well-typed.

Z-well-typed :
  ∀ {Σ} {σ τ : Ty ∞} →
  Σ , [] ⊢ Z ∈ ((σ ⇾ τ) ⇾ (σ ⇾ τ)) ⇾ (σ ⇾ τ)
Z-well-typed {σ = σ} {τ = τ} =
  ƛ (_·_ {σ = υ} {τ = λ { .force → σ ⇾ τ }}
         (ƛ (var · ƛ (var · var · var)))
         (ƛ (var · ƛ (var · var · var))))
  where
  υ : ∀ {i} → Ty′ i
  force υ = υ ⇾′ λ { .force → σ ⇾ τ }
