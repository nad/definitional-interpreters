------------------------------------------------------------------------
-- A type soundness result
------------------------------------------------------------------------

open import Prelude
open import Prelude.Size

import Lambda.Syntax

module Lambda.Type-soundness
  {Name : Type}
  (open Lambda.Syntax Name)
  (open Closure Tm)
  (def : Name → Tm 1)
  (Σ : Name → Ty ∞ × Ty ∞)
  where

open import Equality.Propositional

open import Function-universe equality-with-J
open import Maybe equality-with-J
open import Monad equality-with-J
open import Vec.Data equality-with-J

open import Delay-monad.Always
open import Delay-monad.Bisimilarity

open import Lambda.Delay-crash
open import Lambda.Interpreter def

-- WF-Value, WF-Env and WF-MV specify when a
-- value/environment/potential value is well-formed with respect to a
-- given context (and type).

mutual

  data WF-Value : Ty ∞ → Value → Type where
    lam   : ∀ {n Γ σ τ} {t : Tm (1 + n)} {ρ} →
            Σ , force σ ∷ Γ ⊢ t ∈ force τ →
            WF-Env Γ ρ →
            WF-Value (σ ⇾′ τ) (lam t ρ)
    con   : ∀ b → WF-Value bool (con b)

  WF-Env : ∀ {n} → Ctxt n → Env n → Type
  WF-Env Γ ρ = ∀ x → WF-Value (index Γ x) (index ρ x)

WF-MV : Ty ∞ → Maybe Value → Type
WF-MV σ v = maybe (WF-Value σ) Prelude.⊥ v

-- Some "constructors" for WF-Env.

[]-wf : WF-Env [] []
[]-wf ()

infixr 5 _∷-wf_

_∷-wf_ : ∀ {n} {Γ : Ctxt n} {ρ σ v} →
         WF-Value σ v → WF-Env Γ ρ → WF-Env (σ ∷ Γ) (v ∷ ρ)
(v-wf ∷-wf ρ-wf) fzero    = v-wf
(v-wf ∷-wf ρ-wf) (fsuc x) = ρ-wf x

-- If we can prove □ ∞ (WF-MV σ) (run x), then x does not "go wrong".

does-not-go-wrong : ∀ {σ} {x : Delay-crash Value ∞} →
                    □ ∞ (WF-MV σ) x → ¬ x ≈ crash
does-not-go-wrong (now {x = nothing} ())
does-not-go-wrong (now {x = just x} x-wf) ()
does-not-go-wrong (later x-wf)            (laterˡ x↯) =
  does-not-go-wrong (force x-wf) x↯

-- A "constructor" for □ i ∘ WF-MV.

_>>=-wf_ :
  ∀ {i σ τ} {x : Delay-crash Value ∞} {f : Value → Delay-crash Value ∞} →
  □ i (WF-MV σ) x →
  (∀ {v} → WF-Value σ v → □ i (WF-MV τ) (f v)) →
  □ i (WF-MV τ) (x >>= f)
x-wf >>=-wf f-wf =
  □->>= x-wf λ { {nothing} ()
               ; {just v}  v-wf → f-wf v-wf
               }

-- Well-typed programs do not "go wrong".

module _ (def∈ : (f : Name) →
                 Σ , proj₁ (Σ f) ∷ [] ⊢ def f ∈ proj₂ (Σ f)) where

  mutual

    ⟦⟧-wf : ∀ {i n Γ} (t : Tm n) {σ} → Σ , Γ ⊢ t ∈ σ →
            ∀ {ρ} → WF-Env Γ ρ →
            □ i (WF-MV σ) (⟦ t ⟧ ρ)
    ⟦⟧-wf (var x)   var         ρ-wf = now (ρ-wf x)
    ⟦⟧-wf (lam t)   (lam t∈)    ρ-wf = now (lam t∈ ρ-wf)
    ⟦⟧-wf (t₁ · t₂) (t₁∈ · t₂∈) ρ-wf =
      ⟦⟧-wf t₁ t₁∈ ρ-wf >>=-wf λ f-wf →
      ⟦⟧-wf t₂ t₂∈ ρ-wf >>=-wf λ v-wf →
      ∙-wf f-wf v-wf
    ⟦⟧-wf (call f t) (call t∈) ρ-wf =
      ⟦⟧-wf t t∈ ρ-wf >>=-wf λ v-wf →
      ∙-wf {σ = λ { .force → proj₁ (Σ f) }}
           {τ = λ { .force → proj₂ (Σ f) }}
           (lam (def∈ f) []-wf) v-wf
    ⟦⟧-wf (con b)       con              ρ-wf = now (con b)
    ⟦⟧-wf (if t₁ t₂ t₃) (if t₁∈ t₂∈ t₃∈) ρ-wf =
      ⟦⟧-wf t₁ t₁∈ ρ-wf >>=-wf λ v₁-wf →
      ⟦if⟧-wf v₁-wf t₂∈ t₃∈ ρ-wf

    ∙-wf : ∀ {i σ τ f v} →
           WF-Value (σ ⇾′ τ) f → WF-Value (force σ) v →
           □ i (WF-MV (force τ)) (f ∙ v)
    ∙-wf (lam t₁∈ ρ₁-wf) v₂-wf =
      later λ { .force → ⟦⟧-wf _ t₁∈ (v₂-wf ∷-wf ρ₁-wf) }

    ⟦if⟧-wf : ∀ {i n Γ σ v} {t₂ t₃ : Tm n} →
              WF-Value bool v →
              Σ , Γ ⊢ t₂ ∈ σ →
              Σ , Γ ⊢ t₃ ∈ σ →
              ∀ {ρ} → WF-Env Γ ρ →
              □ i (WF-MV σ) (⟦if⟧ v t₂ t₃ ρ)
    ⟦if⟧-wf (con true)  t₂∈ t₃∈ ρ-wf = ⟦⟧-wf _ t₂∈ ρ-wf
    ⟦if⟧-wf (con false) t₂∈ t₃∈ ρ-wf = ⟦⟧-wf _ t₃∈ ρ-wf

  type-soundness : ∀ {t : Tm 0} {σ} →
                   Σ , [] ⊢ t ∈ σ → ¬ ⟦ t ⟧ [] ≈ crash
  type-soundness {t = t} {σ} =
    Σ , [] ⊢ t ∈ σ            ↝⟨ (λ t∈ → ⟦⟧-wf _ t∈ []-wf) ⟩
    □ ∞ (WF-MV σ) (⟦ t ⟧ [])  ↝⟨ does-not-go-wrong ⟩□
    ¬ ⟦ t ⟧ [] ≈ crash        □
