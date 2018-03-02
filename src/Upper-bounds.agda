------------------------------------------------------------------------
-- Upper bounds of colists containing natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Upper-bounds where

open import Colist
open import Conat hiding (pred) renaming (_+_ to _⊕_; _∸_ to _⊖_)
open import Equality.Propositional
open import Omniscience
open import Prelude

open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import Nat equality-with-J as Nat using (_≤_; _<_; pred)

------------------------------------------------------------------------
-- Upper bounds

-- [ ∞ ] ms ⊑ n means that n is an upper bound of every number in ms.

infix 4 [_]_⊑_

[_]_⊑_ : Size → Colist ℕ ∞ → Conat ∞ → Set
[ i ] ms ⊑ n = □ i (λ m → [ ∞ ] ⌜ m ⌝ ≤ n) ms

-- The conatural number infinity is always an upper bound.

infix 4 _⊑infinity

_⊑infinity : ∀ {i} ns → [ i ] ns ⊑ infinity
_⊑infinity = □-replicate (_≤infinity ∘ ⌜_⌝)

-- A form of transitivity.

transitive-⊑≤ :
  ∀ {i ms n o} → [ i ] ms ⊑ n → [ ∞ ] n ≤ o → [ i ] ms ⊑ o
transitive-⊑≤ p q = □-map (flip transitive-≤ q) p

-- Another form of transitivity.

transitive-◇≤⊑ :
  ∀ {m ns o} → ◇ (m ≤_) ns → [ ∞ ] ns ⊑ o → [ ∞ ] ⌜ m ⌝ ≤ o
transitive-◇≤⊑ {m} {ns} {o} = curry (
  ◇ (m ≤_) ns × [ ∞ ] ns ⊑ o         ↝⟨ Σ-map id swap ∘ uncurry □◇-witness ∘ swap ⟩
  (∃ λ n → m ≤ n × [ ∞ ] ⌜ n ⌝ ≤ o)  ↝⟨ (λ { (_ , m≤n , n≤o) → transitive-≤ (⌜⌝-mono m≤n) n≤o }) ⟩□
  [ ∞ ] ⌜ m ⌝ ≤ o                    □)

-- If m is an upper bound of ms, and no natural number is an upper
-- bound, then m is bisimilar to infinity.

no-finite→infinite :
  ∀ {m ms} →
  (∀ n → ¬ [ ∞ ] ms ⊑ ⌜ n ⌝) →
  [ ∞ ] ms ⊑ m →
  Conat.[ ∞ ] m ∼ infinity
no-finite→infinite {m} {ms} no-finite =
  [ ∞ ] ms ⊑ m               ↝⟨ (λ ms⊑n → uncurry λ n →

      Conat.[ ∞ ] m ∼ ⌜ n ⌝        ↝⟨ ∼→≤ ⟩
      [ ∞ ] m ≤ ⌜ n ⌝              ↝⟨ transitive-⊑≤ ms⊑n ⟩
      [ ∞ ] ms ⊑ ⌜ n ⌝             ↝⟨ no-finite n ⟩□
      ⊥                            □) ⟩

  Infinite m                 ↝⟨ Infinite→∼infinity ⟩□
  Conat.[ ∞ ] m ∼ infinity   □

------------------------------------------------------------------------
-- Least upper bounds

-- The least upper bound of a colist of natural numbers.

Least-upper-bound : Colist ℕ ∞ → Conat ∞ → Set
Least-upper-bound ns n =
  [ ∞ ] ns ⊑ n
    ×
  (∀ n′ → [ ∞ ] ns ⊑ n′ → [ ∞ ] n ≤ n′)

-- Least upper bounds are unique.

lub-unique :
  ∀ {ns n₁ n₂ i} →
  Least-upper-bound ns n₁ → Least-upper-bound ns n₂ →
  Conat.[ i ] n₁ ∼ n₂
lub-unique (lub₁₁ , lub₁₂) (lub₂₁ , lub₂₂) =
  antisymmetric-≤ (lub₁₂ _ lub₂₁) (lub₂₂ _ lub₁₁)

-- If LPO holds, then the least upper bound of a colist of natural
-- numbers can be determined.
--
-- See also Unbounded-space.lub→wlpo.

lpo→lub : LPO → (∀ ms → ∃ λ n → Least-upper-bound ms n)
lpo→lub lpo = λ ms → lub 0 ms , upper-bound 0 ms , least 0 ms
  where
  -- Some simple lemmas.

  <→1≤∸ : ∀ {m n} → m < n → [ ∞ ] ⌜ 1 ⌝ ≤ ⌜ n ∸ m ⌝
  <→1≤∸ {m} {n} =
    m < n                    ↔⟨⟩
    1 + m ≤ n                ↝⟨ Nat._∸-mono Nat.≤-refl {n = m} ⟩
    1 + m ∸ m ≤ n ∸ m        ↝⟨ subst (_≤ n ∸ m) (Nat.+∸≡ m) ⟩
    1 ≤ n ∸ m                ↝⟨ ⌜⌝-mono ⟩□
    [ ∞ ] ⌜ 1 ⌝ ≤ ⌜ n ∸ m ⌝  □

  ≤→∸≤0 : ∀ {m n} → [ ∞ ] ⌜ m ⌝ ≤ ⌜ n ⌝ → [ ∞ ] ⌜ m ∸ n ⌝ ≤ zero
  ≤→∸≤0 {m} {n} =
    [ ∞ ] ⌜ m ⌝ ≤ ⌜ n ⌝     ↝⟨ ⌜⌝-mono⁻¹ ⟩
    (m ≤ n)                 ↝⟨ Nat._∸-mono Nat.≤-refl {n = n} ⟩
    (m ∸ n ≤ n ∸ n)         ↝⟨ subst (m ∸ n ≤_) (Nat.∸≡0 n) ⟩
    (m ∸ n ≤ zero)          ↝⟨ ⌜⌝-mono ⟩□
    [ ∞ ] ⌜ m ∸ n ⌝ ≤ zero  □

  ∸+∸∼ : ∀ {m n o} →
         m < n →
         Conat.[ ∞ ] ⌜ n ∸ m ⌝ ⊕ (o ⊖ n) ∼ (o ⊖ n ⊕ ⌜ n ⌝) ⊖ m
  ∸+∸∼ {m} {n} {o} m<n =
    ⌜ n ∸ m ⌝ ⊕ (o ⊖ n)    ∼⟨ +-comm ⌜ _ ∸ m ⌝ ⟩
    (o ⊖ n) ⊕ ⌜ n ∸ m ⌝    ∼⟨ (_ ∎∼) +-cong ⌜⌝-∸ _ m ⟩
    (o ⊖ n) ⊕ (⌜ n ⌝ ⊖ m)  ∼⟨ Conat.symmetric-∼ (+-∸-assoc (⌜⌝-mono (Nat.<→≤ m<n))) ⟩∎
    (o ⊖ n ⊕ ⌜ n ⌝) ⊖ m    ∎∼

  -- The boolean next-> d ms n is true if the n-th number (counting
  -- from zero) of ms is the first one which is greater than d.

  next-> : ℕ → Colist ℕ ∞ → ℕ → Bool
  next-> _ []       _       = false
  next-> d (m ∷ ms) n       with Nat.≤⊎> m d
  next-> d (m ∷ ms) zero    | inj₁ _ = false
  next-> d (m ∷ ms) (suc n) | inj₁ _ = next-> d (force ms) n
  next-> d (m ∷ ms) zero    | inj₂ _ = true
  next-> d (m ∷ ms) (suc _) | inj₂ _ = false

  -- The number lub d ms is the least upper bound of ms minus d.

  lub : ∀ {i} → ℕ → Colist ℕ ∞ → Conat i
  lub d = λ ms → case lpo (next-> d ms) of λ where
      (inj₁ _)           → zero
      (inj₂ (n , ≡true)) → step ms n ≡true
    module M where
    step : ∀ {i} ms n → next-> d ms n ≡ true → Conat i
    step []       _       ()
    step (m ∷ ms) n       ≡true with Nat.≤⊎> m d
    step (m ∷ ms) zero    ()    | inj₁ _
    step (m ∷ ms) (suc _) ()    | inj₂ _
    step (m ∷ ms) (suc n) ≡true | inj₁ _ = step (force ms) n ≡true
    step (m ∷ ms) zero    _     | inj₂ m>d =
      <→1≤∸ m>d ⁺+ λ { .force → lub m (force ms) }

  -- The number lub d ms is an upper bound of ms with d subtracted
  -- from every element.

  upper-bound :
    ∀ {i} d ms →
    □ i (λ m → [ ∞ ] ⌜ m ∸ d ⌝ ≤ lub d ms) ms
  upper-bound d ms with lpo (next-> d ms)
  ... | inj₁ ≡false = □-map ≤→∸≤0 (step ms ≡false)
    where
    step : ∀ {i} ms (≡false : ∀ n → next-> d ms n ≡ false) →
           [ i ] ms ⊑ ⌜ d ⌝
    step []       _      = []
    step (m ∷ ms) ≡false with Nat.≤⊎> m d
    step (m ∷ ms) ≡false | inj₁ m≤d = ⌜⌝-mono m≤d ∷ λ { .force →
                                      step (force ms) (≡false ∘ suc) }
    step (m ∷ ms) ≡false | inj₂ _   =
      ⊥-elim (Bool.true≢false (≡false 0))

  ... | inj₂ (n , ≡true) = step ms n ≡true
    where
    step : ∀ {i} ms n (≡true : next-> d ms n ≡ true) →
           □ i (λ m → [ ∞ ] ⌜ m ∸ d ⌝ ≤ M.step d ms n ≡true) ms
    step []       _       ()
    step (m ∷ ms) n       ≡true with Nat.≤⊎> m d
    step (m ∷ ms) zero    ()    | inj₁ _
    step (m ∷ ms) (suc _) ()    | inj₂ _
    step (m ∷ ms) (suc n) ≡true | inj₁ m≤d =
      (⌜ m ∸ d ⌝                    ≤⟨ ≤→∸≤0 (⌜⌝-mono m≤d) ⟩
       zero                         ≤⟨ zero ⟩∎
       M.step d (force ms) n ≡true  ∎≤)
        ∷
      λ { .force → step (force ms) n ≡true }

    step (m ∷ ms) zero ≡true | inj₂ m>d =
      lemma₁ ∷ λ { .force →
      □-map (lemma₃ _) (upper-bound m (force ms)) }
      where
      o = lub m (force ms)

      lemma₁ =
        ⌜ m ∸ d ⌝       ≤⟨ m≤m+n ⟩
        ⌜ m ∸ d ⌝ ⊕ o   ∼⟨ Conat.symmetric-∼ (⁺+∼+ _ _) ⟩≤
        <→1≤∸ m>d ⁺+ _  ∎≤

      lemma₂ = λ n →
        ⌜ n ∸ d ⌝                ∼⟨ ⌜⌝-∸ _ d ⟩≤
        ⌜ n ⌝ ⊖ d                ≤⟨ ≤∸+ _ m ∸-mono Nat.≤-refl {n = d} ⟩
        (⌜ n ⌝ ⊖ m ⊕ ⌜ m ⌝) ⊖ d  ∼⟨ Conat.symmetric-∼ (∸+∸∼ m>d) ⟩≤
        ⌜ m ∸ d ⌝ ⊕ (⌜ n ⌝ ⊖ m)  ∼⟨ (_ ∎∼) +-cong Conat.symmetric-∼ (⌜⌝-∸ _ m) ⟩≤
        ⌜ m ∸ d ⌝ ⊕ ⌜ n ∸ m ⌝    ∎≤

      lemma₃ = λ n →
        [ ∞ ] ⌜ n ∸ m ⌝ ≤ o                          ↝⟨ reflexive-≤ _ +-mono_ ⟩
        [ ∞ ] ⌜ m ∸ d ⌝ ⊕ ⌜ n ∸ m ⌝ ≤ ⌜ m ∸ d ⌝ ⊕ o  ↝⟨ transitive-≤ (lemma₂ _) ⟩
        [ ∞ ] ⌜ n ∸ d ⌝ ≤ ⌜ m ∸ d ⌝ ⊕ o              ↝⟨ flip transitive-≤ (∼→≤ (Conat.symmetric-∼ (⁺+∼+ _ _))) ⟩□
        [ ∞ ] ⌜ n ∸ d ⌝ ≤ <→1≤∸ m>d ⁺+ _             □

  -- The number lub d ms is less than or equal to every number that is
  -- an upper bound of ms, minus d.

  least :
    ∀ {i} d ms ub →
    □ ∞ (λ m → [ ∞ ] ⌜ m ⌝ ≤ ub) ms →
    [ i ] lub d ms ≤ ub ⊖ d
  least d ms ub with lpo (next-> d ms)
  ... | inj₁ _           = λ _ → zero
  ... | inj₂ (n , ≡true) = step ms n ≡true ub
    where
    step : ∀ {i} ms n (≡true : next-> d ms n ≡ true) ub →
           □ ∞ (λ m → [ ∞ ] ⌜ m ⌝ ≤ ub) ms →
           [ i ] M.step d ms n ≡true ≤ ub ⊖ d
    step []       _       ()
    step (m ∷ ms) n       ≡true ub with Nat.≤⊎> m d
    step (m ∷ ms) zero    ()    _  | inj₁ _
    step (m ∷ ms) (suc _) ()    _  | inj₂ _
    step (m ∷ ms) (suc n) ≡true ub | inj₁ _   =
      step (force ms) n ≡true ub ∘ □-tail
    step (m ∷ ms) zero    ≡true ub | inj₂ m>d = λ where
      (m≤ub ∷ ms⊑ub) →
        <→1≤∸ m>d ⁺+ _                        ≤⟨ (⁺+-mono _ _ (_ ∎≤) λ { .force → least m (force ms) ub (force ms⊑ub) }) ⟩
        <→1≤∸ m>d ⁺+ (λ { .force → ub ⊖ m })  ∼⟨ ⁺+∼+ _ _ ⟩≤
        ⌜ m ∸ d ⌝ ⊕ (ub ⊖ m)                  ∼⟨ ∸+∸∼ m>d ⟩≤
        (ub ⊖ m ⊕ ⌜ m ⌝) ⊖ d                  ∼⟨ ∸+≡ m≤ub ∸-cong refl {x = d} ⟩≤
        ub ⊖ d                                ∎≤

------------------------------------------------------------------------
-- A relation that can be used to relate the least upper bounds of two
-- colists

-- [ ∞ ] ms ≲ ns implies that the least upper bound of ms is less than
-- or equal to that of ns (see ≲→least-upper-bounds-≤ below).

infix 4 [_]_≲_ [_]_≲′_

[_]_≲_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≲ ns = □ i (λ m → ◇ (m ≤_) ns) ms

[_]_≲′_ : Size → Colist ℕ ∞ → Colist ℕ ∞ → Set
[ i ] ms ≲′ ns = □′ i (λ m → ◇ (m ≤_) ns) ms

-- Some derived cons-like operations.

consʳ-≲ : ∀ {ms ns n i} →
          [ i ] ms ≲ force ns →
          [ i ] ms ≲ n ∷ ns
consʳ-≲ = □-map there

cons-≲ : ∀ {i m ms n ns} →
         m ≤ n →
         [ i ] force ms ≲′ force ns →
         [ i ] m ∷ ms ≲ n ∷ ns
cons-≲ p q = here p ∷ λ { .force → consʳ-≲ (force q) }

cons′-≲ : ∀ {i m ms ns} →
          [ i ] force ms ≲′ force ns →
          [ i ] m ∷ ms ≲ m ∷ ns
cons′-≲ = cons-≲ Nat.≤-refl

-- "Equational" reasoning combinators.

infix  -1 _□≲
infixr -2 step-≲ step-≡≲ _≡⟨⟩≲_ step-∼≲

step-≲ : ∀ {i} ms {ns os} →
         [ ∞ ] ns ≲ os → [ i ] ms ≲ ns → [ i ] ms ≲ os
step-≲ _ {ns} {os} ns≲os ms≲ns = □-map lemma ms≲ns
  where
  lemma = λ {n} →
    ◇ (n ≤_) ns                    ↝⟨ □◇-witness ns≲os ⟩
    (∃ λ o → ◇ (o ≤_) os × n ≤ o)  ↝⟨ (λ { (_ , ◇o≤os , n≤o) → ◇-map (Nat.≤-trans n≤o) ◇o≤os }) ⟩□
    ◇ (n ≤_) os                    □

syntax step-≲ ms ns≲os ms≲ns = ms ≲⟨ ms≲ns ⟩ ns≲os

step-≡≲ : ∀ {i} ms {ns os} → [ i ] ns ≲ os → ms ≡ ns → [ i ] ms ≲ os
step-≡≲ _ ns≲os refl = ns≲os

syntax step-≡≲ ms ns≲os ms≡ns = ms ≡⟨ ms≡ns ⟩≲ ns≲os

_≡⟨⟩≲_ : ∀ {i} ms {ns} → [ i ] ms ≲ ns → [ i ] ms ≲ ns
_ ≡⟨⟩≲ ms≲ns = ms≲ns

step-∼≲ : ∀ {i} ms {ns os} →
          [ i ] ns ≲ os → Colist.[ i ] ms ∼ ns → [ i ] ms ≲ os
step-∼≲ _ ns≲os ms∼ns = □-∼ (Colist.symmetric-∼ ms∼ns) ns≲os

syntax step-∼≲ ms ns≲os ms∼ns = ms ∼⟨ ms∼ns ⟩≲ ns≲os

_□≲ : ∀ {i} ns → [ i ] ns ≲ ns
[]     □≲ = []
n ∷ ns □≲ = cons′-≲ λ { .force → force ns □≲ }

-- If [ ∞ ] ms ≲ ns, then any least upper bound of ms is less than or
-- equal to any least upper bound of ns.
--
-- TODO: Figure out what the status is of the converse statement.

≲→least-upper-bounds-≤ :
  ∀ {m n ms ns} →
  [ ∞ ] ms ≲ ns →
  Least-upper-bound ms m →
  Least-upper-bound ns n →
  [ ∞ ] m ≤ n
≲→least-upper-bounds-≤ {m} {n} {ms} {ns} ms≲ns m-lub =
  Least-upper-bound ns n                   ↝⟨ proj₁ ⟩
  [ ∞ ] ns ⊑ n                             ↝⟨ (λ hyp → flip transitive-◇≤⊑ hyp) ⟩
  (∀ {m} → ◇ (m ≤_) ns → [ ∞ ] ⌜ m ⌝ ≤ n)  ↝⟨ (λ hyp → □-map hyp ms≲ns) ⟩
  [ ∞ ] ms ⊑ n                             ↝⟨ proj₂ m-lub _ ⟩□
  [ ∞ ] m ≤ n                              □
