module Sieve (𝒮 : Set) where

open import Basis
open import Context 𝒮

-- a sieve on Γ is a family of arrows ending in Γ which is closed under precomposition.
-- sieves are equivalent to subfunctors of 𝓎 Γ, but the direct presentation is easier
-- to encode in this development.
record Sieve ..ℓ (Γ : Ctx) : Set (lsuc ℓ) where
  field
    pred
      : {Δ : Ctx}
      → Δ ↩ Γ ﹫ lsuc ℓ
      → Set ℓ
    closed
      : {Δ E : Ctx} (f : Δ ↩ Γ) (g : E ↩ Δ)
      → pred f
      → pred (f ∘ g)

-- a sieve can be pulled back along a renaming
[_]*_ : {ℓ : _} {Γ Δ : Ctx} (f : Δ ↩ Γ) (S : Sieve ℓ Γ) → Sieve ℓ Δ
Sieve.pred ([ f ]* S) g = Sieve.pred S (f ∘ g)
Sieve.closed ([ f ]* S) g h = aux
  where
    aux : Sieve.pred S (f ∘ g) → Sieve.pred S (f ∘ (g ∘ h))
    aux rewrite assoc h g f = Sieve.closed S (f ∘ g) h
