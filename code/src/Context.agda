-- this is an experimental development of the predicative topos of
-- presheaves on contexts of symbols.

module Context (𝒮 : Set) where

open import Basis

open import Prelude.Monoidal
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Natural
open import Prelude.Finite
open import Prelude.List
open import Prelude.Path

open ⊗ using (_,_)

Ctx : Set
Ctx = List 𝒮

data _∋_ ..{ℓ} : Ctx → 𝒮 → Set ℓ where
  top : {Γ : Ctx} {τ : 𝒮} → (τ ∷ Γ) ∋ τ
  pop : {Γ : Ctx} {σ τ : 𝒮} → Γ ∋ σ → (τ ∷ Γ) ∋ σ

-- order-preserving embeddings from James Chapman's thesis
data _↩_ ..{ℓ} : Ctx → Ctx → Set ℓ where
  done : [] ↩ []
  keep : {Γ Δ : Ctx} {σ : 𝒮} (ϱ : Γ ↩ Δ) → (σ ∷ Γ) ↩ (σ ∷ Δ)
  skip : {Γ Δ : Ctx} {σ : 𝒮} (ϱ : Γ ↩ Δ) → (σ ∷ Γ) ↩ Δ

infix 21 _↩_

_∘_ : {ℓ : _} {Γ Δ E : Ctx} → Δ ↩ E ﹫ ℓ  → Γ ↩ Δ ﹫ ℓ → Γ ↩ E ﹫ ℓ
done ∘ done = done
keep f ∘ keep g = keep (f ∘ g)
skip f ∘ keep g = skip (f ∘ g)
f ∘ skip g = skip (f ∘ g)

assoc : {ℓ : _} {Γ Δ E Z : Ctx} (f : Γ ↩ Δ ﹫ ℓ) (g : Δ ↩ E) (h : E ↩ Z) → (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
assoc done done done = refl
assoc (keep f) (keep g) (keep h) rewrite assoc f g h = refl
assoc (keep f) (keep g) (skip h) rewrite assoc f g h = refl
assoc (keep f) (skip g) done rewrite assoc f g done = refl
assoc (keep f) (skip g) (keep h) rewrite assoc f g (keep h) = refl
assoc (keep f) (skip g) (skip h) rewrite assoc f g (skip h) = refl
assoc (skip f) done done rewrite assoc f done done = refl
assoc (skip f) (keep g) (keep h) rewrite assoc f (keep g) (keep h)= refl
assoc (skip f) (keep g) (skip h) rewrite assoc f (keep g) (skip h) = refl
assoc (skip f) (skip g) done rewrite assoc f (skip g) done = refl
assoc (skip f) (skip g) (keep h) rewrite assoc f (skip g) (keep h) = refl
assoc (skip f) (skip g) (skip h) rewrite assoc f (skip g) (skip h) = refl
