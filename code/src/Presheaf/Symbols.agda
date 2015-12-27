module Presheaf.Symbols (𝒮 : Set) where

open import Context 𝒮
open import Presheaf 𝒮

-- The presheaf of symbols of a particular sort
Symbols : ..{ℓ : _} → 𝒮 → Presheaf ℓ
act (Symbols τ) Γ = Γ ∋ τ
map (Symbols τ) ϱ x = x •ˢ ϱ
  where
    _•ˢ_ : {Γ Δ : Ctx} → Δ ∋ τ → Γ ↩ Δ → Γ ∋ τ
    x •ˢ done = x
    top •ˢ keep ϱ = top
    pop x •ˢ keep ϱ = pop (x •ˢ ϱ)
    x •ˢ skip ϱ = pop (x •ˢ ϱ)
