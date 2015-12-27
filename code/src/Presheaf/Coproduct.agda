module Presheaf.Coproduct (𝒮 : Set) where

open import Context 𝒮
open import Presheaf 𝒮

open import Prelude.Monoidal

-- the coproduct of presheaves
_[⊕]_ : ..{ℓ : _} → Presheaf ℓ → Presheaf ℓ → Presheaf ℓ
act (X [⊕] Y) Γ = (Γ ⊩ X) ⊕ (Γ ⊩ Y)
map (X [⊕] Y) ϱ (⊕.inl x) = ⊕.inl (x • ϱ)
map (X [⊕] Y) ϱ (⊕.inr y) = ⊕.inr (y • ϱ)
