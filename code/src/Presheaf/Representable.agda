module Presheaf.Representable (𝒮 : Set) where

open import Context 𝒮
open import Presheaf 𝒮

-- the representable presheaf
𝓎 : ..{ℓ : _} → Ctx → Presheaf ℓ
act (𝓎 Γ) = _↩ Γ
map (𝓎 Γ) f = _∘ f

