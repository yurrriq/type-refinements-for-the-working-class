module Presheaf.Terminal (𝒮 : Set) where

open import Context 𝒮
open import Presheaf 𝒮

open import Prelude.Monoidal

-- the terminal presheaf
[𝟙] : ..(ℓ : _) → Presheaf ℓ
act ([𝟙] ℓ) _ = 𝟙↑
map ([𝟙] ℓ) _ _ = 𝟙↑.*

