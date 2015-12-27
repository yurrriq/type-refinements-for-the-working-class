module Presheaf.Initial (𝒮 : Set) where

open import Context 𝒮
open import Presheaf 𝒮

open import Prelude.Monoidal

-- the initial presheaf
[𝟘] : ..(ℓ : _) → Presheaf ℓ
act ([𝟘] ℓ) _ = 𝟘↑
map ([𝟘] ℓ) _ ()
