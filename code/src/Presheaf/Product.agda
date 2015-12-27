module Presheaf.Product (𝒮 : Set) where

open import Context 𝒮
open import Presheaf 𝒮

open import Prelude.Monoidal
open ⊗ using (_,_)

-- the product of presheaves
_[⊗]_ : ..{ℓ : _} → Presheaf ℓ → Presheaf ℓ → Presheaf ℓ
act (X [⊗] Y) Γ = (Γ ⊩ X) ⊗ (Γ ⊩ Y)
map (X [⊗] Y) f (x , y) = x • f , y • f
