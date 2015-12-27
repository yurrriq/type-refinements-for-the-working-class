module Presheaf (𝒮 : Set) where

open import Basis
open import Context 𝒮

record Presheaf ..ℓ : Set (lsuc ℓ) where
  field
    act : Ctx → Set ℓ
    map : {Γ Δ : Ctx} → Γ ↩ Δ ﹫ ℓ → act Δ → act Γ

open Presheaf public

_⊩_ : {ℓ : _} → Ctx → Presheaf ℓ → Set ℓ
Γ ⊩ X = act X Γ

_•_ : {ℓ : _} {{X : Presheaf ℓ}} {Γ Δ : Ctx} → Δ ⊩ X  → Γ ↩ Δ → Γ ⊩ X
_•_ {{X = X}} x ϱ = map X ϱ x

{-# DISPLAY act X Γ = Γ ⊩ X #-}
{-# DISPLAY map X ϱ x = x • ϱ #-}

-- the set of natural transformations between presheaves
[_,_] : ..{ℓ₀ ℓ₁ : _} → Presheaf ℓ₀ → Presheaf ℓ₁ → Set (ℓ₀ ⊔ ℓ₁)
[ X , Y ] = {Γ : Ctx} → Γ ⊩ X → Γ ⊩ Y
