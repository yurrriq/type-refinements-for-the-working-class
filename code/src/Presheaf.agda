module Presheaf where

open import Basis
open import Category
open import Category.Setoids
open import Category.Opposite
open import Functor

Presheaf
  : ..{ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀ : _}
  → Category ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀
  → ..(ℓˢᵒ₁ ℓˢʰ₁ : _)
  → Set _
Presheaf 𝒞 ℓˢᵒ₁ ℓˢʰ₁ = Functor (𝒞 ᵒᵖ) (SETOID ℓˢᵒ₁ ℓˢʰ₁)

Presheaf₀
  : ..{ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀ : _}
  → Category ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀
  → Set _
Presheaf₀ 𝒞 = Presheaf 𝒞 lzero lzero

_⊩_
  : ..{ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀ ℓˢᵒ₁ ℓˢʰ₁ : _} {𝒞 : Category ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀}
  → obj 𝒞
  → Presheaf 𝒞 ℓˢᵒ₁ ℓˢʰ₁
  → obj (SETOID ℓˢᵒ₁ ℓˢʰ₁)
U ⊩ X =
  Functor.ap₀ X U

_⊢_•_
  : ..{ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀ ℓˢᵒ₁ ℓˢʰ₁ : _} {𝒞 : Category ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀} (X : Presheaf 𝒞 ℓˢᵒ₁ ℓˢʰ₁) {U V : obj 𝒞}
  → S.obj (V ⊩ X)
  → S.obj (homˢ 𝒞 U V)
  → S.obj (U ⊩ X)
X ⊢ x • ϱ =
  (Functor.ap₁ X S.$₀ ϱ) S.$₀ x

