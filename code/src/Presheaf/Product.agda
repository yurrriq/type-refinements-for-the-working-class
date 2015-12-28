module Presheaf.Product where

open import Basis
open import Category
open import Presheaf
open import Functor

open import Prelude.Monoidal hiding (_⊗_)

open Functor.Functor
open ⊗ using (_,_)

_⊗_ : ..{ℓᵒ ℓˢᵒ ℓˢʰ : _} {𝒞 : Category ℓᵒ ℓˢᵒ ℓˢʰ} (X Y : Presheaf 𝒞 ℓˢᵒ ℓˢʰ) → Presheaf 𝒞 ℓˢᵒ ℓˢʰ
ap₀ (X ⊗ Y) c = (c ⊩ X) S.⊗ (c ⊩ Y)
S.⇒₀.ap₀ (S.⇒₀.ap₀ (ap₁ (X ⊗ Y)) f) (x , y) = X ⊢ x • f , Y ⊢ y • f
S.⇒₀.ap₁ (S.⇒₀.ap₀ (ap₁ (X ⊗ Y)) f) (p , q) = (ap₁ X S.$₀ f) S.$₁ p , (ap₁ Y S.$₀ f) S.$₁ q
S.⇒₁.ap₀ (S.⇒₀.ap₁ (ap₁ (X ⊗ Y)) p) = S.⇒₁.ap₀ (S.⇒₀.ap₁ (ap₁ X) p) , S.⇒₁.ap₀ (S.⇒₀.ap₁ (ap₁ Y) p)
S.⇒₁.ap₀ (idn (X ⊗ Y)) = S.⇒₁.ap₀ (idn X) , S.⇒₁.ap₀ (idn Y)
S.⇒₁.ap₀ (cmp (X ⊗ Y) f g) = S.⇒₁.ap₀ (cmp X f g) , S.⇒₁.ap₀ (cmp Y f g)
