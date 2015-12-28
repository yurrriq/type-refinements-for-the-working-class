module Presheaf.Representable where

open import Presheaf

open import Basis
open import Presheaf
open import Category
open import Functor
import Groupoids.Core.Setoid.Ordinary.Monoidal.Homomorphism as S
open import Prelude.Monoidal
open import Prelude.Path

open Functor.Functor
open ⊗ using (_,_)

_⊢𝓎_ : ..{ℓᵒ ℓˢᵒ ℓˢʰ : _} (𝒞 : Category ℓᵒ ℓˢᵒ ℓˢʰ) → obj 𝒞 → Presheaf 𝒞 ℓˢᵒ ℓˢʰ
ap₀ (𝒞 ⊢𝓎 c) d = homˢ 𝒞 d c
S.⇒₀.ap₀ (S.⇒₀.ap₀ (ap₁ (𝒞 ⊢𝓎 c) ) f) g = cmpˢ 𝒞 S.$₀ (g , f)
S.⇒₀.ap₁ (S.⇒₀.ap₀ (ap₁ (𝒞 ⊢𝓎 c)) f) g = cmpˢ 𝒞 S.$₁ (g , S.idn⇒ (homˢ 𝒞 _ _) 𝟙ₙ.*)
S.⇒₁.ap₀ (S.⇒₀.ap₁ (ap₁ (𝒞 ⊢𝓎 c)) f) = cmpˢ 𝒞 S.$₁ (S.idn⇒ (homˢ 𝒞 _ _) 𝟙ₙ.* , f)
S.⇒₁.ap₀ (idn (𝒞 ⊢𝓎 c)) = idn-rhs 𝒞 _
S.⇒₁.ap₀ (cmp (𝒞 ⊢𝓎 c) f g) = S.inv⇒ (homˢ 𝒞 _ _) (cmp-ass 𝒞 f g _)

𝓎_ : ..{ℓᵒ ℓˢᵒ ℓˢʰ : _} {𝒞 : Category ℓᵒ ℓˢᵒ ℓˢʰ} → obj 𝒞 → Presheaf 𝒞 ℓˢᵒ ℓˢʰ
𝓎 c = _ ⊢𝓎 c
