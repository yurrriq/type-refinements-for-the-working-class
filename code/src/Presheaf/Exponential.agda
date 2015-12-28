module Presheaf.Exponential where

open import Basis
open import Category
open import Presheaf
open import Presheaf.Product
open import Presheaf.Representable
open import Functor
open import Natural

open import Prelude.Monoidal hiding (_⇒_ ; _⊗_)

open Functor.Functor
open ⊗ using (_,_)

open Transform

_⇒_ : ..{ℓᵒ ℓˢᵒ ℓˢʰ : _} {𝒞 : Category ℓᵒ ℓˢᵒ ℓˢʰ} (X Y : Presheaf 𝒞 ℓˢᵒ ℓˢʰ) → Presheaf 𝒞 _ _
ap₀ (X ⇒ Y) c = [ (𝓎 c) ⊗ X , Y ]
S.⇒₀.ap₀ (trans (S.⇒₀.ap₀ (S.⇒₀.ap₀ (ap₁ (_⇒_ {𝒞 = 𝒞} X Y)) f) η) c) (g , x) =
  trans η _ S.$₀
    ( cmpˢ 𝒞 S.$₀ (f , g)
    , x
    )
S.⇒₀.ap₁ (trans (S.⇒₀.ap₀ (S.⇒₀.ap₀ (ap₁ (X ⇒ Y)) f) η) c) {z1 , z2} {y1 , y2} (p , q) =
  {!!}
natural (S.⇒₀.ap₀ (S.⇒₀.ap₀ (ap₁ (X ⇒ Y)) f) η) = {!!}
S.⇒₀.ap₁ (S.⇒₀.ap₀ (ap₁ (X ⇒ Y)) f) = {!!}
S.⇒₀.ap₁ (ap₁ (X ⇒ Y)) = {!!}
idn (X ⇒ Y) = {!!}
cmp (X ⇒ Y) = {!!}

---- the exponential of presheaves (via the Yoneda embedding);
---- just a "proof-relevant" generalization of implication in a kripke model
--_[⇒]_ : ..{ℓ : _} → Presheaf ℓ → Presheaf ℓ → Presheaf ℓ
--act (X [⇒] Y) Γ = [ 𝓎 Γ [⊗] X , Y ]
--map (X [⇒] Y) f η (g , x) = η (f ∘ g , x)
