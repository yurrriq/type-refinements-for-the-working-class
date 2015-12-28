module Functor where

open import Basis
open import Prelude.Monoidal
open ⊗ using (_,_)

open import Category

record Functor
    ..{ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀ ℓᵒ₁ ℓˢᵒ₁ ℓˢʰ₁}
    (𝒞 : Category ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀)
    (𝒟 : Category ℓᵒ₁ ℓˢᵒ₁ ℓˢʰ₁)
  : Set (lsuc (ℓᵒ₀ ⊔ ℓˢᵒ₀ ⊔ ℓˢʰ₀ ⊔ ℓᵒ₁ ⊔ ℓˢᵒ₁ ⊔ ℓˢʰ₁)) where
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟
    field
      ap₀
        : 𝒞.obj
        → 𝒟.obj
      ap₁
        : {a b : 𝒞.obj}
        → 𝒞.homˢ a b S.⇒ 𝒟.homˢ (ap₀ a) (ap₀ b)
    field
      idn
        : {a : 𝒞.obj}
        → S.hom⊗ (𝒟.homˢ (ap₀ a) (ap₀ a))
            ( ap₁ S.$₀ 𝒞.idnˢ
            , 𝒟.idnˢ
            )
      cmp
        : {a b c : 𝒞.obj}
        → (g : S.cell₀[ 𝒞.homˢ b c ])
        → (f : S.cell₀[ 𝒞.homˢ a b ])
        → S.hom⊗ (𝒟.homˢ (ap₀ a) (ap₀ c))
            ( ap₁ S.$₀ (𝒞.cmpˢ S.$₀ (g , f))
            , 𝒟.cmpˢ S.$₀ (ap₁ S.$₀ g , ap₁ S.$₀ f)
            )
