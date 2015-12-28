module Natural where

open import Basis
open import Category
open import Category.Setoids
open import Functor
open import Prelude.Monoidal

open ⊗ using (_,_)

record Transform
    ..{ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀ ℓᵒ₁ ℓˢᵒ₁ ℓˢʰ₁}
    {𝒞 : Category ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀}
    {𝒟 : Category ℓᵒ₁ ℓˢᵒ₁ ℓˢʰ₁}
    (F G : Functor 𝒞 𝒟)
  : Set (ℓᵒ₀ ⊔ ℓˢᵒ₀ ⊔ ℓˢʰ₀ ⊔ ℓᵒ₁ ⊔ ℓˢᵒ₁ ⊔ ℓˢʰ₁) where
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟
    module F = Functor.Functor F
    module G = Functor.Functor G

    field
      trans
        : (a : 𝒞.obj)
        → S.obj (𝒟.homˢ (F.ap₀ a) (G.ap₀ a))
      natural
        : {a b : 𝒞.obj}
        → (f : S.obj (𝒞.homˢ a b))
        → S.hom⊗ (𝒟.homˢ (F.ap₀ a) (G.ap₀ b))
            ( 𝒟.cmpˢ S.$₀ (trans b , F.ap₁ S.$₀ f)
            , 𝒟.cmpˢ S.$₀ (G.ap₁ S.$₀ f , trans a)
            )

[_,_]₀ = Transform

open Functor.Functor
open Transform

[_,_]
  : ..{ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀ ℓᵒ₁ ℓˢᵒ₁ ℓˢʰ₁ : _} {𝒞 : Category ℓᵒ₀ ℓˢᵒ₀ ℓˢʰ₀} {𝒟 : Category ℓᵒ₁ ℓˢᵒ₁ ℓˢʰ₁}
  → (F G : Functor 𝒞 𝒟)
  → obj (SETOID (ℓˢʰ₁ ⊔ ℓˢᵒ₁ ⊔ ℓᵒ₁ ⊔ ℓˢʰ₀ ⊔ ℓˢᵒ₀ ⊔ ℓᵒ₀) (ℓˢʰ₁ ⊔ ℓᵒ₀))
S.obj [ F , G ] = [ F , G ]₀
S.hom⊗ ([_,_] {𝒞 = 𝒞} {𝒟 = 𝒟} F G) (η , ζ) =
  (a : obj 𝒞)
    → S.hom⊗ (homˢ 𝒟 (ap₀ F a) (ap₀ G a))
        ( trans η a
        , trans ζ a
        )
S.idn⇒ ([_,_] {𝒟 = 𝒟} F G) 𝟙ₙ.* c = S.idn⇒ (homˢ 𝒟 (ap₀ F c) (ap₀ G c)) 𝟙ₙ.*
S.cmp⇒ ([_,_] {𝒟 = 𝒟} F G) (p , q) a = S.cmp⇒ (homˢ 𝒟 (ap₀ F a) (ap₀ G a)) (p a , q a)
S.inv⇒ ([_,_] {𝒟 = 𝒟} F G) p a = S.inv⇒ (homˢ 𝒟 (ap₀ F a) (ap₀ G a)) (p a)
