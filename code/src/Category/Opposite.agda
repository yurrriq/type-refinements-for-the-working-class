module Category.Opposite where

open import Basis
open import Category
open import Prelude.Monoidal
open ⊗ using (_,_)

_ᵒᵖ
  : ..{ℓᵒ ℓˢᵒ ℓˢʰ : _}
  → Category ℓᵒ ℓˢᵒ ℓˢʰ
  → Category ℓᵒ ℓˢᵒ ℓˢʰ
obj (𝒞 ᵒᵖ) = obj 𝒞
homˢ (𝒞 ᵒᵖ) a b = homˢ 𝒞 b a
idnˢ (𝒞 ᵒᵖ) = idnˢ 𝒞
S.⇒₀.ap₀ (cmpˢ (𝒞 ᵒᵖ)) (f , g) = cmpˢ 𝒞 S.$₀ (g , f)
S.⇒₀.ap₁ (cmpˢ (𝒞 ᵒᵖ)) (p , q) = cmpˢ 𝒞 S.$₁ (q , p)
idn-lhs (𝒞 ᵒᵖ) = idn-rhs 𝒞
idn-rhs (𝒞 ᵒᵖ) = idn-lhs 𝒞
cmp-ass (𝒞 ᵒᵖ) f g h = S.inv⇒ (homˢ 𝒞 _ _) (cmp-ass 𝒞 h g f)
