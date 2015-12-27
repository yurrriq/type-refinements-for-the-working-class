module Presheaf.Exponential (𝒮 : Set) where

open import Context 𝒮
open import Presheaf 𝒮
open import Presheaf.Product 𝒮
open import Presheaf.Representable 𝒮

open import Prelude.Monoidal
open ⊗ using (_,_)

-- the exponential of presheaves (via the Yoneda embedding);
-- just a "proof-relevant" generalization of implication in a kripke model
_[⇒]_ : ..{ℓ : _} → Presheaf ℓ → Presheaf ℓ → Presheaf ℓ
act (X [⇒] Y) Γ = [ 𝓎 Γ [⊗] X , Y ]
map (X [⇒] Y) f η (g , x) = η (f ∘ g , x)
