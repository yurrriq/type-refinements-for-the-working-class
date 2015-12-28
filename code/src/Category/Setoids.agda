module Category.Setoids where

open import Basis
open import Category

open import Prelude.Monoidal
import Groupoids.Core.Setoid.Ordinary.Cell as S

open ⊗ using (_,_)

SETOID : ..(ℓˢᵒ ℓˢʰ : _) → Category _ _ _
obj (SETOID ℓˢᵒ ℓˢʰ) = S.𝔘 S.Dir.≈ ℓˢᵒ ℓˢʰ
homˢ (SETOID _ _)= S.⇒₀._ˢ_
S.⇒₀.ap₀ (idnˢ (SETOID _ _)) x = x
S.⇒₀.ap₁ (idnˢ (SETOID _ _)) p = p
S.⇒₀.ap₀ (cmpˢ (SETOID _ _)) = S.⇒₀.cmp
S.⇒₀.ap₁ (cmpˢ (SETOID _ _)) = S.⇒₀.≾.cmp
S.⇒₁.ap₀ (idn-lhs (SETOID _ _) {A} f) = f S.$₁ S.idn⇒ A 𝟙ₙ.*
S.⇒₁.ap₀ (idn-rhs (SETOID _ _) {A} f) = f S.$₁ S.idn⇒ A 𝟙ₙ.*
S.⇒₁.ap₀ (cmp-ass (SETOID _ _) {A} f g h) = h S.$₁ (g S.$₁ (f S.$₁ S.idn⇒ A 𝟙ₙ.*))
