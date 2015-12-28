module Basis where

open import Agda.Primitive public

module S where
  open import Groupoids.Setoid public
  open import Groupoids.Core.Setoid.Ordinary.Construction.Discrete public

  _$₀_ = ⇒₀.ap₀
  _$₁_ = ⇒₀.ap₁

at-lvl : ..(ℓ : _) → Set ℓ → Set ℓ
at-lvl ℓ A = A

syntax at-lvl ℓ A = A ﹫ ℓ
