module Basis where

open import Agda.Primitive public

at-lvl : ..(ℓ : _) → Set ℓ → Set ℓ
at-lvl ℓ A = A

syntax at-lvl ℓ A = A ﹫ ℓ
