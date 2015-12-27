module Presheaf.Classifier (𝒮 : Set) where

open import Basis
open import Context 𝒮
open import Presheaf 𝒮
open import Presheaf.Exponential 𝒮
open import Presheaf.Product 𝒮
open import Presheaf.Terminal 𝒮
open import Sieve 𝒮

open import Prelude.Monoidal
open ⊗ using (_,_)

-- we have a tower of (relatively) large subobject classifiers
[Ω] : ..(ℓ : _) → Presheaf (lsuc ℓ)
act ([Ω] ℓ) Γ = Sieve _ Γ
map ([Ω] ℓ) ϱ S = [ ϱ ]* S

true : ..{ℓ : _} → [ [𝟙] ℓ , [Ω] ℓ ]
Sieve.pred (true _) _ = 𝟙↑
Sieve.closed (true _) _ _ _ = 𝟙↑.*

false : ..{ℓ : _} → [ [𝟙] ℓ , [Ω] ℓ ]
Sieve.pred (false _) _ = 𝟘↑
Sieve.closed (false _) _ _ ()

-- We have a (relatively) large power object, via the subobject classifier
[℘] : ..{ℓ : _} → Presheaf (lsuc ℓ) → Presheaf (lsuc ℓ)
[℘] {ℓ} X = X [⇒] [Ω] ℓ

[bin-rel] : ..{ℓ : _} → Presheaf (lsuc ℓ) → Presheaf (lsuc ℓ)
[bin-rel] X = [℘] (X [⊗] X)
