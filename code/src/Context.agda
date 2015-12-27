-- this is an experimental development of the predicative topos of
-- presheaves on contexts of symbols.

module Context (𝒮 : Set) where

open import Agda.Primitive
open import Prelude.Monoidal
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Natural
open import Prelude.Finite
open import Prelude.List
open import Prelude.Path

open ⊗ using (_,_)

Ctx : Set
Ctx = List 𝒮

data _∋_ ..{ℓ} : Ctx → 𝒮 → Set ℓ where
  top : {Γ : Ctx} {τ : 𝒮} → (τ ∷ Γ) ∋ τ
  pop : {Γ : Ctx} {σ τ : 𝒮} → Γ ∋ σ → (τ ∷ Γ) ∋ σ

-- order-preserving embeddings from James Chapman's thesis
data OPE ..{ℓ} : Ctx → Ctx → Set ℓ where
  done : OPE [] []
  keep : {Γ Δ : Ctx} {σ : 𝒮} (ϱ : OPE Γ Δ) → OPE (σ ∷ Γ) (σ ∷ Δ)
  skip : {Γ Δ : Ctx} {σ : 𝒮} (ϱ : OPE Γ Δ) → OPE (σ ∷ Γ) Δ

_∘_ : {ℓ : _} {Γ Δ H : Ctx} → OPE {ℓ} Δ H → OPE {ℓ} Γ Δ → OPE {ℓ} Γ H
done ∘ done = done
keep ϱ₀ ∘ keep ϱ₁ = keep (ϱ₀ ∘ ϱ₁)
skip ϱ₀ ∘ keep ϱ₁ = skip (ϱ₀ ∘ ϱ₁)
ϱ₀ ∘ skip ϱ₁ = skip (ϱ₀ ∘ ϱ₁)

assoc : {ℓ : _} {Γ Δ H I : Ctx} (f : OPE {ℓ} Γ Δ) (g : OPE {ℓ} Δ H) (h : OPE {ℓ} H I) → (h ∘ (g ∘ f)) ≡ ((h ∘ g) ∘ f)
assoc done done done = refl
assoc (keep f) (keep g) (keep h) rewrite assoc f g h = refl
assoc (keep f) (keep g) (skip h) rewrite assoc f g h = refl
assoc (keep f) (skip g) done rewrite assoc f g done = refl
assoc (keep f) (skip g) (keep h) rewrite assoc f g (keep h) = refl
assoc (keep f) (skip g) (skip h) rewrite assoc f g (skip h) = refl
assoc (skip f) done done rewrite assoc f done done = refl
assoc (skip f) (keep g) (keep h) rewrite assoc f (keep g) (keep h)= refl
assoc (skip f) (keep g) (skip h) rewrite assoc f (keep g) (skip h) = refl
assoc (skip f) (skip g) done rewrite assoc f (skip g) done = refl
assoc (skip f) (skip g) (keep h) rewrite assoc f (skip g) (keep h) = refl
assoc (skip f) (skip g) (skip h) rewrite assoc f (skip g) (skip h) = refl

record Presheaf ..ℓ : Set (lsuc ℓ) where
  field
    act : Ctx → Set ℓ
    map : {Γ Δ : Ctx} → OPE {ℓ} Γ Δ → act Δ → act Γ

open Presheaf public

_[_] : {ℓ : Level} → Presheaf ℓ → Ctx → Set ℓ
X [ Γ ] = act X Γ

_•_ : {ℓ : Level} {{X : Presheaf ℓ}} {Γ Δ : Ctx} → act X Δ → OPE Γ Δ → act X Γ
_•_ {{X = X}} x ϱ = map X ϱ x

-- The presheaf of symbols of a particular sort
Symbols : ..{ℓ : Level} → 𝒮 → Presheaf ℓ
act (Symbols τ) Γ = Γ ∋ τ
map (Symbols τ) ϱ x = x •ˢ ϱ
  where
    _•ˢ_ : {Γ Δ : Ctx} → Δ ∋ τ → OPE Γ Δ → Γ ∋ τ
    x •ˢ done = x
    top •ˢ keep ϱ = top
    pop x •ˢ keep ϱ = pop (x •ˢ ϱ)
    x •ˢ skip ϱ = pop (x •ˢ ϱ)

-- the set of natural transformations between presheaves
[_,_] : ..{ℓ₀ ℓ₁ : _} → Presheaf ℓ₀ → Presheaf ℓ₁ → Set (ℓ₀ ⊔ ℓ₁)
[ X , Y ] = {Γ : Ctx} → X [ Γ ] → Y [ Γ ]

-- the representable presheaf
𝓎 : ..{ℓ : _} → Ctx → Presheaf ℓ
act (𝓎 Γ) Δ = OPE Δ Γ
map (𝓎 Γ) ϱ₀ ϱ₁ = ϱ₁ ∘ ϱ₀

-- the terminal presheaf
[𝟙] : ..(ℓ : _) → Presheaf ℓ
act ([𝟙] ℓ) _ = 𝟙↑
map ([𝟙] ℓ) _ _ = 𝟙↑.*

-- the product of presheaves
_[⊗]_ : ..{ℓ : _} → Presheaf ℓ → Presheaf ℓ → Presheaf ℓ
act (X [⊗] Y) Γ = (X [ Γ ]) ⊗ (Y [ Γ ])
map (X [⊗] Y) ϱ (x , y) = x • ϱ , y • ϱ

-- the coproduct of presheaves
_[⊕]_ : ..{ℓ : _} → Presheaf ℓ → Presheaf ℓ → Presheaf ℓ
act (X [⊕] Y) Γ = (X [ Γ ]) ⊕ (Y [ Γ ])
map (X [⊕] Y) ϱ (⊕.inl x) = ⊕.inl (x • ϱ)
map (X [⊕] Y) ϱ (⊕.inr y) = ⊕.inr (y • ϱ)

-- the exponential of presheaves (via the Yoneda embedding);
-- just a "proof-relevant" generalization of implication in a kripke model
_[⇒]_ : ..{ℓ : _} → Presheaf ℓ → Presheaf ℓ → Presheaf ℓ
act (X [⇒] Y) Γ = [ 𝓎 Γ [⊗] X , Y ]
map (X [⇒] Y) ϱ η (ϱ′ , x) = η (ϱ ∘ ϱ′ , x)

-- a sieve on Γ is a family of arrows ending in Γ which is closed under precomposition.
-- sieves are equivalent to subfunctors of 𝓎 Γ, but the direct presentation is easier
-- to encode in this development.
record Sieve ..ℓ (Γ : Ctx) : Set (lsuc ℓ) where
  field
    pred
      : {Δ : Ctx}
      → OPE {lsuc ℓ} Δ Γ
      → Set ℓ
    closed
      : {Δ H : Ctx} (ϱ₀ : OPE Δ Γ) (ϱ₁ : OPE H Δ)
      → pred ϱ₀
      → pred (ϱ₀ ∘ ϱ₁)

-- a sieve can be pulled back along a renaming
[_]*_ : {ℓ : _} {Γ Δ : Ctx} (f : OPE {lsuc ℓ} Δ Γ ) (S : Sieve ℓ Γ) → Sieve ℓ Δ
Sieve.pred ([ ϱ ]* S) ϱ′ = Sieve.pred S (ϱ ∘ ϱ′)
Sieve.closed ([ ϱ ]* S) ϱ₀ ϱ₁ = aux
  where
    aux : Sieve.pred S (ϱ ∘ ϱ₀) → Sieve.pred S (ϱ ∘ (ϱ₀ ∘ ϱ₁))
    aux p rewrite assoc ϱ₁ ϱ₀ ϱ = Sieve.closed S (ϱ ∘ ϱ₀) ϱ₁ p

-- we have a tower of (large) subobject classifiers
[Ω] : ..(ℓ : _) → Presheaf (lsuc ℓ)
act ([Ω] ℓ) Γ = Sieve _ Γ
map ([Ω] ℓ) ϱ S = [ ϱ ]* S

true : ..{ℓ : _} → [ [𝟙] ℓ , [Ω] ℓ ]
Sieve.pred (true _) _ = 𝟙↑
Sieve.closed (true _) _ _ _ = 𝟙↑.*

-- We have a (relatively) large power object, via the subobject classifier
[℘] : ..{ℓ : _} → Presheaf (lsuc ℓ) → Presheaf (lsuc ℓ)
[℘] {ℓ} X = X [⇒] [Ω] ℓ

[bin-rel] : ..{ℓ : _} → Presheaf (lsuc ℓ) → Presheaf (lsuc ℓ)
[bin-rel] X = [℘] (X [⊗] X)
