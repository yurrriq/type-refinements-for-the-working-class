-- this is an experimental development of the predicative topos of
-- presheaves on contexts of symbols.

module Context (𝒮 : Set) where

open import Basis
open import Category

open import Prelude.Monoidal
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Natural
open import Prelude.Finite
open import Prelude.List
open import Prelude.Path
open import Prelude.Size

open ⊗ using (_,_)

data Ctx : Set where
  [] : Ctx
  _,_ : Ctx → 𝒮 → Ctx

data _∋_ : Ctx → 𝒮 → Set where
  top : {Γ : Ctx} {τ : 𝒮} → (Γ , τ) ∋ τ
  pop : {Γ : Ctx} {σ τ : 𝒮} → Γ ∋ σ → (Γ , τ) ∋ σ

-- order-preserving embeddings from James Chapman's thesis
data ope : Ctx → Ctx → Set where
  done
    : ope [] []
  keep
    : {Γ Δ : Ctx} {σ : 𝒮}
    → ope Γ Δ
    → ope (Γ , σ) (Δ , σ)
  skip
    : {Γ Δ : Ctx} {σ : 𝒮}
    → ope Γ Δ
    → ope (Γ , σ) Δ

ope-idn : (Γ : Ctx) → ope Γ Γ
ope-idn [] = done
ope-idn (Γ , σ) = keep (ope-idn Γ)

ope-cmp : {Γ Δ E : Ctx} → ope Δ E → ope Γ Δ → ope Γ E
ope-cmp done done = done
ope-cmp (keep f) (keep g) = keep (ope-cmp f g)
ope-cmp (skip f) (keep g) = skip (ope-cmp f g)
ope-cmp done (skip g) = skip g
ope-cmp (keep f) (skip g) = skip (ope-cmp (keep f) g)
ope-cmp (skip f) (skip g) = skip (ope-cmp (skip f) g)

keep-idn : (Γ : Ctx) (τ : 𝒮) → keep {σ = τ} (ope-idn Γ) ≡ ope-idn (Γ , τ)
keep-idn Γ τ = refl

ope-idn-lhs : {Γ Δ : Ctx} (f : ope Γ Δ) → ope-cmp (ope-idn Δ) f ≡ f
ope-idn-lhs {Δ = []} done = refl
ope-idn-lhs {Δ = []} (skip f) = refl
ope-idn-lhs {Δ = Δ , τ} (keep f) rewrite ope-idn-lhs f = refl
ope-idn-lhs {Δ = Δ , τ} (skip (keep f)) rewrite keep-idn Δ τ | ope-idn-lhs f = refl
ope-idn-lhs {Δ = Δ , τ} (skip (skip f)) rewrite keep-idn Δ τ | ope-idn-lhs f = refl

ope-idn-rhs : {Γ Δ : Ctx} (f : ope Γ Δ) → ope-cmp f (ope-idn Γ) ≡ f
ope-idn-rhs done = refl
ope-idn-rhs (keep f) rewrite ope-idn-rhs f = refl
ope-idn-rhs (skip f) rewrite ope-idn-rhs f = refl

ope-cmp-ass : {Γ Δ E Z : Ctx} (f : ope Γ Δ) (g : ope Δ E) (h : ope E Z) → ope-cmp (ope-cmp h g) f ≡ ope-cmp h (ope-cmp g f)
ope-cmp-ass done done done = refl
ope-cmp-ass (keep f) (keep g) (keep h) rewrite ope-cmp-ass f g h = refl
ope-cmp-ass (keep f) (keep g) (skip h) rewrite ope-cmp-ass f g h = refl
ope-cmp-ass (keep f) (skip g) done = refl
ope-cmp-ass (keep f) (skip g) (keep h) rewrite ope-cmp-ass f g (keep h) = refl
ope-cmp-ass (keep f) (skip g) (skip h) rewrite ope-cmp-ass f g (skip h) = refl
ope-cmp-ass (skip f) done done = refl
ope-cmp-ass (skip f) (keep g) (keep h) rewrite ope-cmp-ass f (keep g) (keep h) = refl
ope-cmp-ass (skip f) (keep g) (skip h) rewrite ope-cmp-ass f (keep g) (skip h) = refl
ope-cmp-ass (skip f) (skip g) done = refl
ope-cmp-ass (skip f) (skip g) (keep h) rewrite ope-cmp-ass f (skip g) (keep h) = refl
ope-cmp-ass (skip f) (skip g) (skip h) rewrite ope-cmp-ass f (skip g) (skip h)= refl

category : Category lzero lzero lzero
obj category = Ctx
homˢ category Γ Δ = S.≡.Free (ope Γ Δ)
idnˢ category = ope-idn _
S.⇒₀.ap₀ (cmpˢ category) = ⇒.λ⇓ ope-cmp
S.⇒₀.ap₁ (cmpˢ category) (refl , refl) = refl
idn-lhs category = ope-idn-lhs
idn-rhs category = ope-idn-rhs
cmp-ass category = ope-cmp-ass
