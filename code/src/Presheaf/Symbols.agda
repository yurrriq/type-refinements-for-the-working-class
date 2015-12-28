module Presheaf.Symbols (𝒮 : Set) where

open import Context 𝒮 as Ctx
open import Basis
open import Presheaf
open import Functor

open import Prelude.Monoidal
open import Prelude.Path

open Functor.Functor

private
  _•ˢ_ : {Γ Δ : Ctx} {τ : 𝒮} → Δ ∋ τ → ope Γ Δ → Γ ∋ τ
  x •ˢ done = x
  top •ˢ keep f = top
  pop x •ˢ keep f = pop (x •ˢ f)
  x •ˢ skip f = pop (x •ˢ f)

  ren-id : {Γ : Ctx} {τ : 𝒮} (i : Γ ∋ τ) → i •ˢ ope-idn Γ ≡ i
  ren-id top = refl
  ren-id (pop i) rewrite ren-id i = refl

  ren-cmp : {Γ Δ E : Ctx} {τ : 𝒮} (i : Γ ∋ τ) (f : ope E Δ) (g : ope Δ Γ) → (i •ˢ ope-cmp g f) ≡ ((i •ˢ g) •ˢ f)
  ren-cmp i done done = refl
  ren-cmp top (keep f) (keep g) = refl
  ren-cmp (pop i) (keep f) (keep g) rewrite ren-cmp i f g = refl
  ren-cmp i (keep f) (skip g) rewrite ren-cmp i f g = refl
  ren-cmp i (skip f) done = refl
  ren-cmp i (skip f) (keep g) rewrite ren-cmp i f (keep g) = refl
  ren-cmp i (skip f) (skip g) rewrite ren-cmp i f (skip g) = refl

Symbols : 𝒮 → Presheaf₀ Ctx.category
ap₀ (Symbols τ) Γ = S.≡.Free (Γ ∋ τ)
S.⇒₀.ap₀ (S.⇒₀.ap₀ (ap₁ (Symbols τ) {Γ} {Δ}) f) i = i •ˢ f
S.⇒₀.ap₁ (S.⇒₀.ap₀ (ap₁ (Symbols τ)) f) refl = refl
S.⇒₁.ap₀ (S.⇒₀.ap₁ (ap₁ (Symbols τ)) refl) = refl
S.⇒₁.ap₀ (idn (Symbols τ)) {i} = ren-id i
S.⇒₁.ap₀ (cmp (Symbols τ) f g) = ren-cmp _ f g
