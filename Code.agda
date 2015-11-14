{-# OPTIONS --type-in-type #-}
module Code where

record 𝟙 : Set where
  constructor *

module ≡ where
  data _T_ {A} x : A → Set where
    idn : x T x

module × where
  infixr 1 _T_
  record _T_ A B : Set where
    constructor _,_
    field
      π₀ : A
      π₁ : B
open × using (_,_)

module ⇒ where
  infixr 0 _T_
  _T_ : (A B : Set) → Set
  A T B = A → B

  ! : ∀ {A B} → B → (A T B)
  ! b _ = b

  idn : ∀ {A} → A T A
  idn x = x

  _∘_
    : ∀ {A B C}
    → (g : B T C)
    → (f : A T B)
    → A T C
  (g ∘ f) x = g (f x)

record [_]₀ᵒᵖ 𝒞 : Set where
  constructor ι₀ᵒᵖ
  field
    π₀ᵒᵖ : 𝒞
open [_]₀ᵒᵖ

Hom : Set → Set
Hom 𝒞 = [ 𝒞 ]₀ᵒᵖ → 𝒞 → Set

℘ : Set → Set
℘ 𝒞 = 𝒞 → Set

[_]₁ᵒᵖ
  : ∀ {𝒞}
  → Hom 𝒞
  → Hom [ 𝒞 ]₀ᵒᵖ
[ 𝒞[_,_] ]₁ᵒᵖ (ι₀ᵒᵖ (ι₀ᵒᵖ a)) b = 𝒞[ b , a ]

yo
  : ∀ {𝒞}
  → (𝒞[_,_] : Hom 𝒞)
  → (b : 𝒞)
  → ℘ [ 𝒞 ]₀ᵒᵖ
yo 𝒞[_,_] b a = 𝒞[ a , b ]

co
  : ∀ {𝒞}
  → (𝒞[_,_] : Hom 𝒞)
  → (a : [ 𝒞 ]₀ᵒᵖ)
  → ℘ 𝒞
co 𝒞[_,_] = 𝒞[_,_]

Set[_,_] : Hom Set
Set[_,_] (ι₀ᵒᵖ A) B = A ⇒.T B

∫↓ : (𝒞 : Set) (Ψ : Hom 𝒞) → Set
∫↓ 𝒞 Ψ = ∀ c → Ψ (ι₀ᵒᵖ c) c

record ∫↑ (𝒞 : Set) (Ψ : Hom 𝒞) : Set where
  constructor s↑
  field
    π₀ : 𝒞
    π₁ : Ψ (ι₀ᵒᵖ π₀) π₀

Lan
  : ∀ {𝒞 𝒟 𝒱}
  → (𝒟[_,_] : Hom 𝒟)
  → (_⊗_ : [ 𝒱 ]₀ᵒᵖ → Set → Set)
  → (J : 𝒞 → 𝒟)
  → (F : 𝒞 → 𝒱)
  → ℘ 𝒟
Lan {𝒞 = 𝒞}{𝒟 = 𝒟} 𝒟[_,_] _⊗_ J F d = ∫↑ 𝒞 λ {
    (ι₀ᵒᵖ x) y → ι₀ᵒᵖ (F x) ⊗ 𝒟[ ι₀ᵒᵖ (J y) , d ]
  }

Ran
  : ∀ {𝒞 𝒟 𝒱}
  → (𝒟[_,_] : Hom 𝒟)
  → (_⋔_ : Set → 𝒱 → Set)
  → (J : 𝒞 → 𝒟)
  → (F : 𝒞 → 𝒱)
  → ℘ 𝒟
Ran {𝒞 = 𝒞} {𝒟 = 𝒟} 𝒟[_,_] _⋔_ J F d = ∫↓ 𝒞 λ {
    (ι₀ᵒᵖ x) y → 𝒟[ ι₀ᵒᵖ d , J x ] ⋔ F y
  }

Δ[_] : ∀ {𝒞 𝒥} → 𝒞 → (𝒥 → 𝒞)
Δ[ c ] j = c

kᵒᵖ : ∀ {A B} (f : A → B) → A → [ B ]₀ᵒᵖ
kᵒᵖ f x = ι₀ᵒᵖ (f x)

℘_[_,_] : (A : Set) → Hom (℘ A)
℘ A [ ι₀ᵒᵖ φ , ψ ] = ∀ {x : A} → φ x → ψ x

Setᵒᵖ[_,_] : Set → [ Set ]₀ᵒᵖ → Set
Setᵒᵖ[ A , ι₀ᵒᵖ B ] = Set[ ι₀ᵒᵖ A , B ]

module _
  {W} (W[_,_] : Hom W) (⊤ : W)
  {Ω} (Ω[_,_] : Hom Ω)
  where

  𝔍 : Set
  𝔍 = ℘ [ W ]₀ᵒᵖ

  𝔍[_,_] : Hom 𝔍
  𝔍[ φ , ψ ] = ℘ [ W ]₀ᵒᵖ [ φ , ψ ]

  Lim← : ∀ {𝒞} (𝒥 : ℘ 𝒞) → 𝔍
  Lim← 𝒥 (ι₀ᵒᵖ w) = Ran W[_,_] Setᵒᵖ[_,_] Δ[ ⊤ ] (kᵒᵖ 𝒥) w

  ƛ→ : ∀ {A B C} → (A ×.T B → C) → (A → B ⇒.T C)
  ƛ→ f x y = f (x , y)

  ƛ← : ∀ {A B C} → (A → B ⇒.T C) → (A ×.T B → C)
  ƛ← f (x , y) = f x y

  ∣Ω : (𝒥 : Ω → 𝔍) → 𝔍
  ∣Ω 𝒥 (ι₀ᵒᵖ w) = 𝔍[ ι₀ᵒᵖ (yo W[_,_] w) , Lim← (ƛ← 𝒥) ]
