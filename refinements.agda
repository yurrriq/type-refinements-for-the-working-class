module refinements
  (𝒮 : Set)
  where

  open import Agda.Primitive

  record Unit {ℓ} : Set ℓ where
    constructor tt

  record ∐ {ℓ⁰ ℓ¹} (A : Set ℓ⁰) (B : A → Set ℓ¹) : Set (ℓ⁰ ⊔ ℓ¹) where
    constructor _,_
    field
      fst : A
      snd : B fst


  data SCtx : Set where
    [] : SCtx
    _,_ : SCtx → 𝒮 → SCtx

  module _
    (tm : SCtx → 𝒮 → Set)
    (_↪_ : SCtx → SCtx → Set)
    (_∘_ : {Υ Υ′ Υ″ : SCtx} → Υ′ ↪ Υ″ → Υ ↪ Υ′ → Υ ↪ Υ″)
    (_[_] : {Υ Υ′ : SCtx} {τ : 𝒮} → tm Υ τ → Υ ↪ Υ′ → tm Υ′ τ)
    where

    mutual
      data ref⋆ : SCtx → Set₁ where
        [] : ref⋆ []
        _,_ : {Υ : SCtx} {τ : 𝒮} (Ψ : ref⋆ Υ) (φ : ref Ψ τ) → ref⋆ (Υ , τ)


      postulate
        _↪[_]_ : {Υ Υ′ : SCtx} (Ψ : ref⋆ Υ) (ϱ : Υ ↪ Υ′) (Ψ′ : ref⋆ Υ′) → Set₁
        _[∘]_ : {Υ Υ′ Υ″ : SCtx} {ϱ : _} {ϱ′ : _} {Ψ : ref⋆ Υ} {Ψ′ : ref⋆ Υ′} {Ψ″ : ref⋆ Υ″} → Ψ′ ↪[ ϱ′ ] Ψ″ → Ψ ↪[ ϱ ] Ψ′ → Ψ ↪[ ϱ′ ∘ ϱ ] Ψ″

      record ref {Υ : SCtx} (Ψ : ref⋆ Υ) (τ : 𝒮) : Set₁ where
        field
          pred :
            {Υ′ : SCtx}
            (ϱ : Υ ↪ Υ′)
            (M N : tm Υ′ τ)
              → Set
          pred-symm :
            {Υ′ : SCtx}
            {ϱ : Υ ↪ Υ′}
            (M N : tm Υ′ τ)
              → pred ϱ M N
              → pred ϱ N M
          pred-trans :
            {Υ′ : SCtx}
            {ϱ : Υ ↪ Υ′}
            (M N O : tm Υ′ τ)
            → pred ϱ N O
            → pred ϱ M N
            → pred ϱ M O
            {-
          pred-resp :
            {Υ′ Υ″ : SCtx}
            (Ψ′ : ref⋆ Υ′)
            (Ψ″ : ref⋆ Υ″)
            {ϱ : Υ ↪ Υ′}
            {ϱ′ : Υ′ ↪ Υ″}
            ([ϱ] : Ψ ↪[ ϱ ] Ψ′)
            ([ϱ′] : Ψ′ ↪[ ϱ′ ] Ψ″)
            (M N : tm Υ′ τ)
              → pred [ϱ] M N
              → pred ([ϱ′] [∘] [ϱ]) (M [ ϱ′ ]) (N [ ϱ′ ])
-}

      _∥_⊆_ : {Υ : SCtx} (Ψ : ref⋆ Υ) {τ : 𝒮} (φ ψ : ref Ψ τ) → Set₁
      _∥_⊆_ {Υ = Υ} Ψ {τ = τ} φ ψ =
        {Υ′ Υ″ : SCtx}
        (Ψ′ : ref⋆ Υ′)
        (Ψ″ : ref⋆ Υ″)
        {ϱ : Υ ↪ Υ′}
        {ϱ′ : Υ′ ↪ Υ″}
        ([ϱ] : Ψ ↪[ ϱ ] Ψ′)
        ([ϱ′] : Ψ′ ↪[ ϱ′ ] Ψ″)
        (M N : tm Υ′ τ)
          → ref.pred φ ϱ M N
          → ref.pred ψ (ϱ′ ∘ ϱ) (M [ ϱ′ ]) (N [ ϱ′ ])

      data _⊆⋆_ : {Υ : SCtx} (Ψ Ψ′ : ref⋆ Υ) → Set₁ where
        [] : [] ⊆⋆ []
        _,_ : {Υ : SCtx} {τ : 𝒮} {Ψ Ψ′ : ref⋆ Υ} (p : Ψ ⊆⋆ Ψ′) (φ : ref Ψ τ) (ψ : ref Ψ′ τ) → Ψ′ ∥ φ ⊆⋆[ p ] ⊆ ψ → (Ψ , φ) ⊆⋆ (Ψ′ , ψ)

      _⊆⋆[_] : {Υ : SCtx} {τ : 𝒮} {Ψ Ψ′ : ref⋆ Υ} → ref Ψ τ → Ψ ⊆⋆ Ψ′ → ref Ψ′ τ
      φ ⊆⋆[ _ ] =
        record
          { pred = ref.pred φ
          ; pred-symm = ref.pred-symm φ
          ; pred-trans = ref.pred-trans φ
          }
