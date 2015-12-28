module Category where

open import Basis
open import Prelude.Monoidal
open ⊗ using (_,_)

record Category ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ)) where
  no-eta-equality
  field
    obj
      : Set ℓᵒ
    homˢ
      : obj
      → obj
      → S.𝔘 S.Dir.≈ ℓˢᵒ ℓˢʰ
    idnˢ
      : {a : obj}
      → S.cell₀[ homˢ a a ]
    cmpˢ
      : {a b c : obj}
      → homˢ b c S.⊗ homˢ a b S.⇒₀ homˢ a c

  field
    idn-lhs
      : {a b : obj}
      → (f : S.cell₀[ homˢ a b ])
      → S.hom⊗ (homˢ a b) (cmpˢ S.$₀ (idnˢ , f) , f)
    idn-rhs
      : {a b : obj}
      → (f : S.cell₀[ homˢ a b ])
      → S.hom⊗ (homˢ a b) (cmpˢ S.$₀ (f , idnˢ) , f)
    cmp-ass
      : {a b c d : obj}
      → (f : S.cell₀[ homˢ a b ])
      → (g : S.cell₀[ homˢ b c ])
      → (h : S.cell₀[ homˢ c d ])
      → S.hom⊗ (homˢ a d)
          ( cmpˢ S.$₀ (cmpˢ S.$₀ (h , g) , f)
          , cmpˢ S.$₀ (h , (cmpˢ S.$₀ (g , f)))
          )

open Category public
