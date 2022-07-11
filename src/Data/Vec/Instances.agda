------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Vec
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Instances where

open import Algebra               using (CommutativeRing)
open import Algebra.Module        using (Module)
open import Data.Nat.Base         using (ℕ)
open import Data.Vec.Base
open import Data.Vec.Effectful
open import Data.Vec.Properties
  using (≡-dec)
import Data.Vec.Properties.Equivalence          as VecEquiv
import Data.Vec.Relation.Binary.Equality.Setoid as VecSetoid
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using ()
open import Level
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses

private
  variable
    a : Level
    A : Set a

instance
  vecFunctor = functor
  vecApplicative = applicative

  Vec-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → ∀ {n} → IsDecEquivalence {A = Vec A n} _≡_
  Vec-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_)

module _
  {r ℓr : Level}
  {ring : CommutativeRing r ℓr}
  where

  open CommutativeRing ring hiding (ring) renaming (Carrier to R)
  open VecEquiv  setoid
  open VecSetoid setoid
  
  vecAsModule : (n : ℕ) → Module ring r (r ⊔ ℓr)
  vecAsModule n = record
    { Carrierᴹ = Vec R n
    ; _≈ᴹ_     = _≋_
    ; _+ᴹ_     = zipWith _+_
    ; _*ₗ_     = λ x v → map (x *_) v
    ; _*ᵣ_     = λ v x → map (x *_) v
    ; 0ᴹ       = replicate 0#
    ; -ᴹ_      = map (-_)
    ; isModule = record
        { isBimodule = record
            { isBisemimodule = record
                { +ᴹ-isCommutativeMonoid = record
                    { isMonoid = record
                        { isSemigroup = record
                            { isMagma = record
                                { isEquivalence = ≋-isEquivalence n
                                ; ∙-cong        = zipWith-cong₂ +-cong
                                }
                            ; assoc   = zipWith-assoc′ +-assoc
                            }
                        ; identity    = zipWith-id +-identity
                        }
                    ; comm     = zipWith-comm +-comm
                    }
                ; isPreleftSemimodule = record
                    { *ₗ-cong      =
                        λ { {x} {y} {[]}     {[]}     x≈y u≋v → ≋-refl
                          ; {x} {y} {u ∷ us} {v ∷ vs} x≈y u≋v →
                              ∷-cong₂ (*-cong x≈y (PW.head u≋v))
                                      (map-cong *-cong x≈y (PW.tail u≋v))
                          }
                    ; *ₗ-zeroˡ     =
                        λ { []       → ≋-refl
                          ; (x ∷ xs) → ∷-cong₂ (zeroˡ x) (map-zeroˡ {f = _*_} zeroˡ)
                          }
                    ; *ₗ-distribʳ  =
                        λ { []       _ _ → ≋-refl
                          ; (x₁ ∷ xs) x y →
                              ∷-cong₂ (distribʳ x₁ x y) (map-distribʳ distribʳ)
                          }
                    ; *ₗ-identityˡ =
                        λ { []       → ≋-refl
                          ; (x ∷ xs) → ∷-cong₂ (*-identityˡ x)
                                               (map-identity {f = _*_} *-identityˡ)
                          }
                    ; *ₗ-assoc     =
                        λ { x y xs → map-assoc {x = x} {y = y} {xs = xs} *-assoc }
                    ; *ₗ-zeroʳ     = λ x → map-zeroʳ {x = x} zeroʳ
                    ; *ₗ-distribˡ  =
                        λ { x []       []       → ≋-refl
                          ; x (u ∷ us) (v ∷ vs) → ∷-cong₂ (distribˡ x u v)
                                                          (map-distribˡ distribˡ)
                          }
                    }
                ; isPrerightSemimodule = record
                    { *ᵣ-cong      =
                        λ { {[]}      {[]}     {x} {y} xs≋ys x≈y → ≋-refl
                          ; {x₁ ∷ xs} {y₁ ∷ ys} {x} {y} xs≋ys x≈y →
                              ∷-cong₂ (*-cong x≈y (PW.head xs≋ys))
                                      (map-cong *-cong x≈y (PW.tail xs≋ys))
                          }
                    ; *ᵣ-zeroʳ     =
                        λ { []       → ≋-refl
                          ; (x ∷ xs) → ∷-cong₂ (zeroˡ x) (map-zeroˡ {f = _*_} zeroˡ)
                          }
                    ; *ᵣ-distribˡ  =
                        λ { []       x y → ≋-refl
                          ; (x₁ ∷ xs) x y →
                              ∷-cong₂ (distribʳ x₁ x y) (map-distribʳ distribʳ)
                          }
                    ; *ᵣ-identityʳ =
                        λ { []       → ≋-refl
                          ; (x ∷ xs) →
                              ∷-cong₂ (*-identityˡ x)
                                      (map-identity {f = _*_} *-identityˡ)
                          }
                    ; *ᵣ-assoc     =
                        λ { []       x y → ≋-refl
                          ; (x₁ ∷ xs) x y →
                              ∷-cong₂ (assoc′ *-assoc *-comm *-cong)
                                      (map-assoc′ *-assoc *-comm *-cong)
                          }
                    ; *ᵣ-zeroˡ     = λ { x → map-zeroʳ {f = _*_} zeroʳ }
                    ; *ᵣ-distribʳ  =
                        λ { x []        []       → ≋-refl
                          ; x (x₁ ∷ xs) (y₁ ∷ ys) →
                              ∷-cong₂ (distribˡ x x₁ y₁) (map-distribˡ distribˡ)
                          }
                    }
                ; *ₗ-*ᵣ-assoc          =
                    λ { _ []       y → ≋-refl
                      ; _ (_ ∷ _) y →
                          ∷-cong₂ (assoc′′ *-assoc *-comm *-cong)
                                 (map-assoc′′ *-assoc *-comm *-cong)
                      }
                }
            ; -ᴹ‿cong = map-cong₁ -‿cong
            ; -ᴹ‿inverse = map-inverse -‿inverse
            }
        }
    }
