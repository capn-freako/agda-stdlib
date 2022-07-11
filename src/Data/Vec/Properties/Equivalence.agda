------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vec-related properties on equivalence.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level                   using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Setoid)

module Data.Vec.Properties.Equivalence
  {a ℓa   : Level}
  (setoid : Setoid a ℓa)
  where

open Setoid setoid renaming (Carrier to A)
open import Data.Vec.Relation.Binary.Equality.Setoid setoid

open import Agda.Builtin.Sigma
open import Algebra.Definitions
open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using ()
open import Relation.Binary.ExtensionalEquivalence setoid
open import Relation.Binary.Reasoning.Setoid       setoid

private
  variable
    m n : ℕ
    
∷-cong₂ : ∀ {x y} {xs ys : Vec A n} → x ≈ y → xs ≋ ys → x ∷ xs ≋ y ∷ ys
∷-cong₂ {xs = []} {ys = []} x≈y _                     = x≈y PW.∷ PW.[]
∷-cong₂ {xs = x₁ ∷ []} {ys = y₁ ∷ []} x≈y xs≈ys        =
  x≈y PW.∷ (PW.head xs≈ys) PW.∷ PW.[]
∷-cong₂ {n} {x} {y} {x₁ ∷ xs} {y₁ ∷ ys} x≈y x₁∷xs≋y₁∷ys =
  PW.++⁺ x∷[x₁]≋y∷[y₁] xs≋ys
  where
  x₁≈y₁  = PW.head x₁∷xs≋y₁∷ys
  xs≋ys = PW.tail x₁∷xs≋y₁∷ys
  x∷[x₁]≋y∷[y₁] = ∷-cong₂ {xs = [ x₁ ]} {ys = [ y₁ ]} x≈y
                         ( ∷-cong₂ {x = x₁} {y = y₁} {xs = []} {ys = []}
                                   x₁≈y₁ ≋-refl
                         )

lookup-cong : {u : Vec A m} {v : Vec A m} →
              u ≋ v → (k : Fin m) → lookup u k ≈ lookup v k
lookup-cong {u = x ∷ _}  {v = y ∷ _}  u≋v zero    = PW.head u≋v
lookup-cong {u = _ ∷ xs} {v = _ ∷ ys} u≋v (suc k) =
  lookup-cong {u = xs} {v = ys} (PW.tail u≋v) k

tabulate-cong′ : {f g : Fin n → A} → f ≗ g → tabulate f ≋ tabulate g
tabulate-cong′ {n = zero}    f≗g = ≋-refl
tabulate-cong′ {n = ℕ.suc m} f≗g =
  ∷-cong₂ (f≗g zero) (tabulate-cong′ λ {x → f≗g (Fin.suc x)})

module _ {f : A → A} where

  map-cong₁ : Congruent₁ _≈_ f → Congruent₁ (_≋_{n})  (map f)
  map-cong₁ f-cong {[]}     {[]}     xs≋ys = xs≋ys
  map-cong₁ f-cong {x ∷ xs} {y ∷ ys} xs≋ys =
    ∷-cong₂ (f-cong (PW.head xs≋ys)) (map-cong₁ f-cong (PW.tail xs≋ys))
  
module _ {f : A → A → A} where

  zipWith-cong₂ : Congruent₂ _≈_ f → Congruent₂ (_≋_ {n}) (zipWith f)
  zipWith-cong₂ f-cong₂ {[]} {[]} {[]} {[]} _   _   = ≋-refl
  zipWith-cong₂ f-cong₂ {x ∷ xs} {y ∷ ys} {u ∷ us} {v ∷ vs} x∷xs≋y∷ys u∷us≋v∷vs =
    ∷-cong₂ (f-cong₂ x≈y u≈v) (zipWith-cong₂ f-cong₂ xs≋ys us≋vs)
    where
    x≈y   = PW.head x∷xs≋y∷ys
    xs≋ys = PW.tail x∷xs≋y∷ys
    u≈v   = PW.head u∷us≋v∷vs
    us≋vs = PW.tail u∷us≋v∷vs
  
  zipWith-assoc′ : Associative _≈_ f → Associative _≋_ (zipWith {n = n} f)
  zipWith-assoc′ assoc []       []       []       = ≋-refl
  zipWith-assoc′ assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    ∷-cong₂ (assoc x y z) (zipWith-assoc′ assoc xs ys zs)

  zipWith-comm : ∀ {n} → Commutative _≈_ f → Commutative (_≋_ {n}) (zipWith f)
  zipWith-comm f-comm =
    λ { []       []       → ≋-refl
      ; (x ∷ xs) (y ∷ ys) → ∷-cong₂ (f-comm x y) (zipWith-comm f-comm xs ys) }

  map-cong : ∀ {x y : A} {xs ys : Vec A n} → Congruent₂ _≈_ f →
             x ≈ y → xs ≋ ys → map (f x) xs ≋ map (f y) ys
  map-cong {.zero}      {x} {y} {[]}      {[]}     f-cong x≈y xs≋ys = ≋-refl
  map-cong {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} {y₁ ∷ ys} f-cong x≈y xs≋ys =
    ∷-cong₂ (f-cong x≈y (PW.head xs≋ys)) (map-cong f-cong x≈y (PW.tail xs≋ys))

  map-assoc : ∀ {x y} {xs : Vec A n} → Associative _≈_ f →
              map (f (f x y)) xs ≋ map (f x) (map (f y) xs)
  map-assoc {.zero}      {x} {y} {[]}     f-assoc = ≋-refl
  map-assoc {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} f-assoc =
    ∷-cong₂ (f-assoc x y x₁) (map-assoc f-assoc)

  assoc′ : ∀ {x y z} →
           Associative _≈_ f → Commutative _≈_ f → Congruent₂ _≈_ f →
           f y (f x z) ≈ f (f x y) z
  assoc′ {x} {y} {z} f-assoc f-comm f-cong = begin
    f y (f x z) ≈⟨ sym (f-assoc y x z) ⟩
    f (f y x) z ≈⟨ f-cong (f-comm y x) refl ⟩
    f (f x y) z ∎
           
  assoc′′ : ∀ {x y z} →
           Associative _≈_ f → Commutative _≈_ f → Congruent₂ _≈_ f →
           f y (f x z) ≈ f x (f y z)
  assoc′′ {x} {y} {z} f-assoc f-comm f-cong = begin
    f y (f x z) ≈⟨ assoc′ f-assoc f-comm f-cong ⟩
    f (f x y) z ≈⟨ f-assoc x y z ⟩
    f x (f y z) ∎
           
  map-assoc′ : ∀ {x y} {xs : Vec A n} →
              Associative _≈_ f → Commutative _≈_ f → Congruent₂ _≈_ f →
              map (f y) (map (f x) xs) ≋ map (f  (f x y)) xs
  map-assoc′ {.zero}      {x} {y} {[]}     f-assoc f-comm f-cong = ≋-refl
  map-assoc′ {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} f-assoc f-comm f-cong =
    ∷-cong₂ (assoc′ f-assoc f-comm f-cong) (map-assoc′ f-assoc f-comm f-cong)
  
  map-assoc′′ : ∀ {x y} {xs : Vec A n} →
              Associative _≈_ f → Commutative _≈_ f → Congruent₂ _≈_ f →
              map (f y) (map (f x) xs) ≋ map (f x) (map (f y) xs)
  map-assoc′′ {.zero}      {x} {y} {[]}     f-assoc f-comm f-cong = ≋-refl
  map-assoc′′ {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} f-assoc f-comm f-cong =
    ∷-cong₂ (assoc′′ f-assoc f-comm f-cong) (map-assoc′′ f-assoc f-comm f-cong)

module _ {f : A → A → A} {ε : A} where

  zipWith-idˡ : ∀ {n} → LeftIdentity _≈_ ε f →
               LeftIdentity (_≋_ {n}) (replicate ε) (zipWith f)
  zipWith-idˡ ≈-idˡ = λ { []       → ≋-refl
                        ; (x ∷ xs) → ∷-cong₂ (≈-idˡ x) (zipWith-idˡ ≈-idˡ xs) }

  zipWith-idʳ : ∀ {n} → RightIdentity _≈_ ε f →
               RightIdentity (_≋_ {n}) (replicate ε) (zipWith f)
  zipWith-idʳ ≈-idʳ = λ { []       → ≋-refl
                        ; (x ∷ xs) → ∷-cong₂ (≈-idʳ x) (zipWith-idʳ ≈-idʳ xs) }

  zipWith-id : ∀ {n} → Identity _≈_ ε f →
               Identity (_≋_ {n}) (replicate ε) (zipWith f)
  zipWith-id ≈-id = zipWith-idˡ (fst ≈-id) , zipWith-idʳ (snd ≈-id)

  map-zeroˡ : {xs : Vec A n} → LeftZero _≈_ ε f →
             map (f ε) xs ≋ replicate ε
  map-zeroˡ {.zero}      {[]}     f-zeroˡ = ≋-refl
  map-zeroˡ {.(ℕ.suc _)} {x ∷ xs} f-zeroˡ = ∷-cong₂ (f-zeroˡ x) (map-zeroˡ f-zeroˡ)
  
  map-zeroʳ : {x : A} → RightZero _≈_ ε f →
             map (f x) (replicate {n = n} ε) ≋ replicate ε
  map-zeroʳ {zero}        f-zeroʳ = ≋-refl
  map-zeroʳ {ℕ.suc n} {x} f-zeroʳ = ∷-cong₂ (f-zeroʳ x) (map-zeroʳ f-zeroʳ)
  
  map-identity : {xs : Vec A n} → LeftIdentity _≈_ ε f →
             map (f ε) xs ≋ xs
  map-identity {.zero}      {[]}     f-identity = ≋-refl
  map-identity {.(ℕ.suc _)} {x ∷ xs} f-identity = ∷-cong₂ (f-identity x) (map-identity f-identity)
  
module _ {_⊕_ : A → A → A} {_⊛_ : A → A → A} where

  map-distribʳ : ∀ {x y} {xs : Vec A n} → (_DistributesOverʳ_ _≈_) _⊛_ _⊕_ →
                map ((x ⊕ y) ⊛_) xs ≋ zipWith _⊕_ (map (x ⊛_) xs) (map (y ⊛_) xs)
  map-distribʳ {.zero}      {x} {y} {[]}     ⊛-distrib-⊕ = ≋-refl
  map-distribʳ {.(ℕ.suc _)} {x} {y} {x₁ ∷ xs} ⊛-distrib-⊕ =
    ∷-cong₂ (⊛-distrib-⊕ x₁ x y) (map-distribʳ ⊛-distrib-⊕)

  map-distribˡ : ∀ {x} {xs ys : Vec A n} → (_DistributesOverˡ_ _≈_) _⊛_ _⊕_ →
                map (x ⊛_) (zipWith _⊕_ xs ys) ≋ zipWith _⊕_ (map (x ⊛_) xs)
                                                             (map (x ⊛_) ys)
  map-distribˡ {.zero}      {x} {[]}     {[]}     ⊛-distrib-⊕ = ≋-refl
  map-distribˡ {.(ℕ.suc _)} {x} {x₁ ∷ xs} {y ∷ ys} ⊛-distrib-⊕ =
    ∷-cong₂ (⊛-distrib-⊕ x x₁ y) (map-distribˡ ⊛-distrib-⊕)

module _ {_⊕_ : A → A → A} {⊝_ : A → A} {ε : A} where

  zipWith-inverseˡ : {xs : Vec A n} → LeftInverse _≈_ ε ⊝_ _⊕_ →
                    zipWith _⊕_ (map ⊝_ xs) xs ≋ replicate {n = n} ε
  zipWith-inverseˡ {.zero}      {[]}     ≈-inv = ≋-refl
  zipWith-inverseˡ {.(ℕ.suc _)} {x ∷ xs} ≈-inv =
    ∷-cong₂ (≈-inv x) (zipWith-inverseˡ ≈-inv)
                    
  zipWith-inverseʳ : {xs : Vec A n} → RightInverse _≈_ ε ⊝_ _⊕_ →
                    zipWith _⊕_ xs (map ⊝_ xs) ≋ replicate {n = n} ε
  zipWith-inverseʳ {.zero}      {[]}     ≈-inv = ≋-refl
  zipWith-inverseʳ {.(ℕ.suc _)} {x ∷ xs} ≈-inv =
    ∷-cong₂ (≈-inv x) (zipWith-inverseʳ ≈-inv)
                    
  map-inverse : Inverse _≈_ ε ⊝_ _⊕_ →
                Inverse (_≋_ {n}) (replicate ε) (map ⊝_) (zipWith _⊕_)
  map-inverse {zero}    ≈-inv = (λ { [] → ≋-refl })
                              , (λ { [] → ≋-refl })
  map-inverse {ℕ.suc n} (≈-invˡ , ≈-invʳ) =
    (λ { (x ∷ xs) → ∷-cong₂ (≈-invˡ x) (zipWith-inverseˡ ≈-invˡ) })
    , λ { (x ∷ xs) → ∷-cong₂ (≈-invʳ x) (zipWith-inverseʳ ≈-invʳ) }
