{-# OPTIONS --without-K --safe #-}

module Categories.Category.Monoidal.Instance.PartialFunctions where

open import Data.Maybe using (Maybe; nothing; just; map; zip)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂)
  renaming (swap to swap×; assocʳ′ to assocʳ×; assocˡ′ to assocˡ×)
open import Data.Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
  renaming (swap to swap⊎; assocʳ to assocʳ⊎; assocˡ to assocˡ⊎)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤*; tt to tt*)
open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥*; ⊥-elim to ⊥*-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst₂)
open import Function using (_∘_; case_of_)
open import Level

open import Categories.Category.Instance.PartialFunctions using (PartialFunctions)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory using (RigCategory)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

module Product {o : Level} where
  private
    P = PartialFunctions o

  module _ where
    open Bifunctor

    P⊗ : Bifunctor P P P

    P⊗ .F₀ (X , Y)         = X × Y
    P⊗ .F₁ (f , g) (x , y) = zip (f x) (g y)
    P⊗ .identity   (x , y) = refl

    P⊗ .homomorphism {f = f₁ , f₂} (x₁ , x₂)
      with f₁ x₁ | f₂ x₂
    ... | just y₁ | just y₂ = refl
    ... | nothing | nothing = refl
    P⊗ .homomorphism {g = g₁ , g₂} _ | just y₁ | nothing
      with g₁ y₁
    ... | just z₁ = refl
    ... | nothing = refl
    P⊗ .homomorphism {g = g₁ , g₂} _ | nothing | just y₂
      with g₂ y₂
    ... | just z₂ = refl
    ... | nothing = refl

    P⊗ .F-resp-≈ {f = f₁ , f₂} {g = g₁ , g₂} (f₁≗g₁ , f₂≗g₂) (x₁ , x₂)
      with f₁ x₁ in y₁= | g₁ x₁ in z₁=
    ... | nothing | nothing = refl
    ... | just y₁ | nothing = case subst₂ _≡_ y₁= z₁= (f₁≗g₁ x₁) of λ ()
    ... | nothing | just z₁ = case subst₂ _≡_ y₁= z₁= (f₁≗g₁ x₁) of λ ()
    ... | just y₁ | just z₁
      with f₂ x₂ in y₂= | g₂ x₂ in z₂=
    ... | nothing | nothing = refl
    ... | just y₂ | nothing = case subst₂ _≡_ y₂= z₂= (f₂≗g₂ x₂) of λ ()
    ... | nothing | just z₂ = case subst₂ _≡_ y₂= z₂= (f₂≗g₂ x₂) of λ ()
    ... | just y₂ | just z₂ = cong just (cong₂ _,_ y₁=z₁ y₂=z₂)
      where
        y₁=z₁ = just-injective (subst₂ _≡_ y₁= z₁= (f₁≗g₁ x₁))
        y₂=z₂ = just-injective (subst₂ _≡_ y₂= z₂= (f₂≗g₂ x₂))

  module _ where
    open Monoidal

    PM⊗ : Monoidal P

    PM⊗ .⊗    = P⊗
    PM⊗ .unit = ⊤*

    PM⊗ .unitorˡ    = record
      { from = just ∘ proj₂
      ; to   = just ∘ (tt* ,_)
      ; iso  = record
        { isoˡ = λ _ → refl
        ; isoʳ = λ _ → refl
        }
      }
    PM⊗ .unitorʳ    = record
      { from = just ∘ proj₁
      ; to   = just ∘ (_, tt*)
      ; iso  = record
        { isoˡ = λ _ → refl
        ; isoʳ = λ _ → refl
        }
      }
    PM⊗ .associator = record
      { from = just ∘ assocʳ×
      ; to   = just ∘ assocˡ×
      ; iso  = record
        { isoˡ = λ _ → refl
        ; isoʳ = λ _ → refl
        }
      }

    PM⊗ .unitorˡ-commute-from {f = f} (lift tt , x)
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊗ .unitorˡ-commute-to   {f = f}            x
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊗ .unitorʳ-commute-from {f = f} (x , lift tt)
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊗ .unitorʳ-commute-to   {f = f}  x
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊗ .assoc-commute-from   {f = f} {g = g} {h = h} ((x , y) , z)
      with f x
    ... | nothing = refl
    ... | just fx
      with g y
    ... | nothing = refl
    ... | just gy
      with h z
    ... | nothing = refl
    ... | just hz = refl
    PM⊗ .assoc-commute-to     {f = f} {g = g} {h = h} (x , (y , z))
      with f x
    ... | nothing = refl
    ... | just fx
      with g y
    ... | nothing = refl
    ... | just gy
      with h z
    ... | nothing = refl
    ... | just hz = refl

    PM⊗ .triangle _ = refl
    PM⊗ .pentagon _ = refl

  module _ where
    open Braided
    open NaturalIsomorphism
    open NaturalTransformation

    PB⊗ : Braided PM⊗

    PB⊗ .braiding .F⇒G .η _ = just ∘ swap×
    PB⊗ .braiding .F⇒G .commute     (f , g) (x , y)
      with f x | g y
    ... | nothing | nothing = refl
    ... | just fx | nothing = refl
    ... | nothing | just gy = refl
    ... | just fx | just gy = refl
    PB⊗ .braiding .F⇒G .sym-commute (f , g) (x , y)
      with f x | g y
    ... | nothing | nothing = refl
    ... | just fx | nothing = refl
    ... | nothing | just gy = refl
    ... | just fx | just gy = refl

    PB⊗ .braiding .F⇐G .η _ = just ∘ swap×
    PB⊗ .braiding .F⇐G .commute     (f , g) (y , x)
      with g y | f x
    ... | nothing | nothing = refl
    ... | just gy | nothing = refl
    ... | nothing | just fx = refl
    ... | just gy | just fx = refl
    PB⊗ .braiding .F⇐G .sym-commute (f , g) (y , x)
      with g y | f x
    ... | nothing | nothing = refl
    ... | just gy | nothing = refl
    ... | nothing | just fx = refl
    ... | just gy | just fx = refl

    PB⊗ .braiding .iso (X , Y) = record
      { isoˡ = λ _ → refl
      ; isoʳ = λ _ → refl
      }

    PB⊗ .hexagon₁ _ = refl
    PB⊗ .hexagon₂ _ = refl

  module _ where
    open Symmetric

    PS⊗ : Symmetric PM⊗
    PS⊗ .braided       = PB⊗
    PS⊗ .commutative _ = refl

module Sum {o : Level} where
  private
    P = PartialFunctions o

  module _ where
    open Bifunctor

    P⊕ : Bifunctor P P P

    P⊕ .F₀ (X , Y)          = X ⊎ Y
    P⊕ .F₁ (f , g) (inj₁ x) = map inj₁ (f x)
    P⊕ .F₁ (f , g) (inj₂ y) = map inj₂ (g y)
    P⊕ .identity   (inj₁ x) = refl
    P⊕ .identity   (inj₂ y) = refl

    P⊕ .homomorphism {f = f₁ , f₂} (inj₁ x₁)
      with f₁ x₁
    ... | nothing = refl
    ... | just y₁ = refl
    P⊕ .homomorphism {f = f₁ , f₂} (inj₂ x₂)
      with f₂ x₂
    ... | nothing = refl
    ... | just y₂ = refl

    P⊕ .F-resp-≈ {f = f₁ , f₂} {g = g₁ , g₂} (f₁≗g₁ , f₂≗g₂) (inj₁ x₁) =
      cong (map inj₁) (f₁≗g₁ x₁)
    P⊕ .F-resp-≈ {f = f₁ , f₂} {g = g₁ , g₂} (f₁≗g₁ , f₂≗g₂) (inj₂ x₂) =
      cong (map inj₂) (f₂≗g₂ x₂)

  module _ where
    open Monoidal

    PM⊕ : Monoidal P

    PM⊕ .⊗    = P⊕
    PM⊕ .unit = ⊥*

    PM⊕ .unitorˡ    = record
      { from = [ ⊥*-elim , just ]′
      ; to   = just ∘ inj₂
      ; iso  = record
        { isoˡ = λ where (inj₂ _) → refl
        ; isoʳ = λ             _  → refl 
        }
      }
    PM⊕ .unitorʳ    = record
      { from = [ just , ⊥*-elim ]′
      ; to   = just ∘ inj₁
      ; iso  = record
        { isoˡ = λ where (inj₁ _) → refl
        ; isoʳ = λ             _  → refl
        }
      }
    PM⊕ .associator = record
      { from = just ∘ assocʳ⊎
      ; to   = just ∘ assocˡ⊎
      ; iso  = record
        { isoˡ = λ where
          (inj₁ (inj₁ _)) → refl
          (inj₁ (inj₂ _)) → refl
          (inj₂       _ ) → refl
        ; isoʳ = λ where
          (inj₁       _ ) → refl
          (inj₂ (inj₁ _)) → refl
          (inj₂ (inj₂ _)) → refl
        }
      }

    PM⊕ .unitorˡ-commute-from {f = f} (inj₂ x)
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊕ .unitorˡ-commute-to   {f = f}       x
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊕ .unitorʳ-commute-from {f = f} (inj₁ x)
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊕ .unitorʳ-commute-to   {f = f}       x
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊕ .assoc-commute-from   {f = f} {g = g} {h = h} (inj₁ (inj₁ x))
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊕ .assoc-commute-from   {f = f} {g = g} {h = h} (inj₁ (inj₂ y))
      with g y
    ... | nothing = refl
    ... | just gy = refl
    PM⊕ .assoc-commute-from   {f = f} {g = g} {h = h} (inj₂       z )
      with h z
    ... | nothing = refl
    ... | just hz = refl
    PM⊕ .assoc-commute-to     {f = f} {g = g} {h = h} (inj₁       x )
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PM⊕ .assoc-commute-to     {f = f} {g = g} {h = h} (inj₂ (inj₁ y))
      with g y
    ... | nothing = refl
    ... | just gy = refl
    PM⊕ .assoc-commute-to     {f = f} {g = g} {h = h} (inj₂ (inj₂ z))
      with h z
    ... | nothing = refl
    ... | just hz = refl

    PM⊕ .triangle (inj₁ (inj₁ x ))       = refl
    PM⊕ .triangle (inj₂       y  )       = refl

    PM⊕ .pentagon (inj₁ (inj₁ (inj₁ x))) = refl
    PM⊕ .pentagon (inj₁ (inj₁ (inj₂ y))) = refl
    PM⊕ .pentagon (inj₁ (inj₂       z )) = refl
    PM⊕ .pentagon (inj₂             w  ) = refl

  module _ where
    open Braided
    open NaturalIsomorphism
    open NaturalTransformation
  
    PB⊕ : Braided PM⊕

    PB⊕ .braiding .F⇒G .η _ = just ∘ swap⊎
    PB⊕ .braiding .F⇒G .commute     (f , g) (inj₁ x)
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PB⊕ .braiding .F⇒G .commute     (f , g) (inj₂ y)
      with g y
    ... | nothing = refl
    ... | just gy = refl
    PB⊕ .braiding .F⇒G .sym-commute (f , g) (inj₁ x)
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PB⊕ .braiding .F⇒G .sym-commute (f , g) (inj₂ y)
      with g y
    ... | nothing = refl
    ... | just gy = refl

    PB⊕ .braiding .F⇐G .η _ = just ∘ swap⊎
    PB⊕ .braiding .F⇐G .commute     (f , g) (inj₁ y)
      with g y
    ... | nothing = refl
    ... | just gy = refl
    PB⊕ .braiding .F⇐G .commute     (f , g) (inj₂ x)
      with f x
    ... | nothing = refl
    ... | just fx = refl
    PB⊕ .braiding .F⇐G .sym-commute (f , g) (inj₁ y)
      with g y
    ... | nothing = refl
    ... | just gy = refl
    PB⊕ .braiding .F⇐G .sym-commute (f , g) (inj₂ x)
      with f x
    ... | nothing = refl
    ... | just fx = refl

    PB⊕ .braiding .iso (X , Y) = record
      { isoˡ = λ where
        (inj₁ x) → refl
        (inj₂ y) → refl
      ; isoʳ = λ where
        (inj₁ y) → refl
        (inj₂ x) → refl
      }

    PB⊕ .hexagon₁ (inj₁ (inj₁ x)) = refl
    PB⊕ .hexagon₁ (inj₁ (inj₂ y)) = refl
    PB⊕ .hexagon₁ (inj₂       z ) = refl
    PB⊕ .hexagon₂ (inj₁       x ) = refl
    PB⊕ .hexagon₂ (inj₂ (inj₁ y)) = refl
    PB⊕ .hexagon₂ (inj₂ (inj₂ z)) = refl

  module _ where
    open Symmetric

    PS⊕ : Symmetric PM⊕
    PS⊕ .braided              = PB⊕
    PS⊕ .commutative (inj₁ y) = refl
    PS⊕ .commutative (inj₂ x) = refl

module Rig {o : Level} where
  open Product
  open Sum

  private
    P = PartialFunctions o

  module _ where
    open RigCategory

    PRig : RigCategory P PS⊕ PS⊗

    PRig .annₗ = record
      { from = λ ()
      ; to   = λ ()
      ; iso  = record
        { isoˡ = λ ()
        ; isoʳ = λ ()
        }
      }
    PRig .annᵣ = record
      { from = λ ()
      ; to   = λ ()
      ; iso  = record
        { isoˡ = λ ()
        ; isoʳ = λ ()
        }
      }

    PRig .distribₗ = record
      { from = λ where
        (x , inj₁ y)   → just (inj₁ (x , y))
        (x , inj₂ z)   → just (inj₂ (x , z))
      ; to   = λ where
        (inj₁ (x , y)) → just (x , inj₁ y)
        (inj₂ (x , z)) → just (x , inj₂ z)
      ; iso  = record
        { isoˡ = λ where
          (x , inj₁ y)   → refl
          (x , inj₂ z)   → refl
        ; isoʳ = λ where
          (inj₁ (x , y)) → refl
          (inj₂ (x , z)) → refl
        }
      }
    PRig .distribᵣ = record
      { from = λ where
        (inj₁ x , z)   → just (inj₁ (x , z))
        (inj₂ y , z)   → just (inj₂ (y , z))
      ; to   = λ where
        (inj₁ (x , z)) → just (inj₁ x , z)
        (inj₂ (y , z)) → just (inj₂ y , z)
      ; iso  = record
        { isoˡ = λ where
          (inj₁ x , z)   → refl
          (inj₂ y , z)   → refl
        ; isoʳ = λ where
          (inj₁ (x , z)) → refl
          (inj₂ (y , z)) → refl
        }
      }

    PRig .annₗ-commute ()
    PRig .annᵣ-commute ()

    PRig .dl-commute {f = f} {g = g} {h = h} (x , inj₁ y)
      with f x
    ... | nothing = refl
    ... | just fx
      with g y
    ... | nothing = refl
    ... | just gy = refl
    PRig .dl-commute {f = f} {g = g} {h = h} (x , inj₂ z)
      with f x
    ... | nothing = refl
    ... | just fx
      with h z
    ... | nothing = refl
    ... | just hz = refl
    PRig .dr-commute {f = f} {g = g} {h = h} (inj₁ x , z)
      with f x
    ... | nothing = refl
    ... | just fx
      with h z
    ... | nothing = refl
    ... | just hz = refl
    PRig .dr-commute {f = f} {g = g} {h = h} (inj₂ y , z)
      with g y
    ... | nothing = refl
    ... | just gy
      with h z
    ... | nothing = refl
    ... | just hz = refl

    PRig .laplazaI     (a , inj₁ b)        = refl
    PRig .laplazaI     (a , inj₂ c)        = refl
    PRig .laplazaII    (inj₁ a , c)        = refl
    PRig .laplazaII    (inj₂ b , c)        = refl
    PRig .laplazaIV    (inj₁       a  , d) = refl
    PRig .laplazaIV    (inj₂ (inj₁ b) , d) = refl
    PRig .laplazaIV    (inj₂ (inj₂ c) , d) = refl
    PRig .laplazaVI    (a , b , inj₁ c)    = refl
    PRig .laplazaVI    (a , b , inj₂ d)    = refl
    PRig .laplazaIX    (inj₁ a , inj₁ c)   = refl
    PRig .laplazaIX    (inj₁ a , inj₂ d)   = refl
    PRig .laplazaIX    (inj₂ b , inj₁ c)   = refl
    PRig .laplazaIX    (inj₂ b , inj₂ d)   = refl
    PRig .laplazaX     ()
    PRig .laplazaXI    ()
    PRig .laplazaXIII  ()
    PRig .laplazaXV    ()
    PRig .laplazaXVI   ()
    PRig .laplazaXVII  ()
    PRig .laplazaXIX   (a , inj₂ b)        = refl
    PRig .laplazaXXIII (lift tt , inj₁ a)  = refl
    PRig .laplazaXXIII (lift tt , inj₂ b)  = refl
