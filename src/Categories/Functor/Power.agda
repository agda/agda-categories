{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Power Functors, Exponentials over a Category C

-- Mainly categories where the objects are functions (Fin n -> Obj) considered pointwise
--   and then upgraded to Functors.

module Categories.Functor.Power {o ℓ e} (C : Category o ℓ e) where

open Category C
open HomReasoning
open Equiv

open import Level using (Level; _⊔_)
open import Data.Nat.Base using (ℕ; _+_; zero; suc; _<_)
open import Data.Product using (_,_)
open import Data.Fin.Base using (Fin; inject+; raise; zero; suc; fromℕ<)
open import Data.Sum using (_⊎_; inj₁; inj₂; map) renaming ([_,_] to ⟦_,_⟧; [_,_]′ to ⟦_,_⟧′)
open import Data.Vec.N-ary hiding (curryⁿ)
open import Function.Base as Fun using (flip; _$_) renaming (_∘_ to _∙_; id to idf)

open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor using (Bifunctor; overlap-×)

private
  variable
    i j k : Level
    I I′ J J′ : Set i
    D E : Category i j k
    n n′ m m′ : ℕ

Exp : Set i → Category _ _ _
Exp I = record
  { Obj       = I → Obj
  ; _⇒_       = λ x y → ∀ i → x i ⇒ y i
  ; _≈_       = λ f g → ∀ i → f i ≈ g i
  ; id        = λ _ → id
  ; _∘_       = λ f g i → f i ∘ g i
  ; assoc     = λ _ → assoc
  ; sym-assoc = λ _ → sym-assoc
  ; identityˡ = λ _ → identityˡ
  ; identityʳ = λ _ → identityʳ
  ; identity² = λ _ → identity²
  ; equiv     = record
    { refl  = λ _ → refl
    ; sym   = λ eq i → sym $ eq i
    ; trans = λ eq₁ eq₂ i → trans (eq₁ i) (eq₂ i)
    }
  ; ∘-resp-≈  = λ eq₁ eq₂ i → ∘-resp-≈ (eq₁ i) (eq₂ i)
  }

Power : (n : ℕ) → Category o ℓ e
Power n = Exp (Fin n)

-- Convention: the ′ version is for a general index set, unprimed for a ℕ
-- representing Fin n.  So Powerfunctor D n is Exp C (Fin n) ⇒ D, i.e.
-- essentially C ^ n ⇒ D.
Powerfunctor′ : (D : Category o ℓ e) (I : Set i) → Set (i ⊔ e ⊔ ℓ ⊔ o)
Powerfunctor′ D I = Functor (Exp I) D

Powerfunctor : (D : Category o ℓ e) (n : ℕ) → Set (e ⊔ ℓ ⊔ o)
Powerfunctor D n = Powerfunctor′ D (Fin n)

-- With C = D, so Powerendo n is C ^ n => C
Powerendo′ : (I : Set i) → Set (i ⊔ e ⊔ ℓ ⊔ o)
Powerendo′ I = Powerfunctor′ C I

Powerendo : (n : ℕ) → Set (e ⊔ ℓ ⊔ o)
Powerendo n = Powerfunctor C n

-- Hyperendo n m is C ^ n ⇒ C ^ m
Hyperendo : (n m : ℕ) → Set (e ⊔ ℓ ⊔ o)
Hyperendo n m = Functor (Power n) (Power m)

-- Hyperendo′ I J is C ^ I → C ^ J
Hyperendo′ : (I : Set i) (J : Set j) → Set (i ⊔ j ⊔ e ⊔ ℓ ⊔ o)
Hyperendo′ I J = Functor (Exp I) (Exp J)

-- Parallel composition of Hyperendo′ (via disjoint union of index sets)
infixr 9 _par_

_par_ : (F : Hyperendo′ I I′) (G : Hyperendo′ J J′) → Hyperendo′ (I ⊎ J) (I′ ⊎ J′)
F par G = record
  { F₀           = λ xs →  ⟦ F.F₀ (xs ∙ inj₁) , G.F₀ (xs ∙ inj₂) ⟧′
  ; F₁           = λ fs → ⟦ F.F₁ (fs ∙ inj₁) , G.F₁ (fs ∙ inj₂) ⟧
  ; identity     = ⟦ F.identity , G.identity ⟧
  ; homomorphism = ⟦ F.homomorphism , G.homomorphism ⟧
  ; F-resp-≈     = λ fs≈gs → ⟦ F.F-resp-≈ (fs≈gs ∙ inj₁) , G.F-resp-≈ (fs≈gs ∙ inj₂) ⟧
  }
  where module F = Functor F
        module G = Functor G

-- "flattening" means going from a general disjoint union of Fin to a single Fin,
-- which has the effect of doing from Powerfunctor′ to Powerfunctor
flattenP : (F : Powerfunctor′ D (Fin n ⊎ Fin m)) → Powerfunctor D (n + m)
flattenP {n = n} {m = m} F = record
  { F₀           = λ As → F₀ (As ∙ pack)
  ; F₁           = λ fs → F₁ (fs ∙ pack)
  ; identity     = identity
  ; homomorphism = homomorphism
  ; F-resp-≈     = λ fs≈gs → F-resp-≈ (fs≈gs ∙ pack)
  }
  where open Functor F
        pack = ⟦ inject+ m , raise n ⟧′

-- TODO unpackFun (and pack above) should be in stdlib
private
  unpackFin : ∀ n → Fin (n + m) → Fin n ⊎ Fin m
  unpackFin zero f          = inj₂ f
  unpackFin (suc n) zero    = inj₁ zero
  unpackFin (suc n) (suc f) = map suc idf (unpackFin n f)

-- needs a better name?
unflattenP : Powerfunctor D (n + m) → Powerfunctor′ D (Fin n ⊎ Fin m)
unflattenP {n = n} {m = m} F = record
  { F₀           = λ As → F₀ (As ∙ unpackFin _)
  ; F₁           = λ fs → F₁ (fs ∙ unpackFin _)
  ; identity     = identity
  ; homomorphism = homomorphism
  ; F-resp-≈     = λ fs≈gs → F-resp-≈ (fs≈gs ∙ unpackFin _)
  }
  where open Functor F

-- flatten a Hyperendo′ "on the right" when over a union of Fin
flattenHʳ : (F : Hyperendo′ I (Fin n ⊎ Fin m)) → Hyperendo′ I (Fin (n + m))
flattenHʳ {n = n} {m = m} F = record
  { F₀           = λ As → F₀ As ∙ unpackFin n
  ; F₁           = λ fs → F₁ fs ∙ unpackFin n
  ; identity     = identity ∙ unpackFin n
  ; homomorphism = homomorphism ∙ unpackFin n
  ; F-resp-≈     = λ fs≈gs → F-resp-≈ fs≈gs ∙ unpackFin n
  }
  where open Functor F

-- flatten on both sides.
flattenH : (F : Hyperendo′ (Fin n ⊎ Fin m) (Fin n′ ⊎ Fin m′)) → Hyperendo (n + m) (n′ + m′)
flattenH = flattenHʳ ∙ flattenP

-- Pretty syntax for flattening of parallel composition of Hyperendo
infixr 9 _∥_

_∥_ : (F : Hyperendo n n′) (G : Hyperendo m m′) → Hyperendo (n + m) (n′ + m′)
F ∥ G = flattenH (F par G)

-- split is C ^ (I ⊎ J) to C ^ I × C ^ J, as a Functor
split : Functor (Exp (I ⊎ J)) (Product (Exp I) (Exp J))
split = record
  { F₀           = λ As → As ∙ inj₁ , As ∙ inj₂
  ; F₁           = λ fs → fs ∙ inj₁ , fs ∙ inj₂
  ; identity     = (λ _ → refl) , λ _ → refl
  ; homomorphism = (λ _ → refl) , λ _ → refl
  ; F-resp-≈     = λ eq → (λ i → eq (inj₁ i)) , λ i → eq (inj₂ i)
  }

reduce′ : (H : Bifunctor C C C) (F : Powerendo′ I) (G : Powerendo′ J) → Powerendo′ (I ⊎ J)
reduce′ H F G = H ∘F (F ⁂ G) ∘F split

reduce : ∀ (H : Bifunctor C C C) {n m} (F : Powerendo n) (G : Powerendo m) → Powerendo (n + m)
reduce H F G = flattenP $ reduce′ H F G

flattenP-assocʳ : ∀ {n₁ n₂ n₃} (F : Powerendo′ (Fin n₁ ⊎ Fin n₂ ⊎ Fin n₃)) → Powerendo (n₁ + n₂ + n₃)
flattenP-assocʳ {n₁} {n₂} {n₃} F = record
  { F₀           = λ As → F.F₀ (As ∙ pack)
  ; F₁           = λ fs → F.F₁ (fs ∙ pack)
  ; identity     = F.identity
  ; homomorphism = F.homomorphism
  ; F-resp-≈     = λ fs≈gs → F.F-resp-≈ (fs≈gs ∙ pack)
  }
  where module F = Functor F
        pack = ⟦ inject+ n₃ ∙ inject+ n₂ , ⟦ inject+ n₃ ∙ raise n₁ , raise (n₁ + n₂) ⟧′ ⟧′

reduce2ʳ : ∀ (G : Bifunctor C C C) {n₁ n₂ n₃} (F₁ : Powerendo n₁) (F₂ : Powerendo n₂) (F₃ : Powerendo n₃) → Powerendo ((n₁ + n₂) + n₃)
reduce2ʳ G F₁ F₂ F₃ = flattenP-assocʳ $ reduce′ G F₁ $ reduce′ G F₂ F₃

overlaps : (H : Bifunctor D D E) (F G : Powerfunctor′ D I) → Powerfunctor′ E I
overlaps = overlap-×

overlap2ʳ : (G : Bifunctor C C C) (F₁ F₂ F₃ : Powerendo n) → Powerendo n
overlap2ʳ G F₁ F₂ F₃ = overlaps G F₁ (overlaps G F₂ F₃)

-- select′ i always evaluates at i
select′ : (i : I) → Powerendo′ I
select′ i = record
  { F₀           = _$ i
  ; F₁           = _$ i
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = _$ i
  }

-- select (m < n) is really select′ (Fin n), but only for m < n
select : m < n → Powerendo n
select m<n = select′ (fromℕ< m<n)

triv : (n : ℕ) → Hyperendo n n
triv n = record
  { F₀           = idf
  ; F₁           = idf
  ; identity     = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≈     = idf
  }

-- pad a Hyperendo on the left and right by trivial (i.e. identity) endofunctors
pad : ∀ (l r : ℕ) (F : Hyperendo n m) → Hyperendo ((l + n) + r) ((l + m) + r)
pad l r F = (triv l ∥ F) ∥ triv r

padˡ : ∀ (l : ℕ) (F : Hyperendo n m) → Hyperendo (l + n) (l + m)
padˡ l F = triv l ∥ F

padʳ : ∀ (r : ℕ) (F : Hyperendo n m) → Hyperendo (n + r) (m + r)
padʳ r F = F ∥ triv r

unary : Endofunctor C → Powerendo 1
unary F = record
  { F₀           = λ As → F.F₀ (As zero)
  ; F₁           = λ fs → F.F₁ (fs zero)
  ; identity     = F.identity
  ; homomorphism = F.homomorphism
  ; F-resp-≈     = λ fs≈gs → F.F-resp-≈ (fs≈gs zero)
  }
  where module F = Functor F

unaryH : Endofunctor C → Hyperendo 1 1
unaryH F = record
  { F₀           = λ As → F.F₀ ∙ As
  ; F₁           = λ fs → F.F₁ ∙ fs
  ; identity     = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≈     = λ fs≈gs → F.F-resp-≈ ∙ fs≈gs
  }
  where module F = Functor F

-- "constant"
nullary : Obj → Powerendo 0
nullary X = record
  { F₀           = λ _ → X
  ; F₁           = λ _ → id
  ; identity     = refl
  ; homomorphism = sym identity²
  ; F-resp-≈     = λ _ → refl
  }

nullaryH : Obj → Hyperendo 0 1
nullaryH X = record
  { F₀           = λ _ _ → X
  ; F₁           = λ _ _ → id
  ; identity     = λ _ → refl
  ; homomorphism = λ _ → sym identity²
  ; F-resp-≈     = λ _ _ → refl
  }

binary : Bifunctor C C C → Powerendo 2
binary F = record
  { F₀           = λ As → F.F₀ (As zero , As (suc zero))
  ; F₁           = λ fs → F.F₁ (fs zero , fs (suc zero))
  ; identity     = F.identity
  ; homomorphism = F.homomorphism
  ; F-resp-≈     = λ fs≈gs → F.F-resp-≈ (fs≈gs zero , fs≈gs (suc zero))
  }
  where module F = Functor F

binaryH : Bifunctor C C C → Hyperendo 2 1
binaryH F = record
  { F₀           = λ As _ → F.F₀ (As zero , As (suc zero))
  ; F₁           = λ fs _ → F.F₁ (fs zero , fs (suc zero))
  ; identity     = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≈     = λ fs≈gs _ → F.F-resp-≈ (fs≈gs zero , fs≈gs (suc zero))
  }
  where module F = Functor F

hyp : Powerendo n → Hyperendo n 1
hyp F = record
  { F₀           = λ As _ → F.F₀ As
  ; F₁           = λ fs _ → F.F₁ fs
  ; identity     = λ _ → F.identity
  ; homomorphism = λ _ → F.homomorphism
  ; F-resp-≈     = λ fs≈gs _ → F.F-resp-≈ fs≈gs
  }
  where module F = Functor F

private
  curryⁿ : ∀ n {a b} {A : Set a} {B : Set b} → ((Fin n → A) → B) → N-ary n A B
  curryⁿ zero f     = f (λ ())
  curryⁿ (suc n) {A = A} f = λ x → curryⁿ n (f ∙ addon x)
    where addon : A → (Fin n → A) → Fin (suc n) → A
          addon x _ zero    = x
          addon _ g (suc i) = g i

plex′ : (J → Powerendo′ I) → Hyperendo′ I J
plex′ Fs = record
  { F₀           = flip (Functor.F₀ ∙ Fs)
  ; F₁           = flip (λ j → Functor.F₁ (Fs j))
  ; identity     = λ j → Functor.identity (Fs j)
  ; homomorphism = λ j → Functor.homomorphism (Fs j)
  ; F-resp-≈     = flip (λ j → Functor.F-resp-≈ (Fs j))
  }

plex : N-ary n (Powerendo′ I) (Hyperendo′ I (Fin n))
plex {n = n} = curryⁿ n plex′

-- like pad, but for Powerendo -- on left or right.
widenˡ : ∀ (l : ℕ) (F : Powerendo n) → Powerendo (l + n)
widenˡ l F = record
  { F₀           = λ As → F.F₀ (As ∙ pack)
  ; F₁           = λ {As Bs} fs → F.F₁ (fs ∙ pack)
  ; identity     = F.identity
  ; homomorphism = F.homomorphism
  ; F-resp-≈     = λ fs≈gs → F.F-resp-≈ (fs≈gs ∙ pack)
  }
  where module F = Functor F
        pack = raise l

widenʳ : ∀ (r : ℕ) (F : Powerendo n) → Powerendo (n + r)
widenʳ r F = record
  { F₀           = λ As → F.F₀ (As ∙ pack)
  ; F₁           = λ fs → F.F₁ (fs ∙ pack)
  ; identity     = F.identity
  ; homomorphism = F.homomorphism
  ; F-resp-≈     = λ fs≈gs → F.F-resp-≈ (fs≈gs ∙ pack)
  }
  where module F = Functor F
        pack = inject+ r
