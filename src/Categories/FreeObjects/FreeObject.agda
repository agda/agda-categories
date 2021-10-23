{-# OPTIONS --without-K --safe #-}

module Categories.Objects.FreeObjects.FreeObject where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; sym; refl; cong)
open import Relation.Binary using (IsEquivalence)
open import Categories.Functor renaming (id to idF)
open import Categories.Category
open import Categories.Adjoint
open import Categories.NaturalTransformation

private
  variable
    o ℓ e o' ℓ' e' : Level

record FreeObject {C : Category o ℓ e} {D : Category o' ℓ' e'} (U : Functor D C) (X : Category.Obj C) : Set (suc (e ⊔ e' ⊔ o ⊔ ℓ ⊔ o' ⊔ ℓ')) where

  open Category C renaming (_⇒_ to _⇒₁_ ; _∘_ to _∘₁_; _≈_ to _≈₁_; equiv to equiv₁)
  open Category D renaming (Obj to D_obj ; _⇒_ to _⇒₂_; _≈_ to _≈₂_)
  open Functor U renaming (F₀ to U₀; F₁ to U₁)

  field
     FX : D_obj
     η : X ⇒₁ (U₀ FX)
     _* : ∀ {A : D_obj} → X ⇒₁ U₀ A → FX ⇒₂ A
     *-lift : ∀ {A : D_obj} (f : X ⇒₁ U₀ A) → U₁ (f *) ∘₁ η ≈₁ f
     *-uniq : ∀ {A : D_obj} (f : X ⇒₁ U₀ A) (g : FX ⇒₂ A) → (U₁ g) ∘₁ η ≈₁ f → g ≈₂ f *

  *-cong : ∀ {A : D_obj} {f g : X ⇒₁ U₀ A} → f ≈₁ g → f * ≈₂ g *
  *-cong {A} {f} {g} f≈g = *-uniq g (f *) (IsEquivalence.trans equiv₁ (*-lift f) f≈g)

open FreeObject

module _  {C : Category o ℓ e} {D : Category o' ℓ' e'} (Free : Functor C D) (U : Functor D C) where
  open Category C using (_∘_; _≈_; equiv) renaming (id to idc; Obj to CObj)
  open Category D renaming (_∘_ to _∘′_; _≈_ to _≈′_; id to id′; equiv to equiv′; Obj to DObj)

  -- free object construction is functorial
  FO⇒Functor : (F : (X : Category.Obj C) → FreeObject U X) → Functor C D
  FO⇒Functor F = 
    record
      { F₀ = λ X → FX (F X)
      ; F₁ = λ {X} {Y} f → _* (F X) (η (F Y) ∘ f)
      ; identity = λ {X} → (IsEquivalence.sym equiv′) (*-uniq (F X) (η (F X) ∘ idc) id′ (id-proof {X}))
      ; homomorphism = λ {X} {Y} {Z} {f} {g} →
         (IsEquivalence.sym equiv′)
         (*-uniq (F X)
             (η (F Z) ∘ (g ∘ f))
             ((_* (F Y) (η (F Z) ∘ g)) ∘′ (_* (F X) (η (F Y) ∘ f)))
             (IsEquivalence.sym equiv (hom-proof {X} {Y} {Z} {f} {g}))
         )
      ; F-resp-≈ = λ {X} {Y} {f} {g} f≈g → 
            IsEquivalence.sym 
              equiv′
              (*-uniq (F X) (η (F Y) ∘ f) (_* (F X) (η (F Y) ∘ g)) (resp-proof {X} {Y} {f} {g} f≈g))
      }
        where
          module C = Category C
          module U = Functor U
          open U using (identity; homomorphism) renaming (F₀ to U₀; F₁ to U₁)

          id-proof : ∀ {X : CObj} → U₁ id′ ∘ η (F X) ≈ η (F X) ∘ idc
          id-proof {X} =
             begin
               (U₁ id′) ∘ ηX
                  ≈⟨ U.identity ⟩∘⟨refl ⟩
               idc ∘ ηX
                  ≈⟨ C.identityˡ ⟩
               ηX
                  ≈˘⟨ C.identityʳ ⟩
               ηX ∘ idc
             ∎
             where
              open Category.HomReasoning C
              open FreeObject (F X) renaming (η to ηX)


          hom-proof : ∀ {X : CObj} {Y : CObj} {Z : CObj} {f : C [ X , Y ]} {g : C [ Y , Z ]}
            → (η (F Z) ∘ (g ∘ f)) ≈ (U₁ (_* (F Y) (η (F Z) ∘ g) ∘′ _* (F X) (η (F Y) ∘ f) ) ∘ η (F X))
          hom-proof {X} {Y} {Z} {f} {g} =
            begin
               ηZ ∘ (g ∘ f)
                 ≈˘⟨ C.assoc ⟩
               (ηZ ∘ g) ∘ f
                 ≈˘⟨ (*Y-lift (ηZ ∘ g) ⟩∘⟨refl ) ⟩
               (U₁((ηZ ∘ g) *Y) ∘ ηY) ∘ f
                 ≈⟨ C.assoc ⟩
               U₁ ((ηZ ∘ g) *Y) ∘ (ηY ∘ f)
                 ≈˘⟨ refl⟩∘⟨ *X-lift (ηY ∘ f) ⟩
               U₁((ηZ ∘ g) *Y) ∘ (U₁((ηY ∘ f) *X) ∘ ηX)
                 ≈˘⟨ C.assoc ⟩
               (U₁((ηZ ∘ g) *Y) ∘ U₁((ηY ∘ f) *X)) ∘ ηX
                 ≈˘⟨ U.homomorphism ⟩∘⟨refl ⟩
               U₁ ((ηZ ∘ g) *Y ∘′ (ηY ∘ f) *X) ∘ ηX
            ∎
            where
              open Category.HomReasoning C
              open FreeObject (F X) renaming (η to ηX; _* to _*X; *-lift to *X-lift)
              open FreeObject (F Y) renaming (η to ηY; _* to _*Y; *-lift to *Y-lift)
              open FreeObject (F Z) renaming (η to ηZ)

          resp-proof : {X Y : CObj} {f g : C [ X , Y ]} → C [ f ≈ g ] → U₁ ((F X *) (η (F Y) ∘ g)) ∘ η (F X) ≈ η (F Y) ∘ f
          resp-proof {X} {Y} {f} {g} f≈g =
            begin
              U₁((ηY ∘ g) *X) ∘ ηX
                ≈⟨ *X-lift (ηY ∘ g) ⟩
              (ηY ∘ g)
                ≈˘⟨ refl⟩∘⟨ f≈g ⟩
              (ηY ∘ f)
            ∎
            where
              open Category.HomReasoning C
              open FreeObject (F X) renaming (η to ηX; _* to _*X; *-lift to *X-lift)
              open FreeObject (F Y) renaming (η to ηY; _* to _*Y; *-lift to *Y-lift)

  -- the "unit" of the free object definition is a natural transformation
  FO⇒unit : (F : ((X : Category.Obj C) → FreeObject U X)) → NaturalTransformation idF (U ∘F FO⇒Functor F)
  FO⇒unit F =
    record {
        η = λ X → η (F X)
      ; commute = λ {X} {Y} f → (IsEquivalence.sym equiv) (*-lift (F X) (η (F Y) ∘ f))
      ; sym-commute = λ {X} {Y} f → *-lift (F X) (η (F Y) ∘ f)
    }

  -- define a counit
  FO⇒counit : (F : ((X : CObj) → FreeObject U X)) → NaturalTransformation (FO⇒Functor F ∘F U) idF
  FO⇒counit F =
    record {
        η =  λ X → _* (F (U₀ X)) idc
      ; commute = λ {X} {Y} f → counit-comm {X} {Y} f
      ; sym-commute = λ {X} {Y} → λ f → IsEquivalence.sym equiv′ (counit-comm {X} {Y} f)
    }
      where
        module C = Category C using (id; _∘_; _≈_; equiv; identityˡ; identityʳ; assoc; module HomReasoning)
        module D = Category D using (Obj; id; _∘_; _≈_; equiv; module HomReasoning)

        open Functor U using (identity; homomorphism) renaming (F₀ to U₀; F₁ to U₁)
        open Functor (FO⇒Functor F) using (F₀; F₁) renaming (identity to F_identity; homomorphism to F_homomorphism)

        counit-comm : {X Y : DObj} (f : D [ X , Y ]) → _* (F (U₀ Y)) idc ∘′ F₁ (U₁ f) ≈′ f ∘′ _* (F (U₀ X)) idc
        -- proof idea: id* ∘ FU f ≈ (U f)* ≈ f ∘ id* using *-uniq two times

        -- left identity
        counit-comm-left : {X Y : D.Obj} (f : D [ X , Y ]) → U₁ ((_* (F (U₀ Y)) C.id) D.∘ (F₁ (U₁ f)) ) C.∘ η (F (U₀ X)) C.≈ U₁ f
        counit-comm-left {X} {Y} f =
          begin
            U₁(idc *UY ∘′ F₁(U₁ f)) ∘ ηUX
              ≈⟨ homomorphism ⟩∘⟨refl ⟩
            (U₁ (idc *UY) ∘ U₁ (F₁(U₁ f))) ∘ ηUX
              ≈⟨ C.assoc ⟩
            U₁ (idc *UY) ∘ (U₁(F₁(U₁ f)) ∘ ηUX)
              ≈⟨ refl⟩∘⟨ *UX-lift (ηUY ∘ U₁ f) ⟩
            U₁ (idc *UY) ∘ (ηUY ∘ U₁ f)
              ≈˘⟨ C.assoc ⟩
            (U₁ (idc *UY) ∘ ηUY) ∘ U₁ f
              ≈⟨ *UY-lift idc ⟩∘⟨refl ⟩
            idc ∘ U₁ f
              ≈⟨ C.identityˡ ⟩
            U₁ f
          ∎
          where
            open C.HomReasoning
            open FreeObject (F (U₀ X)) renaming (η to ηUX; *-lift to *UX-lift)
            open FreeObject (F (U₀ Y)) renaming (η to ηUY; _* to _*UY; *-lift to *UY-lift)

        -- right identity
        counit-comm-right : {X Y : DObj} (f : D [ X , Y ]) → U₁ (f ∘′ (_* (F (U₀ X)) idc)) ∘ η (F (U₀ X)) ≈ U₁ f
        counit-comm-right {X} {Y} f =
          begin
            U₁ (f ∘′ (idc *UX)) ∘ ηUX
              ≈⟨ homomorphism ⟩∘⟨refl ⟩
            (U₁ f ∘ U₁ (idc *UX)) ∘ ηUX
              ≈⟨ C.assoc ⟩
            U₁ f ∘ (U₁ (idc *UX) ∘ ηUX)
              ≈⟨ refl⟩∘⟨ *UX-lift idc ⟩
            U₁ f ∘ idc
              ≈⟨ C.identityʳ ⟩
            U₁ f
          ∎
          where
            open C.HomReasoning
            open FreeObject (F (U₀ X)) renaming (η to ηUX; _* to _*UX; *-lift to *UX-lift)

        counit-comm {X} {Y} f =
          begin
            idc *UY ∘′ F₁ (U₁ f)
              ≈⟨ *UX-uniq (U₁ f) (idc *UY ∘′ F₁ (U₁ f)) (counit-comm-left {X} {Y} f) ⟩
            (U₁ f) *UX
              ≈˘⟨ *UX-uniq (U₁ f) (f ∘′ idc *UX) (counit-comm-right {X} {Y} f) ⟩
            f ∘′ idc *UX
          ∎
          where
            open D.HomReasoning
            open FreeObject (F (U₀ X)) renaming (η to ηUX; _* to _*UX; *-lift to *UX-lift; *-uniq to *UX-uniq)
            open FreeObject (F (U₀ Y)) renaming (η to ηUY; _* to _*UY; *-lift to *UY-lift)


  -- Free object functor is left adjoint to the forgetful functor
  FO⇒LAdj : (F : ((X : CObj) → FreeObject U X)) → (FO⇒Functor F) ⊣ U
  FO⇒LAdj F =  record { unit = FO⇒unit F; counit = FO⇒counit F; zig = zig ; zag = zag }
      where
        module C = Category C using (_≈_; _⇒_; Obj; id; _∘_; identityˡ; identityʳ; equiv; module HomReasoning; assoc)
        module D = Category D using (Obj; _⇒_; _≈_; id; _∘_; equiv; module HomReasoning)
        module U = Functor U

        open U using (identity; homomorphism) renaming (F₀ to U₀; F₁ to U₁)
        open Functor (FO⇒Functor F) using (F₀; F₁) renaming (identity to F_identity; homomorphism to F_homomorphism)

        zig-comm1 : {X : CObj} → U₁ id′ ∘ η (F X) ≈ η (F X)
        zig-comm1 {X} =
          begin
            U₁ id′ ∘ ηX
              ≈⟨ identity ⟩∘⟨refl ⟩
            idc ∘ ηX
              ≈⟨ C.identityˡ ⟩
            ηX
          ∎
          where
            open C.HomReasoning
            open FreeObject (F X) renaming (η to ηX)

        zig-helper1 : {X : CObj} → _* (F X) (η (F X)) ≈′ id′
        zig-helper1 {X} =
          begin
            ηX *X
              ≈˘⟨ *X-uniq ηX id′ (zig-comm1 {X}) ⟩
            id′
          ∎
          where
            open D.HomReasoning
            open FreeObject (F X) renaming (η to ηX; _* to _*X; *-uniq to *X-uniq)

        zig-comm2 : {X : CObj} → U₁ (_* (F (U₀ (F₀ X))) idc ∘′ F₁ (η (F X))) ∘ η (F X) ≈ η (F X)
        zig-comm2 {X} =
          begin
            U₁(idc *UFX ∘′ F₁ ηX) ∘ ηX
              ≈⟨ U.homomorphism ⟩∘⟨refl ⟩
            (U₁(idc *UFX) ∘ U₁(F₁ ηX)) ∘ ηX
              ≈⟨ C.assoc ⟩
            U₁(idc *UFX) ∘ (U₁(F₁ ηX) ∘ ηX)
              ≈˘⟨ refl⟩∘⟨ NaturalTransformation.commute (FO⇒unit F) ηX ⟩
            U₁(idc *UFX) ∘ (ηUFX ∘ ηX)
              ≈˘⟨ C.assoc ⟩
            (U₁(idc *UFX) ∘ ηUFX) ∘ ηX
              ≈⟨ *UFX-lift idc ⟩∘⟨refl ⟩
            idc ∘ ηX
              ≈⟨ C.identityˡ ⟩
            ηX
          ∎
          where
            open C.HomReasoning
            open FreeObject (F X) renaming (η to ηX)
            open FreeObject (F (U₀ (F₀ X)) ) renaming (η to ηUFX; _* to _*UFX; *-lift to *UFX-lift)

        zig-helper2 : {X : CObj} → _* (F (U₀ (F₀ X))) idc ∘′ F₁ (η (F X)) ≈′ _* (F X) (η (F X))
        zig-helper2 {X} = *UFX-uniq ηX (idc *UFX ∘′ F₁ ηX) (zig-comm2 {X})
          where
            open FreeObject (F X) renaming (η to ηX; *-uniq to *UFX-uniq)
            open FreeObject (F (U₀ (F₀ X))) renaming (η to ηUFX; _* to _*UFX)

        zig : {X : CObj} → _* (F (U₀ (F₀ X))) idc ∘′ F₁ (η (F X)) ≈′ id′
        zig {X} = IsEquivalence.trans equiv′ zig-helper2 zig-helper1

        zag : {B : DObj} → U₁ (_* (F (U₀ B)) idc) ∘ η (F (U₀ B)) ≈ idc
        zag {B} = *UB-lift idc
          where open FreeObject (F (U₀ B)) renaming (*-lift to *UB-lift)

  -- left adjoints yield free objects
  LAdj⇒FO : (Free ⊣ U) → (X : CObj) → FreeObject U X
  LAdj⇒FO Free⊣U X =  
    record {
          FX = F₀ X
        ; η = η₁ X
        ; _* =  λ {A : DObj} f → ε A ∘′ F₁ f
        ; *-lift = *-lift' 
        ; *-uniq = *-uniq'
      }
        where
          module C = Category C using (_≈_; _⇒_; Obj; id; _∘_; identityˡ; identityʳ; equiv; module HomReasoning; assoc)
          module D = Category D using (Obj; _⇒_; _≈_; id; _∘_; equiv; module HomReasoning; assoc; identityʳ)
          module U = Functor U
          open U using (identity; homomorphism) renaming (F₀ to U₀; F₁ to U₁)
          module Free = Functor Free
          open Free using (F₀; F₁) renaming (identity to F_identity; homomorphism to F_homomorphism; F-resp-≈ to Free-resp-≈)
          open Adjoint (Free⊣U) using (unit; counit; zig; zag)
          open NaturalTransformation unit renaming (η to η₁; sym-commute to η-sym-commute)
          open NaturalTransformation counit renaming (η to ε; commute to ε-commute)

          *-lift' : {A : DObj} (f : C [ X , U₀ A ]) → U₁ (ε A ∘′ F₁ f) ∘ η₁ X ≈ f
          *-lift' {A} f =
            begin
              U₁ (ε A ∘′ F₁ f) ∘ η₁ X
                ≈⟨ U.homomorphism ⟩∘⟨refl ⟩
              (U₁ (ε A) ∘ U₁ (F₁ f)) ∘ η₁ X
                ≈⟨ C.assoc ⟩
              U₁ (ε A) ∘ (U₁ (F₁ f) ∘ η₁ X)
                ≈⟨ refl⟩∘⟨ η-sym-commute f ⟩
              U₁ (ε A) ∘ (η₁ (U₀ A) ∘ f)
                ≈˘⟨ C.assoc ⟩
              (U₁ (ε A) ∘ η₁ (U₀ A)) ∘ f
                ≈⟨ zag ⟩∘⟨refl ⟩
              idc ∘ f
                ≈⟨ C.identityˡ ⟩
              f
            ∎
              where open C.HomReasoning

          *-uniq-sym : {A : DObj} (f : C [ X , U₀ A ]) (g : D [ F₀ X , A ]) → U₁ g ∘ η₁ X ≈ f → ε A D.∘ F₁ f ≈′ g
          *-uniq-sym {A} f g comm_proof =
            begin
                ε A ∘′ F₁ f
                  ≈˘⟨ refl⟩∘⟨ Free-resp-≈ comm_proof ⟩
                ε A ∘′ F₁ (U₁ g ∘ η₁ X)
                  ≈⟨ refl⟩∘⟨ F_homomorphism ⟩
                ε A ∘′ ( F₁ (U₁ g) ∘′ F₁ (η₁ X) )
                  ≈˘⟨ D.assoc ⟩
                (ε A ∘′ F₁ (U₁ g)) ∘′ F₁ (η₁ X)
                  ≈⟨ ε-commute g ⟩∘⟨refl ⟩
                (g ∘′ ε (F₀ X)) ∘′ F₁ (η₁ X)
                  ≈⟨ D.assoc ⟩
                (g ∘′ (ε (F₀ X) ∘′ F₁ (η₁ X)))
                  ≈⟨ refl⟩∘⟨ zig ⟩
                g ∘′ id′
                  ≈⟨ D.identityʳ ⟩
                g
            ∎
                where open D.HomReasoning

          *-uniq' : {A : DObj} (f : C [ X , U₀ A ]) (g : D [ F₀ X , A ]) → U₁ g ∘ η₁ X ≈ f → g ≈′ ε A ∘′ F₁ f
          *-uniq' {A} f g comm_proof =
                  begin
                    g
                      ≈˘⟨ *-uniq-sym f g comm_proof ⟩
                    ε A ∘′ F₁ f
                  ∎
                  where
                    open D.HomReasoning
