{-# OPTIONS --without-K --safe #-}

module Categories.FreeObjects.Free where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Binary using (IsEquivalence)
open import Categories.Functor renaming (id to idF)
open import Categories.Category
open import Categories.Adjoint
open import Categories.NaturalTransformation

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e o' ℓ' e' : Level

record FreeObject {C : Category o ℓ e} {D : Category o' ℓ' e'} (U : Functor D C) (X : Category.Obj C) : Set (suc (e ⊔ e' ⊔ o ⊔ ℓ ⊔ o' ⊔ ℓ')) where

  private
    module C = Category C using (Obj; id; identityʳ; identityˡ; _⇒_; _∘_; equiv; module Equiv)
    module D = Category D using (Obj; _⇒_; _∘_; equiv)
    module U = Functor U using (₀; ₁)

  field
     FX : D.Obj
     η : C [ X , U.₀ FX ]
     _* : ∀ {A : D.Obj} → C [ X , U.₀ A ] → D [ FX , A ]
     *-lift : ∀ {A : D.Obj} (f : C [ X , U.₀ A ]) → C [ (U.₁ (f *) C.∘ η) ≈ f ]
     *-uniq : ∀ {A : D.Obj} (f : C [ X , U.₀ A ]) (g : D [ FX , A ]) → C [ (U.₁ g) C.∘ η ≈ f ] → D [ g ≈ f * ]

  *-cong : ∀ {A : D.Obj} {f g : C [ X , U.₀ A ]} → C [ f ≈ g ] → D [ f * ≈ g * ]
  *-cong {A} {f} {g} f≈g = *-uniq g (f *) (trans (*-lift f) f≈g)    where open C.Equiv


open FreeObject


module _  {C : Category o ℓ e} {D : Category o' ℓ' e'} (U : Functor D C) where

  private
    module C = Category C using (Obj; id; _⇒_; _∘_; identityʳ; identityˡ; assoc; equiv; module Equiv; module HomReasoning)
    module D = Category D using (Obj; id; _⇒_; _∘_; identityʳ; identityˡ; assoc; equiv; module Equiv; module HomReasoning)
    module U = Functor U using (₀; ₁; identity; homomorphism)


  -- free object construction is functorial
  FO⇒Functor : (F : ((X : C.Obj) → FreeObject U X)) → Functor C D
  FO⇒Functor F =
    record
      { F₀ = λ X → FX (F X)
      ; F₁ = λ {X} {Y} f → _* (F X) (η (F Y) C.∘ f)
      ; identity = λ {X} → sym (*-uniq (F X) (η (F X) C.∘ C.id) D.id (id-proof {X}))
      ; homomorphism = λ {X} {Y} {Z} {f} {g} →
          sym (*-uniq (F X) (η (F Z) C.∘ (g C.∘ f))
              ((_* (F Y) (η (F Z) C.∘ g)) D.∘ (_* (F X) (η (F Y) C.∘ f)))
              (⟺ (hom-proof {X} {Y} {Z} {f} {g}))
              )
      ; F-resp-≈ = λ {X} {Y} {f} {g} f≈g → sym (*-uniq (F X) (η (F Y) C.∘ f) (_* (F X) (η (F Y) C.∘ g)) (resp-proof {X} {Y} {f} {g} f≈g))
      }
      where
        open C.HomReasoning
        open D.Equiv

        id-proof : ∀ {X : C.Obj} → C [ U.₁ D.id C.∘ η (F X) ≈ η (F X) C.∘ C.id ]
        id-proof {X} = begin
           (U.₁ D.id) C.∘ FX.η         ≈⟨ U.identity ⟩∘⟨refl ⟩
           C.id C.∘ FX.η               ≈⟨ C.identityˡ ⟩
           FX.η                        ≈˘⟨ C.identityʳ ⟩
           FX.η C.∘ C.id               ∎
           where
            module FX = FreeObject (F X) using (η)


        hom-proof : ∀ {X : C.Obj} {Y : C.Obj} {Z : C.Obj} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
            C [ (η (F Z) C.∘ (g C.∘ f)) ≈ (U.₁ (_* (F Y) (η (F Z) C.∘ g) D.∘ _* (F X) (η (F Y) C.∘ f) ) C.∘ η (F X)) ]
        hom-proof {X} {Y} {Z} {f} {g} =  begin
          FZ.η C.∘ (g C.∘ f)                                                     ≈˘⟨ pushˡ (FY.*-lift (FZ.η C.∘ g)) ⟩
          (U.₁((FZ.η C.∘ g) FY.*) C.∘ FY.η) C.∘ f                                ≈˘⟨ pushʳ (FX.*-lift (FY.η C.∘ f)) ⟩ 
          U.₁((FZ.η C.∘ g) FY.*) C.∘ (U.₁((FY.η C.∘ f) FX.*) C.∘ FX.η)           ≈˘⟨ pushˡ U.homomorphism ⟩     
          U.₁ ((FZ.η C.∘ g) FY.* D.∘ (FY.η C.∘ f) FX.*) C.∘ FX.η                 ∎
          where
            open MR C
            open C.Equiv
            module FX =  FreeObject (F X) using (η; _*; *-lift)
            module FY =  FreeObject (F Y) using (η; _*; *-lift)
            module FZ =  FreeObject (F Z) using (η)


        resp-proof :{X Y : C.Obj} {f g : C [ X , Y ]} → C [ f ≈ g ] → C [ U.₁ ((F X *) (η (F Y) C.∘ g)) C.∘ η (F X) ≈ η (F Y) C.∘ f ]
        resp-proof {X} {Y} {f} {g} f≈g =  begin
            U.₁((FY.η C.∘ g) FX.*) C.∘ FX.η      ≈⟨ FX.*-lift (FY.η C.∘ g) ⟩
            (FY.η C.∘ g)                         ≈˘⟨ refl⟩∘⟨ f≈g ⟩
            (FY.η C.∘ f)                         ∎
            where
              module FX = FreeObject (F X) using (η; _*; *-lift)
              module FY = FreeObject (F Y) using (η; _*; *-lift)


  -- the "unit" of the free object definition is a natural transformation
  FO⇒unit : (F : ((X : C.Obj) → FreeObject U X)) → NaturalTransformation idF (U ∘F FO⇒Functor F)
  FO⇒unit F = record
    { η = λ X → η (F X)
    ; commute = λ {X} {Y} f → sym (*-lift (F X) (η (F Y) C.∘ f))
    ; sym-commute = λ {X} {Y} f → *-lift (F X) (η (F Y) C.∘ f)
    }
    where open C.Equiv


  -- define a counit
  FO⇒counit : (F : ((X : C.Obj) → FreeObject U X)) → NaturalTransformation (FO⇒Functor F ∘F U) idF
  FO⇒counit F = record
    { η =  λ X → _* (F (U.₀ X)) C.id
    ; commute = λ {X} {Y} f → counit-comm {X} {Y} f
    ; sym-commute = λ {X} {Y} → λ f → sym (counit-comm {X} {Y} f)
    }
    where
      open D.Equiv
      module F = Functor (FO⇒Functor F) using (₀; ₁; identity; homomorphism)

      counit-comm : {X Y : D.Obj} (f : D [ X , Y ]) → D [ (_* (F (U.₀ Y)) C.id D.∘ F.₁ (U.₁ f)) ≈ (f D.∘ _* (F (U.₀ X)) C.id) ]
        -- proof idea: id* ∘ FU f ≈ (U f)* ≈ f ∘ id* using *-uniq two times

        -- left identity
      counit-comm-left : {X Y : D.Obj} (f : D [ X , Y ]) → C [ U.₁ ((_* (F (U.₀ Y)) C.id) D.∘ (F.₁ (U.₁ f)) ) C.∘ η (F (U.₀ X))  ≈ U.₁ f ]
      counit-comm-left {X} {Y} f =  begin
        U.₁(C.id FUY.* D.∘ F.₁(U.₁ f)) C.∘ FUX.η               ≈⟨ U.homomorphism ⟩∘⟨refl ⟩
        (U.₁ (C.id FUY.*) C.∘ U.₁ (F.₁(U.₁ f))) C.∘ FUX.η      ≈⟨ C.assoc ⟩
        U.₁ (C.id FUY.*) C.∘ (U.₁(F.₁(U.₁ f)) C.∘ FUX.η)       ≈⟨ refl⟩∘⟨ FUX.*-lift (FUY.η C.∘ U.₁ f) ⟩
        U.₁ (C.id FUY.*) C.∘ (FUY.η C.∘ U.₁ f)                 ≈˘⟨ C.assoc ⟩
        (U.₁ (C.id FUY.*) C.∘ FUY.η) C.∘ U.₁ f                 ≈⟨ FUY.*-lift C.id ⟩∘⟨refl ⟩
        C.id C.∘ U.₁ f                                         ≈⟨ C.identityˡ ⟩
        U.₁ f                                                  ∎
          where
            open C.HomReasoning
            module FUX = FreeObject (F (U.₀ X)) using (η; *-lift)
            module FUY = FreeObject (F (U.₀ Y)) using (η; _*; *-lift)



      -- right identity
      counit-comm-right : {X Y : D.Obj} (f : D [ X , Y ]) → C [ U.₁ (f D.∘ (_* (F (U.₀ X)) C.id)) C.∘ η (F (U.₀ X)) ≈ U.₁ f ]
      counit-comm-right {X} {Y} f =  begin
        U.₁ (f D.∘ (C.id FUX.*)) C.∘ FUX.η                ≈⟨ U.homomorphism ⟩∘⟨refl ⟩
        (U.₁ f C.∘ U.₁ (C.id FUX.*)) C.∘ FUX.η            ≈⟨ C.assoc ⟩
        U.₁ f C.∘ (U.₁ (C.id FUX.*) C.∘ FUX.η)            ≈⟨ refl⟩∘⟨ FUX.*-lift C.id ⟩
        U.₁ f C.∘ C.id                                    ≈⟨ C.identityʳ ⟩
        U.₁ f                                             ∎
        where
          open C.HomReasoning
          module FUX = FreeObject (F (U.₀ X)) using (η; _*; *-lift)


      counit-comm {X} {Y} f =  begin
        C.id FUY.* D.∘ F.₁ (U.₁ f)        ≈⟨ FUX.*-uniq (U.₁ f) (C.id FUY.* D.∘ F.₁ (U.₁ f)) (counit-comm-left {X} {Y} f) ⟩
        (U.₁ f) FUX.*                     ≈˘⟨ FUX.*-uniq (U.₁ f) (f D.∘ C.id FUX.*) (counit-comm-right {X} {Y} f) ⟩
        f D.∘ C.id FUX.*                  ∎
        where
          open D.HomReasoning
          module FUX = FreeObject (F (U.₀ X)) using (η; _*; *-lift; *-uniq)
          module FUY = FreeObject (F (U.₀ Y)) using (η; _*; *-lift)


  -- Free object functor is left adjoint to the forgetful functor
  FO⇒LAdj : (F : ((X : C.Obj) → FreeObject U X)) → (FO⇒Functor F) ⊣ U
  FO⇒LAdj F =  record
    { unit = FO⇒unit F
    ; counit = FO⇒counit F
    ; zig = zig
    ; zag = zag
    }
    where
      module F = Functor (FO⇒Functor F) using (₀; ₁; identity; homomorphism)

      zig-comm1 : {X : C.Obj} → C [ U.₁ D.id C.∘ η (F X) ≈ η (F X) ]
      zig-comm1 {X} =  begin
        U.₁ D.id C.∘ FX.η         ≈⟨ U.identity ⟩∘⟨refl ⟩
        C.id C.∘ FX.η             ≈⟨ C.identityˡ ⟩
        FX.η                      ∎
        where
          open C.HomReasoning
          module FX = FreeObject (F X) using (η)


      zig-helper1 : {X : C.Obj} → D [ _* (F X) (η (F X)) ≈ D.id ]
      zig-helper1 {X} =  begin
        FX.η FX.*           ≈˘⟨ FX.*-uniq FX.η D.id (zig-comm1 {X}) ⟩
        D.id            ∎
        where
          open D.HomReasoning
          module FX = FreeObject (F X) using (η; _*; *-uniq)


      zig-comm2 : {X : C.Obj} → C [ U.₁ (_* (F (U.₀ (F.₀ X))) C.id D.∘ F.₁ (η (F X)) ) C.∘ η (F X) ≈ η (F X) ]
      zig-comm2 {X} = begin
        U.₁(C.id FUFX.* D.∘ F.₁ FX.η) C.∘ FX.η                   ≈⟨ U.homomorphism ⟩∘⟨refl ⟩
        (U.₁(C.id FUFX.*) C.∘ U.₁(F.₁ FX.η)) C.∘ FX.η            ≈⟨ C.assoc ⟩
        U.₁(C.id FUFX.*) C.∘ (U.₁(F.₁ FX.η) C.∘ FX.η)            ≈˘⟨ refl⟩∘⟨ NaturalTransformation.commute (FO⇒unit F) FX.η ⟩
        U.₁(C.id FUFX.*) C.∘ (FUFX.η C.∘ FX.η)                   ≈˘⟨ C.assoc ⟩
        (U.₁(C.id FUFX.*) C.∘ FUFX.η) C.∘ FX.η                   ≈⟨ FUFX.*-lift C.id ⟩∘⟨refl ⟩
        C.id C.∘ FX.η                                            ≈⟨ C.identityˡ ⟩
        FX.η                                                     ∎
        where
          open C.HomReasoning
          module FX = FreeObject (F X) using (η)
          module FUFX = FreeObject (F (U.₀ (F.₀ X)) ) using (η; _*; *-lift)


      zig-helper2 : {X : C.Obj} → D [ _* (F (U.₀ (F.₀ X))) C.id D.∘ F.₁ (η (F X)) ≈ _* (F X) (η (F X)) ]
      zig-helper2 {X} = FX.*-uniq FX.η (C.id FUFX.* D.∘ F.₁ FX.η) (zig-comm2 {X})
        where
          module FX = FreeObject (F X) using (η; *-uniq)
          module FUFX = FreeObject (F (U.₀ (F.₀ X))) using (η; _*)


      zig : {X : C.Obj} → D [ _* (F (U.₀ (F.₀ X))) C.id D.∘ F.₁ (η (F X)) ≈ D.id ]
      zig {X} = trans zig-helper2 zig-helper1 where open D.Equiv

      zag : {B : D.Obj} → C [ U.₁ (_* (F (U.₀ B)) C.id) C.∘ η (F (U.₀ B)) ≈ C.id ]
      zag {B} = FUB.*-lift C.id
        where module FUB = FreeObject (F (U.₀ B)) using (*-lift)



  -- left adjoints yield free objects
  LAdj⇒FO : (Free : Functor C D) → (Free ⊣ U) → (X : C.Obj) → FreeObject U X
  LAdj⇒FO Free Free⊣U X = record
      { FX = F.₀ X
      ; η = η₁ X
      ; _* =  λ {A : D.Obj} f → ε A D.∘ F.₁ f
      ; *-lift = *-lift'
      ; *-uniq = *-uniq'
      }
      where
        module F = Functor Free using (₀; ₁; identity; homomorphism; F-resp-≈)
        open Adjoint (Free⊣U) using (unit; counit; zig; zag)
        open NaturalTransformation unit renaming (η to η₁; sym-commute to η-sym-commute)
        open NaturalTransformation counit renaming (η to ε; commute to ε-commute)


        *-lift' : {A : D.Obj} (f : C [ X , U.₀ A ]) → C [ U.₁ (ε A D.∘ F.₁ f) C.∘ η₁ X ≈ f ]
        *-lift' {A} f =  begin
          U.₁ (ε A D.∘ F.₁ f) C.∘ η₁ X                ≈⟨ U.homomorphism ⟩∘⟨refl ⟩
          (U.₁ (ε A) C.∘ U.₁ (F.₁ f)) C.∘ η₁ X        ≈⟨ C.assoc ⟩
          U.₁ (ε A) C.∘ (U.₁ (F.₁ f) C.∘ η₁ X)        ≈⟨ refl⟩∘⟨ η-sym-commute f ⟩
          U.₁ (ε A) C.∘ (η₁ (U.₀ A) C.∘ f)            ≈˘⟨ C.assoc ⟩
          (U.₁ (ε A) C.∘ η₁ (U.₀ A)) C.∘ f            ≈⟨ zag ⟩∘⟨refl ⟩
          C.id C.∘ f                                  ≈⟨ C.identityˡ ⟩
          f                                           ∎
          where
            open C.HomReasoning


        *-uniq-sym : {A : D.Obj} (f : C [ X , U.₀ A ]) (g : D [ F.₀ X , A ]) → C [ U.₁ g C.∘ η₁ X ≈ f ] → D [ ε A D.∘ F.₁ f ≈ g ]
        *-uniq-sym {A} f g comm_proof = begin
          ε A D.∘ F.₁ f                               ≈˘⟨ refl⟩∘⟨ F.F-resp-≈ comm_proof ⟩
          ε A D.∘ F.₁ (U.₁ g C.∘ η₁ X)                ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
          ε A D.∘ ( F.₁ (U.₁ g) D.∘ F.₁ (η₁ X) )      ≈˘⟨ D.assoc ⟩
          (ε A D.∘ F.₁ (U.₁ g)) D.∘ F.₁ (η₁ X)        ≈⟨ ε-commute g ⟩∘⟨refl ⟩
          (g D.∘ ε (F.₀ X)) D.∘ F.₁ (η₁ X)            ≈⟨ D.assoc ⟩
          (g D.∘ (ε (F.₀ X) D.∘ F.₁ (η₁ X)))          ≈⟨ refl⟩∘⟨ zig ⟩
          g D.∘ D.id                                  ≈⟨ D.identityʳ ⟩
          g                                           ∎
          where
            open D.HomReasoning

        *-uniq' : {A : D.Obj} (f : C [ X , U.₀ A ]) (g : D [ F.₀ X , A ]) → C [ U.₁ g C.∘ η₁ X ≈ f ] → D [ g ≈ ε A D.∘ F.₁ f ]
        *-uniq' {A} f g comm_proof =  begin
          g                             ≈˘⟨ *-uniq-sym f g comm_proof ⟩
          ε A D.∘ F.₁ f                 ∎
          where
            open D.HomReasoning
