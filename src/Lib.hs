{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, QuantifiedConstraints, FunctionalDependencies, OverloadedLabels, OverloadedStrings, TemplateHaskell, EmptyCase, InstanceSigs #-}
module Lib  where

import Data.Constraint
import Data.Row
import Data.Row.Internal
import qualified Data.Row.Records as R
import qualified Data.Row.Variants as V
import GHC.TypeLits
import Data.Kind
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Base.TH
import GHC.TypeLits.Singletons
import Data.Word
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
{--
  ----------------------
  Data.Constraint review
  ----------------------
--}

-- First, we need some type classes...

class (KnownNat (N s)) => HasN (s :: Symbol) where
  type N s :: Nat

instance HasN "Foo"  where
  type N "Foo" = 1337

data D = DA | DB | DC

type C :: D -> Symbol ->  Constraint
class (KnownSymbol s) => C  d  s

instance C 'DA "Foo"

class  ( C 'DA  s
       , KnownSymbol s
       , (C 'DA s => HasN s) -- We can turn quantified constraints into entailments using `implied`
       ) => E s              -- e.g. (forall x. P x => Q x) can be transformed into (forall x. P x :- Q x)
                             -- Note that type inference is bad and you usually have to annotate explicitly
                             -- Also note that this *is* a quantified constraint even though there isn't a forall
instance ( C 'DA s
         , KnownSymbol s
         , HasN s
         ) => E s

-- `trans` is composition for entailments
(==>) :: (a :- b) -> (b :- c) -> (a :- c)
(==>) = flip trans -- WHY DO PROGRAMMERS ALWAYS WRITE HYPOTHETICAL SYLLOGISM THE WRONG WAY???? Yeah yeah composition whatever...

-- If C1 is a superclass of C2, we can always reify the superclass relation into an entailment (C1 :- C2)
superclass :: E s :- C 'DA s
superclass = Sub Dict

foo :: Dict (E "Foo")
foo = Dict

anImplication :: forall (s :: Symbol). E s :- KnownNat (N s)
anImplication = unmapDict goA -- `unmapDict` transforms a function :: Dict C1 -> Dict C2
                              -- into an entailment C1 :- C2
  where
    -- It should be obvious that (E s) implies (KnownNat (N s)), but GHC can't infer it directly.
    -- The main use (afaik) of Data.Constraint is to convince GHC of things it should know but, annoyingly, doesn't
    goA :: Dict (E s) -> Dict (KnownNat (N s))
    goA de = mapDict (superclass ==> unmapDict goB) de
      -- mapDict maps an entailment over a dictionary. i.e. mapDict (C1 :- C2) (Dict C1) == Dict C2
      where
       -- \\ basically means "on the basis of" or "with evidence"
       goB :: Dict (C 'DA s) -> Dict (KnownNat (N s))
       goB Dict = Dict
                 \\ mapDict (implied :: C 'DA s :- HasN s) Dict -- Here we use transform the quantified constraint into an entailment
                 \\ de -- Note that we need this last one solely because we didn't explicitly bring
                       -- the dictionary into scope in goA. It's superfluous here, but sometimes
                       -- (usually when you're unwrapping existential type variables) you can't actually
                       -- write the correct type annotation or signature for a dict

testImplication :: forall (s :: Symbol). Dict (E s) -> IO ()
testImplication eDict = go $ mapDict anImplication eDict
  where
    go :: forall (n :: Nat). Dict (KnownNat n) -> IO ()
    go Dict = putStrLn $ show (fromSing $ sing @s)
                      <> " = "
                      <> show (fromSing $ sing @n)
                      \\ eDict

-- Typically you can only infer from sub-class to super-class.
-- However, if your class is a constraint synonym
-- i.e. if: 1) It has a superclass. 2) It only has one instance. 3) The context of the one instance == the superclass
-- then you can infer in both directions.
-- (This is actually useful, I promise)
class E s => F s
instance E s => F s

down :: E s :- F s
down = Sub Dict

up :: F s :- E s
up = Sub Dict


{--
  ----------------------
  Data.Row review
  ----------------------
--}

-- row-types is probably most commonly used as an extensible records library...

$(singletons [d|
 data Color = Red | Blue | Pink | Black | Orange
    deriving Eq
 |])
type Person = "name"           .== String
           .+ "phoneNumber"   .== Int
           .+ "favoriteColor" .== Color

mkPerson :: String -> Int -> Color -> Rec Person
mkPerson name num col = #name .== name
                     .+ #phoneNumber .== num
                     .+ #favoriteColor .== col

type PetOwner = Person .+ "pet" .== String

-- look at this extensibility!
adoptAPet :: Rec Person -> String -> Rec PetOwner
adoptAPet person pet'sName = person .+ #pet .== pet'sName

lostTheirPet :: Rec PetOwner -> Rec Person
lostTheirPet petOwner = petOwner .- #pet

-- but that's only half the fun.
-- most row types libraries also support variants
-- (which are, I guess, extensible Sums)

type EchoRequest = "erID"   .== Word16
                .+ "erSeq"  .== Word16
                .+ "erData" .== Word16

type EchoReply = EchoRequest -- same structure

type SourceQuench = "unused" .== Word32
                 .+ "dgPort" .== ByteString

type ICMPMessage = "echoRequest"   .== Rec EchoRequest
                 .+ "echoReply"    .== Rec EchoReply
                 .+ "sourceQuench" .== Rec SourceQuench


-- we can construct Variants w/ IsJust (it's a pattern)
anICMPCode :: Var ICMPMessage
anICMPCode = IsJust #sourceQuench (  #unused .== 0
                                  .+ #dgPort .== "u got haxxed bro!")


-- we can deconstruct Variants w/ `trial'`
trySourceQuench :: Var ICMPMessage -> Maybe (Rec SourceQuench)
trySourceQuench icmp = V.trial' icmp #sourceQuench

-- Extensibility, however, is only part of what makes row-types so much fun.
-- The library authors provide a series of functions for transforming
-- type paramaterized by Row Types into other types parameterized by the same row
-- when each element of the row satisfies some constraint

-- Here's a silly example:

class Known a  where
  conjure :: a

instance Known (Proxy (a :: k)) where
  conjure = Proxy
instance Known (Proxy (a :: Type)) where
  conjure = Proxy

-- We use the higher-order `Forall` constraint to assert that each element in a row satisfies some argument constraint
type AllKnown r = Forall r Known

-- Forall is a type class (so it can be partially applied), and it has a method `metamorph`:

{- Note: This is how upstream row-types define this. In a moment I'll show you how I improved it :)
-- | Any structure over a row in which every element is similarly constrained can
-- be metamorphized into another structure over the same row.
class Forall (r :: Row k) (c :: k -> Constraint) where
  -- | A metamorphism is an anamorphism (an unfold) followed by a catamorphism (a fold).
  -- The parameter 'p' describes the output of the unfold and the input of the fold.
  -- For records, @p = (,)@, because every entry in the row will unfold to a value paired
  -- with the rest of the record.
  -- For variants, @p = Either@, because there will either be a value or future types to
  -- explore.
  -- 'Const' can be useful when the types in the row are unnecessary.
  metamorph :: forall (p :: * -> * -> *) (f :: Row k -> *) (g :: Row k -> *) (h :: k -> *). Bifunctor p
            => Proxy (Proxy h, Proxy p)
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ, HasType ℓ τ ρ)
               => Label ℓ -> f ρ -> p (f (ρ .- ℓ)) (h τ))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c τ, FrontExtends ℓ τ ρ, AllUniqueLabels (Extend ℓ τ ρ))
               => Label ℓ -> p (g ρ) (h τ) -> g (Extend ℓ τ ρ))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r
-}

-- row-types provides a bunch of fun functions built off of metamorph. default' is a simple one that lets you initialize
-- a record given some suitable constraint on all of the elements:
-- default' :: forall c ρ. (Forall ρ c, AllUniqueLabels ρ) => (forall a. c a => a) -> Rec ρ

-- For some (r :: Row k), R.Map is a type family which maps some "functor like thing" of type (k -> Type) over the row
conjureRow :: forall r. (AllKnown (R.Map Proxy r), WellBehaved r, WellBehaved (R.Map Proxy r)) => Rec (R.Map Proxy r)
conjureRow = R.default' @Known @(R.Map Proxy r) conjure

-- OK let's try some fancy type stuff...
data Field = SymbolField Symbol
           | NatField Nat
           | ColorField Color

type KPerson =  "name"          .== Field
             .+ "phoneNumber"   .== Field
             .+ "favoriteColor" .== Field

-- Every element of a row has to be of the same kind. This is kind of annoying.
-- Because we have to wrap every element in 'Field', we have a type level structure that is
-- unfortunately opaque. We might want a constraint which allows us to provide compile-time
-- validation of KPerson rows (i.e. such that the "name" field is always a NatField).
--
-- But we cannot do this with the Forall that we have. row-type's Forall only constraints the *elements* of the row,
-- but to validate our KPerson type, we need a two-place (relational) constraint on the labels *and* the elements.
-- something like:

type ValidateKField :: Symbol -> Field -> Constraint
class ValidateKField fieldLabel field

instance ValidateKField "name" ('SymbolField s)
instance ValidateKField "phoneNumber" ('NatField n)
instance ValidateKField "favoriteColor" ('ColorField c)

-- Important observation: If we had a relational Forall, i.e.
-- class ForallX (r :: Row k) (c :: Symbol -> k -> Constraint)
-- we could define the "basic" Forall as a special case

type ValidKPerson (r :: Row Field) = ForallX r ValidateKField

-- Anyway that was the insight that let me figure out how to do universal instantiation!
-- time to switch to https://github.com/gnumonik/row-types/blob/biforall/src/Data/Row/Internal.hs
