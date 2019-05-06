{-# LANGUAGE FlexibleInstances, GADTs, TypeOperators,PolyKinds, KindSignatures, DataKinds, RankNTypes, ScopedTypeVariables #-}
module Data.Choice where

import Data.Bifunctor
import Data.Biapplicative

data Pick :: [k] -> k -> * where
  Absurd :: forall a .  Pick '[] a
  Here :: forall a b . Pick (a ': b) a
  Next ::  forall a bs c . Pick bs c -> Pick (a ':  bs) c

data Choose a b c where
    CLeft  :: Choose a b a
    CRight :: Choose a b b

newtype Choice a b = Choice (forall r . Choose  a b r -> r)
newtype ChoiceT t a b = ChoiceT (forall r . Choose (t a) (t b) r -> r)

data HSum :: [*] -> * where
  HExists :: forall a as . Pick as a -> a -> HSum as

data HSumT :: ( k -> * ) -> [k] -> *  where
  HExistsT :: forall f a as . Pick as a -> f a -> HSumT f as

newtype HChoice as = HChoice (forall r . Pick as r  -> r )

newtype HChoiceT f as = HChoiceT (forall r . Pick as r -> f r )

-- | this looks kinda like a profunctor sortah?
newtype Handled f g res source   =  ItsHandled  {unhandle :: f source -> g res}

caseT :: HSumT f ls -> HChoiceT (Handled f g res) ls -> g res
caseT (HExistsT Absurd _) (HChoiceT f) =  (error "impossible case!") --- error "absurd proofs happened here" -- or just do
caseT (HExistsT pf val) (HChoiceT f) =  unhandle (f pf) val
