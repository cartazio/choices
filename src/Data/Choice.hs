{-# LANGUAGE FlexibleInstances, GADTs, TypeOperators,PolyKinds, KindSignatures, DataKinds, RankNTypes, ScopedTypeVariables, EmptyCase #-}
module Data.Choice where

--import Data.Bifunctor
--import Data.Biapplicative
--import Data.Bifunctor.Flip

data Pick :: [k] -> k -> * where
  Here :: forall a b . Pick (a ': b) a
  Next ::  forall a bs c . Pick bs c -> Pick (a ':  bs) c

data Choose a b c where
    CLeft  :: Choose a b a
    CRight :: Choose a b b

-- Either with evidence! Sigma encoding of simple sum!
data Sum  a b where
  TheSum:: (Choose a b c) ->  c -> Sum  a b

-- EitherT if it were a CBN Sum
data SumT f  a b where
  TheSumT:: (Choose a b c) -> f c -> SumT f a b

newtype Choice a b = Choice (forall r . Choose  a b r -> r)
newtype ChoiceT t a b = ChoiceT (forall r . Choose (t a) (t b) r -> r)


data HSum :: [*] -> * where
  HExists :: forall a as . Pick as a -> a -> HSum as

data HSumT :: ( k -> * ) -> [k] -> *  where
  HExistsT :: forall f a as . Pick as a -> f a -> HSumT f as


-- | HChoice is just a CBN product / N tuple / HList
newtype HChoice as = HChoice (forall r . Pick as r  -> r )

newtype HChoiceT f as = HChoiceT (forall r . Pick as r -> f r )

-- | this looks kinda like a profunctor sortah? Its mostly a hack so i can write down f a -> g result for
-- the RHS of a case
-- this looks like it should be a flipped profunctor and also a contrafunctor
newtype Handled f g res source   =  ItsHandled  {unhandle :: f source -> g res}

caseT :: HSumT f ls -> HChoiceT (Handled f g res) ls -> g res
--caseT (HExistsT Absurd _) (HChoiceT f) =  (error "impossible case!") --- error "absurd proofs happened here" -- or just do
caseT (HExistsT pf val) (HChoiceT f) =  unhandle (f pf) val


caseSimp ::  forall r ls .  HSum ls -> HChoiceT (FlipArrow r) ls -> r
caseSimp (HExists pf val ) (HChoiceT f) = getFA (f pf) val

--- simplified flipped profunctor for function type
newtype FlipArrow  (b :: * ) (a :: * ) = FA { getFA :: a -> b }

-- this is also equivalent to CBN Unit / 0 Arity tuple
emptyChoice :: HChoice '[]
emptyChoice = HChoice  (\ pk ->( case pk of {} ))

emptyChoiceFA :: forall r . HChoiceT (FlipArrow r) '[]
emptyChoiceFA =  HChoiceT  (\ pk ->( case pk of {} ))

emptyHSumAbsurd :: forall r . HSum '[] -> r
emptyHSumAbsurd esum = caseSimp esum emptyChoiceFA
