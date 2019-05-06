{-# LANGUAGE FlexibleInstances, GADTs, TypeOperators,PolyKinds, KindSignatures, DataKinds, RankNTypes, ScopedTypeVariables, EmptyCase #-}

{-# LANGUAGE TupleSections, DeriveFunctor #-}
{-# LANGUAGE DerivingVia, StandaloneDeriving, GeneralizedNewtypeDeriving #-}
module Data.Choice where

import Data.Bool (bool)
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

hcaseT :: HSumT f ls -> HChoiceT (Handled f g res) ls -> g res
--caseT (HExistsT Absurd _) (HChoiceT f) =  (error "impossible case!") --- error "absurd proofs happened here" -- or just do
hcaseT (HExistsT pf val) (HChoiceT f) =  unhandle (f pf) val


mhcaseT :: forall f ls r .  Monad f => f (HSum ls) -> HChoiceT (RevApp f r) ls -> f r
mhcaseT fsum (HChoiceT fun ) =
                              do   thesum <- fsum
                                   case thesum of
                                      (HExists path val ) ->
                                        do
                                         theFun <- unwrap  $  fun  path
                                         return $ theFun val

newtype PolyChoice ls f r = PC { unpc :: forall a . f  (Pick ls a , a)  -> f r }
instance Functor f => Functor (PolyChoice ls f) where
  fmap f  arg = PC (\ tup ->  fmap f    $ unpc arg tup )

-- need to add some extra bits for this to work, some sort of cps
--genCaseTA :: forall f ls r . Applicative f => f (HSum ls) -> HChoiceT (RevApp f r) ls -> f r
--genCaseTA fsum ohChoice = undefined
--    where
--      --continuations!!!
--      --funChoice :: PolyChoice ls f r -> f r
--      --funChoice f =  () `fmap` fsum

--      conSum1 :: HChoiceT (Handled f f r) ls -> PolyChoice ls f r
--      conSum1 (HChoiceT handFun)  = PC ( \ ftup -> ( \( path,val )-> unhandle (handFun path) val ) `fmap` ftup )

flattenChoice :: forall f r ls .  Applicative f =>  HChoiceT (RevApp f r) ls -> HChoiceT (Handled f f r) ls
flattenChoice (HChoiceT fn) = HChoiceT $ \path-> ItsHandled $ (<*>) (unwrap $ fn  path)
{-
f (a -> b) -> (f a -> f b )
is easy
, we can't do the opposite sadly .. unless we can join at the end

roughly we want to take
f (a + b) -> (f (a -> c) & f (b -> c)) -> f c

using partially applied (<*>)
we can rewrite that to


-}
--- I just need to have a way to partially apply  \i -> f (i -> r) at the type level
newtype RevApp f o i = RAP {unwrap :: f (i -> o)}

-- this is a flipped profunctor, a contrafunctor etc
newtype SelectM f a = SelectM { fromSelectM :: f a }
    deriving (Functor, Applicative, Monad)

newtype SelectA f a = SelectA { fromSelectA :: f a }
    deriving (Functor, Applicative)

class Applicative f =>  Selective f where
  ctsCase :: f (HSum ls) -> HChoiceT (RevApp f r) ls  -> f r



--- arppxo copy pasta for comparisons start here

instance Monad f => Selective (SelectM f) where
    ctsCase = mhcaseT

ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS x t e = branchFromCase (bool (Right ()) (Left ()) <$> x) (const <$> t) (const <$> e)


-- | An operator alias for 'select', which is sometimes convenient. It tries to
-- follow the notational convention for 'Applicative' operators. The angle
-- bracket pointing to the left means we always use the corresponding value.
-- The value on the right, however, may be skipped, hence the question mark.
(<*?) :: Selective f => f (Either a b) -> f (a -> b) -> f b
(<*?) = select

infixl 4 <*?

-- | The 'branch' function is a natural generalisation of 'select': instead of
-- skipping an unnecessary effect, it chooses which of the two given effectful
-- functions to apply to a given argument; the other effect is unnecessary. It
-- is possible to implement 'branch' in terms of 'select', which is a good
-- puzzle (give it a try!).
branch :: Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch x l r = fmap (fmap Left) x <*? fmap (fmap Right) l <*? r

-- Implementing select via branch:
-- selectB :: Selective f => f (Either a b) -> f (a -> b) -> f b
-- selectB x y = branch x y (pure id)

-- | We can write a function with the type signature of 'select' using the
-- 'Applicative' type class, but it will always execute the effects associated
-- with the second argument, hence being potentially less efficient.
selectA :: Applicative f => f (Either a b) -> f (a -> b) -> f b
selectA x y = (\e f -> either f id e) <$> x <*> y




select :: Selective f => f (Either a b) -> f (a -> b) -> f b
select = selectB
-- also copied from paper
-- | Conditionally perform an effect.
whenS :: Selective f => f Bool -> f () -> f ()
whenS x y = select (bool (Right ()) (Left ()) <$> x) (const <$> y)
-- this one is copied from the paper
selectB :: Selective f => f (Either a b) -> f (a -> b) -> f b
selectB x y = branchFromCase x y (pure id)

 ---- copies from selective functor end here for comparison


branchFromCase :: forall f a b c. Selective f => f (Either a b) -> f (a -> c) -> f (b-> c) ->  f c
branchFromCase sumIn leftF rightF = ctsCase hsumOut choiceOUT
  where
    hsumOut :: f (HSum [a,b])
    hsumOut = (\x -> case x of  Left a -> HExists Here a ; Right b -> HExists (Next Here) b) `fmap` sumIn
    choiceOUT :: HChoiceT (RevApp f c) [a,b]
    choiceOUT = HChoiceT (\x -> case x of
                                    Here -> RAP leftF ;
                                    Next Here -> RAP rightF ;
                                    Next (Next _) -> error "literally a bug in gadt coverage checking?!")

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




{-
class Applicative f => Selective f where
    select :: f (Either a b) -> f (a -> b) -> f b

branch :: Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
whenA :: Applicative f => f Bool

-}
