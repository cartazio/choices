{-# LANGUAGE FlexibleInstances, GADTs, RankNTypes, ScopedTypeVariables #-}
module Data.Choice where

import Data.Bifunctor
import Data.Biapplicative

data Choose a b c where
    CLeft  :: Choose a b a
    CRight :: Choose a b b

newtype Choice a b = Choice (forall r . Choose  a b r -> r)
newtype ChoiceT t a b = Choice (forall r . Choose (t a) (t b) r -> r)

