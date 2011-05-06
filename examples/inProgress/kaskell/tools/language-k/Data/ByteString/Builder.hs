{-# LANGUAGE OverloadedStrings #-}

module Data.ByteString.Builder
    ( module Blaze.ByteString.Builder
    , module Blaze.ByteString.Builder.Char8
    , module Data.Monoid
    , (<>)
--    , intercalate
    , Data.ByteString.Builder.unwords
    ) where

import Blaze.ByteString.Builder
import Blaze.ByteString.Builder.Char8
import qualified Data.List as List hiding (unwords)
import Data.Monoid
import Data.String

instance IsString Builder where
    fromString = Blaze.ByteString.Builder.Char8.fromString

instance Show Builder where
    show = show . toByteString

-- monoid extras

infixl 4 <>

(<>) :: Monoid a => a -> a -> a
(<>) = mappend

intercalate :: (Monoid a) => a -> [a] -> a
intercalate x = mconcat . (List.intersperse x)

unwords :: (Monoid a, IsString a) => [a] -> a
unwords = intercalate " "
