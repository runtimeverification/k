{-# LANGUAGE OverloadedStrings #-}

module ByteStringUtils
  ( mySub, mySubG                                             -- pcre-less wrappers and reimplementations
  , split, join, rstrip, replace                              -- MissingH wrappers
  , deleteAll, readBool, readNumber, readColor, compareStr
  , ByteString, unpack, pack, cons, uncons, append, singleton -- ByteString exports
  ) where
  import Style
  import Data.ByteString.Char8 (ByteString, unpack, pack, cons, uncons, append, singleton)
  import qualified Data.ByteString.Char8 as B
  import qualified Data.String.Utils as MH -- todo: get rid of me
  import qualified Data.List.Utils as MH -- todo: get rid of me
  import Data.Char
  import Text.Regex.Less.Quackers
  import Text.Regex.Less
  import qualified Text.Regex.PCRE as PCRE

  -- | Delete all occurrences
  deleteAll :: Char -> ByteString -> ByteString
  deleteAll x = B.filter ((/=) x)

  -- | Attempt to read in a truth value into a bool
  readBool :: ByteString -> Bool
  readBool s | isTrue s  = True
             | isFalse s = False
             | otherwise = error $ "Unable to read " ++ unpack s ++ " as a truth value"
    where isTrue  = flip compareStr $ ["true","t","yes","y"]
          isFalse = flip compareStr $ ["false","f","no","n","nil"]

  -- | Attempt to read in a number value into an int
  readNumber :: ByteString -> Int
  readNumber s = tryRead areNumbers s $ "Unable to parse: " ++ unpack s ++ " as a number"

  -- | Attempt to read in the string as a color, or raise a runtime error
  readColor :: ByteString -> Color
  readColor s = tryRead isColor s $ "Unable to parse: " ++ unpack s ++ " as a color"

  -- Read utilities
  tryRead :: Read a => (ByteString -> Bool) -> ByteString -> String -> a
  tryRead p s err = if p s then read (unpack (canonicalize s)) else error err

  tryReadInt :: ByteString -> String -> Int
  tryReadInt = tryRead areNumbers

  -- Is it a color
  isColor :: ByteString -> Bool
  isColor = flip compareStr $ [ "Black", "Red", "Green", "Yellow", "Blue", "Magenta", "Cyan"
                              , "White", "Dullblack", "Dullred", "Dullgreen", "Dullyellow"
                              , "Dullblue", "Dullmagenta", "Dullcyan", "Dullwhite"
                              ]

  areNumbers :: ByteString -> Bool
  areNumbers = B.all isDigit

  -- A canonical form, also is in a form ready to be read in should the string be a constructor
  -- The canonical form is that the first letter is capital, and all others are lowercase
  canonicalize :: ByteString -> ByteString
  canonicalize s = case uncons s of Just (c, cs) -> toUpper c `cons` B.map toLower cs
                                    Nothing      -> B.empty

  -- | Compare the contents of the config item to see if it occurs in passed strings.
  compareStr :: ByteString -> [ByteString] -> Bool
  compareStr s ss = canonicalize s `elem` map canonicalize ss

  -- Make an instance of ByteStrings for the pcre-less package's Quackers
  instance QLR ByteString where
    compile = compile . unpack

  -- | Perform a substitution
  mySub :: String -> String -> String -> String
  mySub old new s = case s =~ old of
                      m@(_,x:xs) -> subs m new
                      _          -> s
  -- | Performa all substitutions, pcre-less seems to have several bugs in it with their subg
  mySubG :: String -> String -> String -> String
  mySubG old new s = if s == mySub old new s then s
                     else mySubG old new (mySub old new s)

  {- MissingH functions. Todo: redefine them locally to increase efficiency and remove dependencies -}
  split :: ByteString -> ByteString -> [ByteString]
  split delim s = map pack $ unpack delim `MH.split` unpack s

  join :: ByteString -> [ByteString] -> ByteString
  join delim ss = pack $ unpack delim `MH.join` map unpack ss

  rstrip :: ByteString -> ByteString
  rstrip = pack . MH.rstrip . unpack

  replace :: ByteString -> ByteString -> ByteString -> ByteString
  replace old new s = pack $ MH.replace (unpack old) (unpack new) (unpack s)


