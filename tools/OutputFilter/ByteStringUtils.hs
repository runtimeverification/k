{-# LANGUAGE OverloadedStrings #-}

module ByteStringUtils
  ( deleteAll, readBool, readNumber, readColor, compareStr
  , split, join, rstrip, replace                              -- MissingH wrappers
  , mySub, mySubG                                             -- pcre-less wrappers and reimplementations
  , ByteString, unpack, pack, cons, uncons, append, singleton -- ByteString exports
  ) where
  import Style
  import Data.ByteString.Char8 (ByteString, unpack, pack, cons, uncons, append, singleton)
  import Data.List
  import qualified Data.ByteString.Char8 as B
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

  {- | Given a delimiter and a ByteString, join the items by using the delimiter.

       Example:

         > join "|" ["foo", "bar", "baz"] -> "foo|bar|baz"

       Adapted from MissingH
  -}
  join :: ByteString -> [ByteString] -> ByteString
  join delim l = B.concat (intersperse delim l)

  {- | Given a delimiter and a bytestring, split into components.

       Example:

         > split "," "foo,bar,,baz," -> ["foo", "bar", "", "baz", ""]

         > split "ba" ",foo,bar,,baz," -> [",foo,","r,,","z,"]

       Adapted from MissingH
  -}
  split :: ByteString -> ByteString -> [ByteString]
  split delim str | str == B.empty = []
                  | otherwise      =
                    let (first, rem) = breakList (startswith delim) str in
                    first : case uncons rem of
                              Nothing -> []
                              Just (a,b) | rem == delim -> []
                                         | otherwise          -> split delim (B.drop (B.length delim) rem)

  startswith :: ByteString -> ByteString -> Bool
  startswith = B.isPrefixOf

  breakList :: (ByteString -> Bool) -> ByteString -> (ByteString, ByteString)
  breakList func = spanList (not . func)

  spanList :: (ByteString -> Bool) -> ByteString -> (ByteString, ByteString)
  spanList func bs = case uncons bs of
                         Nothing                      -> ("","")
                         Just (x,xs) | func (cons x xs) -> (cons x ys, zs)
                                     | otherwise -> ("", cons x xs)
                           where (ys,zs) = spanList func xs

  -- | Same as 'strip', but applies only to the right side of the string. Adapted from MissingH
  rstrip :: ByteString -> ByteString
  rstrip = B.reverse . lstrip . B.reverse

  wschars :: ByteString
  wschars = " \t\r\n"

  lstrip :: ByteString -> ByteString
  lstrip s = case uncons s of
               Nothing -> ""
               Just (x,xs) -> if B.elem x wschars
                              then lstrip xs
                              else s

  {- | Given a list and a replacement list, replaces each occurance of the search
       list with the replacement list in the operation list.

         Example:

           >replace "," "." "127,0,0,1" -> "127.0.0.1"

        This could logically be thought of as:

          >replace old new l = join new . split old $ l
   -}

  replace :: ByteString -> ByteString -> ByteString -> ByteString
  replace old new s = join new . split old $ s


