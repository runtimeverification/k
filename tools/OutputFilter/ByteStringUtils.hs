{-# LANGUAGE OverloadedStrings #-}

module ByteStringUtils where
  import Data.ByteString.Char8 (ByteString, unpack, pack, cons, uncons, append, singleton)
  import qualified Data.ByteString.Char8 as B
  import qualified Data.String.Utils as MH
  import qualified Data.List.Utils as MH
  import Text.Regex.Less.Quackers

  -- Delete all occurrences
  deleteAll :: Char -> ByteString -> ByteString
  deleteAll x = B.filter ((/=) x)

  -- Bytestring versions of split and join
  -- todo, make this more efficient (i.e. do it natively rather than pack/unpack)
  split :: ByteString -> ByteString -> [ByteString]
  split delim s = map pack $ unpack delim `MH.split` unpack s

  join :: ByteString -> [ByteString] -> ByteString
  join delim ss = pack $ unpack delim `MH.join` map unpack ss

  rstrip :: ByteString -> ByteString
  rstrip = pack . MH.rstrip . unpack

  replace :: ByteString -> ByteString -> ByteString -> ByteString
  replace old new s = pack $ MH.replace (unpack old) (unpack new) (unpack s)

  -- Make an instance of ByteStrings for the pcre-less package's Quackers
  instance QLR ByteString where
    compile = compile . unpack
