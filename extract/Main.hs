module Main where

import Data.ByteString.Fiat.Internal hiding (IO, putStrLn)
import Data.Word
import Data.Word (Word8)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (Ptr, plusPtr)
import GHC.Prim
import System.IO.Unsafe (unsafePerformIO)

c2w8 :: Char -> Word8
c2w8 = fromIntegral . fromEnum

{- | Converts a String to a [Word8]. -}
s2w8 :: String -> [Word8]
s2w8 = Prelude.map c2w8

{- | Converts a Word8 to a Char. -}
w82c :: Word8 -> Char
w82c = toEnum . fromIntegral

w82s :: [Word8] -> String
w82s = Prelude.map w82c

printPS :: Rep -> CRep -> BScrep -> IO String
printPS h h' bs =
    let (bs', mres) = unconsBS h h' bs in
    case mres of
        Nothing -> return []
        Just c  -> (w82c c:) <$> printPS h h' bs'

printPS0 :: PS0 -> IO String
printPS0 bs =
    let (bs', mres) = ghcUnconsDSL' bs in
    case mres of
        Nothing -> return []
        Just c  -> (w82c c:) <$> printPS0 bs'

main :: IO ()
main = do
    putStrLn "ByteString list..."

    let h0 = emptyHeap
    let b0 = emptyBS any' h0
    putStrLn . ("b0 = " ++) =<< printPS any' h0 b0
    let b1 = consBS any' h0 b0 (c2w8 'a')
    putStrLn . ("b1 = " ++) =<< printPS any' h0 b1
    let b2 = consBS any' h0 b1 (c2w8 'b')
    putStrLn . ("b2 = " ++) =<< printPS any' h0 b2
    let b3 = consBS any' h0 b2 (c2w8 'c')
    putStrLn . ("b3 = " ++) =<< printPS any' h0 b3
    let (b4, mres1) = unconsBS any' h0 b3
    putStrLn . ("b4 = " ++) =<< printPS any' h0 b4
    print mres1
    let (b5, mres2) = unconsBS any' h0 b4
    putStrLn . ("b5 = " ++) =<< printPS any' h0 b5
    print mres2

    -- b3 has the final heap state
    let b6 = appendBS any' h0 b3 b2
    putStrLn . ("bs6 = " ++) =<< printPS any' h0 b6

    putStrLn "ByteString heap..."

    let bs0 = ghcEmptyDSL'
    putStrLn . ("bs0 = " ++) =<< printPS0 bs0
    let bs1 = ghcConsDSL' bs0 (c2w8 'a')
    putStrLn . ("bs1 = " ++) =<< printPS0 bs1
    let bs2 = ghcConsDSL' bs1 (c2w8 'b')
    putStrLn . ("bs2 = " ++) =<< printPS0 bs2
    let bs3 = ghcConsDSL' bs2 (c2w8 'c')
    putStrLn . ("bs3 = " ++) =<< printPS0 bs3
    let (bs4, mres1') = ghcUnconsDSL' bs3
    putStrLn . ("bs4 = " ++) =<< printPS0 bs4
    print mres1'
    let (bs5, mres2') = ghcUnconsDSL' bs4
    putStrLn . ("bs5 = " ++) =<< printPS0 bs5
    print mres2'

    let bs6 = ghcAppendDSL' bs3 bs2
    putStrLn . ("bs6 = " ++) =<< printPS0 bs6

    let bs6'' = ghcAppendDSL'' bs3 bs2
    putStrLn . ("bs6'' = " ++) =<< printPS0 bs6''
  where
    any' = unsafeCoerce ()

ghcAppendDSL'' :: PS0 -> PS0 -> PS0
ghcAppendDSL'' p p0 = unsafePerformIO $
  if 0 < psLength0 p
  then
    if 0 < psLength0 p0
    then do
      cod <- mallocBytes ((+) (psLength0 p) (psLength0 p0))
      copyBytes cod (plusPtr (unsafeCoerce (psBuffer0 p)) (psOffset0 p))
                (psLength0 p)
      copyBytes (plusPtr cod (psLength0 p))
                (plusPtr (unsafeCoerce (psBuffer0 p0)) (psOffset0 p0))
                (psLength0 p0)
      return $ MakePS0 (unsafeCoerce cod)
                       ((+) (psLength0 p) (psLength0 p0)) 0
                       ((+) (psLength0 p) (psLength0 p0))
    else return p
  else return p0
