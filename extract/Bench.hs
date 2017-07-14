{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import           Control.DeepSeq
import           Criterion.Main
import           Criterion.Types
import           Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Fiat as Fiat
import           Data.ByteString.Fiat.Internal hiding (IO, map, fmap)
import qualified Data.ByteString.Fiat.Internal as Internal
import qualified Data.Foldable as F
import           Data.Monoid
import           Data.Word (Word8)
import           System.Environment (getArgs, withArgs)
import           System.IO.Unsafe
import           Foreign.Ptr (plusPtr, nullPtr)
import           Foreign.ForeignPtr
import           Foreign.Storable
import           Foreign.Marshal.Array
import           Foreign.Marshal.Utils
import           GHC.ForeignPtr (mallocPlainForeignPtrBytes)
import qualified Weigh

import qualified "bytestring" Data.ByteString as BS

instance NFData PS0 where
    rnf (MakePS0 !_ !_ !_ !_) = ()

c2w8 :: Char -> Word8
c2w8 = fromIntegral . fromEnum

w82c :: Word8 -> Char
w82c = toEnum . fromIntegral

packBench :: [Int] -> ByteString
packBench = BS.pack . map c2w8 . concatMap show

packFiatBench :: [Int] -> Fiat.ByteString
packFiatBench = Fiat.pack . map c2w8 . concatMap show

unpackBench :: ByteString -> [Int]
unpackBench = map (read . (:[]) . w82c) . BS.unpack

unpackFiatBench :: Fiat.ByteString -> [Int]
unpackFiatBench = map (read . (:[]) . w82c) . Fiat.unpack

consBench :: [Int] -> ByteString
consBench = F.foldr' BS.cons BS.empty . map c2w8 . concatMap show

consFiatBench :: [Int] -> Fiat.ByteString
consFiatBench = F.foldr' Fiat.cons Fiat.empty . map c2w8 . concatMap show

unconsBench :: ByteString -> [Int]
unconsBench xs = case BS.uncons xs of
    Nothing -> []
    Just (w, xs') -> read [w82c w] : unconsBench xs'

unconsFiatBench :: Fiat.ByteString -> [Int]
unconsFiatBench xs = case Fiat.uncons xs of
    Nothing -> []
    Just (w, xs') -> read [w82c w] : unconsFiatBench xs'

appendBench :: [Int] -> ByteString
appendBench =  F.foldl' (<>) BS.empty . map (BS.pack . map c2w8 . show)

appendFiatBench :: [Int] -> Fiat.ByteString
appendFiatBench = F.foldl' (<>) Fiat.empty . map (Fiat.pack . map c2w8 . show)

-- main :: IO ()
-- main = memoryMain

main :: IO ()
main = do
    arg:args <- getArgs
    withArgs args $ case arg of
        "time"   -> speedMain
        "memory" -> memoryMain
        _        -> error "Unknown sub-command: use time or memory"

speedMain :: IO ()
speedMain = defaultMainWith defaultConfig { csvFile = Just "bench.csv" }
    $ replicate 1
    (
    bgroup "[Int]" $ flip map [5 :: Int] $ \i ->
        let sz = 10^i
            inp = take sz [1..]
            inp' = take (sz `div` 10) [1..] in
        bgroup (show sz)
        [ bench "ByteString.pack"        (nf packBench inp)
        , bench "ByteString.Fiat.pack"   (nf packFiatBench inp)

        , bench "ByteString.unpack"      (nf unpackBench (packBench inp))
        , bench "ByteString.Fiat.unpack" (nf unpackFiatBench (packFiatBench inp))

        , bench "ByteString.cons"        (nf consBench inp')
        , bench "ByteString.Fiat.cons"   (nf consFiatBench inp')

        , bench "ByteString.uncons"      (nf unconsBench (packBench inp))
        , bench "ByteString.Fiat.uncons" (nf unconsFiatBench (packFiatBench inp))

        , bench "ByteString.append"      (nf appendBench inp')
        , bench "ByteString.Fiat.append" (nf appendFiatBench inp')
        ]
    )

memoryMain :: IO ()
memoryMain = do
    let sz = 10^(5 :: Int)
        inp = take sz [1..]
        inp' = take (sz `div` 10) [1..]
     -- withArgs [] $ Weigh.mainWith $ do
    Weigh.mainWith $ do
        Weigh.func "ByteString.pack"        packBench inp
        Weigh.func "ByteString.Fiat.pack"   packFiatBench inp

        Weigh.func "ByteString.unpack"      unpackBench (packBench inp)
        Weigh.func "ByteString.Fiat.unpack" unpackFiatBench (packFiatBench inp)

        Weigh.func "ByteString.cons"        consBench inp'
        Weigh.func "ByteString.Fiat.cons"   consFiatBench inp'

        Weigh.func "ByteString.uncons"      unconsBench (packBench inp)
        Weigh.func "ByteString.Fiat.uncons" unconsFiatBench (packFiatBench inp)

        Weigh.func "ByteString.append"      appendBench inp'
        Weigh.func "ByteString.Fiat.append" appendFiatBench inp'

compute :: (Double, Double)
compute =
    let x  = 92.18; dx = 1.567
        y  = 93.44; dy = 1.507
        z  = 100.0 - (100.0 * y) / x
        dz = z * (dy / y + dx / x)
    in (z, abs dz)

extractedPack :: [Internal.Word] -> PS0
extractedPack xs = unsafeDupablePerformIO $
    let len = length xs in
    if 0 < len
    then do
        cod <- mallocPlainForeignPtrBytes len
        withForeignPtr cod $ \ptr ->
            pokeArray ptr xs
        return $ MakePS0 cod len 0 len
    else do
        ptr <- newForeignPtr_ nullPtr
        return $ MakePS0 ptr 0 0 0

extractedCons :: PS0 -> Internal.Word -> PS0
extractedCons p w = unsafeDupablePerformIO $
  if 0 < psOffset0 p
  then do
    withForeignPtr (psBuffer0 p) $ \ptr ->
      pokeByteOff ptr (psOffset0 p - 1) w
    return $ MakePS0
      (psBuffer0 p) (psBufLen0 p)
      (psOffset0 p - 1) (psLength0 p + 1)
  else
    if psLength0 p + 1 <= psBufLen0 p
    then do
      withForeignPtr (psBuffer0 p) $ \ptr1 ->
        withForeignPtr (psBuffer0 p) $ \ptr2 ->
          copyBytes ptr1 (plusPtr ptr2 1) (psLength0 p)
      withForeignPtr (psBuffer0 p) $ \ptr ->
        pokeByteOff ptr 0 w
      return $ MakePS0
        (psBuffer0 p) (psBufLen0 p) 0
        (psLength0 p + 1)
    else
      if 0 < psBufLen0 p
      then do
        np <- mallocPlainForeignPtrBytes (psLength0 p + 1)
        withForeignPtr (psBuffer0 p) $ \ptr1 ->
          withForeignPtr np $ \ptr2 ->
            copyBytes ptr1 (plusPtr ptr2 1) (psLength0 p)
        withForeignPtr np $ \ptr -> pokeByteOff ptr 0 w
        return $ MakePS0
          np (psLength0 p + 1)
          0 (psLength0 p + 1)
      else do
        np <- mallocPlainForeignPtrBytes 1
        withForeignPtr np $ \ptr -> pokeByteOff ptr 0 w
        return $ MakePS0 np 1 0 1
