{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import           Control.DeepSeq
import           Criterion.Main
import qualified Data.ByteString as BS
import           Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Fiat as Fiat
import qualified Data.ByteString.Fiat.Internal as Internal
import qualified Data.Foldable as F
import           Data.Monoid
import           Data.Word (Word8)

instance NFData Internal.PS0 where
    rnf (Internal.MakePS0 !_ !_ !_ !_) = ()

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
consBench = foldr BS.cons BS.empty . concatMap (map c2w8 . show)

consFiatBench :: [Int] -> Fiat.ByteString
consFiatBench = foldr Fiat.cons Fiat.empty . concatMap (map c2w8 . show)

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

instance Monoid Fiat.ByteString where
    mempty  = Fiat.empty
    mappend = Fiat.append

appendFiatBench :: [Int] -> Fiat.ByteString
appendFiatBench = F.foldl' (<>) Fiat.empty . map (Fiat.pack . map c2w8 . show)

main :: IO ()
main = defaultMain
    [
    bgroup "[Int]" $ flip map [3 :: Int] $ \i ->
        let sz = 10^i; inp = take sz [1..] in
        bgroup (show sz)
        [ bench "ByteString.pack"        (nf packBench inp)
        , bench "ByteString.Fiat.pack"   (nf packFiatBench inp)

        , bench "ByteString.unpack"      (nf unpackBench (packBench inp))
        , bench "ByteString.Fiat.unpack" (nf unpackFiatBench (packFiatBench inp))

        , bench "ByteString.cons"        (nf consBench inp)
        , bench "ByteString.Fiat.cons"   (nf consFiatBench inp)

        , bench "ByteString.uncons"      (nf unconsBench (packBench inp))
        , bench "ByteString.Fiat.uncons" (nf unconsFiatBench (packFiatBench inp))

        , bench "ByteString.append"      (nf packBench inp)
        , bench "ByteString.Fiat.append" (nf packFiatBench inp)
        ]
    ]

-- packOpt :: [Word8] -> Internal.PS0
-- packOpt xs = unsafeDupablePerformIO $
--     let len = length xs in
--     if 0 < len
--     then do
--         cod <- mallocPlainForeignPtrBytes len
--         withForeignPtr cod $ \ptr ->
--             pokeArray ptr xs
--         return $ Internal.MakePS0 cod len 0 len
--     else do
--         ptr <- newForeignPtr_ nullPtr
--         return $ Internal.MakePS0 ptr 0 0 0
