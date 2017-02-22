{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Blaze.ByteString.Builder as Blaze
import qualified Blaze.ByteString.Builder.Char8 as Blaze
import           Control.DeepSeq
import           Criterion.Main
import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BSI
import qualified Data.ByteString.Builder as BB
import           Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Fiat as Fiat
import qualified Data.ByteString.Fiat.Internal as Internal
import qualified Data.ByteString.Lazy as LBS
import           Data.Function ((&))
import           Data.List (foldl')
import qualified Data.List as List
import           Data.Monoid ((<>))
import           Data.Word (Word8)
import           Test.QuickCheck.Arbitrary
import           Test.QuickCheck.Gen
import           Test.QuickCheck.Random

import System.IO.Unsafe
import Foreign.Ptr (Ptr, plusPtr, nullPtr)
import Foreign.ForeignPtr (ForeignPtr, withForeignPtr, newForeignPtr_)
import Foreign.Storable (Storable, poke, pokeElemOff)
import Foreign.Marshal.Array
import Foreign.Marshal.Alloc
import GHC.Base
import GHC.ForeignPtr (mallocPlainForeignPtrBytes)

unsafeCoerce = GHC.Base.unsafeCoerce#

-- instance NFData Fiat.ByteString where
--     rnf (Fiat.BPS (Internal.MakePS0 !a !b !c !d) !e) = ()

instance NFData Internal.PS0 where
    rnf (Internal.MakePS0 !a !b !c !d) = ()

c2w8 :: Char -> Word8
c2w8 = fromIntegral . fromEnum

showStr :: [Integer] -> ByteString
showStr = BS.pack . map c2w8 . concatMap show

packBytes :: [Word8] -> ByteString
packBytes ws = unsafePackLenBytes (List.length ws) ws

unsafePackLenBytes :: Int -> [Word8] -> ByteString
unsafePackLenBytes len xs0 =
    unsafeCreate len $ \p -> go p xs0
  where
    go !_ []     = return ()
    go !p (x:xs) = poke p x >> go (p `plusPtr` 1) xs

unsafeCreate :: Int -> (Ptr Word8 -> IO ()) -> ByteString
unsafeCreate l f = unsafeDupablePerformIO (create l f)
{-# INLINE unsafeCreate #-}

create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
create l f = do
    fp <- mallocByteString l
    withForeignPtr fp $ \p -> f p
    return $! BSI.PS fp 0 l
{-# INLINE create #-}

mallocByteString :: Int -> IO (ForeignPtr a)
mallocByteString l = mallocPlainForeignPtrBytes l
{-# INLINE mallocByteString #-}

showStr' :: [Integer] -> ByteString
showStr' = packBytes . map c2w8 . concatMap show

showFiatStr :: [Integer] -> Fiat.ByteString
showFiatStr = Fiat.pack . map c2w8 . concatMap show

pokeList :: Ptr Word8 -> [Word8] -> IO ()
pokeList !_ []     = return ()
pokeList !p (x:xs) = poke p x >> pokeList (p `plusPtr` 1) xs

pokeList' :: Ptr Word8 -> [Word8] -> IO ()
pokeList' p xs = go xs 0#
  where go [] _          = return ()
        go (val:vals) n# = do pokeElemOff p (I# n#) val; go vals (n# +# 1#)

pack' :: [Word8] -> Internal.PS0
pack' l = unsafeDupablePerformIO $ do
    cod <- mallocPlainForeignPtrBytes len
    withForeignPtr cod $ \p -> pokeList' p l
    return $ Internal.MakePS0 (unsafeCoerce cod) len 0 len
  where
    len = length l

showFiatStr' :: [Integer] -> Fiat.ByteString
showFiatStr' = pack' . map c2w8 . concatMap show

pack'' :: ([] Word8) -> Internal.PS0
pack'' xs =
  unsafeDupablePerformIO
    ((&) (length xs) (\len ->
      (\c t e -> if c then t else e) (0 < len)
        (do cod <- mallocPlainForeignPtrBytes len
            Foreign.ForeignPtr.withForeignPtr cod $ \ptr ->
                pokeArray (plusPtr ptr 0) xs
            return $ Internal.MakePS0 cod len 0 len)
        (Prelude.return (Internal.MakePS0
          (unsafePerformIO (newForeignPtr_ nullPtr))
          0 0 0))))

showFiatStr'' :: [Integer] -> Fiat.ByteString
showFiatStr'' = pack'' . map c2w8 . concatMap show

showByteString :: [Integer] -> ByteString
showByteString = foldl' (<>) "" . map (BS.pack . map c2w8 . show)

showByteStringBuilder :: [Integer] -> ByteString
showByteStringBuilder = LBS.toStrict . BB.toLazyByteString . go
  where
    go [] = mempty
    go (x:xs) = BB.integerDec x <> go xs

showBlazeBuilder :: [Integer] -> ByteString
showBlazeBuilder = Blaze.toByteString . go
  where
    go [] = mempty
    go (x:xs) = Blaze.fromShow x  <> go xs

main :: IO ()
main = defaultMain
  [
  bgroup "[Integer]" $
    map (\i ->
      let sz = 10^i
          inp = take sz [1..]
      in bgroup (show sz)
         [ bench "(++) . show" (nf showStr inp)
         , bench "(++)' . show" (nf showStr' inp)
         --, bench "(<>) . show" (nf showByteString (if i < 6 then inp else []))
         , bench "Fiat (++) . show" (nf showFiatStr inp)
         , bench "Fiat' (++) . show" (nf showFiatStr' inp)
         , bench "Fiat'' (++) . show" (nf showFiatStr'' inp)
         -- -- , bench "putM" (nf showPutM inp)
         -- , bench "bytestring-builder" (nf showByteStringBuilder inp)
         -- , bench "blaze-builder" (nf showBlazeBuilder inp)
         ]
    )
    [1..2 :: Integer]
  ]
  where
