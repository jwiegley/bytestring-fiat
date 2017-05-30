module Main where

import qualified Data.ByteString.Fiat as BS
import           Data.ByteString.Fiat.Internal hiding (IO, putStrLn)
import           Data.Word (Word8)
import           Foreign.Marshal.Alloc (mallocBytes)
import           Foreign.Marshal.Utils (copyBytes)
import           Foreign.Ptr (Ptr, plusPtr)
import           GHC.Prim
import           System.IO.Unsafe (unsafePerformIO)

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

-- printPS :: Rep -> CRep -> BScrep -> IO String
-- printPS h h' bs =
--     let (bs', mres) = unconsBS h h' bs in
--     case mres of
--         Nothing -> return []
--         Just c  -> (w82c c:) <$> printPS h h' bs'

printPS0 :: PS0 -> IO String
printPS0 bs =
    let (bs', mres) = ghcUnconsDSL' bs in
    case mres of
        Nothing -> return []
        Just c  -> (w82c c:) <$> printPS0 bs'

printPS1 :: BS.ByteString -> IO String
printPS1 bs =
    case BS.uncons bs of
        Nothing -> return []
        Just (c, bs') -> (w82c c:) <$> printPS1 bs'

main :: IO ()
main = do
    -- putStrLn "ByteString list..."

    -- let h0 = emptyHeap
    -- let b0 = emptyBS any' h0
    -- putStrLn . ("b0 = " ++) =<< printPS any' h0 b0
    -- let b1 = consBS any' h0 b0 (c2w8 'a')
    -- putStrLn . ("b1 = " ++) =<< printPS any' h0 b1
    -- let b2 = consBS any' h0 b1 (c2w8 'b')
    -- putStrLn . ("b2 = " ++) =<< printPS any' h0 b2
    -- let b3 = consBS any' h0 b2 (c2w8 'c')
    -- putStrLn . ("b3 = " ++) =<< printPS any' h0 b3
    -- let (b4, mres1) = unconsBS any' h0 b3
    -- putStrLn . ("b4 = " ++) =<< printPS any' h0 b4
    -- print mres1
    -- let (b5, mres2) = unconsBS any' h0 b4
    -- putStrLn . ("b5 = " ++) =<< printPS any' h0 b5
    -- print mres2

    -- -- b3 has the final heap state
    -- let b6 = appendBS any' h0 b3 b2
    -- putStrLn . ("bs6 = " ++) =<< printPS any' h0 b6

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

    putStrLn "ByteString test..."

    let s0 = BS.empty
    putStrLn . ("s0 = " ++) =<< printPS1 s0
    let s1 = BS.cons (c2w8 'a') (BS.cons (c2w8 'a') s0)
    putStrLn . ("s1 = " ++) =<< printPS1 s1
    let Just (_, s2) = BS.uncons s1
    putStrLn . ("s2 = " ++) =<< printPS1 s2
    let s3 = BS.cons (c2w8 'b') s2
    putStrLn . ("s3 = " ++) =<< printPS1 s3
    putStrLn . ("s1 = " ++) =<< printPS1 s1

    putStrLn "ByteString via Internal..."

    let s0 = BS.empty
    putStrLn . ("s0 = " ++) =<< printPS1 s0
    let s1 = BS.cons (c2w8 'a') s0
    putStrLn . ("s1 = " ++) =<< printPS1 s1
    let s2 = BS.cons (c2w8 'b') s1
    putStrLn . ("s2 = " ++) =<< printPS1 s2
    let s3 = BS.cons (c2w8 'c') s2
    putStrLn . ("s3 = " ++) =<< printPS1 s3
    case BS.uncons s3 of
        Nothing -> return ()
        Just (mres1', s4) -> do
            putStrLn . ("s4 = " ++) =<< printPS1 s4
            print mres1'
            case BS.uncons s4 of
                Nothing -> return ()
                Just (mres2', s5) -> do
                    putStrLn . ("s5 = " ++) =<< printPS1 s5
                    print mres2'

            let s6 = BS.append s3 s2
            putStrLn . ("s6 = " ++) =<< printPS1 s6
  where
    any' = unsafeCoerce ()
