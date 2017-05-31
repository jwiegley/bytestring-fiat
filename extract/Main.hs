{-# LANGUAGE PackageImports #-}

module Main where

import qualified "bytestring" Data.ByteString as BSH
import qualified Data.ByteString.Fiat as BS
import           Data.ByteString.Fiat.Internal hiding (IO, putStrLn)
import           Data.Word (Word8)
import           Foreign.Marshal.Alloc (mallocBytes)
import           Foreign.Marshal.Utils (copyBytes)
import           Foreign.Ptr (Ptr, plusPtr)
import           GHC.Prim
import           System.IO.Unsafe (unsafePerformIO)
import           Test.Hspec
import           Test.QuickCheck

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

printPSH :: BSH.ByteString -> IO String
printPSH bs =
    case BSH.uncons bs of
        Nothing -> return []
        Just (c, bs')  -> (w82c c:) <$> printPSH bs'

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
main = hspec $ do
    describe "Basic tests" $ do
        it "Haskell ByteString baseline" $ do
            let s0 = BSH.empty
            printPSH s0 `shouldReturn` ""
            let s1 = BSH.cons (c2w8 'a') s0
            printPSH s1 `shouldReturn` "a"
            let s2 = BSH.cons (c2w8 'b') s1
            printPSH s2 `shouldReturn` "ba"
            let s3 = BSH.cons (c2w8 'c') s2
            printPSH s3 `shouldReturn` "cba"
            case BSH.uncons s3 of
                Nothing -> return ()
                Just (mres1', s4) -> do
                    mres1' `shouldBe` c2w8 'c'
                    printPSH s4 `shouldReturn` "ba"
                    case BSH.uncons s4 of
                        Nothing -> return ()
                        Just (mres2', s5) -> do
                            mres2' `shouldBe` c2w8 'b'
                            printPSH s5 `shouldReturn` "a"

                    let s6 = BSH.append s3 s2
                    printPSH s6 `shouldReturn` "cbaba"

        it "Constructs ByteStrings (directly)" $ do
            let bs0 = ghcEmptyDSL'
            printPS0 bs0 `shouldReturn` ""
            let bs1 = ghcConsDSL' bs0 (c2w8 'a')
            printPS0 bs1 `shouldReturn` "a"
            let bs2 = ghcConsDSL' bs1 (c2w8 'b')
            printPS0 bs2 `shouldReturn` "ba"
            let bs3 = ghcConsDSL' bs2 (c2w8 'c')
            printPS0 bs3 `shouldReturn` "cba"
            let (bs4, mres1') = ghcUnconsDSL' bs3
            mres1' `shouldBe` Just (c2w8 'c')
            printPS0 bs4 `shouldReturn` "ba"
            let (bs5, mres2') = ghcUnconsDSL' bs4
            mres2' `shouldBe` Just (c2w8 'b')
            printPS0 bs5 `shouldReturn` "a"

            let bs6 = ghcAppendDSL' bs3 bs2
            printPS0 bs6 `shouldReturn` "cbaba"

        it "Constructs ByteStrings (using the BS interface)" $ do
            let s0 = BS.empty
            printPS1 s0 `shouldReturn` ""
            let s1 = BS.cons (c2w8 'a') s0
            printPS1 s1 `shouldReturn` "a"
            let s2 = BS.cons (c2w8 'b') s1
            printPS1 s2 `shouldReturn` "ba"
            let s3 = BS.cons (c2w8 'c') s2
            printPS1 s3 `shouldReturn` "cba"
            case BS.uncons s3 of
                Nothing -> return ()
                Just (mres1', s4) -> do
                    printPS1 s4 `shouldReturn` "ba"
                    mres1' `shouldBe` c2w8 'c'
                    case BS.uncons s4 of
                        Nothing -> return ()
                        Just (mres2', s5) -> do
                            printPS1 s5 `shouldReturn` "a"
                            mres2' `shouldBe` c2w8 'b'

                    let s6 = BS.append s3 s2
                    printPS1 s6 `shouldReturn` "cbaba"

        it "Handles cons followed by uncons" $ do
            let s0 = BS.empty
            printPS1 s0 `shouldReturn` ""
            let s1 = BS.cons (c2w8 'a') (BS.cons (c2w8 'a') s0)
            printPS1 s1 `shouldReturn` "aa"
            let Just (res, s2) = BS.uncons s1
            printPS1 s2 `shouldReturn` "a"
            res `shouldBe` c2w8 'a'
            let s3 = BS.cons (c2w8 'b') s2
            printPS1 s3 `shouldReturn` "ba"
            printPS1 s1 `shouldReturn` "aa"
