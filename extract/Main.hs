module Main where

import Data.ByteString.Fiat hiding (putStrLn)
import Data.Word

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

printPS :: CRep -> BScrep -> IO String
printPS h bs =
    let (bs', mres) = unconsBS h bs in
    case mres of
        Nothing -> return []
        Just c  -> (w82c c:) <$> printPS h bs'

printPS0 :: PS0 -> IO String
printPS0 bs =
    let (bs', mres) = ghcUnconsDSL' bs in
    case mres of
        Nothing -> return []
        Just c  -> (w82c c:) <$> printPS0 bs'

main :: IO ()
main = do
    putStrLn "Heaps..."

    let h0 = emptyHeap
    let (h1, addr) = allocHeap h0 (of_nat 100)
    print $ to_nat0 addr
    let (h2, addr') = allocHeap h1 (of_nat 200)
    print $ to_nat0 addr'
    let h3 = pokeHeap h2 (of_nat 105) (c2w8 'a')
    let (_h4, val) = peekHeap h3 (of_nat 105)
    print val

    putStrLn "ByteString list..."

    let b0 = emptyBS h0
    putStrLn . ("b0 = " ++) =<< printPS h0 b0
    let b1 = consBS h0 b0 (c2w8 'a')
    putStrLn . ("b1 = " ++) =<< printPS h0 b1
    let b2 = consBS h0 b1 (c2w8 'b')
    putStrLn . ("b2 = " ++) =<< printPS h0 b2
    let b3 = consBS h0 b2 (c2w8 'c')
    putStrLn . ("b3 = " ++) =<< printPS h0 b3
    let (b4, mres1) = unconsBS h0 b3
    putStrLn . ("b4 = " ++) =<< printPS h0 b4
    print mres1
    let (b5, mres2) = unconsBS h0 b4
    putStrLn . ("b5 = " ++) =<< printPS h0 b5
    print mres2

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

    let bs6 = ghcAppendDSL' bs2 bs3
    putStrLn . ("bs6 = " ++) =<< printPS0 bs6
