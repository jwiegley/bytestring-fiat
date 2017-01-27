module Main where

import ByteStringExt hiding (IO, fmap, map)
import Data.Word
import Foreign.Marshal.Alloc
import Foreign.Marshal.Utils
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe
import GHC.Base

c2w8 :: Char -> Word8
c2w8 = fromIntegral . fromEnum

{- | Converts a String to a [Word8]. -}
s2w8 :: String -> [Word8]
s2w8 = map c2w8

{- | Converts a Word8 to a Char. -}
w82c :: Word8 -> Char
w82c = toEnum . fromIntegral

w82s :: [Word8] -> String
w82s = map w82c

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

printPS1 :: PS1 -> IO String
printPS1 bs =
    let (bs', mres) = hsUnconsDSL' bs in
    case mres of
        Nothing -> return []
        Just c  -> (w82c c:) <$> printPS1 bs'

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

    putStrLn "Haskell ByteString heap..."

    let hs0 = hsEmptyDSL'
    putStrLn . ("hs0 = " ++) =<< printPS1 hs0
    let hs1 = hsConsDSL' hs0 (c2w8 'a')
    putStrLn . ("hs1 = " ++) =<< printPS1 hs1
    let hs2 = hsConsDSL' hs1 (c2w8 'b')
    putStrLn . ("hs2 = " ++) =<< printPS1 hs2
    let hs3 = hsConsDSL' hs2 (c2w8 'c')
    putStrLn . ("hs3 = " ++) =<< printPS1 hs3
    let (hs4, mres1'') = hsUnconsDSL' hs3
    putStrLn . ("hs4 = " ++) =<< printPS1 hs4
    print mres1''
    let (hs5, mres2'') = hsUnconsDSL' hs4
    putStrLn . ("hs5 = " ++) =<< printPS1 hs5
    print mres2''

    -- let hs6 = hsAppendDSL' hs2 hs3
    -- putStrLn . ("hs6 = " ++) =<< printPS1 hs6

castWord8Ptr :: Int -> Foreign.Ptr.Ptr Data.Word.Word8
castWord8Ptr = unsafeCoerce

castWord8PtrIO :: IO (Foreign.Ptr.Ptr Data.Word.Word8) -> IO Int
castWord8PtrIO = unsafeCoerce

data PS1 = MakePS1
    { psBuffer1 :: Int -- Foreign.Ptr.Ptr Word8
    , psBufLen1 :: Size
    , psOffset1 :: Size
    , psLength1 :: Size
    }

hsEmptyDSL' :: PS1
hsEmptyDSL' = MakePS1 0 0 0 0

hsConsDSL' :: PS1 -> Word8 -> PS1
hsConsDSL' p w = System.IO.Unsafe.unsafePerformIO $
  if ltb 0 (psOffset1 p)
    then do
      let pos = psOffset1 p - 1
      Foreign.Storable.poke (castWord8Ptr (psBuffer1 p + pos)) w
      return $ MakePS1 (psBuffer1 p) (psBufLen1 p) pos ((+) (psLength1 p) 1)
    else
      if leb ((+) (psLength1 p) 1) (psBufLen1 p)
        then do
          (GHC.Base.>>=)
            ((\x y -> Foreign.Marshal.Utils.copyBytes (castWord8Ptr x) (castWord8Ptr y))
              (psBuffer1 p) ((+) (psBuffer1 p) 1)
              (psLength1 p)) (\_ ->
            fmap (\_ -> MakePS1 (psBuffer1 p) (psBufLen1 p) 0
              ((+) (psLength1 p) 1))
              ((\x y -> Foreign.Storable.poke (castWord8Ptr x) y)
                ((+) (psBuffer1 p) 0) w));
        else
          if ltb 0 (psBufLen1 p)
            then do
              (GHC.Base.>>=)
                ((\x -> castWord8PtrIO (Foreign.Marshal.Alloc.mallocBytes x))
                  ((+) (psLength1 p) 1)) (\cod ->
                (GHC.Base.>>=)
                  ((\x y -> Foreign.Marshal.Utils.copyBytes (castWord8Ptr x) (castWord8Ptr y))
                    (psBuffer1 p) ((+) cod 1) (psLength1 p))
                  (\_ ->
                  (GHC.Base.>>=)
                    ((\x -> Foreign.Marshal.Alloc.free (castWord8Ptr x))
                      (psBuffer1 p)) (\_ ->
                    (GHC.Base.>>=)
                      ((\x y -> Foreign.Storable.poke (castWord8Ptr x) y)
                        ((+) cod 0) w) (\_ ->
                      return (MakePS1 cod
                        ((+) (psLength1 p) 1) 0
                        ((+) (psLength1 p) 1))))));
            else do
              (GHC.Base.>>=)
                ((\x -> castWord8PtrIO (Foreign.Marshal.Alloc.mallocBytes x))
                  1) (\cod ->
                (GHC.Base.>>=)
                  ((\x y -> Foreign.Storable.poke (castWord8Ptr x) y)
                    ((+) cod 0) w) (\_ ->
                  return (MakePS1 cod 1 0 1)))

hsUnconsDSL' :: PS1 -> (,) PS1 (Maybe Word8)
hsUnconsDSL' p = System.IO.Unsafe.unsafePerformIO $
  if ltb 0 (psLength1 p)
    then do
      a <- Foreign.Storable.peek (castWord8Ptr ((+) (psBuffer1 p) (psOffset1 p)))
      return (MakePS1 (psBuffer1 p) (psBufLen1 p)
                      (if eqb1 (psLength1 p) 1 then 0 else psOffset1 p + 1)
                      (psLength1 p - 1), Just a)
    else return (p, Nothing)

{-
hsAppendDSL' :: PS1 -> PS1 -> PS1
hsAppendDSL' p p1 =
  System.IO.Unsafe.unsafePerformIO
    (case ltb 0 (psLength1 p) of {
      True ->
       case ltb 0 (psLength1 p1) of {
        True ->
         (GHC.Base.>>=)
           ((\x -> castWord8PtrIO (Foreign.Marshal.Alloc.mallocBytes x))
             ((+) (psLength1 p) (psLength1 p1))) (\cod ->
           (GHC.Base.>>=)
             ((\x y -> Foreign.Marshal.Utils.copyBytes (castWord8Ptr x) (castWord8Ptr y))
               ((+) (psBuffer1 p) (psOffset1 p)) cod (psLength1 p))
             (\_ ->
             return (MakePS1 cod
               ((+) (psLength1 p) (psLength1 p1)) 0
               ((+) (psLength1 p) (psLength1 p1)))));
        False -> return p};
      False -> return p1})
-}
