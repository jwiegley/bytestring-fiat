Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.Computation.FixComp
  ByteString.Heap
  ByteString.ByteString.

(************************************************************************
 ** Semantics of the Haskell ByteString library in Fiat.               **
 ************************************************************************)

Definition singleton_Spec (w : Word8) : Comp ByteString :=
  xs  <- callCons ByteStringSpec emptyS;
  res <- callMeth ByteStringSpec consS xs w;
  ret (fst res).

(*
Definition pack_Spec (xs : list Word8) : Comp ByteString :=
Definition unpack_Spec (bs : ByteString) : Comp (ByteString * list Word8) :=
Definition snoc (bs : ByteString) (w : Word8) : Comp (ByteString * unit) :=
*)

Import LeastFixedPointFun.

Definition foldr_Spec {A} :
  ByteString -> (Word8 -> A -> A) -> A -> Comp (ByteString * A) :=
  LeastFixedPoint (fDom := [ByteString; Word8 -> A -> A; A])
                  (fCod := ByteString * A)
    (fun rec (bs : ByteString) (f : Word8 -> A -> A) (z : A) =>
       p <- uncons bs;
       Ifopt snd p as w
       Then bs' <- rec (fst p) f z;
            ret (fst bs', f w (snd bs'))
       Else ret (bs, z)).

(*
append :: ByteString -> ByteString -> ByteString
head :: ByteString -> Word8
unsnoc :: ByteString -> Maybe (ByteString, Word8)
last :: ByteString -> Word8
*)

Definition tail_Spec (bs : ByteString) : Comp (ByteString * bool) :=
  p <- uncons bs;
  ret (Ifopt snd p as w
       Then (fst p, true)
       Else (bs, false)).

(*
init :: ByteString -> ByteString
null :: ByteString -> Bool
length :: ByteString -> Int
map :: (Word8 -> Word8) -> ByteString -> ByteString
reverse :: ByteString -> ByteString
intersperse :: Word8 -> ByteString -> ByteString
intercalate :: ByteString -> [ByteString] -> ByteString
transpose :: [ByteString] -> [ByteString]
foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr' :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
concat :: [ByteString] -> ByteString
concatMap :: (Word8 -> ByteString) -> ByteString -> ByteString
any :: (Word8 -> Bool) -> ByteString -> Bool
all :: (Word8 -> Bool) -> ByteString -> Bool
maximum :: ByteString -> Word8
minimum :: ByteString -> Word8
scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanr :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
replicate :: Int -> Word8 -> ByteString
unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
take :: Int -> ByteString -> ByteString
drop :: Int -> ByteString -> ByteString
splitAt :: Int -> ByteString -> (ByteString, ByteString)
takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
group :: ByteString -> [ByteString]
groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
inits :: ByteString -> [ByteString]
tails :: ByteString -> [ByteString]
split :: Word8 -> ByteString -> [ByteString]
splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]
isPrefixOf :: ByteString -> ByteString -> Bool
isSuffixOf :: ByteString -> ByteString -> Bool
isInfixOf :: ByteString -> ByteString -> Bool
breakSubstring :: ByteString -> ByteString -> (ByteString, ByteString)
findSubstring :: ByteString -> ByteString -> Maybe Int
findSubstrings :: ByteString -> ByteString -> [Int]
elem :: Word8 -> ByteString -> Bool
notElem :: Word8 -> ByteString -> Bool
find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
filter :: (Word8 -> Bool) -> ByteString -> ByteString
partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
index :: ByteString -> Int -> Word8
elemIndex :: Word8 -> ByteString -> Maybe Int
elemIndices :: Word8 -> ByteString -> [Int]
elemIndexEnd :: Word8 -> ByteString -> Maybe Int
findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
findIndices :: (Word8 -> Bool) -> ByteString -> [Int]
count :: Word8 -> ByteString -> Int
zip :: ByteString -> ByteString -> [(Word8, Word8)]
zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
unzip :: [(Word8, Word8)] -> (ByteString, ByteString)
sort :: ByteString -> ByteString
copy :: ByteString -> ByteString
*)

(*
packCString :: CString -> IO ByteString
packCStringLen :: CStringLen -> IO ByteString
useAsCString :: ByteString -> (CString -> IO a) -> IO a
useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
getLine :: IO ByteString
getContents :: IO ByteString
putStr :: ByteString -> IO ()
putStrLn :: ByteString -> IO ()
interact :: (ByteString -> ByteString) -> IO ()
readFile :: FilePath -> IO ByteString
writeFile :: FilePath -> ByteString -> IO ()
appendFile :: FilePath -> ByteString -> IO ()
hGetLine :: Handle -> IO ByteString
hGetContents :: Handle -> IO ByteString
hGet :: Handle -> Int -> IO ByteString
hGetSome :: Handle -> Int -> IO ByteString
hGetNonBlocking :: Handle -> Int -> IO ByteString
hPut :: Handle -> ByteString -> IO ()
hPutNonBlocking :: Handle -> ByteString -> IO ByteString
hPutStr :: Handle -> ByteString -> IO ()
hPutStrLn :: Handle -> ByteString -> IO ()
*)

(*
breakByte :: Word8 -> ByteString -> (ByteString, ByteString)
*)
