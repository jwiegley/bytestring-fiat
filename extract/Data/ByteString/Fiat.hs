{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}

module Data.ByteString.Fiat (

        -- * The @ByteString@ type
        ByteString,             -- abstract, instances: Eq, Ord, Show, Read, Data, Typeable, Monoid

        -- * Introducing and eliminating 'ByteString's
        empty,                  -- :: ByteString
        singleton,              -- :: Word8   -> ByteString
        pack,                   -- :: [Word8] -> ByteString
        unpack,                 -- :: ByteString -> [Word8]

        -- * Basic interface
        cons,                   -- :: Word8 -> ByteString -> ByteString
        snoc,                   -- :: ByteString -> Word8 -> ByteString
        append,                 -- :: ByteString -> ByteString -> ByteString
        head,                   -- :: ByteString -> Word8
        uncons,                 -- :: ByteString -> Maybe (Word8, ByteString)
        unsnoc,                 -- :: ByteString -> Maybe (ByteString, Word8)
        last,                   -- :: ByteString -> Word8
        tail,                   -- :: ByteString -> ByteString
        init,                   -- :: ByteString -> ByteString
        null,                   -- :: ByteString -> Bool
        length,                 -- :: ByteString -> Int

        -- * Transforming ByteStrings
        map,                    -- :: (Word8 -> Word8) -> ByteString -> ByteString
        reverse,                -- :: ByteString -> ByteString
        intersperse,            -- :: Word8 -> ByteString -> ByteString
        intercalate,            -- :: ByteString -> [ByteString] -> ByteString
        transpose,              -- :: [ByteString] -> [ByteString]

        -- * Reducing 'ByteString's (folds)
        foldl,                  -- :: (a -> Word8 -> a) -> a -> ByteString -> a
        foldl',                 -- :: (a -> Word8 -> a) -> a -> ByteString -> a
        foldl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
        foldl1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8

        foldr,                  -- :: (Word8 -> a -> a) -> a -> ByteString -> a
        foldr',                 -- :: (Word8 -> a -> a) -> a -> ByteString -> a
        foldr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
        foldr1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8

        -- ** Special folds
        concat,                 -- :: [ByteString] -> ByteString
        concatMap,              -- :: (Word8 -> ByteString) -> ByteString -> ByteString
        any,                    -- :: (Word8 -> Bool) -> ByteString -> Bool
        all,                    -- :: (Word8 -> Bool) -> ByteString -> Bool
        maximum,                -- :: ByteString -> Word8
        minimum,                -- :: ByteString -> Word8

        -- * Building ByteStrings
        -- ** Scans
        scanl,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
        scanl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
        scanr,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
        scanr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString

        -- ** Accumulating maps
        mapAccumL,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
        mapAccumR,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)

        -- ** Generating and unfolding ByteStrings
        replicate,              -- :: Int -> Word8 -> ByteString
        unfoldr,                -- :: (a -> Maybe (Word8, a)) -> a -> ByteString
        unfoldrN,               -- :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)

        -- * Substrings

        -- ** Breaking strings
        take,                   -- :: Int -> ByteString -> ByteString
        drop,                   -- :: Int -> ByteString -> ByteString
        splitAt,                -- :: Int -> ByteString -> (ByteString, ByteString)
        takeWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
        dropWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
        span,                   -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        spanEnd,                -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        break,                  -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        breakEnd,               -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        group,                  -- :: ByteString -> [ByteString]
        groupBy,                -- :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
        inits,                  -- :: ByteString -> [ByteString]
        tails,                  -- :: ByteString -> [ByteString]
        stripPrefix,            -- :: ByteString -> ByteString -> Maybe ByteString
        stripSuffix,            -- :: ByteString -> ByteString -> Maybe ByteString

        -- ** Breaking into many substrings
        split,                  -- :: Word8 -> ByteString -> [ByteString]
        splitWith,              -- :: (Word8 -> Bool) -> ByteString -> [ByteString]

        -- * Predicates
        isPrefixOf,             -- :: ByteString -> ByteString -> Bool
        isSuffixOf,             -- :: ByteString -> ByteString -> Bool
        isInfixOf,              -- :: ByteString -> ByteString -> Bool

        -- ** Search for arbitrary substrings
        breakSubstring,         -- :: ByteString -> ByteString -> (ByteString,ByteString)
        findSubstring,          -- :: ByteString -> ByteString -> Maybe Int
        findSubstrings,         -- :: ByteString -> ByteString -> [Int]

        -- * Searching ByteStrings

        -- ** Searching by equality
        elem,                   -- :: Word8 -> ByteString -> Bool
        notElem,                -- :: Word8 -> ByteString -> Bool

        -- ** Searching with a predicate
        find,                   -- :: (Word8 -> Bool) -> ByteString -> Maybe Word8
        filter,                 -- :: (Word8 -> Bool) -> ByteString -> ByteString
        partition,              -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)

        -- * Indexing ByteStrings
        index,                  -- :: ByteString -> Int -> Word8
        elemIndex,              -- :: Word8 -> ByteString -> Maybe Int
        elemIndices,            -- :: Word8 -> ByteString -> [Int]
        elemIndexEnd,           -- :: Word8 -> ByteString -> Maybe Int
        findIndex,              -- :: (Word8 -> Bool) -> ByteString -> Maybe Int
        findIndices,            -- :: (Word8 -> Bool) -> ByteString -> [Int]
        count,                  -- :: Word8 -> ByteString -> Int

        -- * Zipping and unzipping ByteStrings
        zip,                    -- :: ByteString -> ByteString -> [(Word8,Word8)]
        zipWith,                -- :: (Word8 -> Word8 -> c) -> ByteString -> ByteString -> [c]
        unzip,                  -- :: [(Word8,Word8)] -> (ByteString,ByteString)

        -- * Ordered ByteStrings
        sort,                   -- :: ByteString -> ByteString

        -- * Low level conversions
        -- ** Copying ByteStrings
        copy,                   -- :: ByteString -> ByteString

        -- ** Packing 'CString's and pointers
        packCString,            -- :: CString -> IO ByteString
        packCStringLen,         -- :: CStringLen -> IO ByteString

        -- ** Using ByteStrings as 'CString's
        useAsCString,           -- :: ByteString -> (CString    -> IO a) -> IO a
        useAsCStringLen,        -- :: ByteString -> (CStringLen -> IO a) -> IO a

        -- * I\/O with 'ByteString's

        -- ** Standard input and output
        getLine,                -- :: IO ByteString
        getContents,            -- :: IO ByteString
        putStr,                 -- :: ByteString -> IO ()
        putStrLn,               -- :: ByteString -> IO ()
        interact,               -- :: (ByteString -> ByteString) -> IO ()

        -- ** Files
        readFile,               -- :: FilePath -> IO ByteString
        writeFile,              -- :: FilePath -> ByteString -> IO ()
        appendFile,             -- :: FilePath -> ByteString -> IO ()

        -- ** I\/O with Handles
        hGetLine,               -- :: Handle -> IO ByteString
        hGetContents,           -- :: Handle -> IO ByteString
        hGet,                   -- :: Handle -> Int -> IO ByteString
        hGetSome,               -- :: Handle -> Int -> IO ByteString
        hGetNonBlocking,        -- :: Handle -> Int -> IO ByteString
        hPut,                   -- :: Handle -> ByteString -> IO ()
        hPutNonBlocking,        -- :: Handle -> ByteString -> IO ByteString
        hPutStr,                -- :: Handle -> ByteString -> IO ()
        hPutStrLn,              -- :: Handle -> ByteString -> IO ()

        breakByte

  ) where

import qualified Prelude as P
import Prelude hiding           (reverse,head,tail,last,init,null
                                ,length,map,lines,foldl,foldr,unlines
                                ,concat,any,take,drop,splitAt,takeWhile
                                ,dropWhile,span,break,elem,filter,maximum
                                ,minimum,all,concatMap,foldl1,foldr1
                                ,scanl,scanl1,scanr,scanr1
                                ,readFile,writeFile,appendFile,replicate
                                ,getContents,getLine,putStr,putStrLn,interact
                                ,zip,zipWith,unzip,notElem)

import Data.Bits                (finiteBitSize, shiftL, (.|.), (.&.))

import Data.ByteString.Fiat.Internal
    hiding (IO, Ptr, Word, PS(..), singleton,
            empty, fmap, find, filter, partition, map)
import qualified Data.ByteString.Fiat.Internal as Internal

import qualified Data.List as List

import Data.Word                (Word8)
import Data.Maybe               (isJust)

import Control.Exception        (finally, bracket, assert, throwIO)
import Control.Monad            (when)

import Foreign.C.String         (CString, CStringLen)
import Foreign.C.Types          (CSize)
import Foreign.ForeignPtr       (ForeignPtr, withForeignPtr, touchForeignPtr,
                                 newForeignPtr)
import Foreign.ForeignPtr.Unsafe(unsafeForeignPtrToPtr)
import Foreign.Marshal.Alloc    (allocaBytes, finalizerFree)
import Foreign.Marshal.Array    (allocaArray)
import Foreign.Ptr
import Foreign.Storable         (Storable(..))

import System.IO                (stdin,stdout,hClose,hFileSize
                                ,hGetBuf,hPutBuf,openBinaryFile
                                ,IOMode(..))
import System.IO.Error          (mkIOError, illegalOperationErrorType)


import System.IO                (hGetBufNonBlocking, hPutBufNonBlocking)

import System.IO                (hGetBufSome)

import Data.IORef
import GHC.IO.Handle.Internals
import GHC.IO.Handle.Types
import GHC.IO.Buffer
import GHC.IO.BufferedIO as Buffered
import GHC.IO                   (unsafePerformIO, unsafeDupablePerformIO)
import Data.Char                (ord)
import Foreign.Marshal.Utils    (copyBytes)

import GHC.Prim                 (Word#)
import GHC.Base                 (build)
import GHC.Word hiding (Word8)


data ByteString = BPS { getPS :: Internal.PS0
                      , getFptr :: Maybe (ForeignPtr Word8) }

pattern PS a b c <- BPS (Internal.MakePS0 a _ b c) _

wrap_ :: Internal.PS0 -> ByteString
wrap_ ps0 =
    let bs@(Internal.MakePS0 p _ _ _) = ps0
        fptr = unsafePerformIO $ newForeignPtr finalizerFree (unsafeCoerce p) in
    BPS bs (Just fptr)

empty :: ByteString
empty = wrap_ Internal.ghcEmptyDSL'

singleton :: Word8 -> ByteString
singleton w = wrap_ (Internal.ghcConsDSL' Internal.ghcEmptyDSL' w)



pack :: [Word8] -> ByteString
pack xs = wrap_ (Internal.ghcPackDSL' xs)

unpack :: ByteString -> [Word8]
unpack = Internal.ghcUnpackDSL' . getPS

unpackFoldr :: ByteString -> (Word8 -> a -> a) -> a -> a
unpackFoldr bs k z = error "NYI"



null :: ByteString -> Bool
null (PS _ _ l) = l == 0

length :: ByteString -> Int
length (PS _ _ l) = l


infixr 5 `cons`
infixl 5 `snoc`

cons :: Word8 -> ByteString -> ByteString
cons w bs = wrap_ (Internal.ghcConsDSL' (getPS bs) w)

snoc :: ByteString -> Word8 -> ByteString
snoc (PS x s l) c = error "NYI"


head :: ByteString -> Word8
head (PS x s l) = error "NYI"

tail :: ByteString -> ByteString
tail (PS p s l) = error "NYI"

uncons :: ByteString -> Maybe (Word8, ByteString)
uncons bs =
    let (bs', mres) = Internal.ghcUnconsDSL' (getPS bs) in
    fmap (, BPS bs' Nothing) mres

last :: ByteString -> Word8
last ps@(PS x s l) = error "NYI"

init :: ByteString -> ByteString
init ps@(PS p s l) = error "NYI"

unsnoc :: ByteString -> Maybe (ByteString, Word8)
unsnoc (PS x s l) = error "NYI"

append :: ByteString -> ByteString -> ByteString
append bs1 bs2 = wrap_ (Internal.ghcAppendDSL' (getPS bs1) (getPS bs2))


map :: (Word8 -> Word8) -> ByteString -> ByteString
map f (PS fp s len) = error "NYI"

reverse :: ByteString -> ByteString
reverse (PS x s l) = error "NYI"

intersperse :: Word8 -> ByteString -> ByteString
intersperse c ps@(PS x s l) = error "NYI"

transpose :: [ByteString] -> [ByteString]
transpose ps = error "NYI"

foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl f z (PS fp off len) = error "NYI"

foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' f v (PS fp off len) = error "NYI"

foldr :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr k z (PS fp off len) = error "NYI"

foldr' :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr' k v (PS fp off len) = error "NYI"

foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 f ps = error "NYI"

foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' f ps = error "NYI"

foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1 f ps = error "NYI"

foldr1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1' f ps = error "NYI"

concat :: [ByteString] -> ByteString
concat = error "NYI"

concatMap :: (Word8 -> ByteString) -> ByteString -> ByteString
concatMap f = error "NYI"


any :: (Word8 -> Bool) -> ByteString -> Bool
any f (PS x s l) = error "NYI"

all :: (Word8 -> Bool) -> ByteString -> Bool
all f (PS x s l) = error "NYI"

maximum :: ByteString -> Word8
maximum xs@(PS x s l) = error "NYI"

minimum :: ByteString -> Word8
minimum xs@(PS x s l) = error "NYI"

mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL f acc (PS fp o len) = error "NYI"

mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f acc (PS fp o len) = error "NYI"


scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanl f v (PS fp s len) = error "NYI"

scanl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanl1 f ps = error "NYI"

scanr :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanr f v (PS fp s len) = error "NYI"

scanr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanr1 f ps = error "NYI"

replicate :: Int -> Word8 -> ByteString
replicate w c = error "NYI"

unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
unfoldr f = error "NYI"

unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
unfoldrN i f x0 = error "NYI"

take :: Int -> ByteString -> ByteString
take n ps@(PS x s l) = error "NYI"

drop  :: Int -> ByteString -> ByteString
drop n ps@(PS x s l) = error "NYI"

splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt n ps@(PS x s l) = error "NYI"

takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhile f ps = error "NYI"

dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile f ps = error "NYI"


break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
break p ps = error "NYI"


breakByte :: Word8 -> ByteString -> (ByteString, ByteString)
breakByte c p = error "NYI"

breakEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd  p ps = error "NYI"

span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
span p ps = error "NYI"

spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
spanByte c ps@(PS x s l) = error "NYI"

spanEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd  p ps = error "NYI"

splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]
splitWith pred_ (PS fp off len) = error "NYI"

split :: Word8 -> ByteString -> [ByteString]
split w (PS x s l) = error "NYI"

group :: ByteString -> [ByteString]
group xs = error "NYI"

groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy k xs = error "NYI"

intercalate :: ByteString -> [ByteString] -> ByteString
intercalate s = error "NYI"


intercalateWithByte :: Word8 -> ByteString -> ByteString -> ByteString
intercalateWithByte c f@(PS ffp s l) g@(PS fgp t m) = error "NYI"

index :: ByteString -> Int -> Word8
index ps n = error "NYI"

elemIndex :: Word8 -> ByteString -> Maybe Int
elemIndex c (PS x s l) = error "NYI"

elemIndexEnd :: Word8 -> ByteString -> Maybe Int
elemIndexEnd ch (PS x s l) = error "NYI"

elemIndices :: Word8 -> ByteString -> [Int]
elemIndices w (PS x s l) = error "NYI"

count :: Word8 -> ByteString -> Int
count w (PS x s m) = error "NYI"

findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
findIndex k (PS x s l) = error "NYI"

findIndices :: (Word8 -> Bool) -> ByteString -> [Int]
findIndices p ps = error "NYI"

elem :: Word8 -> ByteString -> Bool
elem c ps = error "NYI"

notElem :: Word8 -> ByteString -> Bool
notElem c ps = error "NYI"

filter :: (Word8 -> Bool) -> ByteString -> ByteString
filter k ps@(PS x s l) = error "NYI"

find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
find f p = error "NYI"

partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
partition f s = error "NYI"

isPrefixOf :: ByteString -> ByteString -> Bool
isPrefixOf (PS x1 s1 l1) (PS x2 s2 l2) = error "NYI"

stripPrefix :: ByteString -> ByteString -> Maybe ByteString
stripPrefix bs1@(PS _ _ l1) bs2 = error "NYI"

isSuffixOf :: ByteString -> ByteString -> Bool
isSuffixOf (PS x1 s1 l1) (PS x2 s2 l2) = error "NYI"

stripSuffix :: ByteString -> ByteString -> Maybe ByteString
stripSuffix bs1@(PS _ _ l1) bs2@(PS _ _ l2) = error "NYI"

isInfixOf :: ByteString -> ByteString -> Bool
isInfixOf p s = error "NYI"

breakSubstring :: ByteString -- ^ String to search for
               -> ByteString -- ^ String to search in
               -> (ByteString,ByteString) -- ^ Head and tail of string broken at substring
breakSubstring pat = error "NYI"

findSubstring :: ByteString -- ^ String to search for.
              -> ByteString -- ^ String to seach in.
              -> Maybe Int
findSubstring pat src = error "NYI"

findSubstrings :: ByteString -- ^ String to search for.
               -> ByteString -- ^ String to seach in.
               -> [Int]
findSubstrings pat src = error "NYI"


zip :: ByteString -> ByteString -> [(Word8,Word8)]
zip ps qs = error "NYI"

zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
zipWith f ps qs = error "NYI"

zipWith' :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString
zipWith' f (PS fp s l) (PS fq t m) = error "NYI"

unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
unzip ls = error "NYI"


inits :: ByteString -> [ByteString]
inits (PS x s l) = error "NYI"

tails :: ByteString -> [ByteString]
tails p = error "NYI"


sort :: ByteString -> ByteString
sort (PS input s l) = error "NYI"

useAsCString :: ByteString -> (CString -> IO a) -> IO a
useAsCString (PS fp o l) action = error "NYI"

useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
useAsCStringLen p@(PS _ _ l) f = error "NYI"


packCString :: CString -> IO ByteString
packCString cstr = error "NYI"

packCStringLen :: CStringLen -> IO ByteString
packCStringLen (cstr, len) = error "NYI"


copy :: ByteString -> ByteString
copy (PS x s l) = error "NYI"

getLine :: IO ByteString
getLine = error "NYI"


hGetLine :: Handle -> IO ByteString
hGetLine h = error "NYI"

mkPS :: RawBuffer Word8 -> Int -> Int -> IO ByteString
mkPS buf start end = error "NYI"

mkBigPS :: Int -> [ByteString] -> IO ByteString
mkBigPS _ pss = error "NYI"


hPut :: Handle -> ByteString -> IO ()
hPut h (PS ps s l) = error "NYI"

hPutNonBlocking :: Handle -> ByteString -> IO ByteString
hPutNonBlocking h bs@(PS ps s l) = error "NYI"

hPutStr :: Handle -> ByteString -> IO ()
hPutStr = error "NYI"

hPutStrLn :: Handle -> ByteString -> IO ()
hPutStrLn h ps = error "NYI"

putStr :: ByteString -> IO ()
putStr = error "NYI"

putStrLn :: ByteString -> IO ()
putStrLn = error "NYI"

hGet :: Handle -> Int -> IO ByteString
hGet h i = error "NYI"

hGetNonBlocking :: Handle -> Int -> IO ByteString
hGetNonBlocking h i = error "NYI"

hGetSome :: Handle -> Int -> IO ByteString
hGetSome hh i = error "NYI"

illegalBufferSize :: Handle -> String -> Int -> IO a
illegalBufferSize handle fn sz = error "NYI"

hGetContents :: Handle -> IO ByteString
hGetContents hnd = error "NYI"

hGetContentsSizeHint :: Handle
                     -> Int -- ^ first read size
                     -> Int -- ^ initial buffer size increment
                     -> IO ByteString
hGetContentsSizeHint hnd = error "NYI"

getContents :: IO ByteString
getContents = error "NYI"

interact :: (ByteString -> ByteString) -> IO ()
interact transformer = error "NYI"

readFile :: FilePath -> IO ByteString
readFile f = error "NYI"

writeFile :: FilePath -> ByteString -> IO ()
writeFile f txt = error "NYI"

appendFile :: FilePath -> ByteString -> IO ()
appendFile f txt = error "NYI"

findIndexOrEnd :: (Word8 -> Bool) -> ByteString -> Int
findIndexOrEnd k (PS x s l) = error "NYI"

errorEmptyList :: String -> a
errorEmptyList fun = error "NYI"

moduleError :: String -> String -> a
moduleError fun msg = error "NYI"

moduleErrorIO :: String -> String -> IO a
moduleErrorIO fun msg = error "NYI"

moduleErrorMsg :: String -> String -> String
moduleErrorMsg fun msg = error "NYI"

findFromEndUntil :: (Word8 -> Bool) -> ByteString -> Int
findFromEndUntil f ps@(PS x s l) = error "NYI"
