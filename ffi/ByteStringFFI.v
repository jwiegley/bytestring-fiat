(** This is the code we intend to approximate with the FFI refined version of
    ByteString:

  import Data.Word8
  import GHC.ForeignPtr
  import GHC.IO

  data ByteString = PS {-# UNPACK #-} !(ForeignPtr Word8) -- payload
                       {-# UNPACK #-} !Int                -- offset
                       {-# UNPACK #-} !Int                -- length
      deriving (Typeable)

  {--[ cons ]---------------------------------------------------------------}

  mallocByteString :: Int -> IO (ForeignPtr a)
  mallocByteString l = GHC.mallocPlainForeignPtrBytes l

  create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
  create l f = do
      fp <- mallocByteString l
      withForeignPtr fp $ \p -> f p
      return $! PS fp 0 l

  unsafeCreate :: Int -> (Ptr Word8 -> IO ()) -> ByteString
  unsafeCreate l f = unsafeDupablePerformIO (create l f)

  foreign import ccall unsafe "string.h memcpy" c_memcpy
      :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)

  memcpy :: Ptr Word8 -> Ptr Word8 -> Int -> IO ()
  memcpy p q s = c_memcpy p q (fromIntegral s) >> return ()

  cons :: Word8 -> ByteString -> ByteString
  cons c (PS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
          poke p c
          memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)

  {--[ uncons ]-------------------------------------------------------------}

  accursedUnutterablePerformIO :: IO a -> a
  accursedUnutterablePerformIO (IO m) = case m realWorld# of (# _, r #) -> r

  uncons :: ByteString -> Maybe (Word8, ByteString)
  uncons (PS x s l)
      | l <= 0    = Nothing
      | otherwise = Just (accursedUnutterablePerformIO $ withForeignPtr x
                                                       $ \p -> peekByteOff p s,
                          PS x (s+1) (l-1))
*)