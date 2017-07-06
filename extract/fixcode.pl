#!/usr/bin/env perl

$imports = <<'END_IMPORTS';
import qualified Data.ByteString.Fiat.HString as HString
import qualified Data.Char
import qualified Data.Function
import qualified Data.List
import qualified Data.Maybe
import qualified Data.Ratio
import qualified Data.Word
import qualified Foreign.ForeignPtr
import qualified Foreign.ForeignPtr.Unsafe
import qualified Foreign.Marshal.Alloc
import qualified Foreign.Marshal.Array
import qualified Foreign.Marshal.Utils
import qualified Foreign.Ptr
import qualified Foreign.Storable
import qualified GHC.Real
import qualified GHC.ForeignPtr
import qualified Prelude
import qualified System.IO.Unsafe
END_IMPORTS

while (<>) {
    s/import qualified Prelude/$imports/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/'\\000'/0/g;

    next if /^ghcDenote ::/ .. /^$/;
    next if /^heapCanonical0 ::/ .. /^$/;
    next if /^byteStringHeap0 ::/ .. /^$/;
    next if /^compare3 ::/ .. /^$/;
    next if /^within_bool ::/ .. /^$/;
    next if /^within_bool0 ::/ .. /^$/;
    next if /^fits_bool ::/ .. /^$/;
    next if /^fits_bool0 ::/ .. /^$/;
    next if /^overlaps_bool ::/ .. /^$/;
    next if /^overlaps_bool0 ::/ .. /^$/;
    next if /^keep_range ::/ .. /^$/;
    next if /^keep_range0 ::/ .. /^$/;
    next if /^drop_range ::/ .. /^$/;
    next if /^drop_range0 ::/ .. /^$/;
    next if /^copy_bytes ::/ .. /^$/;
    next if /^copy_bytes0 ::/ .. /^$/;
    next if /^load_into_map ::/ .. /^$/;
    next if /^load_into_map0 ::/ .. /^$/;
    next if /^heapSpec ::/ .. /^$/;
    next if /^heapSpec0 ::/ .. /^$/;
    next if /^heapCanonical ::/ .. /^$/;
    next if /^byteStringSpec ::/ .. /^$/;
    next if /^byteStringHeap ::/ .. /^$/;
    next if /^byteStringCanonical ::/ .. /^$/;
    next if /^buffer_to_list ::/ .. /^$/;
    next if /^buffer_to_list0 ::/ .. /^$/;

    next if /^emptyBS ::/ .. /^$/;
    next if /^packBS ::/ .. /^$/;
    next if /^unpackBS ::/ .. /^$/;
    next if /^consBS ::/ .. /^$/;
    next if /^unconsBS ::/ .. /^$/;
    next if /^appendBS ::/ .. /^$/;

    next if /^emptyDSL ::/ .. /^$/;
    next if /^ghcEmptyDSL ::/ .. /^$/;
    next if /^packDSL ::/ .. /^$/;
    next if /^ghcPackDSL ::/ .. /^$/;
    next if /^unpackDSL ::/ .. /^$/;
    next if /^ghcUnpackDSL ::/ .. /^$/;
    next if /^consDSL ::/ .. /^$/;
    next if /^ghcConsDSL ::/ .. /^$/;
    next if /^unconsDSL ::/ .. /^$/;
    next if /^ghcUnconsDSL ::/ .. /^$/;
    next if /^appendDSL ::/ .. /^$/;
    next if /^ghcAppendDSL ::/ .. /^$/;

    print;
}
