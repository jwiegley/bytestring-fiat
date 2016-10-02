all: result/bin/bytestring-fiat

result/bin/bytestring-fiat: ByteStringExt.hs	\
	HString.hs				\
	Main.hs					\
	Setup.hs				\
	default.nix				\
	bytestring-fiat.cabal
	nix-build -E 'let pkgs = import <nixpkgs> {}; in pkgs.stdenv.lib.callPackageWith (pkgs // pkgs.haskell.packages.ghc801) ./default.nix {}'

ByteStringExt.hs: Makefile.coq			\
	ByteStringExt.v				\
	fixcode.pl
	make -f Makefile.coq && perl -i fixcode.pl $@

Makefile.coq: ../_CoqProject
	coq_makefile -f $< -o $@

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f *.glob *.v.d *.vo *.hi *.o Main result *.hp .*.aux
	rm -f bytestring-fiat ByteStringExt.hs
